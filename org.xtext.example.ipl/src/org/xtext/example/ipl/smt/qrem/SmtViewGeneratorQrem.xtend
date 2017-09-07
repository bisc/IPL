package org.xtext.example.ipl.smt.qrem

import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import org.eclipse.xtext.resource.IEObjectDescription
import org.osate.aadl2.AadlPackage
import org.osate.aadl2.BooleanLiteral
import org.osate.aadl2.ComponentImplementation
import org.osate.aadl2.IntegerLiteral
import org.osate.aadl2.PropertySet
import org.osate.aadl2.RealLiteral
import org.osate.aadl2.SubprogramGroupImplementation
import org.osate.aadl2.SubprogramImplementation
import org.osate.aadl2.instance.ComponentInstance
import org.osate.aadl2.instance.util.InstanceUtil
import org.osate.aadl2.instantiation.InstantiateModel
import org.osate.aadl2.modelsupport.resources.OsateResourceUtil
import org.osate.aadl2.properties.PropertyNotPresentException
import org.osate.xtext.aadl2.properties.util.EMFIndexRetrieval
import org.osate.xtext.aadl2.properties.util.PropertyUtils
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ViewDecl
import org.xtext.example.ipl.interfaces.SmtViewGenerator
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.util.TimeRec
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType

import static java.lang.Math.toIntExact

import static extension org.eclipse.xtext.EcoreUtil2.*

class SmtViewGeneratorQrem implements SmtViewGenerator {

	// to not run background generation every time when looking for models
	private var viewGenerated = false

	// storage for component properties and their types; <prop name , prop type> -> (archelem index -> prop value)
	// faces externally  
	private var Map<String, Map<Integer, Object>> propValueMap = new HashMap
	private var Map<String, IPLType> propTypeMap = new HashMap

	// generates a preamble and AADL SMT; does not touch IPL formulas 
	override public def String generateViewSmt(IPLSpec spec) {
		TimeRec::startTimer("generateBackgroundSmt")

		val preamble = '''
(set-logic ALL)
(set-option :produce-models true)
(set-option :model_evaluator.completion true)

'''
//(assert (= (abs_int (- 1)) 1)) - how to write it for cvc4
//(assert (= (abs_int -1) 1)) - how to write it for z3
		val pluginTerms = '''
(define-fun abs_int ((_arg Int)) Int (ite (>= _arg 0) _arg (- _arg)))
(define-fun abs_real ((_arg Real)) Real (ite (>= _arg 0) _arg (- _arg)))

'''

		// gather view declarations
		val viewDecs = spec.eAllOfType(ViewDecl)

		if (viewDecs.size == 0)
			return preamble

		val compMap = new HashMap<String, List<Integer>>
		propTypeMap = new HashMap<String, IPLType>
		propValueMap = new HashMap<String, Map<Integer, Object>>
		val subCompMap = new HashMap<Integer, List<Integer>>

		// parse aadl structures to prep for smt generation
		viewDecs.forEach [ viewDecl |
			populateAadlSmtStructures(viewDecl.ref, compMap, subCompMap)
		]

		viewGenerated = true
		println("Done populating AADL SMT")

		// generate aadl->smt 
		var decls = "(define-sort ArchElem () Int)\n"
		decls += compMap.keySet.map['(declare-fun ' + it + '(ArchElem) Bool)'].join('\n')

		val defns = compMap.entrySet.map [
			if (value.
				empty) '''(assert (forall ((x ArchElem)) (= («key» x) false)))''' else '''(assert (forall ((x ArchElem)) (= («key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR») )))'''
		].join('\n')

		val props = propTypeMap.keySet.map [
			'(declare-fun ' + it + ' (ArchElem) ' + IPLUtils::typesIPL2Smt(propTypeMap.get(it)) + ')\n'
		].join + '\n' + propValueMap.keySet.map [ name |
			propValueMap.get(name).entrySet.map['(assert (= (' + name + ' ' + key + ') ' + value + '))\n'].join
		].join

		var subComps = '(declare-fun isSubcomponentOf (ArchElem ArchElem) Bool)\n'
		subComps += subCompMap.entrySet.map [
			'''(assert (forall ((x ArchElem)) (= (isSubcomponentOf «key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR»))))'''
		].join('\n')

		println("Done generating AADL SMT")

		TimeRec::stopTimer("generateBackgroundSmt")
		// background generation output
		'''; Preamble
«preamble»
; Plugin terms
«pluginTerms»

; Arch elements
«decls»

«defns»
		
; Properties and subcomponents
«props»

; Subcomponents
«subComps»

		'''
	}

	override public def boolean isViewGenerated() {
		viewGenerated
	}

	// product of background generation; resets it itself
	override public def Map getPropTypeMap() {
		propTypeMap
	}

	// same
	override public def Map getPropValueMap() {
		propValueMap
	}

	private def populateAadlSmtStructures(ComponentImplementation comp, Map<String, List<Integer>> typeMap,
		Map<Integer, List<Integer>> subCompMap) {

		if (comp instanceof SubprogramImplementation || comp instanceof SubprogramGroupImplementation) {
			// Fail...
			throw new RuntimeException("Can't instantiate subprogram")
		}

		// instantiate aadl model
		val inst = InstantiateModel::buildInstanceModelFile(comp)
		val cic = new ComponentIndexCache
		// find a package and get all property set imports 
		val AadlPackage cont = comp.getContainerOfType(AadlPackage)
		val pss = cont.ownedPublicSection.importedUnits.filter [
			it instanceof PropertySet
		].toList as List // up-casting to make the function swallow this list
		inst.allComponentInstances.forEach[populateComponentInst(it, typeMap, cic, subCompMap, pss)]
	}

	private def populateComponentInst(ComponentInstance comp, Map<String, List<Integer>> map, ComponentIndexCache cic,
		Map<Integer, List<Integer>> subCompMap, List<PropertySet> propsets) {

		val index = cic.indexForComp(comp)

		// System::out.println(index + ") " + comp.category.toString + ': ' + InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended + ' ' + comp.name)
		map.add('isArchElem', index)
		map.add('is' + comp.category.toString.toFirstUpper, index)
		InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended.forEach[map.add('is' + name, index)]

		val ci = InstanceUtil::getComponentImplementation(comp, 0, null)
		if (ci !== null) {
			map.add('is' + ci.name.replace('.', '_'), index)
		}

		// handling subcomponents
		comp.children.forEach [
			switch (it) {
				ComponentInstance: {
					val scIndex = cic.indexForComp(it)
					propTypeMap.put(name, new ComponentType('EMPTY'))

					if (propValueMap.get(name) === null)
						propValueMap.put(name, new HashMap)

					propValueMap.get(name).put(index, scIndex)

					// propMap.add(new Pair(name,  as IPLType/*tp.typeOf(comp) -- cannot handle systemInstance yet*/), 
					// index, scIndex.toString
					subCompMap.add(index, scIndex)
				}
			}
		]

		// handling properties more parsimoniously
		for (ps : propsets)
			for (prop : ps.ownedProperties) { // each property
				if (comp.acceptsProperty(prop)) { // if accepts, add to the map
					val type = IPLUtils::typeFromPropType(prop)
					if (type !== null) {
						val propExp = try {
								PropertyUtils::getSimplePropertyValue(comp, prop)
							} catch (PropertyNotPresentException e) {
								null
							}

						// have to go through this dance because otherwise does not get cast
						val value = switch propExp {
							BooleanLiteral: propExp.getValue()
							IntegerLiteral: toIntExact(propExp.getValue()) // it returns long
							RealLiteral: propExp.getValue()
							default: null
						}

						if (value !== null) {
							propTypeMap.put(prop.name, type)
							if (propValueMap.get(prop.name) === null)
								propValueMap.put(prop.name, new HashMap)

							propValueMap.get(prop.name).put(index, value)
						}
					}
				}
			}
	}

	static class ComponentIndexCache {
		var next = 0
		val map = new HashMap<ComponentInstance, Integer>

		def indexForComp(ComponentInstance comp) {
			val entry = map.get(comp)
			if (entry === null) {
				map.put(comp, next)
				next++
			} else {
				entry
			}
		}

	}

	private def <K, V> add(Map<K, List<V>> map, K key, V item) {
		if (map.get(key) === null) {
			map.put(key, new ArrayList<V>)
		}

		map.get(key).add(item)
	}

}
