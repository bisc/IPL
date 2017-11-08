package org.xtext.example.ipl.smt.qrem

import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import java.util.Map.Entry
import org.osate.aadl2.AadlPackage
import org.osate.aadl2.BooleanLiteral
import org.osate.aadl2.ComponentImplementation
import org.osate.aadl2.IntegerLiteral
import org.osate.aadl2.ListValue
import org.osate.aadl2.PropertyExpression
import org.osate.aadl2.PropertySet
import org.osate.aadl2.RealLiteral
import org.osate.aadl2.SubprogramGroupImplementation
import org.osate.aadl2.SubprogramImplementation
import org.osate.aadl2.instance.ComponentInstance
import org.osate.aadl2.instance.InstanceReferenceValue
import org.osate.aadl2.instance.util.InstanceUtil
import org.osate.aadl2.instantiation.InstantiateModel
import org.osate.aadl2.properties.PropertyNotPresentException
import org.osate.xtext.aadl2.properties.util.PropertyUtils
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ViewDecl
import org.xtext.example.ipl.interfaces.SmtViewGenerator
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.util.TimeRecCPU
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.ListType

import static java.lang.Math.toIntExact

import static extension org.eclipse.xtext.EcoreUtil2.*

class SmtViewGeneratorQrem implements SmtViewGenerator {

	// to not run background generation every time when looking for models
	private var viewGenerated = false

	private val cic = new ComponentIndexCache
	// storage for component properties and their types; <prop name , prop type> -> (archelem index -> prop value)
	// faces externally  
	private var Map<String, Map<Integer, Object>> propValueMap = new HashMap
	private var Map<String, IPLType> propTypeMap = new HashMap

	// generates a preamble and AADL SMT; does not touch IPL formulas 
	override public def String generateViewSmt(IPLSpec spec) {
		TimeRecCPU::startTimer("generateBackgroundSmt")

		val preamble = '''
(set-logic ALL)
(set-option :produce-models true)
(set-option :model_evaluator.completion true)

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
		decls += compMap.keySet.map['''(declare-fun «it» (ArchElem) Bool)'''].join('\n')

		val defns = compMap.entrySet.map [
			if (value.
				empty) '''(assert (forall ((x ArchElem)) (= («key» x) false)))''' else '''(assert (forall ((x ArchElem)) (= («key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR») )))'''
		].join('\n')

		// properties: declarations & assertions
		// the code below is quite complex due to different types of values that properties might take
		val props = propTypeMap.keySet.map [ propName |
			val type = propTypeMap.get(propName)
			val Map propValues = propValueMap.get(propName) // propValues: map compIndex -> object 
			if (type instanceof ListType) { // list of something
			// lists are tricky to represent in SMT. Using 0-based arrays with an explicit length function for each array.
			// the length function needs to be universal, otherwise the containment function does not know what to call 
			// Alternative: implementing using an axiomatic recursive datatype proved to perform very poorly when trying to find if X in a list element
				val listSortName = propName + '_sort'
				val listLengthFn = 'length'
//				val listLengthFn = propName + '_length'
				// declaration of list type 
				'''(define-sort «listSortName» () (Array Int «IPLUtils::typesIPL2Smt(type.elemType)» ))''' + '\n' + 
				// declaration of the property 
				'''(declare-fun «propName» (ArchElem) «listSortName»)'''+ '\n' +
				// declaration of the length function: using not archelem, but directly the array -- 
				// TODO if this doesn't work, try the old one and put archelem in 
				'''(declare-fun «listLengthFn» ((Array Int «IPLUtils::typesIPL2Smt(type.elemType)»)) (Int))''' + '\n' +
//				'''(declare-fun «listLengthFn» (ArchElem) (Int))''' + '\n' +
				// assertions for each list (one per arch elem)
				propValues.entrySet.map [ Entry<Object, Object> indexListPair | /* key - compIndex, value - list of values */
					val int compIndex = indexListPair.key as Integer
					val List valueList = indexListPair.value as List<Object>
					// assertions for each list element's position and value
					valueList.map [ listElem |
						'''(assert (= (select («propName» «compIndex») «
							valueList.indexOf(listElem)») «listElem»))''' + '\n'
					].join + 
					// assertions of length for each list 
					'''(assert (= («listLengthFn» («propName» «compIndex»)) «valueList.size»))''' + '\n'
//					'''(assert (= («listLengthFn» «compIndex») «valueList.size»))''' + '\n'
				].join + '\n'
			} else { // simple type
				'''(declare-fun «propName» (ArchElem) «IPLUtils::typesIPL2Smt(type)»)''' + '\n' +
					propValues.entrySet.map [ Entry<Object, Object> pair | // key - compIndex, value - simple object
						'''(assert (= («propName» «pair.key») «pair.value»))''' + '\n' 
					].join
			} // TODO implement set type? 
		].join + '\n'

		var subComps = '(declare-fun isSubcomponentOf (ArchElem ArchElem) Bool)\n'
		subComps += subCompMap.entrySet.map [
			'''(assert (forall ((x ArchElem)) (= (isSubcomponentOf «key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR»))))'''
		].join('\n')

		// (assert (= (abs_int (- 1)) 1)) - how to write it for cvc4
		// (assert (= (abs_int -1) 1)) - how to write it for z3
		val pluginTerms = '''
(define-fun abs_int ((_arg Int)) Int (ite (>= _arg 0) _arg (- _arg)))
(define-fun abs_real ((_arg Real)) Real (ite (>= _arg 0) _arg (- _arg)))
(define-fun max_int ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun max_real ((x Real) (y Real)) Real (ite (< x y) y x))
(define-fun min_int ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun min_real((x Real) (y Real)) Real (ite (< x y) x y))
(define-fun list_contains_elem ((l (Array Int ArchElem)) (e ArchElem)) Bool 
	(exists ((i Int)) (and (>= i 0) (< i (length l)) (= (select l i) e))))
'''

		println("Done generating AADL SMT")

		TimeRecCPU::stopTimer("generateBackgroundSmt")
		// background generation output
		'''; Preamble
«preamble»

; Arch elements
«decls»

«defns»

; Properties and subcomponents
«props»

; Subcomponents
«subComps»

; Plugin terms
«pluginTerms»
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

		// find a package and get all property set imports 
		val AadlPackage cont = comp.getContainerOfType(AadlPackage)
		val pss = cont.ownedPublicSection.importedUnits.filter [
			it instanceof PropertySet
		].toList as List // up-casting to make the function swallow this list
		inst.allComponentInstances.forEach[populateComponentInst(it, typeMap, subCompMap, pss)]
	}

	private def populateComponentInst(ComponentInstance comp, Map<String, List<Integer>> map,
		Map<Integer, List<Integer>> subCompMap, List<PropertySet> propsets) {

		val compIndex = cic.indexForComp(comp)

//		println(compIndex + ") " + comp.category.toString + ': ' + InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended + ' ' + comp.name)
		map.add('isArchElem', compIndex)
		map.add('is' + comp.category.toString.toFirstUpper, compIndex)
		InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended.forEach[map.add('is' + name, compIndex)]

		val ci = InstanceUtil::getComponentImplementation(comp, 0, null)
		if (ci !== null) {
			map.add('is' + ci.name.replace('.', '_'), compIndex)
		}

		// handling subcomponents
		comp.children.forEach [
			switch (it) {
				ComponentInstance: {
					val scIndex = cic.indexForComp(it)
					propTypeMap.put(name, new ComponentType('SUBCOMP'))

					if (propValueMap.get(name) === null)
						propValueMap.put(name, new HashMap)

					propValueMap.get(name).put(compIndex, scIndex)

					// propMap.add(new Pair(name,  as IPLType/*tp.typeOf(comp) -- cannot handle systemInstance yet*/), 
					// index, scIndex.toString
					subCompMap.add(compIndex, scIndex)
				}
			}
		]

		// handling properties more parsimoniously
		for (ps : propsets)
			for (prop : ps.ownedProperties) { // each property
				if (comp.acceptsProperty(prop)) { // if accepts, add to the map
					val type = IPLUtils::typeFromPropType(prop.propertyType)
					if (type !== null) { // only considering the types we know 
						val value = if (type instanceof ListType) { // a list property type
								val ListValue listVal = try {
										val propExp = PropertyUtils::getSimplePropertyListValue(comp, prop)
										if(propExp instanceof ListValue) propExp else null
									} catch (PropertyNotPresentException e) {
										null
									}
								// TODO need to control that we don't add lots of nulls to lists
								if (listVal !== null) {
									val outputList = new ArrayList
									listVal.ownedListElements.forEach [
										outputList.add(aadlSimpleValue2Object(it))
									]
									outputList
								} else
									null

							} else { // a simple, non-list property 
								val PropertyExpression propExp = try {
										PropertyUtils::getSimplePropertyValue(comp, prop)
									} catch (PropertyNotPresentException e) {
										null
									}

								aadlSimpleValue2Object(propExp)
							}

						if (value !== null) {
							propTypeMap.put(prop.name, type)
							if (propValueMap.get(prop.name) === null)
								propValueMap.put(prop.name, new HashMap)

							propValueMap.get(prop.name).put(compIndex, value)
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

	// converts an AADL simple value into a Java object
	// assumes a populated component index cache for instance reference values
	private def aadlSimpleValue2Object(PropertyExpression propExp) {
		// have to go through this dance because otherwise does not get cast
		switch propExp {
			BooleanLiteral:
				propExp.getValue()
			IntegerLiteral:
				toIntExact(propExp.getValue()) // it returns long
			RealLiteral:
				propExp.getValue()
			InstanceReferenceValue: {
				// only deal with component instances
				val refObject = propExp.referencedInstanceObject
				if (refObject instanceof ComponentInstance)
					cic.indexForComp(refObject) // more concrete than just ReferenceValue
				else
					null
			}
			default:
				null
		}
	}

	private def <K, V> add(Map<K, List<V>> map, K key, V item) {
		if (map.get(key) === null) {
			map.put(key, new ArrayList<V>)
		}

		map.get(key).add(item)
	}

}
