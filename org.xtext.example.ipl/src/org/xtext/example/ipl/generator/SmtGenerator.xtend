package org.xtext.example.ipl.generator

import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import org.osate.aadl2.Property
import org.osate.aadl2.PropertySet
import org.eclipse.xtext.resource.IEObjectDescription
import org.osate.aadl2.AadlBoolean
import org.osate.aadl2.AadlInteger
import org.osate.aadl2.AadlReal
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
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Expression
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.ViewDec
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLTypeProvider
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

import static extension org.eclipse.xtext.EcoreUtil2.*
import static extension org.xtext.example.ipl.validation.IPLRigidityProvider.isRigid

class SmtGenerator {

	
	private var setDecls = ""
	private var anonSetNum = 0
	
	// does not touch IPL formulas 
	public def String generateBackgroundSmt(List<IPLSpec> specs) { 
		
		setDecls = ""
		anonSetNum = 0
		
		val compMap = new HashMap<String, List<Integer>>
		val propMap = new HashMap<Pair<String, String>, HashMap<Integer, String>>
		val subCompMap = new HashMap<Integer, List<Integer>>
		setDecls = ""
		anonSetNum = 0
		
		specs.forEach[ spec | spec.eAllOfType(ViewDec).forEach[ viewDec |
				generateAADLSMT(viewDec.ref, compMap, propMap, subCompMap)
			]
		]
		println("Done populating AADL SMT")
		
		val decls = compMap.keySet.map['(declare-fun ' + it + '(ArchElem) Bool)'].join('\n')
		
		val defns = compMap.entrySet.map[if (value.empty) '''(assert (forall ((x ArchElem)) (= («key» x) false)))''' else '''(assert (forall ((x ArchElem)) (= («key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR») )))'''].join('\n')
		
		val props = propMap.keySet.map['(declare-fun ' + first + ' (ArchElem) ' + second + ')\n'].join + '\n' +
			propMap.entrySet.map[ 
				val name = key.first
				value.entrySet.map['(assert (= (' + name + ' ' + key + ') ' + value + '))\n'].join
			].join
			
		val subComps = subCompMap.entrySet.map[
				'''(assert (forall ((x ArchElem)) (= (isSubcomponentOf «key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR»))))'''
		].join('\n')
		
		println("Done generating AADL SMT")
		
		'''
		(define-sort ArchElem () Int)
		
		; Anonymous sets
		«setDecls»
		
		; Components
		«decls»
		
		«defns»
		
		
		; Properties and subcomponents
		«props»
		
		; isSubcomponentOf
		(declare-fun isSubcomponentOf (ArchElem ArchElem) Bool)
		«subComps»
		
		'''
	}

	public def String generateSMTFormula(Formula f) { 
		if (f.rigid) {
			'(assert ' + generateFormula(f) + ')'
		} else {
			''
		}
	}
	
	public def String generateSMTFormulaNeg(Formula f) { 
		if (f.rigid) {
			'(assert (not ' + generateFormula(f) + '))'
		} else {
			''
		}
	}
	
	private def dispatch String generateFormula(FormulaOperation fop) {
		
		val op = if (fop.op == '&' || fop.op == '^') {
			'and'
		} else if (fop.op == '||' || fop.op == 'V') {
			'or'
		} else if (fop.op == '->') {
			'=>'
		} else {
			throw new RuntimeException
		}
		
		'''(«op» «generateFormula(fop.left)» «generateFormula(fop.right)»)'''
	}
	
	private def dispatch String generateFormula(Negation neg) {
		'''(not «generateFormula(neg.child)»)'''
	}
	
	private def dispatch String generateFormula(Set f) {
		generateAnonSet(f) // TODO: this will need to be augmented for membership-check functions
	}
	
	private def dispatch String generateFormula(QAtom q) {
		
		val tp = new IPLTypeProvider
		
		val varType = (tp.typeOf(q.set) as SetType).elemType;
		
		val quant = if (q.op == 'forall' || q.op == 'A') 'forall' else 'exists'
		val quantOp = if (quant == 'forall') '=>' else 'and' // forall with implication, exists with conjunction
		
		// switching on the set member type
		switch (varType) {
			ComponentType: '''(«quant» ((«q.^var» ArchElem)) («quantOp» («'is' + (varType as ComponentType).name.replace('.', '_')» «q.^var») «generateFormula(q.exp)»))'''
			IntType, RealType, BoolType: {
				val funName = generateAnonSet(q.set); 
				val z3TypeName = switch(varType) { IntType: "Int" RealType: "Real" BoolType:"Bool"	}
				
				// actual quantified expression
				'''(«quant» ((«q.^var» «z3TypeName»)) («quantOp» («funName» «q.^var») «generateFormula(q.exp)»))'''}
			default: '; Unimplemented set member type'
		}
	}
	
	private def dispatch String generateFormula(TermOperation top) {
	 	if (top.op == '!=') 
	 		'''(not (= «generateFormula(top.left)» «generateFormula(top.right)»))'''
	 	else
	 		'''(«top.op» «generateFormula(top.left)» «generateFormula(top.right)»)'''
	}
	
	private def dispatch String generateFormula(ExprOperation eop) {
	 	'''(«eop.op» «generateFormula(eop.left)» «generateFormula(eop.right)»)'''
	}
	
	private def dispatch String generateFormula(Fun f) {
		if (f.args.length > 0)
			'''(«f.name.name»«FOR arg : f.args» «generateFormula(arg)»«ENDFOR»)'''
		else
			'''(«f.name.name» ())'''
	}
	
	private def dispatch String generateFormula(PropertyExpression pe) {
		'''(«pe.right.id» «generateFormula(pe.left)»)'''
	}
	
	private def dispatch String generateFormula(ID id) {
		//TODO: ArchElem support
		id.id
	}
	
	private def dispatch String generateFormula(Int i) {
		i.value.toString
	}
	
	private def dispatch String generateFormula(Real r) {
		r.value.toString
	}
	
	/*def dispatch String generateFormula(EDouble r) {
		r.toString
	}*/
	
	private def dispatch String generateFormula(Bool b) {
		b.value.toString
	}
	

	private def generateAADLSMT(ComponentImplementation comp, Map<String, List<Integer>> typeMap, HashMap<Pair<String, String>, HashMap<Integer, String>> propMap, HashMap<Integer, List<Integer>> subCompMap) {
		
		if (comp instanceof SubprogramImplementation
			|| comp instanceof SubprogramGroupImplementation) {
			//Fail...
			throw new RuntimeException("Can't instantiate subprogram")			
		}
	
		val inst = InstantiateModel::buildInstanceModelFile(comp)
		val cic = new ComponentIndexCache
		
		inst.allComponentInstances.forEach[ generateComponentInst(it, typeMap, cic, propMap, subCompMap) ]
	}
	
	private def generateComponentInst(ComponentInstance comp, Map<String, List<Integer>> map, ComponentIndexCache cic, HashMap<Pair<String, String>, HashMap<Integer, String>> propMap, HashMap<Integer, List<Integer>> subCompMap) {
		
		val index = cic.indexForComp(comp)
		
		//System::out.println(index + ") " + comp.category.toString + ': ' + InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended + ' ' + comp.name)
		
		map.add('isArchElem', index)
		map.add('is' + comp.category.toString.toFirstUpper, index)
		InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended.forEach[map.add('is' + name, index)]
		
		val ci = InstanceUtil::getComponentImplementation(comp, 0, null)
		if (ci !== null) { 
			map.add('is' + ci.name.replace('.', '_'), index)
		}
		
		comp.children.forEach[
			switch (it) {
				ComponentInstance: {
					val scIndex = cic.indexForComp(it)
					propMap.add(new Pair(name, 'ArchElem'), index, scIndex.toString)
					subCompMap.add(index, scIndex)
				}
			}
		]
		
		for (IEObjectDescription ieo: EMFIndexRetrieval::getAllPropertySetsInWorkspace(comp.getComponentClassifier())) { 

			val ps = OsateResourceUtil.getResourceSet().getEObject(ieo.getEObjectURI(), true) as PropertySet;
			for (prop : ps.ownedProperties) {
				if (comp.acceptsProperty(prop)) {
					val type = fromPropType(prop)
					if (type !== null) {
						
						val propExp = try { 
							PropertyUtils::getSimplePropertyValue(comp, prop)
						} catch (PropertyNotPresentException e) {
							null
						}
						
						val value = switch propExp {
							BooleanLiteral: String::valueOf(propExp.getValue())
							IntegerLiteral: String::valueOf(propExp.getValue())
							RealLiteral: String::valueOf(propExp.getValue())
							default: null
						}
						
						if (value !== null) {
							propMap.add(new Pair(prop.name, type), index, value)
						}
					}
				}
			}
		}	
	}
	
	// helper function to generate anonymous sets, returning membership f-n name
	def String generateAnonSet(Expression set) { 
		val tp = new IPLTypeProvider
		val elemType =  (tp.typeOf(set) as SetType).elemType;
		
		val funName = '''anonSetMb«anonSetNum++»''';
		val z3TypeName = switch(elemType) { IntType: "Int" RealType: "Real" BoolType:"Bool"	}
		
		// declaring an anonymous set	 
		setDecls += '''(define-fun «funName» ((_x «z3TypeName»)) Bool
		(or «(set as Set).members.map[ '''(= _x «generateFormula(it)»)'''].join(" ")»   
		) ) 
		''';
		funName
	}
	
	private def String fromPropType(Property property) {
		switch (property.propertyType) {
			AadlBoolean: 'Bool'
			AadlInteger: 'Int'
			AadlReal: 'Real'
			default: null
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
	
	static class Pair<T, U> {
		
		val T first
		val U second
		
		new(T first, U second) {
			this.first = first
			this.second = second
		}
		
		override equals(Object that) {
			switch (that) {
				Pair<T, U>: first == that.first && second == that.second
				default: false
			}
		}
		
		override hashCode() {
			37 * first.hashCode + second.hashCode
		}
		
		override toString() {
			'<' + first.toString + ', ' + second.toString + '>'
		}
	}
	
		def <K, V> add(Map<K, List<V>> map, K key, V item) { 
		if (map.get(key) === null) {
			map.put(key, new ArrayList<V>)
		}
		
		map.get(key).add(item)	
	}
	
	def <K, L, V> add(Map<K, HashMap<L, V>> map, K key, L key2, V value) { 
		if (map.get(key) === null) {
			map.put(key, new HashMap<L, V>)
		}
		
		map.get(key).put(key2, value)
	}
	
	
}