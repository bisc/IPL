package org.xtext.example.ipl.generator

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import org.eclipse.xtext.resource.IEObjectDescription
import org.osate.aadl2.AadlBoolean
import org.osate.aadl2.AadlInteger
import org.osate.aadl2.AadlReal
import org.osate.aadl2.BooleanLiteral
import org.osate.aadl2.ComponentImplementation
import org.osate.aadl2.IntegerLiteral
import org.osate.aadl2.Property
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
import org.xtext.example.ipl.IPLConfig
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Expression
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Lst
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.ViewDecl
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IPLTypeProvider
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

import static extension org.eclipse.xtext.EcoreUtil2.*

class SmtGenerator {

	private val tp = new IPLTypeProvider

	// state for formula part
	// all quantified variables: name, type
	private var Map<String, IPLType> scopeDecls = new HashMap

	// flexible "variables"
	private var Map<String, IPLType> flexDecls = new HashMap // type details of flex "variables"; flexName -> flexVarType
	private var Map<String, List<String>> flexArgs = new HashMap // argument names of flex clauses; flexName -> <varName>
	private var Map<String, ModelExpr> flexClauses = new HashMap // mapping between clauses and var names; flexName -> <IPL lang elem>
	private var flexNum = 0

	// probes for finding model values	
	private var Map<String, String> probingClauses = new HashMap

	// blocking clauses for finding model values; set externally
	private var List<Map<String, Object>> blockingValues = new ArrayList

	// anonymous sets encoded as functions
	private var setDecls = ""
	private var anonSetNum = 0

	// generates a preamble and AADL SMT; does not touch IPL formulas 
	public def String generateBackgroundSmt(IPLSpec spec) {

		setDecls = ""
		anonSetNum = 0

		val preamble = '''(set-logic ALL)
(set-option :produce-models true)
(set-option :model_evaluator.completion true)

'''

		// gather view declarations
		val viewDecs = spec.eAllOfType(ViewDecl)

		if (viewDecs.size == 0)
			return preamble

		val compMap = new HashMap<String, List<Integer>>
		val propMap = new HashMap<Pair<String, String>, HashMap<Integer, String>>
		val subCompMap = new HashMap<Integer, List<Integer>>

		// parse aadl structures to prep for smt generation
		viewDecs.forEach [ viewDecl |
			populateAadlSmtStructures(viewDecl.ref, compMap, propMap, subCompMap)
		]

		println("Done populating AADL SMT")

		// generate aadl->smt 
		var decls = "(define-sort ArchElem () Int)\n"
		decls += compMap.keySet.map['(declare-fun ' + it + '(ArchElem) Bool)'].join('\n')

		val defns = compMap.entrySet.map [
			if (value.
				empty) '''(assert (forall ((x ArchElem)) (= («key» x) false)))''' else '''(assert (forall ((x ArchElem)) (= («key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR») )))'''
		].join('\n')

		val props = propMap.keySet.map['(declare-fun ' + it.key + ' (ArchElem) ' + it.value + ')\n'].join + '\n' +
			propMap.entrySet.map [
				val name = key.key
				value.entrySet.map['(assert (= (' + name + ' ' + key + ') ' + value + '))\n'].join
			].join

		var subComps = '(declare-fun isSubcomponentOf (ArchElem ArchElem) Bool)\n'
		subComps += subCompMap.entrySet.map [
			'''(assert (forall ((x ArchElem)) (= (isSubcomponentOf «key» x) (or«FOR elem : value» (= x «elem»)«ENDFOR»))))'''
		].join('\n')

		println("Done generating AADL SMT")

		// final output
		'''	«preamble»
			
			; Arch elements
			«decls»
			
			«defns»
					
			; Properties and subcomponents
			«props»
			
			; Subcomponents
			«subComps»
			
		'''
	}

	public def String generateSmtFormula(Formula f) {
		reset

		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
		«if (setDecls.length > 0)
			'''; Anonymous sets
				«setDecls» '''»
		
		(assert «formulaStr»)'''
	}

	public def String generateSmtFormulaNeg(Formula f) {
		reset

		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
		«if (setDecls.length > 0)
			'''; Anonymous sets
«setDecls» '''»
		
		«if (IPLConfig.ENABLE_PROBING_VARS) 
			'''«scopeDecls.keySet.map['(declare-const ' + probe(it) +' '
					+ typesIPL2Smt(scopeDecls.get(it))+')'
			].join('\n')»'''»
		
		«probingClauses.values.join('\n')»
		
		(assert (not «formulaStr»))'''
	}

	public def String generateSmtFlexDecl() {
		if (IPLConfig.ENABLE_FLEXIBLE_ABSTRACTION_WITH_ARGS) // with args
			flexDecls.keySet.map [
				'''(declare-fun «it» («flexArgs.get(it).map[typesIPL2Smt(scopeDecls.get(it))].join(' ')») ''' +
					'''«switch (flexDecls.get(it)) { IntType: "Int" RealType: "Real" BoolType: "Bool" }»)'''
			].join('\n') + '\n'
		else // no args
			flexDecls.keySet.map [
				'''(declare-const «it» «switch (flexDecls.get(it)) { IntType: "Int" RealType: "Real" BoolType: "Bool" }»)'''
			].join('\n') + '\n'
	}

	public def setBlockingValues(List<Map<String, Object>> blocks) {
		blockingValues = blocks
	}

	// returns the scope declaration
	// won't clear it later
	public def getLastFormulaScopeDecls() {
		scopeDecls
	}

	// won't clear it later
	public def getLastFormulaFlexDecls() {
		flexDecls
	}

	// won't clear it later
	public def getLastFormulaFlexClauses() {
		flexClauses
	}

	/*public def String getLastFormulaScopeEvals(){
	 * 	scope.map[ v | '''(eval «v.key»)'''].join('\n')
	 }*/
	// === RIGID GENERATION FUNCTIONS ===
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

	private def dispatch String generateFormula(Lst f) {
		// TODO: implement
	}

	private def dispatch String generateFormula(QAtom q) {

		val varType = (tp.typeOf(q.set) as SetType).elemType;
		scopeDecls.put(q.^var, varType)

		val quant = if(q.op == 'forall' || q.op == 'A') 'forall' else 'exists'
		// forall comes with implication, exists with conjunction
		val quantOp = if(quant == 'forall') '=>' else 'and'

		// switching on the set member type
		switch (varType) {
			ComponentType: // TODO implement blocking for components
			'''(«quant» ((«q.^var» ArchElem)) («quantOp» («'is' + (varType as ComponentType)
				.name.replace('.', '_')» «q.^var») «generateFormula(q.exp)»))'''
			IntType,
			RealType,
			BoolType: {
				val setMbFunName = generateAnonSet(q.set);
				val z3TypeName = switch (varType) { IntType: "Int" RealType: "Real" BoolType: "Bool" }

				// probing constraint - set
				if (IPLConfig.ENABLE_PROBING_VARS) {
					probingClauses.put(probe(q.^var), '''(assert («setMbFunName» «probe(q.^var)»))''')
				}

				// do blocking for this variable if needed
				var blockingClauses = ''
				blockingClauses = blockingValues.map [ nameValueMap |
					if (nameValueMap.containsKey(q.^var)) {
						if (IPLConfig.ENABLE_PROBING_VARS) {
							probingClauses.put(probe(q.^var), probingClauses.get(probe(q.^var)) + '''
							
							(assert (distinct «probe(q.^var)» «nameValueMap.get(q.^var)» ))''')
						}

						'''(distinct «q.^var» «nameValueMap.get(q.^var)» )'''
					} else
						''
				].join(' ')

				// the old way of doing blocking: 
				// if (blockingValues.get(q.^var) !== null)
//					 blockingClauses = blockingValues.get(q.^var).map['''(distinct «q.^var» «it» )'''].join(' ') // forEach[blockingClauses += it]	
				// actual quantified expression
				'''(«quant» ((«q.^var» «z3TypeName»)) («quantOp» (and («setMbFunName» «q.^var») «blockingClauses») 
						«generateFormula(q.exp)»))'''
			}
			default:
				'; Unimplemented set member type'
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
		// TODO: ArchElem support
		id.id
	}

	private def dispatch String generateFormula(Int i) {
		i.value.toString
	}

	private def dispatch String generateFormula(Real r) {
		r.value.toString
	}

	/*def dispatch String generateFormula(EDouble r) {
	 * 	r.toString
	 }*/
	private def dispatch String generateFormula(Bool b) {
		b.value.toString
	}

	// === FLEXIBLE GENERATION FUNCTIONS ===
	private def dispatch String generateFormula(ModelExpr mdex) {

		// poll downstream for type & generate an abstraction
		val String abst = switch(mdex.expr){
			ProbQuery:	createFlexAbstraction(new BoolType)
			RewardQuery:  createFlexAbstraction(new RealType)
			default:  throw new UnexpectedException('Unknown model formula') 
		}
		
		flexClauses.put(abst, mdex) 
		val args = flexArgs.get(abst)
		
		// generate smt for the abstraction
		// non-nullary functions need extra ( ) around them
		if (args !== null && args.length > 0)
			'''(«abst» «args.map[it].join(' ')»)'''
		else
			abst
	}

	/*private def dispatch String generateFormula(ProbQuery pq) {
		throw new UnexpectedException('Was not supposed to reach here')
	}

	private def dispatch String generateFormula(RewardQuery pq) {
		throw new UnexpectedException('Was not supposed to reach here')
	}*/

	// === HELPER FUNCTIONS === 
	
	private def String probe(String varName) {
		varName + '_probe'
	}

	private def String createFlexAbstraction(IPLType type) {

		if (IPLConfig.ENABLE_FLEXIBLE_ABSTRACTION_WITH_ARGS) {
			val String name = '''_flex«flexNum++»'''
			flexDecls.put(name, type)

			flexArgs.put(name, new ArrayList)
			scopeDecls.forEach [ varName, varType |
				flexArgs.get(name).add(varName)
			]
			name
		} else {
			val String name = '''_flex«flexNum++»'''
			flexDecls.put(name, new BoolType)
			name
		}
	}

	// reset the formula parsing state
	private def reset() {
		// creating new ones to be independent from its clients
		scopeDecls = new HashMap//scopeDecls.clear
		flexDecls = new HashMap//flexDecls.clear
		flexClauses = new HashMap//flexClauses.clear
		
		flexArgs.clear
		flexNum = 0
		probingClauses.clear

		setDecls = ""
		anonSetNum = 0
	}

	// helper function to generate anonymous sets, returning membership f-n name
	private def String generateAnonSet(Expression set) {
		val elemType = (tp.typeOf(set) as SetType).elemType;

		val funName = '''anonSetMb«anonSetNum++»''';
		val z3TypeName = switch (elemType) { IntType: "Int" RealType: "Real" BoolType: "Bool" }

		// declaring an anonymous set	 
		setDecls += '''(define-fun «funName» ((_x «z3TypeName»)) Bool
		(or «(set as Set).members.map[ '''(= _x «generateFormula(it)»)'''].join(" ")»   
		) ) 
		''';
		funName
	}

	private def populateAadlSmtStructures(ComponentImplementation comp, Map<String, List<Integer>> typeMap,
		HashMap<Pair<String, String>, HashMap<Integer, String>> propMap, HashMap<Integer, List<Integer>> subCompMap) {

		if (comp instanceof SubprogramImplementation || comp instanceof SubprogramGroupImplementation) {
			// Fail...
			throw new RuntimeException("Can't instantiate subprogram")
		}

		val inst = InstantiateModel::buildInstanceModelFile(comp)
		val cic = new ComponentIndexCache

		inst.allComponentInstances.forEach[generateComponentInst(it, typeMap, cic, propMap, subCompMap)]
	}

	private def generateComponentInst(ComponentInstance comp, Map<String, List<Integer>> map, ComponentIndexCache cic,
		HashMap<Pair<String, String>, HashMap<Integer, String>> propMap, HashMap<Integer, List<Integer>> subCompMap) {

		val index = cic.indexForComp(comp)

		// System::out.println(index + ") " + comp.category.toString + ': ' + InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended + ' ' + comp.name)
		map.add('isArchElem', index)
		map.add('is' + comp.category.toString.toFirstUpper, index)
		InstanceUtil::getComponentType(comp, 0, null).selfPlusAllExtended.forEach[map.add('is' + name, index)]

		val ci = InstanceUtil::getComponentImplementation(comp, 0, null)
		if (ci !== null) {
			map.add('is' + ci.name.replace('.', '_'), index)
		}

		comp.children.forEach [
			switch (it) {
				ComponentInstance: {
					val scIndex = cic.indexForComp(it)
					propMap.add(new Pair(name, 'ArchElem'), index, scIndex.toString)
					subCompMap.add(index, scIndex)
				}
			}
		]

		for (IEObjectDescription ieo : EMFIndexRetrieval::getAllPropertySetsInWorkspace(
			comp.getComponentClassifier())) {

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

	private def String fromPropType(Property property) {
		switch (property.propertyType) {
			AadlBoolean: 'Bool'
			AadlInteger: 'Int'
			AadlReal: 'Real'
			default: null
		}
	}

	private def String typesIPL2Smt(IPLType t) {
		switch (t) {
			BoolType: 'Bool'
			IntType: 'Int'
			RealType: 'Real'
			default: 'UNKNOWN TYPE'
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

	/*static class Pair<T, U> {
	 * 	
	 * 	val T first
	 * 	val U second
	 * 	
	 * 	new(T first, U second) {
	 * 		this.first = first
	 * 		this.second = second
	 * 	}
	 * 	
	 * 	override equals(Object that) {
	 * 		switch (that) {
	 * 			Pair<T, U>: first == that.first && second == that.second
	 * 			default: false
	 * 		}
	 * 	}
	 * 	
	 * 	override hashCode() {
	 * 		37 * first.hashCode + second.hashCode
	 * 	}
	 * 	
	 * 	override toString() {
	 * 		'<' + first.toString + ', ' + second.toString + '>'
	 * 	}
	 }*/
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
