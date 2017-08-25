package org.xtext.example.ipl.smt.herbrand

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import org.eclipse.emf.ecore.util.EcoreUtil
import org.eclipse.xtext.resource.IEObjectDescription
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
import org.xtext.example.ipl.IPLConfig
import org.xtext.example.ipl.TimeRec
import org.xtext.example.ipl.Utils
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
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermFormula
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.ViewDecl
import org.xtext.example.ipl.transform.ProbeTransformer
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IPLTypeProvider
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

import static java.lang.Math.toIntExact

import static extension org.eclipse.emf.ecore.util.EcoreUtil.*
import static extension org.eclipse.xtext.EcoreUtil2.*
import org.xtext.example.ipl.interfaces.SmtFormulaGenerator

// implementation of generation by mapping ArchElem -> Int
class SmtFormulaGeneratorHerbrand implements SmtFormulaGenerator {

	private val tp = new IPLTypeProvider

	// state for formula part
	// all quantified variables: name, type
	private var Map<String, IPLType> scopeDecls = new HashMap

	// for flexible "variables"
	// type details of flex "variables"; flexName -> flexVarType
	private var Map<String, IPLType> flexDecls = new HashMap 
	 // mapping between clauses and var names; flexName -> <IPL lang elem>
	private var Map<String, ModelExpr> flexClauses = new HashMap
	 // argument names (from scope) of flex clauses; flexName -> <varName>. Does not face externally
	private var Map<String, List<String>> flexArgs = new HashMap
	private var flexNum = 0 // for naming flexible abstractions
	
	// INPUTS
	// SET EXTERNALLY blocking clauses for finding model values; 
	private var List<Map<String, Object>> blockingValues = new ArrayList // has to be not null
	// SET EXTERNALLY interpretation of flexible variables; set of scope vals (name, value) -> <flex name -> value(s)>; 
	private var Map<Map<String, Object>, Map<String, Object>> flexsVals = new HashMap // has to be not null
	
	// anonymous sets encoded as functions; does not face externally 
	private var setDecls = ""
	private var anonSetNum = 0

	
	// probes for finding model values; does not face externally 	
	private var Map<String, String> probingClauses = new HashMap
	
	// an alternative formula for probes 	
	private String probingFormula = ''
	private boolean probingFormulaSwitch = false // switch on when generating probes, for modelexpr 
	



	// NOT USED
	override public def String generateSmtFormula(Formula f) {
		/*reset

		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
		«if (setDecls.length > 0)
			'''; Anonymous sets
				«setDecls» '''»
		; Probing
		«if (IPLConfig.ENABLE_PROBING_VARS) 
			'''«scopeDecls.keySet.map['(declare-const ' + Utils::probe(it) +' '
					+ Utils::typesIPL2Smt(scopeDecls.get(it))+')'
			].join('\n')»'''»
		
		«probingClauses.values.join('\n')»
		
		«probingFormula»
		
		;Formula 
		(assert «formulaStr»)'''*/
	}

	override public def String generateSmtFormulaNeg(Formula f, boolean probing) {
		reset

		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
					«if (setDecls.length > 0)
			'''; Anonymous sets
«setDecls» '''»
					
					; Flex decls
					«generateSmtFlexDecl»
					
					; Probing
					«if (IPLConfig.ENABLE_PROBING_VARS) 
			'''«scopeDecls.keySet.map['(declare-const ' + Utils::probe(it) +' '
					+ Utils::typesIPL2Smt(scopeDecls.get(it))+')'
			].join('\n')»'''»
					
					«if (IPLConfig.ENABLE_PROBING_VARS && probing) 
			probingClauses.values.join('\n') + generateProbingBlockingClauses + '\n' + probingFormula »
					
					; Formula 
					«if (!probing) 
			'(assert (not ' + formulaStr  +'))'»'''
	}



	// set repeatedly only during model finding
	override public def setBlockingValues(List<Map<String, Object>> blocks) {
		blockingValues = blocks
	}
	
	// set only for the final call
	override public def setFlexsVals(Map vals) {
		flexsVals = vals
	}


	// returns the scope declaration
	// won't clear it later
	override public def getFormulaScopeDecls() {
		scopeDecls
	}

	// won't clear it later
	override public def getFormulaFlexDecls() {
		flexDecls
	}

	// won't clear it later
	override public def getFormulaFlexClauses() {
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
		val formula = switch (varType) { 
			ComponentType: {
			val archElemMbFun = getArchElemMbFun(varType as ComponentType)
			
			// TODO the bottom part can be factored out as a helper function for all types (argument: membership set)
			// probing constraint - archelem
			if (IPLConfig.ENABLE_PROBING_VARS) 
				probingClauses.put(Utils::probe(q.^var), '''(assert («archElemMbFun» «Utils::probe(q.^var)»))''')

			// FIXME inserting the blocking at the innermost quantification, not sure if right
			var blockingClauses = if (q.getAllContents(false).forall[! (it instanceof QAtom)]) // if no more qatoms down below
				generateScopeBlockingClauses
			else 
				''				
			// blocking for components
			/*var blockingClauses = blockingValues.map[ nameValueMap |
				if(nameValueMap.containsKey(q.^var)) {
					// blocking clauses applied to probes
					if (IPLConfig.ENABLE_PROBING_VARS) {
						probingClauses.put(Utils::probe(q.^var), probingClauses.get(Utils::probe(q.^var)) + '''
						
						(assert (distinct «Utils::probe(q.^var)» «nameValueMap.get(q.^var)» ))''')
					}
					'''(distinct «q.^var» «nameValueMap.get(q.^var)» )'''
				} else 
					''
			].join(' ')*/			
			
			// actual quantified expression
			'''(«quant» ((«q.^var» ArchElem)) («quantOp» (and («archElemMbFun» «q.^var») «blockingClauses»)
					«generateFormula(q.exp)»))'''
			}	
			IntType,
			RealType,
			BoolType: {
				val setMbFunName = generateAnonSet(q.set);
				val z3TypeName = switch (varType) { IntType: "Int" RealType: "Real" BoolType: "Bool" }

				// probing constraint - set
				if (IPLConfig.ENABLE_PROBING_VARS) 
					probingClauses.put(Utils::probe(q.^var), '''(assert («setMbFunName» «Utils::probe(q.^var)»))''')
				
				// FIXME inserting the blocking at the innermost quantification, not sure if right
				var blockingClauses = if (q.getAllContents(false).forall[! (it instanceof QAtom)]) // if no more qatoms down below
					generateScopeBlockingClauses
				else 
					''	
				// do blocking for this variable if needed
				/*var blockingClauses = blockingValues.map [ nameValueMap |
					if (nameValueMap.containsKey(q.^var)) {
						if (IPLConfig.ENABLE_PROBING_VARS) {
							probingClauses.put(Utils::probe(q.^var), probingClauses.get(Utils::probe(q.^var)) + '''
							
							(assert (distinct «Utils::probe(q.^var)» «nameValueMap.get(q.^var)» ))''')
						}

						'''(distinct «q.^var» «nameValueMap.get(q.^var)» )'''
					} else
						''
				].join(' ')*/

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
		
		// check and see if want to construct a probing analogue of the formula (w/o qatoms)
		if(IPLConfig::ENABLE_PROBING_VARS && q.getAllContents(false).forall[! (it instanceof QAtom)]){
			val copyExp = EcoreUtil::copy(q.exp)
			val replExp = (new ProbeTransformer).replaceVarsWithProbes(copyExp, scopeDecls) 
			val a = copyExp.class 
			probingFormulaSwitch = true // no need for negation: looking for the same _constraints_ as vars
			probingFormula += '(assert ' + switch(replExp) { // have to do this because not clear what replExp casts to 
				FormulaOperation: generateFormula(replExp)
				Negation: generateFormula(replExp)
				TermFormula:  generateFormula(replExp)
				TAtom: generateFormula(replExp)
				QAtom: throw new UnexpectedException("Not supposed to work on QAtoms") 
			} + ')\n'
			probingFormulaSwitch = false
		}
		
		formula
	}
	
	/*private def dispatch String generateFormula(Fun f) {
		val decl = f.name   
		if (decl.name != "abs" || decl.paramTypes.size != 1 || 
			!(decl.paramTypes.get(0) instanceof TypeReal) || !(decl.retType instanceof TypeReal))
			throw new UnsupportedOperationException("Function " + decl.name + " is not supported yet")
		
		'''(«decl.name» «f.args.map[generateFormula(it)].join(' ')»)'''
	}*/ 

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
			'''(«f.name.name» «f.args.map[generateFormula(it)].join(' ')»)''' //FOR arg : f.args» «generateFormula(arg)»«ENDFOR»
		else
			'''«f.name.name»'''
	}

	private def dispatch String generateFormula(PropertyExpression pe) {
		'''(«pe.right.id» «generateFormula(pe.left)»)'''
	}

	private def dispatch String generateFormula(ID id) {
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

		if (probingFormulaSwitch) { // when probing, need to apply an existing abstraction to probes
				// TODO fix this hack that assumes only one flexible abstraction
				val abst = flexClauses.keySet.get(0)
				return '''(«abst» «flexArgs.get(abst).map[Utils::probe(it)].join(' ')»)'''
		}

		// normal flow: 
		
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
		if (args !== null && args.length > 0){
			'''(«abst» «args.map[it].join(' ')»)'''
		} else
			abst
	}

	/*private def dispatch String generateFormula(ProbQuery pq) {
		throw new UnexpectedException('Was not supposed to reach here')
	}

	private def dispatch String generateFormula(RewardQuery pq) {
		throw new UnexpectedException('Was not supposed to reach here')
	}*/

	// === HELPER FUNCTIONS === 
	
	// needs to be populated with proper abstractions already, after generating for formula
	private def String generateSmtFlexDecl() {
		if (IPLConfig.ENABLE_FLEXIBLE_ABSTRACTION_WITH_ARGS) { // with args
			val funDecls = flexDecls.keySet.map [
				'''(declare-fun «it» («flexArgs.get(it).map[Utils::typesIPL2Smt(scopeDecls.get(it))].join(' ')») ''' +
					'''«switch (flexDecls.get(it)) { IntType: "Int" RealType: "Real" BoolType: "Bool" }»)'''
			].join('\n') + '\n'
			
			var asserts = ''
			for ( scopeVal : flexsVals.keySet ) {
				val flexsVal = flexsVals.get(scopeVal) // set of flexible variables
				asserts += flexsVal.keySet.map[ flexName | {
					val args = flexArgs.get(flexName) // (scope vars) arguments
					if (args.size > 0) // function
						'''(assert (= («flexName» «args.map[scopeVal.get(it)].join(' ')») «flexsVal.get(flexName)»))''' + '\n'
					else // constant, no parentheses
						'''(assert (= «flexName» «flexsVal.get(flexName)»))''' + '\n'
					}	
				].join('\n')
			} 
			
			funDecls + asserts
			
		} else { // no args
			flexDecls.keySet.map [
				'''(declare-const «it» «switch (flexDecls.get(it)) { IntType: "Int" RealType: "Real" BoolType: "Bool" }»)'''
			].join('\n') + '\n'
			throw new UnsupportedOperationException("Not updated for flexs interp as above")
		}
	}
	
	private def String getArchElemMbFun(ComponentType ct) {
		'is' + ct.name.replace('.', '_')
	}

	// blocking for actual vars
	private def String generateScopeBlockingClauses() {
		blockingValues.map [ nameValueMap |
			'(or ' + nameValueMap.keySet.map[ varName |
				'(distinct ' + varName + ' ' + nameValueMap.get(varName) + ')'
			].join(' ') + ')'
		].join('\n')
	}

	// blocking for probes
	private def String generateProbingBlockingClauses() {
		blockingValues.map [ nameValueMap |
			'(assert (or ' + nameValueMap.keySet.map[ varName |
				'(distinct ' + Utils::probe(varName) + ' ' + nameValueMap.get(varName) + ')'
			].join(' ') + '))'
		].join('\n') + '\n'
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
		scopeDecls = new HashMap //scopeDecls.clear
		flexDecls = new HashMap //flexDecls.clear
		flexClauses = new HashMap //flexClauses.clear
		
		flexArgs.clear
		flexNum = 0
		probingClauses.clear
		probingFormula = ''

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


}
