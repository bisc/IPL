package org.xtext.example.ipl.smt.qrem

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.LinkedList
import java.util.List
import java.util.Map
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
import org.xtext.example.ipl.transform.VarFreeVarTransformer
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IPLTypeProviderSpec
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

import static extension org.eclipse.emf.ecore.util.EcoreUtil.*
import static extension org.eclipse.xtext.EcoreUtil2.*
import static extension org.xtext.example.ipl.util.IPLUtils.*

// implementation of formula generation with removal of quantifiers
class SmtFormulaGeneratorQrem {

	private var IPLTypeProviderSpec tp  

	// free constants replacing quantified variables: name, type
	private var Map<String, IPLType> freeVarDecls = new HashMap
	// list of parameters for each variable term. Empty list if no parameters
	// private var Map<String, List<Pair<String, IPLType>>> termParams = new HashMap
	// a generated string that asserts that each term belongs to its type
	private var String freeVarTypeRests

	// for quantified variables in their pure form; used for flexible clauses
	private var Map<String, IPLType> quantVarDecls = new HashMap

	// for flexible abstractions 
	// type details of flex "variables"; flexName -> flexVarType
	private var Map<String, IPLType> flexDecls = new HashMap
	// mapping between clauses and var names; flexName -> <IPL lang elem>
	private var Map<String, ModelExpr> flexClauses = new HashMap
	// argument names (from scope) of flex clauses; flexName -> <varName>
	private var Map<String, List<String>> flexArgs = new HashMap
	private var flexNum = 0 // for naming flexible abstractions
	// INPUTS
	// SET EXTERNALLY blocking clauses for finding model values; 
	private var List<Map<String, Object>> varBlockingValues = new ArrayList // has to be not null
	// SET EXTERNALLY interpretation of flexible variables; set of scope vals (name, value) -> <flex name -> value(s)>; 
	private var Map<Map<String, Object>, Map<String, Object>> flexsVals = new HashMap // has to be not null
	// anonymous sets encoded as functions; does not face externally 
	private var setDecls = ""
	private var anonSetCount = 0

	public def String generateFormulaSmtFind(Formula f) {
		reset
		val spec = f.getContainerOfType(IPLSpec)
		if (spec !== null)
			tp = new IPLTypeProviderSpec(spec)

		val Formula fQF = removeQuants(f.copy)
		println('Quantifiers removed: ' + IPLPrettyPrinter::print_formula(fQF))

		// this populates anonymous sets
		val formulaStr = generateFormula(fQF)

		'''
		«if (setDecls.length > 0)
	'''; Anonymous sets
«setDecls» '''»
		
		; Term defs & type restrictions
		«generateSmtTermDecl»
		«freeVarTypeRests»
		
		; Flex decls
		«generateSmtFlexDecl»
		
		; Blocking
		«generateBlockingClauses»
		
		; Formula 
		«'(assert ' + formulaStr  +')'»'''

	}

	// checks sat(neg formula) without creating terms 
	public def String generateFormulaSmtCheck(Formula f) {
		reset
		val spec = f.getContainerOfType(IPLSpec)
		if (spec !== null)
			tp = new IPLTypeProviderSpec(spec)

		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
		«if (setDecls.length > 0)
			'''; Anonymous sets
«setDecls» '''» 
		
		; Flex decls
		«generateSmtFlexDecl»
		
		; Formula 
		(assert (not «formulaStr»))'''
	}

	// set repeatedly only during model finding
	public def setBlockingValues(List<Map<String, Object>> blocks) {
		varBlockingValues = blocks
	}

	// set only for the final call
	public def setFlexsVals(Map vals) {
		flexsVals = vals
	}

	// returns the scope declaration
	// won't clear it later
	public def Map getFormulaTermDecls() {
		freeVarDecls
	}

	// won't clear it later
	public def Map getFormulaFlexDecls() {
		flexDecls
	}

	// won't clear it later
	public def Map getFormulaFlexClauses() {
		flexClauses
	}

	// won't clear it later
	public def Map<String, List<String>> getFormulaFlexArgs() {
		flexArgs
	}

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
		// termDecls.put(q.^var, varType) -- vars don't go into term decls
		quantVarDecls.put(q.^var, varType) // if in this clause, then operating variables -- not terms
		val quant = if(q.op == 'forall' || q.op == 'A') 'forall' else 'exists'
		// forall comes with implication, exists with conjunction
		val quantOp = if(quant == 'forall') '=>' else 'and'

		// switching on the set member type
		val formula = switch (varType) {
			ComponentType: {
				val archElemMbFun = getArchElemMbFun(varType as ComponentType)

				// actual quantified expression
				'''(«quant» ((«q.^var» ArchElem)) («quantOp» (and («archElemMbFun» «q.^var»))
					«generateFormula(q.exp)»))'''
			}
			IntType,
			RealType,
			BoolType: { // these types require an anon set
				val setMbFunName = generateAnonSet(q.set);

				// actual quantified expression
				'''(«quant» ((«q.^var» «varType.typesIPL2Smt»)) («quantOp» (and («setMbFunName» «q.^var»)) 
	«generateFormula(q.exp)»))'''
			}
			default:
				'; Unimplemented set member type'
		}

		formula
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
			'''(«f.decl.name» «f.args.map[generateFormula(it)].join(' ')»)''' // FOR arg : f.args» «generateFormula(arg)»«ENDFOR»
		else
			'''«f.decl.name»'''
	}

	private def dispatch String generateFormula(PropertyExpression pe) {
		'''(«pe.right.id» «generateFormula(pe.left)»)'''
	}

	private def dispatch String generateFormula(ID id) {
		// doesn't matter if a free var or a quantified one
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

		// normal flow: 
		// poll downstream for type & generate an abstraction
		val String abst = switch (mdex.expr) {
			ProbQuery: createFlexAbstraction(mdex, new BoolType)
			RewardQuery: createFlexAbstraction(mdex, new RealType)
			default: throw new UnexpectedException('Unknown model formula')
		}

		flexClauses.put(abst, mdex)
		val args = flexArgs.get(abst)

		// generate smt for the abstraction
		// non-nullary functions need extra ( ) around them
		if (args !== null && args.length > 0) {
			'''(«abst» «args.map[it].join(' ')»)'''
		} else
			abst
	}

	// === HELPER FUNCTIONS === 

	// replaces quantified variables with free constant terms
	// does not resolve terms -- they are all IDs
	private def Formula removeQuants(Formula f) {
		// assumes that all QATOMS are in the front 
		freeVarTypeRests = ''
		val Map<String, String> oldVar2New = new HashMap

		// TODO have to be careful to not touch QRATOMS
		// first unwrap qatoms and populate sets as needed
		val i = f.eAll.filter(QAtom)
		while (i.hasNext) {
			val QAtom q = i.next

			val varName = IPLUtils::freeVar(q.^var)
			oldVar2New.put(q.^var, varName)
			val varType = (tp.typeOf(q.set) as SetType).elemType; // goes up to IPLSpec
			freeVarDecls.put(varName, varType)
				
			// generate type restrictions
			// switching on the set member type
			switch (varType) {
				ComponentType: {
					val archElemMbFun = getArchElemMbFun(varType as ComponentType)

					freeVarTypeRests += '''(assert («archElemMbFun» «varName»))
					'''
				}
				IntType,
				RealType,
				BoolType: {
					val setMbFunName = generateAnonSet(q.set);

					freeVarTypeRests += '''(assert («setMbFunName» «varName»))
					'''
				}
				default:
					throw new IllegalArgumentException('Unimplemented set member type')
			}
		}

		// replace variables in the rest of the formula		
		// FIXME is this cast safe? 
		(new VarFreeVarTransformer).replaceVarsWithTerms(f, oldVar2New, freeVarDecls) as Formula

	}

	// generates declarations of free variables; empty if none
	// needs to be populated with terms already, after generating for formula
	private def String generateSmtTermDecl() {
		/*termDecls.keySet.map[ termName |
		 * '''(declare-fun «termName» «{
		 * 	val params = termParams.get(termName)
		 * 	'(' + params.map[it.value.typesIPL2Smt].join(' ')+ ')'
		 * 	}» «termDecls.get(termName).typesIPL2Smt»)'''
		 ].join('\n')*/
		freeVarDecls.keySet.map [ termName |
			'''(declare-const «termName» «freeVarDecls.get(termName).typesIPL2Smt»)'''
		].join('\n')
	}

	private def String getArchElemMbFun(ComponentType ct) {
		'is' + ct.name.replace('.', '_')
	}

	// blocking for terms
	private def String generateBlockingClauses() {
		varBlockingValues.map [ nameValueMap |
			'(assert (or ' + nameValueMap.keySet.map [ termName |
				'(distinct ' + termName + ' ' + nameValueMap.get(termName) + ')'
			].join(' ') + '))'
		].join('\n') + '\n'
	}

	// creates a new symbol for an abstraction of a flexible clause
	private def String createFlexAbstraction(ModelExpr mdex, IPLType type) {

		val Map<String, IPLType> paramDecls = decideParamDeclsForFlex

		val String abstrName = '''_flex«flexNum++»'''
		flexDecls.put(abstrName, type)

		flexArgs.put(abstrName, new ArrayList)

		// decide the parameter list: 
		// find all contents of expression that are also terms/vars
		mdex.eAllContents.filter(ID).forEach [
			if (paramDecls.containsKey(it.id))
				flexArgs.get(abstrName).add(it.id)
		]
		/*paramDecls.forEach [ varName, varType |
		 * 	flexArgs.get(abstrName).add(varName)
		 ]*/
		abstrName
	}

	// creates smt declarations of flexible abstractions
	// needs to be populated with proper abstractions already, after generating for formula
	private def String generateSmtFlexDecl() {

		val Map<String, IPLType> paramDecls = decideParamDeclsForFlex

		// generate declarations
		val funDecls = flexDecls.keySet.map [
			'''(declare-fun «it» («flexArgs.get(it).
						map[IPLUtils::typesIPL2Smt(paramDecls.get(it))].join(' ')») ''' +
				'''«flexDecls.get(it).typesIPL2Smt»)'''
		].join('\n') + '\n'

		// generate interpretations from term valuations
		var asserts = ''
		if (!flexsVals.empty) { // an optimization 
		// map flex name -> map <term name -> term value>, to block redundant assertions
			val Map<String, List<Map<String, Object>>> projectionBlocks = new HashMap
			flexDecls.keySet.forEach[projectionBlocks.put(it, new LinkedList)] // initialize proj blocks
			for (termVal : flexsVals.keySet) { // an evaluation of quant vars (encoded as terms)
				val flexsVal = flexsVals.get(termVal) // set of flexible variables with their values
				asserts += flexsVal.keySet.map [ flexName |
					{
						val args = flexArgs.get(flexName).map[IPLUtils::freeVar(it)] // arguments (encoded as quant vars, so need conversion to terms) 
						val termValFiltered = termVal.filter [ termName, obj |
							args.contains(termName)
						]
						if (projectionBlocks.get(flexName).contains(termValFiltered)) {
							'' // already generated an assertion for this, skipping
						} else { // first time processing this value 
							projectionBlocks.get(flexName).add(termValFiltered)
							if (args.size > 0) // function
								'''(assert (= («flexName» «args.map[termVal.get(it)].join(' ')») «flexsVal.get(flexName)»))''' +
									'\n'
							else // constant, no parentheses
								'''(assert (= «flexName» «flexsVal.get(flexName)»))''' + '\n'
						}
					}
				].join('\n')
			}
		}

		funDecls + asserts

	}

	// decide which declarations to use - terms or vars (depending on use case) 
	private def Map<String, IPLType> decideParamDeclsForFlex() {
		if (!freeVarDecls.empty && !quantVarDecls.empty)
			throw new UnexpectedException("Error: both terms and quant vars are considered")

		if (!freeVarDecls.empty)
			freeVarDecls
		else if (!quantVarDecls.empty)
			quantVarDecls
		else
			new HashMap // neither: then no parameters for the abstraction
	}

	// reset the formula parsing state
	private def reset() {
		// creating new ones to be independent from its clients
		freeVarDecls = new HashMap // scopeDecls.clear
		freeVarTypeRests = ''
		flexDecls = new HashMap // flexDecls.clear
		flexClauses = new HashMap // flexClauses.clear
		quantVarDecls = new HashMap

		flexArgs.clear
		flexNum = 0

		setDecls = ""
		anonSetCount = 0
	}

	// helper function to generate anonymous sets, returning membership f-n name
	private def String generateAnonSet(Expression set) {
		val elemType = (tp.typeOf(set) as SetType).elemType;

		val funName = '''anonSetMb«anonSetCount++»''';

		// declaring an anonymous set	 
		setDecls += '''(define-fun «funName» ((_x «elemType.typesIPL2Smt»)) Bool
		(or «(set as Set).members.map[ '''(= _x «generateFormula(it)»)'''].join(" ")»   
		) ) 
		''';
		funName
	}

}
