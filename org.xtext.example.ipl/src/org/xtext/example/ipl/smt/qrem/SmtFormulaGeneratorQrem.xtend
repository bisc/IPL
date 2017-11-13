package org.xtext.example.ipl.smt.qrem

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.LinkedList
import java.util.List
import java.util.Map
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.Const
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
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.transform.PropAbstTransformer
import org.xtext.example.ipl.transform.Var2FreeVarPartialTransformer
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IPLTypeProvider
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

import static extension org.eclipse.emf.ecore.util.EcoreUtil.*
import static extension org.eclipse.xtext.EcoreUtil2.*
import static extension org.xtext.example.ipl.util.IPLUtils.*

// implementation of formula generation with removal of quantifiers
// not allowed to copy formulas
// expected flow: genCheck -> remove quant -> genFind -> genCheck 
// (no quant reset between quant and genFind)
class SmtFormulaGeneratorQrem {
	// initialized in constructor
	private var IPLSpec spec
	private var IPLTypeProvider tp

	// QUANT STATE: variables tracking quantifiers
	// free constants replacing quantified variables: name, type
	private var Map<String, IPLType> freeVarDecls = new HashMap
	// list of parameters for each variable term. Empty list if no parameters
	// private var Map<String, List<Pair<String, IPLType>>> termParams = new HashMap
	// a generated string that asserts that each term belongs to its type
	private var String freeVarTypeRests

	// for quantified variables in their pure form; used for flexible clauses
	private var Map<String, IPLType> quantVarDecls = new HashMap

	// for anonymous sets encoded as functions; does not face externally 
	private var setMemberFnDecls = ""
	private var anonSetCount = 0

	// DEEP STATE: variables tracking abstractions & transfer clauses
	// for flexible abstractions 
	// type details of flex "variables"; flexName -> flexVarType
	private var Map<String, IPLType> flexDecls = new HashMap
	// mapping between clauses and var names; flexName -> <IPL lang elem>
	private var Map<String, ModelExpr> flexClauses = new HashMap
	// argument names (from scope) of flex clauses; flexName -> <varName>
	private var Map<String, List<String>> flexArgs = new HashMap
	private var flexNum = 0 // for naming flexible abstractions
	// clauses for which values need to be transferred + their generated SMT code 
	private var Map<Formula, String> transferClausesSmt = new HashMap
	// clauses to their types
	private var Map<Formula, IPLType> transferClausesType = new HashMap

	// INPUTS
	// SET EXTERNALLY interpretation of flexible variables; 
	// flex name -> <(varname, value) -> flex value>; 
	private var Map<String, Map<Map<String, Object>, Object>> flexsVals = null

	new(IPLSpec _spec) {
		spec = _spec
		tp = new IPLTypeProvider(spec)
	}

	// generate a formula for finding models, with given types of free variables
	// assumes the formula to be quantifier-free, free var declarations populated
	public def String generateFormulaSmtFind(Formula fQF) {
		resetDeepState // no resetting quant state here!
		// assuming that quantifiers were removed and free var decls were set 
		// set free var types for the provider  
		tp.freeVarTypes = freeVarDecls

		// create a propositional abstraction
		val trans = new PropAbstTransformer
		val fPropAbst = trans.performPropAbst(fQF.copy, tp)
		println('Prop abst: ' + IPLPrettyPrinter::print_formula(fPropAbst))
		val String fPropAbstSmt = generateFormula(fPropAbst)
		val String propAbstDecls = trans.getPropAbstNames.map [
			'(declare-const ' + it + ' Bool)\n'
		].join('\n')
		fPropAbst.delete(true)
		resetDeepState // may have encountered flex symbols, forget them
		// create the actual formula (this populates anonymous sets)
		val formulaSmt = generateFormula(fQF)

		'''
		«if (setMemberFnDecls.length > 0)
	'''; Set membership functions
«setMemberFnDecls» '''»
		
		; Term defs & type restrictions
		«generateSmtTermDecl»
		«freeVarTypeRests»
		
		; Prop abstr decls
		«propAbstDecls»
		
		; Flex decls
		«generateSmtFlexDecl»
		
		; Formula 
		«'(assert (distinct\n' + formulaSmt + '\n' + fPropAbstSmt +'\n))'»'''

	}

	// checks sat(neg formula) without creating terms 
	public def String generateFormulaSmtCheck(Formula f) {
		resetDeepState
		resetQuantState // remove the possible carryover of free vars/ anon sets from model finding
		// this populates anonymous sets
		val formulaStr = generateFormula(f)

		'''
		«if (setMemberFnDecls.length > 0)
			'''; Anonymous sets
«setMemberFnDecls» '''» 
		
		; Flex decls
		«generateSmtFlexDecl»
		
		; Formula 
		(assert (not «formulaStr»))'''
	}

	// removes quantifiers from a prenexed formula 
	// (assumes that all QATOMS are in the front)
	// replaces quantified variables with free constant terms
	// populates freeVarDecls and freeVarTypeRests
	// does not resolve terms -- they are all IDs
	public def Formula removeQuants(Formula f) {
		resetDeepState
		resetQuantState

		// get all quant variable declarations in the formula 
		val varDecls = newHashMap 
		f.eAll.filter(QAtom).forEach[ 
			val qdomType = tp.getQdomType(it.dom)
			// TODO factor out qdom type -> var type inference? 
			val varType = if(qdomType instanceof SetType) qdomType.elemType else qdomType // goes up to IPLSpec
			varDecls.put(it.^var, varType)
		]

		// get a list of quant vars that are args of any flex clause 
		// to remove only their quants
		val List<String> varsToRemove = new ArrayList
		f.eAllOfType(ModelExpr).forEach [ mdex |
			createArgListForFlexAbst(mdex, varDecls).forEach [ arg |
				varsToRemove.add(arg)
			]
		]
		// mapping var names from formula to free var names
		val Map<String, String> oldVar2New = new HashMap
		
		// TODO have to be careful to not touch QRATOMS
		// first unwrap qatoms and populate sets as needed
		val i = f.eAllOfType(QAtom).iterator
		while (i.hasNext) {
			val QAtom q = i.next

			// other vars remain quantified
			if (varsToRemove.contains(q.^var)) {
				val varName = IPLUtils::freeVar(q.^var)
				oldVar2New.put(q.^var, varName)
				val qdomType = tp.getQdomType(q.dom)
				val varType = if(qdomType instanceof SetType) qdomType.elemType else qdomType // goes up to IPLSpec
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
						if (qdomType instanceof SetType) { // need an anon set here
							val setMbFunName = generateSetMemberFn(q.dom as Expression);

							freeVarTypeRests += '''(assert («setMbFunName» «varName»))
							'''
						} else {
							// do nothing here because no extra restrictions are needed
						}
					}
					default:
						throw new IllegalArgumentException('Unimplemented set member type')
				}
			}

		}

		// replace variables in the rest of the formula		
		(new Var2FreeVarPartialTransformer).replaceVarsWithTerms(f, oldVar2New) as Formula

	}

	// set only for the final call
	public def setFlexsVals(Map vals) {
		flexsVals = vals
	}

	// returns the scope declaration
	// won't clear it later
	public def Map getFormulaVarDecls() {
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

	public def Map getTransferClausesSmt() {
		transferClausesSmt
	}

	public def Map getTransferClausesTypes() {
		transferClausesType
	}

	// === RIGID GENERATION FUNCTIONS ===
	private def dispatch String generateFormula(FormulaOperation fop) {

		val op = if (fop.op == '&' || fop.op == '^' || fop.op == 'and') {
				'and'
			} else if (fop.op == '||' || fop.op == 'V' || fop.op == 'or') {
				'or'
			} else if (fop.op == '->' || fop.op == '=>') {
				'=>'
			} else if (fop.op == '<->' || fop.op == '<=>') {
				'='
			} else {
				throw new RuntimeException
			}

		'''(«op» «generateFormula(fop.left)» «generateFormula(fop.right)»)'''
	}

	private def dispatch String generateFormula(Negation neg) {
		'''(not «generateFormula(neg.child)»)'''
	}

	private def dispatch String generateFormula(Set f) {
		generateSetMemberFn(f) // TODO: this will need to be augmented for membership-check functions
	}

	private def dispatch String generateFormula(Lst f) {
		// TODO: implement
	}

	private def dispatch String generateFormula(QAtom q) {
		val qdomType = tp.getQdomType(q.dom)
		val varType = if(qdomType instanceof SetType) qdomType.elemType else qdomType // goes up to IPLSpec
			// val varType = (tp.typeOf(q.set) as SetType).elemType;
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
			BoolType: {
				if (qdomType instanceof SetType) { // these types require an anon set
					val setMbFunName = generateSetMemberFn(q.dom as Expression);

					// actual quantified expression
					'''(«quant» ((«q.^var» «varType.typesIPL2Smt»)) («quantOp» (and («setMbFunName» «q.^var»)) 
	«generateFormula(q.exp)»))'''

				} else { // here we just have an int without an anon set
				// actual quantified expression
					'''(«quant» ((«q.^var» «varType.typesIPL2Smt»)) 
	«generateFormula(q.exp)»)'''
				}
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
		val String abst = createFlexAbstraction(mdex, tp.typeOf(mdex))
		/*switch (mdex.expr) {
		 * 	ProbQuery: createFlexAbstraction(mdex, new BoolType)
		 * 	RewardQuery: createFlexAbstraction(mdex, new RealType)
		 * 	default: throw new UnexpectedException('Unknown model formula')
		 }*/
		// save the clause, get args
		flexClauses.put(abst, mdex)
		val args = flexArgs.get(abst)
 
		// save the param terms for later evaluation
		mdex.params.vals.forEach [
			transferClausesSmt.put(it, generateFormula(it)) 
			transferClausesType.put(it, tp.typeOf(it)) // sometimes passing free var names to type provider w/ a non-free spec
		// println('Type of clause ' + it + ' is ' + tp.typeOf(it))
		]

		// generate smt for the abstraction
		// non-nullary functions need extra ( ) around them
		if (args !== null && args.length > 0) {
			'''(«abst» «args.map[it].join(' ')»)'''
		} else
			abst
	}

	// === HELPER FUNCTIONS === 
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

	public def String generateBlockingClauses(List<Map<String, Object>> blockingList) {
		blockingList.map [ nameValueMap |
			'(assert (or ' + nameValueMap.keySet.map [ termName |
				'(distinct ' + termName + ' ' + nameValueMap.get(termName) + ')'
			].join(' ') + '))'
		].join('\n') + '\n'
	}

	// infers the type of a quantified variable -- depending on whether it's a set or an explicit type (e.g. int)
	private def IPLType getQuantVarType(QAtom q) {
	}

	// creates a new symbol for an abstraction of a flexible clause
	private def String createFlexAbstraction(ModelExpr mdex, IPLType type) {

		val String abstrName = '''_flex«flexNum++»''' 
		flexDecls.put(abstrName, type)
		flexArgs.put(abstrName, createArgListForFlexAbst(mdex, determineParamDeclsForFlex))

		abstrName
	}

	// generates the var parameter list (not model params) of a given flexible abstraction  
	// by finding all contents of expression that are also terms/vars
	// has to be called once the quant/free var data is populated already
	private def List<String> createArgListForFlexAbst(ModelExpr mdex, Map<String, IPLType> varDecls) {
		val List argList = new ArrayList<String>
		mdex.eAll.filter(ID).forEach [ 
			if (varDecls.containsKey(it.id)) {
				if (!argList.contains(it.id))
					argList.add(it.id)
			}
		]
		argList
	// old, brute force way: 	
	/*paramDecls.forEach [ varName, varType |
	 * 	flexArgs.get(abstrName).add(varName)
	 */
	}

	// creates smt declarations & constraints for flexible abstractions
	// precondition: the class needs to be populated with proper abstractions 
	// (so call after generating for formula)
	private def String generateSmtFlexDecl() {

		val Map<String, IPLType> paramDecls = determineParamDeclsForFlex

		// generate declarations
		val funDecls = flexDecls.keySet.map [
			'''(declare-fun «it» («flexArgs.get(it).
						map[IPLUtils::typesIPL2Smt(paramDecls.get(it))].join(' ')») ''' +
				'''«flexDecls.get(it).typesIPL2Smt»)'''
		].join('\n') + '\n'

		var asserts = ''
		// generate flex interpretations from free var valuations
		if (flexsVals !== null) { // an optimization 
		// block redundant assertions (because of filtered args)
		// map flex name -> map <term name -> term value>, to block redundant assertions
			val Map<String, List<Map<String, Object>>> projectionBlocks = new HashMap
			flexDecls.keySet.forEach[projectionBlocks.put(it, new LinkedList)] // initialize proj blocks
			asserts = flexsVals.keySet.map [ flexName |
				{ // a flexible term 
					val args = flexArgs.get(flexName).map[IPLUtils::freeVar(it)] // arguments (encoded as quant vars, so need conversion to terms) 
					val flexVals = flexsVals.get(flexName)
					flexVals.keySet.map [ varVal | // an evaluation of quant vars (encoded as free vars)
						val flexValue = flexVals.get(varVal)

						val termValFiltered = varVal.filter [ termName, obj |
							args.contains(termName)
						]
						// check if already asserted
						if (projectionBlocks.get(flexName).contains(termValFiltered)) {
							'' // already generated an assertion for this, skipping
						} else { // first time processing this value 
							projectionBlocks.get(flexName).add(termValFiltered)
							if (args.size > 0) // function
								'''(assert (= («flexName» «args.map[varVal.get(it)].join(' ')») «flexValue»))'''
							else // constant, no parentheses
								'''(assert (= «flexName» «flexValue»))'''
						}
					].join('\n')
				}
			].join('\n')

		} // flexsVals ?= null
		funDecls + asserts
	}

	// decides which parameter declarations to use in flexible abstractions 
	// options: 
	// - free vars -- if those are available (which means we're in model finding mode) 
	// - quant vars -- if we are in checking mode (which is when free vars have to be empty)
	private def Map<String, IPLType> determineParamDeclsForFlex() {
		// TODO fix this, perhaps return a union? 
//		if (!freeVarDecls.empty && !quantVarDecls.empty)
//			throw new UnexpectedException("Error: both free vars and quant vars are considered")

		if (!freeVarDecls.empty)
			freeVarDecls
		else 
			quantVarDecls // if both are empty, this returns an empty one
			
//		else if (!quantVarDecls.empty)
//			quantVarDecls
//		else
//			new HashMap // neither: then no parameters for the abstraction
	}

	// reset the parsing state of the quantifiers/free variables
	// includes anonymous sets because they describe restrictions on free variables
	private def resetQuantState() {
		freeVarDecls = new HashMap
		freeVarTypeRests = ''
		quantVarDecls = new HashMap

		setMemberFnDecls = ""
		anonSetCount = 0
	}

	// reset the parsing state of the formula's 'depths'
	private def resetDeepState() {
		// creating new storages to be independent from its clients
		flexDecls = new HashMap // flexDecls.clear
		flexClauses = new HashMap // flexClauses.clear
		transferClausesSmt = new HashMap
		transferClausesType = new HashMap

		flexArgs.clear
		flexNum = 0
	}

	// helper function to generate anonymous sets, returning membership f-n name
	// TODO issue with current impl: during rigid verif, using quant vars is impossible here 
	// since set f-n declaration is outside of their scope 
	// potential change: introduce a flag that enables returning of the whole expression, without declaration 
	private def String generateSetMemberFn(Expression set) {
		val elemType = (tp.typeOf(set) as SetType).elemType;
		switch (set) {
			Const: { // an explicitly specified set constant, create an anon set
				val funName = '''anonSetMb«anonSetCount++»''';

				// declaring an anonymous set	 
				setMemberFnDecls += '''(define-fun «funName» ((_x «elemType.typesIPL2Smt»)) Bool
				(or «(set as Set).members.map[ '''(= _x «generateFormula(it)»)'''].join(" ")»   
				) ) 
				''';
				funName
			}
			ID: { // must be a set variable, fetch its declaration
				val funName = set.id
				setMemberFnDecls += '''(declare-fun «funName» ((«elemType.typesIPL2Smt»)) Bool)''' + '\n'
				// declaration not necessary - the type provider already did that 
				// val decl = spec.decls.findFirst[it.name == funName] as VarDecl
				// typesDecl2IPL(decl.type)
				funName
			}
			default:
				throw new UnexpectedException("Error: unexpected quantification domain " + set)
		}
	}

}
