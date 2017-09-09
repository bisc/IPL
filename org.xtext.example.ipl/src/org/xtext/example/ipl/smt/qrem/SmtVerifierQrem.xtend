package org.xtext.example.ipl.smt.qrem;

import java.net.URL
import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.Arrays
import java.util.HashMap
import java.util.List
import java.util.Map
import java.util.regex.Matcher
import java.util.regex.Pattern
import org.eclipse.core.runtime.FileLocator
import org.eclipse.emf.ecore.util.EcoreUtil.Copier
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.interfaces.SmtVerifier
import org.xtext.example.ipl.prism.plugin.PrismPlugin
import org.xtext.example.ipl.transform.ClauseValueTransformer
import org.xtext.example.ipl.transform.PrenexTransformer
import org.xtext.example.ipl.transform.VarValueTransformer
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.util.TimeRec
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType

import static extension org.eclipse.emf.ecore.util.EcoreUtil.*

// implementation of generation by removing quants and mapping ArchElem -> Int
// makes copies of formula and manages mappings between them
public class SmtVerifierQrem implements SmtVerifier {

	private val SmtViewGeneratorQrem smtViewGenerator = new SmtViewGeneratorQrem
	private var SmtFormulaGeneratorQrem smtFormulaGenerator = null // initialized on call

	// declarations of quantified variables
	private var Map<String, IPLType> freeVarDecls
	// each map in the list is an valuation of all declared variables
	private var List<Map<String, Object>> freeVarVals = new ArrayList<Map<String, Object>>

	// declarations of flexible abstractions
	private var Map<String, IPLType> flexDecls
	// pointers to flexible clauses, by name
	private var Map<String, ModelExpr> flexClauses
	
	// pointers to value transfer clauses, with smt gen code
	// they implicitly reference the clauses in the QF formula
	private var Map<Formula, String> transferClausesSmt 
	private var Map<Formula, IPLType> transferClausesTypes 
	private var Map<Map<String, Object>, Map<Formula, Object>>  transferClauseVals = new HashMap
	//private var Map<Formula, Formula> transferClausesPNF2QF

	// caching view smt
	private var String viewSmt = ''
	
	val IPLPrettyPrinter pp = new IPLPrettyPrinter
	
	// standard IPL verification
	override public def boolean verifyNonRigidFormula(Formula origFormula, ModelDecl md, IPLSpec spec, String filename,
		IFileSystemAccess2 fsa) {
		freeVarVals.clear
		smtFormulaGenerator = new SmtFormulaGeneratorQrem(spec)
		 
		// check if it's valid in its current form with any interpretation of flexible terms
		println('Checking if rigid verification discharges the formula')
		if (verifyRigidFormula(origFormula, spec, filename, fsa))
			return true

		// transform to prenex normal form; make a copy to not mess with IPLSpec
		val fPNF = (new PrenexTransformer).toPrenexNormalForm(origFormula.copy)
		println('Prenex normal form: ' + pp.print(fPNF))
		
		// remove quantifiers and populate freeVarDecls
		val Formula fQF = smtFormulaGenerator.removeQuants(fPNF.copy)
		println('Quantifiers removed: ' + IPLPrettyPrinter::print_formula(fQF))
		
		// find models: candidate valuations for sat of negformula
		// populate transfer clauses 
		TimeRec::startTimer("findNegModels")
		if (!findModels(fQF, spec, filename, fsa))
			throw new UnexpectedException("Failed to find models, check the formula")
		TimeRec::stopTimer("findNegModels")

		// freeVarDecls populated, if in existence
		// flex decls are also set
		// clause vals should be there too 
		// what remains is to save flex clauses -- coming from fQF
		flexClauses = smtFormulaGenerator.formulaFlexClauses

		// find valuations for each flexible abstraction
		smtFormulaGenerator.flexsVals = findFlexsVals(md, filename, fsa)

		// run the ultimate smt here
		println('Final verification after MCs: ' + pp.print(fPNF))
		val res = verifyRigidFormula(fPNF, spec, filename + "-final", fsa)
		fQF.delete(true)
		fPNF.delete(true)
		
		return res
	}
	
	// simple verification of negated formula
	// touches: scopeDecls  (but not flexDecls)
	override public def boolean verifyRigidFormula(Formula f, IPLSpec spec, String filename, IFileSystemAccess2 fsa) {
		TimeRec::startTimer("verifyRigidFormula")
		// optimization: not rerun AADL generation for every model find
		if (!smtViewGenerator.isViewGenerated)
			viewSmt = smtViewGenerator.generateViewSmt(spec)
		// can be called by itself or from non-rigid, so need to check 
		if (smtFormulaGenerator === null)
			smtFormulaGenerator = new SmtFormulaGeneratorQrem(spec)

		val String formulaSmt = smtFormulaGenerator.generateFormulaSmtCheck(f)
		println("Done generating IPL SMT")

		freeVarDecls = smtFormulaGenerator.formulaVarDecls

		val filenameWithExt = filename + '.smt'
		fsa.generateFile(filenameWithExt, viewSmt + formulaSmt + ''' 
			
			(check-sat) 
			(get-model)
		''')

		System::out.println("Done generating SMT, see file " + filenameWithExt)

		// call smt 
		var z3Filename = fsa.getURI(filenameWithExt)
		var z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path

		TimeRec::startTimer("z3")
		var z3Res = IPLUtils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
		TimeRec::stopTimer("z3")
		// z3Res = z3Res.replaceAll("\\s+", ""); // remove whitespace
		var z3ResLines = z3Res.split('\n')
		val z3ResFirstLine = z3ResLines.get(0)

		TimeRec::stopTimer("verifyRigidFormula")
		if (z3ResFirstLine == "unsat") {
			println("unsat, formula is valid")
			true
		} else if (z3ResFirstLine == "sat") {
			println("sat, formula is invalid")
			false
		} else {
			println("error: " + z3ResLines.join('\n'))
			false
		}
	}
		
	// finds all variable assignments that satisfy a QF formula
	// @returns true if managed to find all models, false otherwise 
	// implicit result: populates termDecls, flexDecls, clauses, termVals 
	override public Boolean findModels(Formula fQF, IPLSpec spec, String filename, IFileSystemAccess2 fsa) {
		freeVarVals.clear

		// optimization: not rerun AADL generation for every model find
		if (!smtViewGenerator.isViewGenerated)
			viewSmt = smtViewGenerator.generateViewSmt(spec)

		// need just one run of generation to initialize var/clause declarations 
		var formulaSmt = smtFormulaGenerator.generateFormulaSmtFind(fQF)
		println("Done generating IPL SMT")

		freeVarDecls = smtFormulaGenerator.formulaVarDecls
		flexDecls = smtFormulaGenerator.formulaFlexDecls
		println('''Free vars: «freeVarDecls»; Flex: «flexDecls»''')

		// values to be populated in the loop below
		transferClausesSmt = smtFormulaGenerator.transferClausesSmt
		transferClausesTypes = smtFormulaGenerator.transferClausesTypes

		// no variables -> no need to look for models
		if (freeVarDecls.size == 0) {
			println('No free vars; aborting model search')
			return true
		}
		
		// model search loop 
		println("Starting SMT model search...")
		val filenameWithExt = filename + '.smt'
		var String blockingClauses = ''
		while (true) {
			
			fsa.generateFile(filenameWithExt, viewSmt + formulaSmt + '\n\n' + '''  
				; Blocking 
				«blockingClauses»
				
				(check-sat) 
				
				«freeVarDecls.keySet.map['(get-value (' + /*smtFormulaGenerator.resolveTerm(*/it + '))'].join('\n') + '\n'»
				
				«transferClausesSmt.values.map['(get-value (' + it + '))'].join('\n') + '\n'»
			''')

			System::out.println("Done generating SMT, see file " + filenameWithExt)

			// call smt 
			val z3Filename = fsa.getURI(filenameWithExt)
			val z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path
			TimeRec::startTimer("z3")
			val z3Res = IPLUtils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
			TimeRec::stopTimer("z3")
			val z3ResLines = z3Res.split('\n')
			val z3ResFirstLine = z3ResLines.get(0)
			val String[] z3ResAfterFirst = Arrays.copyOfRange(z3ResLines, 1, z3ResLines.size)

			// interpret smt results
			if (z3ResFirstLine == "unsat") {
				println("unsat; all models found")
				// interpret: if the scope is empty, then the formula has been shown to be invalid
				// if the scope is not empty, then we might have blocked the values - thus finding all models 				
				return true
			} else if (z3ResFirstLine == "sat") {
				println('''sat; looking for models with terms: «freeVarDecls»''')
				if (!populateEvals(z3ResAfterFirst)) { // side effect: populates termVals
					println("Finding models error; stopping model search")
					return false
				}
			} else {
				println("SMT error; stopping model search: " + z3ResLines.join('\n'))
				return false
			}

			// a new iteration
			blockingClauses = smtFormulaGenerator.generateBlockingClauses(freeVarVals)
		}

	}

	// find valuations for each flexible variable
	// implicitly works on references to the QF instance of the formula
	// returns a map: term evaluation -> flex values 
	// Map<Map<String, Object>, Map<String, Object>> 
	private def Map findFlexsVals(ModelDecl md, String filename, IFileSystemAccess2 fsa) { 
		// now the current formula state is populated: 
		// scope decls are set, but can get spoiled by rigid verification, so making a copy
		val oldScopeDecls = freeVarDecls.immutableCopy
		
		// if term vals are empty, add one just to continue 
		if (freeVarVals.size == 0)
			freeVarVals.add(new HashMap)

		// collect all values of flex variable
		// set of scope vals (name, value) -> <flex name -> value(s)>
		val Map<Map<String, Object>, Map<String, Object>> flexsVals = new HashMap
		
		// cache of values projected on parameters, to not repeat MC several times 
		// flex name ->  (proj val -> flex value) 
		val Map<String, Map< Map<String, Object>, Object>> flexsValueCache = new HashMap

		// basically go through candidate valuations one by one, obtaining MC results for each
		// need an immutable copy because verifyRigidFormula clears evals for itself (actually now it doesnt)
		for (varVal : freeVarVals.immutableCopy) {
			// above but for a given scope eval
			val Map<String, Object> flexVals = new HashMap

			println("Considering valuation " + varVal)
			// var boolean flexVerRes = true
			// iterate through flexible parts (although not expecting > 1)
			for (e : flexDecls.entrySet) {
				val flexName = e.key
				val flexType = e.value

				// String flexName, IPLType flexType |
				println("Considering flex variable: " + flexName)
				
				// check if cache contains the values
				var flexCache = flexsValueCache.get(flexName) 
				val filteredTermVal = varVal.filter[termName, obj | // leaves the evals that are params of the flex
					smtFormulaGenerator.formulaFlexArgs.get(flexName).contains(termName)
				]
				if (flexCache !== null && flexCache.containsKey(filteredTermVal)) { // cache contains, use the value 
					print('Skipping val ')
					flexVals.put(flexName, flexCache.get(filteredTermVal))
				} else { // failed to find a cached value, have to run MC
					// find a flexible subformula; original in the formula
					val ModelExpr origFlexExpr = flexClauses.get(flexName)
	
					// make a copy to feed to prism, to not spoil the original formula it for further iterations
					// to preserve clause pointers, use a copier which stores a map old->new for eobjects
					//var newFlexExpr = origFlexExpr.copy
					val Copier copier = new Copier();
					var newFlexExpr = copier.copy(origFlexExpr) as ModelExpr
	
					println('Flexible formula before replacement: ' + pp.print(newFlexExpr) + 
						", params: " + newFlexExpr.params.vals.map[pp.print(it)])
					
					// construct clauseVal and clauseType with updated references to newFlexExpr
					val Map<Formula, Object> clauseValUpd = new HashMap
					val clauseVal = transferClauseVals.get(varVal)
					clauseVal.forEach[clause, value|
						clauseValUpd.put(copier.get(clause) as Formula, value)
					]
					
					val Map<Formula, IPLType> clauseTypeUpd = new HashMap
					transferClausesTypes.forEach[clause, type|
						clauseTypeUpd.put(copier.get(clause) as Formula, type)
					]
					
					// put values of clauses into formula (e.g. aggregate expressions in model params) 
					newFlexExpr = (new ClauseValueTransformer).replaceClausesWithValues(
						newFlexExpr, clauseValUpd, clauseTypeUpd) as ModelExpr
	
					// put rigid values into formula (including model parameters and property values)
					newFlexExpr = (new VarValueTransformer).replaceVarsWithValues(
						newFlexExpr,
						varVal,
						oldScopeDecls,
						smtViewGenerator.propTypeMap,
						smtViewGenerator.propValueMap
					) as ModelExpr
	
					// set up prism data
					val prop = pp.print(newFlexExpr)
					val paramVals = newFlexExpr.params.vals.map[pp.print(it)]
					// prop = prop.substring(1, prop.length-1) // remove $
	
					// don't need the copied formula anymore
					newFlexExpr.delete(true)
	
					println('''Invoking PRISM: model «md.name», prop «prop», params «md.params», param vals «paramVals», ''')
	
					// call model checker and replace part of formula with the result
					TimeRec::startTimer("new PrismPlugin")
					val PrismPlugin prism = new PrismPlugin(md.name, fsa)
					TimeRec::stopTimer("new PrismPlugin")
	
					TimeRec::startTimer("prismCheck")
					val Object flexVal = switch (flexType) {
						RealType: {
							prism.runPrismQuery(prop, md.params, paramVals, filename)
						}
						BoolType: {
							prism.verifyPrismBooleanProp(prop, md.params, paramVals, filename)
						}
						default:
							throw new UnexpectedException("Expected type of flexible expression: " + flexType)
					}
					TimeRec::stopTimer("prismCheck")
	
					// add to evaluation
					flexVals.put(flexName, flexVal)
					
					// add to cache
					if(flexCache === null) {
						flexCache = new HashMap
						flexsValueCache.put(flexName, flexCache)
					}
					flexCache.put(filteredTermVal, flexVal)
					
				} // end if

			} // done for all flex vars 
			flexsVals.put(varVal, flexVals)

		}
		flexsVals		
	}

	// finds all variable assignments that satisfy a negated formula
	// thus, these are candidates for the formula to NOT be valid
	// @returns true if managed to find all models, false otherwise 
	// implicit result: populates scopeDecls and flexDecls; maybe scopeVals 
	override public def Boolean findNegModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		throw new UnexpectedException('Method not used')
	}

	// get (additional) variable evaluations from the model (z3 output)
	// touches: modelFound, scopeVals; reads: scopeDecls
	private def Boolean populateEvals(String[] z3ResAfterFirst) {
		// find the string with value with regex
		var modelFound = true // assume so until proven otherwise

		// parse evaluations for vars
		val newVarEval = new HashMap
		freeVarVals.add(newVarEval)
		val Pattern p1 = Pattern.compile(varValueParsingPattern)
		freeVarDecls.forEach [ name, termType, count |
			val seq = z3ResAfterFirst.get(count)
			var Matcher m = p1.matcher(seq)

			if (m.find) {
				/*println('Match found in: ' + seq)
				println('Groups: ')
				for (i : 0 ..< m.groupCount + 1)
					println(i + ':' + m.group(i))*/

				val termName = m.group(1) // see modelParsingPattern
				val valueSmt = m.group(2)
				 
				if(name != termName)
					throw new UnexpectedException('''Naming error: term «name» is not «termName»''')
				
				addValueToEval(newVarEval, termName, valueSmt, termType)
			} else {
				println('Match not found in: ' + seq)
				throw new UnexpectedException("Match not found")
			}
		]
		
		// parse evaluations for clauses
		val Map<Formula, Object> newClauseEval = new HashMap
		transferClauseVals.put(newVarEval, newClauseEval)
		val Pattern p2 = Pattern.compile(clauseValueParsingPattern)
		transferClausesSmt.forEach[ clause, smtCode, count | 
			val seq = z3ResAfterFirst.get(freeVarDecls.size + count)
			var Matcher m = p2.matcher(seq)
			
			if (m.find) {
				val valueSmt = m.group(1) // see the pattern
				
				/*println('Match found in: ' + seq)
				println('Groups: ')
				for (i : 0 ..< m.groupCount + 1)
					println(i + ':' + m.group(i))*/
				
				addValueToEval(newClauseEval, clause, valueSmt, transferClausesTypes.get(clause))
			}
		]

		println('Var values found:' + freeVarVals)
		println('Clause values found:' + transferClauseVals)
		modelFound
	}

	// returns a regex parsing pattern for free variable values (complex enough that deserves its own function) 
	private def String varValueParsingPattern() {
		// decoding: beginning of input, two escaped parentheses, basically any name with alphanum and underscores 
		// then whitespace, then the value (alphanumeric, with possible dots, 2nd group)
		// then two more parentheses, then end of input 
		// zero group - everything that matched
		// first group - name of the terminal
		// second group - the value 
		'''\A\(\(([\p{Alnum}_]*)\s([\p{Alnum}\.]*)\)\)\z'''
	// '''(?s)\A\((\((.*?)\)\s?\s?)*\)\z''' // '''\((\(.*\)\s?)*\)'''//define-fun «Pattern.quote(varName)»(!\d*)* \(.*\) (\w*)\s*([\p{Alnum}\.]*)\)'''
	}
	
	// returns a regex parsing pattern for value transfer clauses (complex enough that deserves its own function) 
	private def String clauseValueParsingPattern() {
		// decoding: beginning of input, two escaped parentheses, then anything 
		// then whitespace, then the value (alphanumeric, with possible dots, 2nd group)
		// then two more parentheses, then end of input 
		// zero group - everything that matched
		// first group - the value 
		'''\A\(\(.*\s([\p{Alnum}\.]*)\)\)\z'''
	}

	// helper function: adds a value to a valuation, doing all the checks as well 
	// the map is from the Object type (String, Formula, ...) to Object (Value)
	private def addValueToEval(Map eval, Object key, String valueSmt, IPLType termType) {
		// if evals don't have a var, add a list
		//if (!eval.containsKey(varName))
			//eval.put(varName, new LinkedList)

		/*if (smtType != IPLUtils::typesIPL2Smt(termType))
			if (!(smtType == 'Int' && termType instanceof ComponentType)) // special case
				println('''Type error: variable «varName»:«termType» gets value «valueSmt» of type «smtType»''');*/

		switch (termType) { // variable type from scope
			IntType:
				eval.put(key, Integer.parseInt(valueSmt))
			RealType:
				eval.put(key, Float.parseFloat(valueSmt))
			BoolType:
				eval.put(key, Boolean.parseBoolean(valueSmt))
			ComponentType: {
				eval.put(key, Integer.parseInt(valueSmt)) // because ArchElem is a renaming of Int
			}
			default:
				println('''Type error: undefined type «termType» of variable «key»''')
		}
	}
	
}
