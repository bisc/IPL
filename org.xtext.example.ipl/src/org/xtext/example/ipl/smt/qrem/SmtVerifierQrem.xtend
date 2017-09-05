package org.xtext.example.ipl.smt.qrem;

import java.net.URL
import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.LinkedList
import java.util.List
import java.util.Map
import java.util.regex.Matcher
import java.util.regex.Pattern
import org.eclipse.core.runtime.FileLocator
import org.eclipse.emf.ecore.util.EcoreUtil
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.interfaces.SmtVerifier
import org.xtext.example.ipl.prism.plugin.PrismPlugin
import org.xtext.example.ipl.transform.VarValueTransformer
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.util.TimeRec
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import java.util.Arrays

// implementation of generation by mapping ArchElem -> Int
public class SmtVerifierQrem implements SmtVerifier {

	private val smtViewGenerator = new SmtViewGeneratorQrem
	private val smtFormulaGenerator = new SmtFormulaGeneratorQrem

	// declarations of quantified variables
	private var Map<String, IPLType> termDecls
	// each map in the list is an valuation of all declared variables
	private var List<Map<String, Object>> termVals = new ArrayList<Map<String, Object>>

	// declarations of flexible abstractions
	private var Map<String, IPLType> flexDecls
	// pointers to flexible clauses, by name
	private var Map<String, ModelExpr> flexClauses

	// caching view smt
	private var String viewSmt = ''
	
	val IPLPrettyPrinter pp = new IPLPrettyPrinter

	// standard IPL verification
	override public def boolean verifyNonRigidFormula(Formula origFormula, ModelDecl md, IPLSpec spec, String filename,
		IFileSystemAccess2 fsa) {
		termVals.clear

		// check if it's valid anyway, regardless of flexible terms
		println('Checking if rigid verification discharges the formula')
		if (verifyRigidFormula(origFormula, spec, filename, fsa))
			return true

		// find models: candidate valuations for sat of negformula
		TimeRec::startTimer("findNegModels")
		if (!findModels(origFormula, spec, filename, fsa))
			throw new UnexpectedException("Failed to find models, check the formula")
		TimeRec::stopTimer("findNegModels")

		// reset blocking state of the smt generator because find models was just called
		smtFormulaGenerator.blockingValues = new ArrayList
	
		// term vals populated, if in existence
		// flex decls are also set
		// what remains is to save flex clauses
		flexClauses = smtFormulaGenerator.formulaFlexClauses

		// find valuations for each flexible abstraction
		smtFormulaGenerator.flexsVals = findFlexsVals(md, filename, fsa)

		// run the ultimate smt here
		println('Final verification after MCs: ' + pp.print(origFormula))
		return verifyRigidFormula(origFormula, spec, filename + "-final", fsa)

	}
	
	// simple verification of negated formula
	// touches: scopeDecls  (but not flexDecls)
	override public def boolean verifyRigidFormula(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		TimeRec::startTimer("verifyRigidFormula")
		// optimization: not rerun AADL generation for every model find
		if (!smtViewGenerator.isViewGenerated)
			viewSmt = smtViewGenerator.generateViewSmt(s)

		val String formulaSmt = smtFormulaGenerator.generateFormulaSmtCheck(f)
		println("Done generating IPL SMT")

		termDecls = smtFormulaGenerator.formulaTermDecls

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
	
	// find valuations for each flexible variable
	// returns a map: term evaluation -> flex values 
	// Map<Map<String, Object>, Map<String, Object>> 
	private def Map findFlexsVals(ModelDecl md, String filename, IFileSystemAccess2 fsa) { 
		// now the current formula state is populated: 
		// scope decls are set, but can get spoiled by rigid verification
		val oldScopeDecls = termDecls.immutableCopy
		
		// if term vals are empty, add one just to continue 
		if (termVals.size == 0)
			termVals.add(new HashMap)

		// collect all values of flex variable
		// set of scope vals (name, value) -> <flex name -> value(s)>
		val Map<Map<String, Object>, Map<String, Object>> flexsVals = new HashMap
		
		// cache of values projected on parameters, to not repeat MC several times 
		// flex name ->  (proj val -> flex value) 
		val Map<String, Map< Map<String, Object>, Object>> flexsValueCache = new HashMap

		// basically go through candidate valuations one by one, obtaining MC results for each
		// need an immutable copy because verifyRigidFormula clears evals for itself (actually now it doesnt)
		for (termVal : termVals.immutableCopy) {
			// above but for a given scope eval
			val Map<String, Object> flexVals = new HashMap

			println("Considering valuation " + termVal)
			// var boolean flexVerRes = true
			// iterate through flexible parts (although not expecting > 1)
			for (e : flexDecls.entrySet) {
				val flexName = e.key
				val flexType = e.value

				// String flexName, IPLType flexType |
				println("Considering flex variable: " + flexName)
				
				// check if cache contains the values
				var flexCache = flexsValueCache.get(flexName) 
				val filteredTermVal = termVal.filter[termName, obj | // leaves the evals that are params of the flex
					smtFormulaGenerator.formulaFlexArgs.get(flexName).contains(termName)
				]
				if (flexCache !== null && flexCache.containsKey(filteredTermVal)) { // cache contains, use the value 
					print('Skipping val ')
					flexVals.put(flexName, flexCache.get(filteredTermVal))
				} else { // failed to find a cached value, have to run MC
					// find a flexible subformula; original in the formula
					val ModelExpr origflexMdlExpr = flexClauses.get(flexName)
	
					// make a copy to feed to prism, to not spoil the original formula it for further iterations
					var newflexMdlExpr = EcoreUtil::copy(origflexMdlExpr)
	
					println('Flexible formula before replacement: ' + pp.print(newflexMdlExpr) + ", params: " +
						newflexMdlExpr.params.vals.map[pp.print(it)])
	
					// put rigid values into it (including model parameters and property values)
					newflexMdlExpr = (new VarValueTransformer).replaceVarsWithValues(
						newflexMdlExpr,
						termVal,
						oldScopeDecls,
						smtViewGenerator.propTypeMap,
						smtViewGenerator.propValueMap
					) as ModelExpr
	
					// set up prism data
					var prop = pp.print(newflexMdlExpr)
					// prop = prop.substring(1, prop.length-1) // remove $
					val paramVals = newflexMdlExpr.params.vals.map[pp.print(it)]
	
					// don't need the copied formula anymore
					EcoreUtil::delete(newflexMdlExpr)
	
					println('''Invoking PRISM: model «md.name», params «md.params», param vals «paramVals», prop «prop»''')
	
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
			flexsVals.put(termVal, flexVals)

		}
		flexsVals		
	}
		
	// finds all variable assignments that satisfy a formula
	// thus, these are candidates for the formula to NOT be valid
	// @returns true if managed to find all models, false otherwise 
	// implicit result: populates scopeDecls and flexDecls; maybe scopeVals 
	override public Boolean findModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		termVals.clear

		// optimization: not rerun AADL generation for every model find
		if (!smtViewGenerator.isViewGenerated)
			viewSmt = smtViewGenerator.generateViewSmt(s)

		// initial run of formula to initialize scope declarations 
		var formulaSmt = smtFormulaGenerator.generateFormulaSmtFind(f)
		println("Done generating IPL SMT")

		termDecls = smtFormulaGenerator.formulaTermDecls
		flexDecls = smtFormulaGenerator.formulaFlexDecls
		println('''Terms: «termDecls»; Flex: «flexDecls»''')

		// no variables -> no need to look for models
		if (termDecls.size == 0) {
			println('No terms for quantified variables; aborting model search')
			return true
		}
		// model search loop 
		println("Starting SMT model search...")
		val filenameWithExt = filename + '.smt'
		while (true) {
			fsa.generateFile(filenameWithExt, viewSmt + formulaSmt + ''' 
				
				(check-sat) 
				«termDecls.keySet.map['(get-value (' + /*smtFormulaGenerator.resolveTerm(*/it + '))'].join('\n')»
				
			''')

			System::out.println("Done generating SMT, see file " + filenameWithExt)

			// call smt 
			var z3Filename = fsa.getURI(filenameWithExt)
			var z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path
			TimeRec::startTimer("z3")
			var z3Res = IPLUtils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
			TimeRec::stopTimer("z3")
			var z3ResLines = z3Res.split('\n')
			val z3ResFirstLine = z3ResLines.get(0)
			val String[] z3ResAfterFirst = Arrays.copyOfRange(z3ResLines, 1, z3ResLines.size)

			// interpret smt results
			if (z3ResFirstLine == "unsat") {
				println("unsat; all models found")
				// interpret: if the scope is empty, then the formula has been shown to be invalid
				// if the scope is not empty, then we might have blocked the values - thus finding all models 				
				return true
			} else if (z3ResFirstLine == "sat") {
				println('''sat; looking for models with terms: «termDecls»''')
				if (!populateEvals(z3ResAfterFirst)) { // side effect: populates termVals
					println("Finding models error; stopping model search")
					return false
				}
			} else {
				println("SMT error; stopping model search: " + z3ResLines.join('\n'))
				return false
			}

			smtFormulaGenerator.blockingValues = termVals
			// a new iteration
			formulaSmt = smtFormulaGenerator.generateFormulaSmtFind(f)
			println("Done generating IPL SMT")
		}

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
		val newEval = new HashMap
		termVals.add(newEval)

		val Pattern p = Pattern.compile(modelParsingPattern)

		termDecls.forEach [ name, termType, count |
			val seq = z3ResAfterFirst.get(count)
			var Matcher m = p.matcher(seq)

			if (m.find) {
				/*println('Match found in: ' + seq)
				println('Groups: ')
				for (i : 0 ..< m.groupCount + 1)
					println(i + ':' + m.group(i))*/

				val termName = m.group(1) // see modelParsingPattern
				val valueSmt = m.group(2)
				 
				if(name != termName)
					println('''Naming error: term «name» is not «termName»''')
				
				addValueToEval(newEval, termName, valueSmt, termType)
			} else {
				println('Match not found in: ' + seq)
				throw new UnexpectedException("Match not found")
			}
		]

		println('Values found:' + termVals)
		modelFound
	}

	// returns a model parsing pattern (complex enough that deserves its own function) 
	private def String modelParsingPattern() {
		// decoding: beginning of input, two escaped parentheses, basically anything 
		// then whitespace, then the value (alphanumeric, with possible dots, 2nd group)
		// then two more parentheses, then end of input 
		// zero group - everything that matched
		// first group - name of the terminal
		// second group - the value 
		'''\A\(\(\(*([\p{Alnum}_]*).*\s([\p{Alnum}\.])*\)\)\z'''
	// '''(?s)\A\((\((.*?)\)\s?\s?)*\)\z''' // '''\((\(.*\)\s?)*\)'''//define-fun «Pattern.quote(varName)»(!\d*)* \(.*\) (\w*)\s*([\p{Alnum}\.]*)\)'''
	}

	// helper function: adds a value to a valuation, doing all the checks as well 
	private def addValueToEval(Map<String, Object> eval, String varName, String valueSmt, IPLType termType) {
		// if evals don't have a var, add a list
		if (!eval.containsKey(varName))
			eval.put(varName, new LinkedList)

		/*if (smtType != IPLUtils::typesIPL2Smt(termType))
			if (!(smtType == 'Int' && termType instanceof ComponentType)) // special case
				println('''Type error: variable «varName»:«termType» gets value «valueSmt» of type «smtType»''');*/

		switch (termType) { // variable type from scope
			IntType:
				eval.put(varName, Integer.parseInt(valueSmt))
			RealType:
				eval.put(varName, Float.parseFloat(valueSmt))
			BoolType:
				eval.put(varName, Boolean.parseBoolean(valueSmt))
			ComponentType: {
				eval.put(varName, Integer.parseInt(valueSmt)) // because ArchElem is a renaming of Int
			}
			default:
				println('''Type error: undefined type «termType» of variable «varName»''')
		}
	}
	
}
