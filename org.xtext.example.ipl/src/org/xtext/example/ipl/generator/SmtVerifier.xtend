package org.xtext.example.ipl.generator;

import java.net.URL
import java.util.ArrayList
import java.util.HashMap
import java.util.LinkedList
import java.util.List
import java.util.Map
import java.util.regex.Matcher
import java.util.regex.Pattern
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.xtext.example.ipl.Utils
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.prism.plugin.PrismPlugin
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType

public class SmtVerifier {

	private val smtGenerator = new SmtGenerator
	
	private var Map<String, IPLType> scopeDecls // declarations of scoped variables
	// each map in the list is an evaluation of scope
	private var List<Map<String, Object>> scopeVals = new ArrayList<Map<String, Object>>
	
	private var Map<String, IPLType> flexDecls // declarations of flexible abstractions
	private var Boolean modelFound = false 

	public def boolean verifyNonRigidFormula(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		scopeVals.clear
		
		// check if it's valid anyway, regardless of flexible terms
		if (verifyRigidFormula(f, s, filename, fsa))
			return true
		
		// find models: candidate valuations for sat of negformula
		findNegModels(f,s,filename,fsa)
			
		// TODO maybe just add an empty one? 
		// basically go through candidate valuations one by one, obtaining MC results for each
		return scopeVals.map[ nameValueMap | 
				println("Considering valuation " + nameValueMap)
				
				
				flexDecls.forEach[flexName, flexType|
					println("Considering flex variable " + flexName)
					
					// find a flexible subformula
					println('Flexible formula: ' + smtGenerator.lastFormulaFlexClauses.get(flexName).toString())
					
					// put rigid values into it 
					
					// pass parameters to the model 
					
					// call model checker
					(new PrismPlugin).verify('', fsa)
					
					// record result in flexEvals 
				]
				
				// put scope & flex evals into formulaNeg (can replace QAtom or put a restriction on it)
				
				// run the resulting formula through smt 
				
				// if we rejected it (unsat), move on 
				// otherwise:
				return false

		].reduce[resSoFar, thisRes| resSoFar && thisRes]
	}


	// finds all variable assignments that satisfy a negated formula
	// thus, these are candidates for the formula to NOT be valid
	public def Boolean findNegModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		scopeVals.clear
		val String backgrSmt = smtGenerator.generateBackgroundSmt(s)
		
		// initial run of formula to initialize scope declarations 
		var formulaSmt = smtGenerator.generateSmtFormulaNeg(f)
		println("Done generating IPL SMT")
		scopeDecls = smtGenerator.lastFormulaScopeDecls
		flexDecls = smtGenerator.lastFormulaFlexDecls
		println('''Scope: «scopeDecls»; Flex: «flexDecls»''')
		val flexDeclsSmt = smtGenerator.generateSmtFlexDecl	
						
		// model search loop 
		println("Starting SMT model search...")
		while(true) { 
			fsa.generateFile(filename, backgrSmt + flexDeclsSmt + formulaSmt + ''' 
				
				(check-sat) 
				(get-model)
				
			''')
			
			System::out.println("Done generating SMT, see file " + filename)

			// call smt 
			var z3Filename = fsa.getURI(filename)
			var z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path

			var z3Res = Utils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
			var z3ResLines = z3Res.split('\n')
			val z3ResFirstLine = z3ResLines.get(0)

			// interpret smt results
			if (z3ResFirstLine == "unsat") {
				println("unsat; all models found")
				// interpret: if the scope is empty, then the formula has been shown to be invalid
				// if the scope is not empty, then we might have blocked the values - thus finding all models 				
				return true
			} else if (z3ResFirstLine == "sat") {
				println('''sat; looking for models with scope: «scopeDecls»''')
				if (!populateEvals(z3Res)) { 
					println("Finding models error; stopping model search")
					return false
				} 
			} else {
				println("SMT error; stopping model search: " + z3ResLines.join('\n'))
				return false
			}
			
			smtGenerator.blockingValues = scopeVals
			// a new iteration
			formulaSmt = smtGenerator.generateSmtFormulaNeg(f)
			println("Done generating IPL SMT")
		}

	}

	// simple verification of negated formula
	public def boolean verifyRigidFormula(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		scopeVals.clear
		val String backgrSmt = smtGenerator.generateBackgroundSmt(s)
		val String formulaSmt = smtGenerator.generateSmtFormulaNeg(f)
		println("Done generating IPL SMT")
		
		scopeDecls = smtGenerator.lastFormulaScopeDecls

		fsa.generateFile(filename, backgrSmt + formulaSmt + ''' 
			
			(check-sat) 
			(get-model)
			
		''')

		System::out.println("Done generating SMT, see file " + filename)

		// call smt 
		var z3Filename = fsa.getURI(filename)
		var z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path

		var z3Res = Utils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
		// z3Res = z3Res.replaceAll("\\s+", ""); // remove whitespace
		var z3ResLines = z3Res.split('\n')
		val z3ResFirstLine = z3ResLines.get(0)

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


	// get (additional) variable evaluations from the model (z3 output)
	private def Boolean populateEvals(String z3Res) {
		// note: z3 doesn't return values of quantified vars on (eval <varname) or (get value (<varlist>))
		// the only way to get the values is to:
		// (1) ensure they are sufficiently bound with user-provided symbols
		// (2) run (get-model)
		// ideally, one would parse out arbitrary skolem functions and extract values from them
		// find the string with value with regex
		modelFound = true // assume so until proven otherwise
		val newEval = new HashMap
		scopeVals.add(newEval)
		
		scopeDecls.forEach [ varName, varType |
			// decoding: (define fun, then var name, then ! followed by any digits, 
			// then parentheses with something, then a type (word, 1st group) in parentheses
			// then whitespace (incl \n), then the value (alphanumeric, with possible dots, 2nd group)
			// zero group - everything that matched
			// first group - the type
			// second group - the value 
			val Pattern p = Pattern.compile('''\(define-fun «varName»!\d* \(.*\) (\w*)\s*([\p{Alnum}\.]*)\)''')

			val Matcher m = p.matcher(z3Res)

			if (m.find) {
				//println('Match:' + m.group)
				val typeSmt = m.group(1)
				val valueSmt = m.group(2)  
					
				// if evals don't have a var, add a list
		  		if (!newEval.containsKey(varName)) 
		  			newEval.put(varName, new LinkedList)
		  			

				switch(varType) { // variable type from scope
				  	IntType: {
				  		if (typeSmt != 'Int') 
				  			print('''Type error: variable «varName»:«varType» gets a value «valueSmt»''' );
				  		
				  		newEval.put(varName, Integer.parseInt(valueSmt))	
				  	}
				  	RealType: {
				  		if (typeSmt != 'Real') 
				  			print('''Type error: variable «varName»:«varType» gets a value «valueSmt»''' );
				  			
		  				newEval.put(varName, Float.parseFloat(valueSmt))
			  		}
				  	BoolType: {
				  		if (typeSmt != 'Bool') 
				  			print('''Type error: variable «varName»:«varType» gets a value «valueSmt»''' );
				  			
			  			newEval.put(varName, Boolean.parseBoolean(valueSmt))
		  			}
		  			default: 
				  	 	println('''Type error: undefined type «varType» of variable «varName»''')
				 }
				 
			} else {
				println('''Error parsing z3 output: match for «varName» (type «varType») not found in:
					 «z3Res»''')
				modelFound = false
			}
			
			// has to be only one match per variable
			if(m.find) {
				println('''Error parsing z3 output: several matches for «varName»; unexpected second: «m.group» ''')
				modelFound = false
			}
		]
		println('Values found:' + scopeVals)
		modelFound
	}
}
