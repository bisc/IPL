package org.xtext.example.ipl.generator;

import java.net.URL
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
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType

public class SmtVerifier {

	private val smtGenerator = new SmtGenerator
	private var List<Pair<String, IPLType>> scope = new LinkedList
	private var Map<String, List<Object>> scopeEvals = new HashMap

	def boolean verifyRigidFormula(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		val String backgrSmt = smtGenerator.generateBackgroundSmt(s)
		val String formulaSmt = smtGenerator.generateSmtFormulaNeg(f)
		println("Done generating IPL SMT")

		scope = smtGenerator.lastFormulaScope

		// val evals = smtGenerator.lastFormulaScopeEvals
		// val filename = resource.URI.trimFileExtension.lastSegment + '.z3';
		// val filename = resource.URI.trimFileExtension.lastSegment + '.z3';
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

		if (z3ResFirstLine.equals("unsat")) {
			println("unsat, formula is valid")
			true
		} else if (z3ResFirstLine.equals("sat")) {
			println("sat, formula is invalid")
			false
		} else {
			println("error: " + z3ResLines.join('\n'))
			false
		}
	}

	def boolean findModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) {
		val String backgrSmt = smtGenerator.generateBackgroundSmt(s)
		val String formulaSmt = smtGenerator.generateSmtFormula(f)
		println("Done generating IPL SMT")

		scope = smtGenerator.lastFormulaScope
		// val evals = smtGenerator.lastFormulaScopeEvals
		println('''Scope: «scope»''')

		fsa.generateFile(filename, backgrSmt + formulaSmt + ''' 
			
			(check-sat) 
			(get-model)
			
		''')
		// «evals»
		System::out.println("Done generating SMT, see file " + filename)

		// call smt 
		var z3Filename = fsa.getURI(filename)
		var z3FilePath = FileLocator.toFileURL(new URL(z3Filename.toString)).path

		var z3Res = Utils.executeShellCommand("z3 -smt2 " + z3FilePath, null)
		// z3Res = z3Res.replaceAll("\\s+", ""); // remove whitespace
		var z3ResLines = z3Res.split('\n')
		val z3ResFirstLine = z3ResLines.get(0)

		if (z3ResFirstLine.equals("unsat")) {
			println("unsat, formula is valid")
			true
		} else if (z3ResFirstLine.equals("sat")) {
			println("sat, looking for models")
			populateEvals(z3Res)
			false
		} else {
			println("error: " + z3ResLines.join('\n'))
			false
		}
	}

	// get the variable evaluations from the model (z3 output)
	private def populateEvals(String z3Res) {
		// note: z3 doesn't return values of quantified vars on (eval <varname) or (get value (<varlist>))
		// the only way to get the values is to:
		// (1) ensure they are sufficiently bound with user-provided symbols
		// (2) run (get-model)
		// ideally, one would parse out arbitrary skolem functions and extract values from them
		// find the string with value with regex
		println('''Scope: «scope»''')
		scope.forEach [ v |
			// decoding: (define fun, then var name, then ! followed by any digits, 
			// then parentheses with something, then a type (word, 1st group) in parentheses
			// then whitespace (incl \n), then the value (alphanumeric, 2nd group
			// zero group - everything that matched
			// first group - the type
			// second group - the value 
			val Pattern p = Pattern.compile('''\(define-fun «v.key»!\d* \(.*\) (\w*)\s*(\p{Alnum}*)\)''')

			val Matcher m = p.matcher(z3Res)

			if (m.find) {
				println('Match:' + m.group)
				val typeSmt = m.group(1)
				val valueSmt = m.group(2)  
					
				// if evals don't have a var, add a list
		  		if (!scopeEvals.containsKey(v.key)) 
		  			scopeEvals.put(v.key, new LinkedList)
		  			

				switch(v.value) { // variable type from scope
				  	IntType: {
				  		if (typeSmt != 'Int') 
				  			print('''Type error: variable «v.key»:«v.value» gets a value «valueSmt»''' );
				  		
				  		scopeEvals.get(v.key).add(Integer.parseInt(valueSmt))	
				  	}
				  	RealType: {
				  		if (typeSmt != 'Real') 
				  			print('''Type error: variable «v.key»:«v.value» gets a value «valueSmt»''' );
				  			
		  				scopeEvals.get(v.key).add(Float.parseFloat(valueSmt))
			  		}
				  	BoolType: {
				  		if (typeSmt != 'Bool') 
				  			print('''Type error: variable «v.key»:«v.value» gets a value «valueSmt»''' );
				  			
			  			scopeEvals.get(v.key).add(Boolean.parseBoolean(valueSmt))
		  			}
		  			default: 
				  	 	println('''Type error: undefined type «v.value» of variable «v.key»''')
				 }
				 println(scopeEvals)
			} else {
				println('''Error parsing z3 output: match for «v.key» (type «v.value») not found in:
					 «z3Res»''')
			}

		]

	}
}
