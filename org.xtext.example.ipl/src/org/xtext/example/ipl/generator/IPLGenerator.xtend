/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.generator

import java.net.URL
import org.eclipse.core.runtime.FileLocator
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.AbstractGenerator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.generator.IGeneratorContext
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.validation.IPLRigidityProvider

//import org.xtext.example.ipl.iPL.EDouble

/**
 * Generates code from your model files on save.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#code-generation
 */
class IPLGenerator extends AbstractGenerator {

	private val smtVerifier = new SmtVerifier

	override void doGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		val specs = resource.allContents.filter(IPLSpec).toList
		
		// generation of SMT for IPL formulas
		/*val formulasSMT = specs.map [ IPLSpec s |
			s.formulas.map [ Formula f |
				smtVerifier.verifyRigidFormula(f, s, resource, fsa)
			].join('\n')
		].join('\n')*/
		
		specs.forEach[ s |
			s.formulas.forEach[ f, i |
				val filename = resource.URI.trimFileExtension.lastSegment + '-f' + i + '.z3' 
				if(IPLRigidityProvider::isRigid(f))
					smtVerifier.verifyRigidFormula(f, s, filename, fsa)
				else // TODO preprocessing needed
					smtVerifier.findNegModels(f, s, filename, fsa)
			]
		]
		

	}
	
}
