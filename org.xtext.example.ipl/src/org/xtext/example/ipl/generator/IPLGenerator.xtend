/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.generator

import java.lang.management.ManagementFactory
import java.net.URL
import java.rmi.UnexpectedException
import java.util.HashMap
import java.util.LinkedList
import java.util.List
import java.util.Map
import org.eclipse.core.resources.IFile
import org.eclipse.core.resources.IMarker
import org.eclipse.core.resources.ResourcesPlugin
import org.eclipse.core.runtime.FileLocator
import org.eclipse.core.runtime.Path
import org.eclipse.emf.common.util.URI
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.swt.widgets.Display
import org.eclipse.xtext.generator.AbstractGenerator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.generator.IGeneratorContext
import org.eclipse.xtext.nodemodel.util.NodeModelUtils
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl
import org.xtext.example.ipl.smt.qrem.SmtVerifierQrem
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.TimeRecWall
import org.xtext.example.ipl.validation.IPLRigidityProvider

/**
 * Values to indicate the result of verification
 */
enum VerificationResult { 
	Valid, Invalid, Error
}

/**
 * A class that serves as an entry point to IPL verification. 
 * 
 * Triggered by building model files.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#code-generation
 */
class IPLGenerator extends AbstractGenerator {
	
	private val Map<URI, List<IMarker>> markers = new HashMap
	
	/**
	 * Called before generation, for timing setup. 
	 */  
	override public void beforeGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		// set up timing
		var mxb = ManagementFactory.getThreadMXBean()
		mxb.threadContentionMonitoringEnabled = true
		println('CPU time support available:' + mxb.isThreadCpuTimeSupported)
		println('CPU time support enabled:' + mxb.isThreadCpuTimeEnabled)
		println('Contention monitoring:' + mxb.isThreadContentionMonitoringEnabled)
		
		TimeRecWall::reset 
		
		deleteMarkers(resource)
	}

	/**
	 * Called on build. Performs verification of each formula in the file, and marks the results with icons. 
	 */
	override public void doGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		val specs = resource.allContents.filter(IPLSpec).toList
		
		// have to make a new instance of Verifier for every formula 
		// 		to not carry over Generator's state
		specs.forEach[ spec |
			spec.formulas.forEach[ f, i |
				val filename = resource.URI.trimFileExtension.lastSegment + '-f' + i // no extension, smt generator adds it
				println('\n\nVerifying ' + IPLPrettyPrinter::printIPL(f))
				val node = NodeModelUtils::getNode(f) // for marker creation
				try { 
					val boolean res = if(!(new IPLRigidityProvider(spec)).isRigid(f)) { // non-rigid, full-scale IPL
						// find a model declaration
						val mdls = spec.decls.filter[it instanceof ModelDecl]
						if (mdls.size == 0) {
							throw new UnexpectedException('Cannot verify non-rigid formulas without a model')
						} else {  
							TimeRecWall::startTimer("verifyNonRigidFormula")
							val boolean resNR = (new SmtVerifierQrem).verifyNonRigidFormula(f, mdls.get(0) as ModelDecl, spec, filename, fsa)
							TimeRecWall::stopTimer("verifyNonRigidFormula")
							
							println("IPL non-rigid formula verified, result: " + resNR)
							resNR
						} 
					} else { //rigid, shortcut
						val boolean resR = (new SmtVerifierQrem).verifyRigidFormula(f, spec, filename, fsa)
						println("IPL rigid formula verified, result: " + resR)
						resR
					}
					
					// show markers in a different thread
					if (res)
						createMarker(resource, node.startLine, VerificationResult::Valid, 'Formula valid') 
					else
						createMarker(resource, node.startLine, VerificationResult::Invalid, 'Formula invalid')
   					
					
				} catch (UnexpectedException e) { 
					println("IPL verification error: " + e)
					e.printStackTrace
					
					// show marker in a different thread
					createMarker(resource, node.startLine, VerificationResult::Error, 'Verification error: ' + e.message)
				}
			]
		]
		
		//direct check in comparison
		//(new DirectPrismChecker).directCheck(fsa)
		
		// output timing results
		TimeRecWall::exportAllTimers(resource.URI.trimFileExtension.lastSegment, fsa)
	}
	
	/**
	 *  Shows a marker with a verification result for a given resource.
	 *  Uses async exec to interact with UI properly.   
	 */
	def private createMarker(Resource resource, int line, VerificationResult result, String text) { 
		Display.getDefault().syncExec(new Runnable() {
			override public run() {
				
				var absolutePath = FileLocator.toFileURL(new URL(resource.URI.toString)).path
				val IFile file = ResourcesPlugin::workspace.root.getFileForLocation(new Path(absolutePath))
				
				// create a marker
				val marker = file.createMarker(IMarker.PROBLEM/*'org.xtext.example.ipl.marker'*/)
				
				var markerList = markers.get(resource.URI) 
				if (markerList === null) { 
					markerList = new LinkedList
					markers.put(resource.URI, markerList)
				}
				markerList.add(marker)
				
				// set marker attributes
				if (marker.exists()) {
					marker.setAttribute(IMarker.MESSAGE, text);
					marker.setAttribute(IMarker.LINE_NUMBER, line); 
					switch (result) {
						case VerificationResult::Valid: 
							marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_INFO)
						
						case VerificationResult::Invalid:  
							marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_WARNING)
						
						case VerificationResult::Error: 
							marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_WARNING)
					}
				} else 
					throw new UnexpectedException('Failed to create a result marker')
			}				    
		});
	}
	
	/**
	 * Removes all markers for a resource
	 */
	def private deleteMarkers(Resource resource) { 
		// delete own markers
		if (markers.containsKey(resource.URI))
			markers.get(resource.URI).forEach[it.delete]
		
		// in case markers carried over from an earlier session
		var absolutePath = FileLocator.toFileURL(new URL(resource.URI.toString)).path
		val IFile file = ResourcesPlugin::workspace.root.getFileForLocation(new Path(absolutePath))
		file.deleteMarkers(IMarker.PROBLEM, true, 0)
	}

	/**
	 * Called after generation. Currently not used.
	 */	
	override public void afterGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
	}
	
}
