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
import org.eclipse.xtext.generator.AbstractGenerator
import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.generator.IGeneratorContext
import org.eclipse.xtext.nodemodel.util.NodeModelUtils
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl
import org.xtext.example.ipl.smt.herbrand.SmtVerifierHerbrand
import org.xtext.example.ipl.util.IPLPrettyPrinter
import org.xtext.example.ipl.util.TimeRec
import org.xtext.example.ipl.validation.IPLRigidityProvider

//import org.xtext.example.ipl.iPL.EDouble

/**
 * Generates code from your model files on save.
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#code-generation
 */
class IPLGenerator extends AbstractGenerator {
	
	private val Map<URI, List<IMarker>> markers = new HashMap
	
	// setting up for timing 
	override public void beforeGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		// set up timing
		var mxb = ManagementFactory.getThreadMXBean()
		mxb.threadContentionMonitoringEnabled = true
		println('CPU time support available:' + mxb.isThreadCpuTimeSupported)
		println('CPU time support enabled:' + mxb.isThreadCpuTimeEnabled)
		println('Contention monitoring:' + mxb.isThreadContentionMonitoringEnabled)
		
		TimeRec::reset 
		
		deleteMarkers(resource)
	}

	override public void doGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		val specs = resource.allContents.filter(IPLSpec).toList
		
		// have to renew smt verifier every formula to not carry state in SMTGenerator over
		specs.forEach[ spec |
			spec.formulas.forEach[ f, i |
				val filename = resource.URI.trimFileExtension.lastSegment + '-f' + i // no extension, smt generator adds it
				println('\n\nVerifying ' + IPLPrettyPrinter::print_formula(f))
				val node = NodeModelUtils::getNode(f) // for marker creation
				if(!IPLRigidityProvider::isRigid(f)) { // non-rigid, full-scale IPL
					// find a model declaration
					val mdls = spec.decls.filter[it instanceof ModelDecl]
					if (mdls.size == 0) {
						println('Error: cannot verify non-rigid formulas without a model')
					} else {  
						TimeRec::startTimer("verifyNonRigidFormula")
						val boolean res = (new SmtVerifierHerbrand).verifyNonRigidFormula(f, mdls.get(0) as ModelDecl, spec, filename, fsa)
						TimeRec::stopTimer("verifyNonRigidFormula")
						
						println("IPL non-rigid formula verified, result: " + res)
						createMarker(resource, node.startLine, res)
					} 
				} else { //rigid, shortcut
						val res = (new SmtVerifierHerbrand).verifyRigidFormula(f, spec, filename, fsa)
						println("IPL rigid formula verified, result: " + res)
						createMarker(resource, node.startLine, res)
				}
			]
		]
		
		//direct check in comparison
		//(new DirectPrismChecker).directCheck(fsa)
		
		// output timing results
		TimeRec::exportAllTimers(resource.URI.trimFileExtension.lastSegment, fsa)
	}
	
	def private createMarker(Resource resource, int line, boolean result) { 
		var absolutePath = FileLocator.toFileURL(new URL(resource.URI.toString)).path
		val IFile file = ResourcesPlugin::workspace.root.getFileForLocation(new Path(absolutePath))
		
		val marker = file.createMarker(IMarker.PROBLEM/*'org.xtext.example.ipl.marker'*/)
		
		var markerList = markers.get(resource.URI) 
		if (markerList === null) { 
			markerList = new LinkedList
			markers.put(resource.URI, markerList)
		}
		markerList.add(marker)
		
		if (marker.exists()) {
			println('Marker exists') 
			if (result) { 
				marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_INFO);
				marker.setAttribute(IMarker.MESSAGE, "Formula valid");
			} else { 
				marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_WARNING);
				marker.setAttribute(IMarker.MESSAGE, "Formula invalid");	
			}
			marker.setAttribute(IMarker.LINE_NUMBER, line); 
		} else 
			throw new UnexpectedException('Failed to create a result marker')
	}
	
	def private deleteMarkers(Resource resource) { 
		// delete own markers
		if (markers.containsKey(resource.URI))
			markers.get(resource.URI).forEach[it.delete]
		
		// in case markers carried over from an earlier session
		var absolutePath = FileLocator.toFileURL(new URL(resource.URI.toString)).path
		val IFile file = ResourcesPlugin::workspace.root.getFileForLocation(new Path(absolutePath))
		file.deleteMarkers(IMarker.PROBLEM, true, 0)
	}
	
	override public void afterGenerate(Resource resource, IFileSystemAccess2 fsa, IGeneratorContext context) {
		/*var z3FilePath = FileLocator.toFileURL(new URL(resource.URI.toString)).path
		val IFile file = ResourcesPlugin::workspace.root.getFileForLocation(new Path(z3FilePath))
		val marker = file.createMarker('org.xtext.example.ipl.marker')
		marker.setAttribute(IMarker.SEVERITY, IMarker::SEVERITY_INFO);
		marker.setAttribute(IMarker.MESSAGE, 'testmessage');
		marker.setAttribute(IMarker.LINE_NUMBER, 5); 
		marker.setAttribute(IMarker.CHAR_START,0);
		marker.setAttribute(IMarker.CHAR_END,5);*/
	}
	
}
