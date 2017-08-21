package org.xtext.example.ipl.prism.plugin

import java.net.URL
import java.util.List
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2

class PrismPlugin {
	val String relativePrismLoc = "../model/prism/"
	
	var String modelName
	var PrismConnectorAPI pc
	var IFileSystemAccess2 fsa
	
	var String prismModelAbsolutePath
	
	new(String _modelName, IFileSystemAccess2 _fsa) { 
		modelName = _modelName
		fsa = _fsa
		
		pc = new PrismConnectorAPI()
		prismModelAbsolutePath = FileLocator.toFileURL(new URL(fsa.getURI(relativePrismLoc + 
			_modelName + ".prism").toString)).path
		}
	
	
	public def boolean verifyProbQuery(String prop, List<String> params) {

		// put property into a file
		val String propsRelativePath = relativePrismLoc + "myprops.props"
		fsa.generateFile(propsRelativePath, prop)

		var propsAbsolutePath = FileLocator.toFileURL(new URL(fsa.getURI(relativePrismLoc + "mapbot.props").toString)).path
		var prismPolPath = FileLocator.toFileURL(new URL(fsa.getURI(relativePrismLoc + 'strat-out').toString)).path

		println("Model path: " + prismModelAbsolutePath)
		println("Props path: " + propsAbsolutePath)

		// call prism   
		var res = PrismConnectorAPI::modelCheckFromFileS(prismModelAbsolutePath, propsAbsolutePath, prismPolPath);
		println(res)
		
		true
	// val res = PrismConnectorAPI.modelCheckFromFileS(myModel,myProps, myPolicy)
	/*var URL templateUrl = FileLocator.toFileURL(
	 * 	Platform.getBundle(Activator.PLUGIN_ID).getResource("model/")
	 * )
	 System::out.println(templateUrl)*/
	// getResource("res/sched/sched-model-template.pml"))
	}
	
	public def double verifyRewardQuery(){
		1.0
	}
}
