package org.xtext.example.ipl.prism.plugin

import java.net.URL
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2

class PrismPlugin {
	def boolean verify(String prop, IFileSystemAccess2 fsa) {
		println("PRISM!")

		// call prism   
		System.out.println(System.getProperty("java.library.path"));

		val PrismConnectorAPI pc = new PrismConnectorAPI()

		var prismModelUri = fsa.getURI("../model/prism/prismtmp.prism")
		var prismPropsUri = fsa.getURI("../model/prism/mapbot.props")
		var prismPolUri = fsa.getURI("../model/prism/strat-out")
		System::out.println(prismModelUri)

//	        irrelevant
//	        var homePath = ResourcesPlugin.getWorkspace().getRoot().getLocation().toString()
//	        System::out.println(homePath)
		println(new URL(prismModelUri.toString))

		var prismModelPath = FileLocator.toFileURL(new URL(prismModelUri.toString)).path
		var prismPropsPath = FileLocator.toFileURL(new URL(prismPropsUri.toString)).path
		var prismPolPath = FileLocator.toFileURL(new URL(prismPolUri.toString)).path

		println("path: " + prismModelPath)

		var res = PrismConnectorAPI.modelCheckFromFileS(prismModelPath, prismPropsPath, prismPolPath);
		println(res)
		
		true
	// val res = PrismConnectorAPI.modelCheckFromFileS(myModel,myProps, myPolicy)
	/*var URL templateUrl = FileLocator.toFileURL(
	 * 	Platform.getBundle(Activator.PLUGIN_ID).getResource("model/")
	 * )
	 System::out.println(templateUrl)*/
	// getResource("res/sched/sched-model-template.pml"))
	}
}
