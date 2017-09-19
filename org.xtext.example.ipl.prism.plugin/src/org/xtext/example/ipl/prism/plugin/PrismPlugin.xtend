package org.xtext.example.ipl.prism.plugin

import java.io.File
import java.net.URL
import java.util.List
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2
import java.io.FileNotFoundException
import java.rmi.UnexpectedException

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
	
	
	public def boolean verifyPrismBooleanProp(String property, List<String> paramsDecl, List<String> paramVals, String attemptName) {
		Boolean.parseBoolean(modelCheck(property, paramsDecl, paramVals, attemptName))
	}
	
	public def double runPrismQuery(String property, List<String> paramsDecl, List<String> paramVals, String attemptName) {
		val res = modelCheck(property, paramsDecl, paramVals, attemptName)
		if (res == 'Infinity')
			throw new UnexpectedException("Received infinity from prism: check that the path formula holds with P=1")
		
		Double.parseDouble(res)
	}
	
	public def close() {
		// really meaning to call the object, but it's a static method prevented by xtend
		PrismConnectorAPI::close  
	}
	
	private def String modelCheck(String property, List<String> paramsDecl, List<String> paramVals, String attemptName) {
		
		if (paramsDecl.size != paramVals.size)
			throw new IllegalArgumentException("Need the same quantity of parameter declarations and values")

		// put property into a file
		val String propsRelativePath = relativePrismLoc + attemptName + ".props"
		fsa.generateFile(propsRelativePath, property+'\n')

		var propsAbsolutePath = FileLocator.toFileURL(new URL(fsa.getURI(propsRelativePath/*"mapbot.props"*/).toString)).path
		var prismPolPath = FileLocator.toFileURL(new URL(fsa.getURI(relativePrismLoc + 'strat-out').toString)).path

		println("Model path: " + prismModelAbsolutePath)
		println("Props path: " + propsAbsolutePath)

		if(!new File(prismModelAbsolutePath).exists) 
			throw new FileNotFoundException("Error: prism model not found in " + prismModelAbsolutePath)
		
		
		//prep parameter string
		var String paramInst = ''
		
		for (i : 0 ..< paramsDecl.size) {
			if (paramInst.length > 0)
				 paramInst += ','
				
			paramInst += '''«paramsDecl.get(i)»=«paramVals.get(i)»'''
		}
		
		// call prism -- leaving default params in place as needed    
		var res = if (paramInst.length > 0)
			PrismConnectorAPI::modelCheckFromFileS(prismModelAbsolutePath, 
				propsAbsolutePath, prismPolPath, -1/*prop to check - all*/, paramInst)
		else  
			PrismConnectorAPI::modelCheckFromFileS(prismModelAbsolutePath, 
				propsAbsolutePath, prismPolPath)
			
		println('Prism result: ' + res)
		res
	// val res = PrismConnectorAPI.modelCheckFromFileS(myModel,myProps, myPolicy)
	/*var URL templateUrl = FileLocator.toFileURL(
	 * 	Platform.getBundle(Activator.PLUGIN_ID).getResource("model/")
	 * )
	 System::out.println(templateUrl)*/
	// getResource("res/sched/sched-model-template.pml"))
	}
	
	/*public def double verifyRewardQuery(){
		1.0
	}*/
}
