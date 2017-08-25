package org.xtext.example.ipl.standalone

import org.eclipse.xtext.generator.IFileSystemAccess2
import org.xtext.example.ipl.prism.plugin.PrismPlugin
import org.xtext.example.ipl.TimeRec

// uses prism directly to check properties
class DirectPrismChecker {
	
	def directCheck(IFileSystemAccess2 fsa){ 
		TimeRec::startTimer("directCheck")
		
		
		println('Starting direct check')
		var checkRes = true
		for (locStart: 0..<7)
			for (locEnd: 0..<7) {
				val pp = new PrismPlugin('prism_probs', fsa) 
				val res = pp.runPrismQuery('R{"time"}min=? [F l = ' + locEnd + ']', newArrayList('INITIAL_LOCATION', 'TARGET_LOCATION', 'INITIAL_BATTERY'),
					newArrayList(String.valueOf(locStart), String.valueOf(locEnd), String.valueOf(30000)), "directCheck")
				 
				// TODO query AADL here to check times from the prediction model?  
				 
				if (res == 'infinity' || res > 55)
					checkRes = checkRes && true
				else 
					checkRes = checkRes && false
				
			}
					
		if (checkRes)
			println('Direct check: true')
		else 
			println('Direct check: false')
					
		TimeRec::stopTimer("directCheck")
	}
	
	def static void main(String[] args) {
		
	}
}