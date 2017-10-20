package org.xtext.example.ipl.util

import java.lang.management.ManagementFactory
import java.net.URL
import java.nio.file.Files
import java.nio.file.Paths
import java.util.HashMap
import java.util.Map
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2

class TimeRecWall {
	
	private static Map<String, Long> timers = new HashMap
	private static Map<String, String> log = newHashMap



	public def static startTimer(String timerName) {
		if(timers.containsKey(timerName)){ // save an old timer 
			dumpTimerToLog(timerName)
		}
		
		timers.put(timerName, getThreadWallTime)
	}
	
	public def static stopTimer(String timerName) {
		if(!timers.containsKey(timerName))
			throw new IllegalArgumentException('Timer ' + timerName + ' not found')
		
		dumpTimerToLog(timerName)
		timers.remove(timerName)
	}
	
	private def static void dumpTimerToLog(String timer) { 
		// better log
		if(!log.containsKey(timer))
			log.put(timer, timer) // initialize with the timer name
			
		log.put(timer, log.get(timer) + ',' + (getThreadWallTime - timers.get(timer))/(1000L as float))
	}

	public def static void exportAllTimers(String attemptName, IFileSystemAccess2 fsa) {
		timers.forEach[key, value| dumpTimerToLog(key)]
		
		println('Exported timing log')
		//fsa.generateFile('timing_' + attemptName + '.time', timerLog)
		var path = FileLocator.toFileURL(new URL(fsa.getURI('').trimSegments(1).toString)).path
		//var File file = new File()
		val file = Paths.get(path + '/timing_data/' + 'timing_' + attemptName + '.csv')
		//Files.write(file, timerLog.getBytes())
		Files.write(file, log.values.join('\n').getBytes())
	}

	public def static reset(){
		 log.clear
		 timers.clear
	}

	public def static long getThreadWallTime() {
		 System.currentTimeMillis();
	}

}
