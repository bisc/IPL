package org.xtext.example.ipl.util

import java.lang.management.ManagementFactory
import java.net.URL
import java.nio.file.Files
import java.nio.file.Paths
import java.util.HashMap
import java.util.Map
import org.eclipse.core.runtime.FileLocator
import org.eclipse.xtext.generator.IFileSystemAccess2

class TimeRecCPU {
	
	private static Map<String, Pair<Long, Long>> timers = new HashMap
	private static String timerLog = ''
	private static Map<String, String> log = newHashMap

	public def static startTimer(String timerName) {
		if(timers.containsKey(timerName)){ // save an old timer 
			dumpTimerToLog(timerName)
		}
		
		timers.put(timerName, getThreadUserTime -> getThreadTotalTime)
	}
	
	public def static stopTimer(String timerName) {
		if(!timers.containsKey(timerName))
			throw new IllegalArgumentException('Timer ' + timerName + ' not found')
		
		dumpTimerToLog(timerName)
		timers.remove(timerName)
	}
	
	private def static void dumpTimerToLog(String timer) { 
		val Pair<Long, Long> p = timers.get(timer)
		val out = '''«timer»,«(getThreadUserTime -  p.key)/(1000000000L as float)»,''' + 
		'''«(getThreadTotalTime - p.value)/(1000000000L as float)»
		'''
		timerLog += out 
		
		// better log
		if(!log.containsKey(timer))
			log.put(timer, timer) // initialize with the timer name
			
		log.put(timer, log.get(timer) + ',' + (getThreadTotalTime -  p.value)/(1000000000L as float))
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
		 timerLog = 'Timer name,user time,total time\n'
		 log.clear
		 timers.clear
	}

	// user + system
	public def static long getThreadTotalTime() {
		ManagementFactory.getThreadMXBean().currentThreadCpuTime
	}

	// user
	public def static long getThreadUserTime() {
		ManagementFactory.getThreadMXBean().currentThreadUserTime
	}
}
