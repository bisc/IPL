package org.xtext.example.ipl.util

import java.io.BufferedReader
import java.io.File
import java.io.InputStreamReader
import java.rmi.UnexpectedException
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.osate.aadl2.AadlBoolean
import org.osate.aadl2.AadlInteger
import org.osate.aadl2.AadlReal
import org.osate.aadl2.Property
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.IPLPackage
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType

class IPLUtils { 
	/** 
	 * Run a shell command in the specified directory.  
	 * @param command command to be run
	 * @param dir the directory to run the command in. If dir is null, runs it in the current directory of the process.
	 * @return output of the command
	 */
	public def static String executeShellCommand(String command, File dir) {
		var StringBuffer output = new StringBuffer()
		System::out.println('''Shell command:«command»'''.toString)
		var Process p
		try {
			p = Runtime::getRuntime().exec(command, null, dir)
			p.waitFor()
			var BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()))
			var String line = ""
			while ((line = reader.readLine()) !== null) {
				output.append('''«line»
'''.toString)
			}
		} catch (Exception e) {
			e.printStackTrace()
		}

		return output.toString()
	}

	// helper to create ecore values
	public def static EObject createEcoreValueFromIPL(IPLType type, Object value) {
		switch (type) {
			BoolType: {
				val EClass eb = IPLPackage.eINSTANCE.bool
				val Bool i = EcoreUtil::create(eb) as Bool
				i.value = value.toString
				i
			}
			IntType: {
				val EClass ei = IPLPackage.eINSTANCE.int
				val Int i = EcoreUtil::create(ei) as Int
				i.value = value as Integer
				i
			}
			RealType: {
				val EClass er = IPLPackage.eINSTANCE.real
				val Real i = EcoreUtil::create(er) as Real
				i.value = value as Float
				i
			}
			ComponentType: { // replacing component references with integers
				val EClass ei = IPLPackage.eINSTANCE.int
				val Int i = EcoreUtil::create(ei) as Int
				i.value = value as Integer
				i
			}
			default:
				throw new UnexpectedException("Unknown type")
		}
	}
	
	// type conversion AADL -> IPL
	public def static IPLType typeFromPropType(Property property) {
		switch (property.propertyType) {
			AadlBoolean: new BoolType
			AadlInteger: new IntType 
			AadlReal: new RealType
			default: null
		}
	}
	
	// type conversion IPL -> SMT
	public def static String typesIPL2Smt(IPLType t) {
		switch (t) {
			BoolType: 'Bool'
			IntType: 'Int'
			RealType: 'Real'
			ComponentType: 'ArchElem'
			default: 'UNKNOWN TYPE'
		}
	}
	
	// var name to free var name
	public def static String freeVar(String varName) {
		varName + '_free'
	}
	
	// var name to propositional abstraction name
	public def static String propAbst(String varName) {
		varName + '_propAbst'
	}
	
}
