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
import org.osate.aadl2.PropertyType
import org.osate.aadl2.ReferenceType
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.IPLPackage
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.Type
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeLst
import org.xtext.example.ipl.iPL.TypeReal
import org.xtext.example.ipl.iPL.TypeSet
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.ComponentType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.ListType
import org.xtext.example.ipl.validation.RealType
import org.xtext.example.ipl.validation.SetType

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
	
	// type conversion: AADL -> IPL
	public def static IPLType typeFromPropType(PropertyType propertyType) {
		switch (propertyType) {
			AadlBoolean: new BoolType
			AadlInteger: new IntType 
			AadlReal: new RealType
			ReferenceType: new ComponentType('REFERENCE') // a reference to an AADL architectural element, 
												// could encode it as integers but this seems less broken
			org.osate.aadl2.ListType: new ListType(typeFromPropType(propertyType.elementType))
			default: null
		}
	}
	
	// type conversion: type declaration -> IPL
	public static def IPLType typesDecl2IPL(Type t) {
		switch (t) {
			TypeInt: new IntType
			TypeReal: new RealType
			TypeBool: new BoolType
			TypeSet: new SetType(IPLUtils.typesDecl2IPL((t as TypeSet).elem))
			TypeLst: new ListType(IPLUtils.typesDecl2IPL((t as TypeLst).elem))
		}
	}
	
	
	// type conversion: IPL -> SMT
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
