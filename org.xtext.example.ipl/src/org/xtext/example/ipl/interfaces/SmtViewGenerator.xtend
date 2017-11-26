package org.xtext.example.ipl.interfaces

import java.util.Map
import org.xtext.example.ipl.iPL.IPLSpec

/** API for a class that generates an SMT translation of an AADL view  */
interface SmtViewGenerator { 
	
	/** Generate SMT for AADL views described in the spec */ 
	public def String generateViewSmt(IPLSpec spec)

	/** Checks if view has been generated previously */
	public def boolean isViewGenerated() 
	
	/** Returns the map <property name, type> 
	 * A product of view generation 
	 */
	public def Map getPropTypeMap() 

	/** Returns the map <property name, value> 
	 * A product of view generation 
	 */
	public def Map getPropValueMap()
}