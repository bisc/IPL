package org.xtext.example.ipl.interfaces

import java.util.Map
import org.xtext.example.ipl.iPL.IPLSpec

// view -> SMT generator 
interface SmtViewGenerator { 
	
	// generate SMT for AADL views 
	public def String generateViewSmt(IPLSpec spec)

	public def boolean isViewGenerated() 
	
	// product of background generation; resets it itself
	public def Map getPropTypeMap() 

	// same
	public def Map getPropValueMap()
}