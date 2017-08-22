package org.xtext.example.ipl.interfaces

import java.util.List
import java.util.Map
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.IPLSpec

interface SmtGenerator {
	// generate AADL SMT
	public def String generateBackgroundSmt(IPLSpec spec)

	// generate SMT for formula 	
	public def String generateSmtFormula(Formula f)
	
	// generate SMT for negated formula
	public def String generateSmtFormulaNeg(Formula f)
	
	// needs to be populated with proper abstractions already, after generating for formula
	public def String generateSmtFlexDecl()
	
	public def void setBlockingValues(List<Map<String, Object>> blocks) 
	
	// set only for the final call
	public def void setFlexsVals(Map vals) 
	
	// product of background generation; resets it itself
	public def Map getPropTypeMap() 
	
	// same
	public def Map getPropValueMap() 

	// returns the scope declaration
	// won't clear it later
	public def Map getLastFormulaScopeDecls() 

	// won't clear it later
	public def Map getLastFormulaFlexDecls() 

	// won't clear it later
	public def Map getLastFormulaFlexClauses() 
	
	public def boolean isBackgroundGenerated() 

}