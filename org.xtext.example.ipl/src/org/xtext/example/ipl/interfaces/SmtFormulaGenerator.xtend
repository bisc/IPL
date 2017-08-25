package org.xtext.example.ipl.interfaces

import java.util.List
import java.util.Map
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.IPLSpec

// use only one generator per each formula, do not reuse
interface SmtFormulaGenerator {
	
	// FORMULA GENERATION 
	 
	// generate SMT for formula 	
	public def String generateSmtFormula(Formula f)
	
	// generate SMT for negated formula
	public def String generateSmtFormulaNeg(Formula f, boolean probing)
	
	// FORMULA VALUES 

	// returns the scope declaration
	// won't clear it later
	public def Map getFormulaScopeDecls() 

	// won't clear it later
	public def Map getFormulaFlexDecls() 

	// won't clear it later
	public def Map getFormulaFlexClauses()

	// EXTERNAL MODIFICATIONS 

	public def void setBlockingValues(List<Map<String, Object>> blocks)
	
	// set only for the final call
	public def void setFlexsVals(Map vals) 
	

}