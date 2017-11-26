package org.xtext.example.ipl.interfaces

import java.util.List
import java.util.Map
import org.xtext.example.ipl.iPL.Formula

/**
 * API for a formula -> smt generator
 * Use one generator per each formula, do not reuse.
 */
interface SmtFormulaGenerator {
	
	// FORMULA GENERATION 
	 
	/** generate SMT for formula */ 
	public def String generateFormulaSmtFind(Formula f)
	
	/** generate SMT for negated formula */ 
	public def String generateFormulaSmtCheck(Formula f)
	
	/** returns a formula without quantifiers */
	public def Formula removeQuants(Formula f) 
	
	// FORMULA INFO/VALUES 
	
	/** returns variable declarations of a formula */
	public def Map getFormulaVarDecls()

	/** returns the flexible abstraction declarations */
	public def Map getFormulaFlexDecls() 

	/** returns the flexible clauses */
	public def Map getFormulaFlexClauses()
	
	/** returns list of args for each flexible abstraction */
	public def Map<String, List<String>> getFormulaFlexArgs()
	
	/** returns transfer clauses <name, clause object> */
	public def Map getTransferClausesSmt() 
	
	/** returns transfer clause types <name, type> */
	public def Map getTransferClausesTypes()
	
	// EXTERNAL MODIFICATIONS 
	
	/** Generates blocking clauses for a given list of values */
	public def String generateBlockingClauses(List<Map<String, Object>> blockingList) 
	
	/** set the values for each flexible abstraction/transfer clause for final verification */ 
	public def void setFlexsVals(Map vals) 
	

}