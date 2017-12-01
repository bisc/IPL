package org.xtext.example.ipl.interfaces

import org.eclipse.xtext.generator.IFileSystemAccess2
import org.eclipse.xtext.util.CancelIndicator
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl

/**
 * API for a class that performs verification based on SMT value-finding. 
 */
interface SmtVerifier {
	/**  full-scale IPL verification */
	public def VerificationResult verifyNonRigidFormula(Formula origFormula, ModelDecl md, IPLSpec spec,
		String filename, IFileSystemAccess2 fsa, CancelIndicator ci)
		
	/** finds all variable assignments that satisfy a formula
	* thus, these are candidates for the formula to NOT be valid
	* @returns true if managed to find all models, false otherwise 
	* implicit result: populates scopeDecls and flexDecls; maybe scopeVals 
	*/
	public def boolean findModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa)
	
	/** Simple verification by SAT of a negated formula without finding flexible interpretations. 
	 * Works correctly on rigid formulas, and is severely incomplete on flexibe formulas.  
	 * Touches quantified state but not deep state for the formula generator.  
	 */
	public def VerificationResult verifyRigidFormula(Formula f, IPLSpec s, String filename,
		IFileSystemAccess2 fsa, CancelIndicator ci)
	
}