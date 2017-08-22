package org.xtext.example.ipl.interfaces

import org.eclipse.xtext.generator.IFileSystemAccess2
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelDecl

interface SmtVerifier {
	// full-scale IPL verification
	public def boolean verifyNonRigidFormula(Formula origFormula, ModelDecl md, IPLSpec spec, String filename,
		IFileSystemAccess2 fsa)
		
	// finds all variable assignments that satisfy a negated formula
	// thus, these are candidates for the formula to NOT be valid
	// @returns true if managed to find all models, false otherwise 
	// implicit result: populates scopeDecls and flexDecls; maybe scopeVals 
	public def Boolean findNegModels(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa) 
	
	// simple verification of negated formula
	// touches: scopeDecls  (but not flexDecls)
	public def boolean verifyRigidFormula(Formula f, IPLSpec s, String filename, IFileSystemAccess2 fsa)
	
}