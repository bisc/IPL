package org.xtext.example.ipl

class IPLConfig {
	// whether flexible terms are given arguments (all of the vars in scope)
	static public val Boolean ENABLE_FLEXIBLE_ABSTRACTION_WITH_ARGS = true
	 
	// use the probing heuristic to coerce z3 into giving models of quantified variables
	static public val Boolean ENABLE_PROBING_VARS = true
}