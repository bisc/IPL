package org.xtext.example.ipl

// Holds global configuration parameters for IPL verification
class IPLConfig {
	// whether flexible terms are given arguments (all of the vars in scope)
	// DO NOT SWITCH OFF
	static public val Boolean ENABLE_FLEXIBLE_ABSTRACTION_WITH_ARGS = true
	 
	// use the probing heuristic to coerce z3 into giving models of quantified variables
	// NOT USED
	static public val Boolean ENABLE_PROBING_VARS = true

	// set to remove all quantifiers (and replace each quantified variable with a free one) 
	// if false, removed only quantifiers of variables that are parameters of flexible abstractions
	static public val Boolean REMOVE_ALL_QUANTS = true
}