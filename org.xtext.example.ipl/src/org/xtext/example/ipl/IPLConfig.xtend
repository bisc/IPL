package org.xtext.example.ipl

/**
 *  Holds global configuration parameters for IPL verification
 */
class IPLConfig {
	 
	// if true, removes all quantifiers (and replaces each quantified variable with a free one) 
		// this leads to comb explosion when some quantifiers are auxiliary and do not affect the flexible clause
		// however, recommended when there's too many quantifiers -- otherwise, the performance of SMT is poor 
	// if false, removed only quantifiers of variables that are parameters of flexible abstractions
		// a smarter tactic, reduces the number of models
	static public val Boolean REMOVE_ALL_QUANTS = false
}