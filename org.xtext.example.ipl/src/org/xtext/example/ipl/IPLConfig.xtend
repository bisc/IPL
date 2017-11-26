package org.xtext.example.ipl

/**
 *  Holds global configuration parameters for IPL verification
 */
class IPLConfig {
	 
	// set to remove all quantifiers (and replace each quantified variable with a free one) 
	// if false, removed only quantifiers of variables that are parameters of flexible abstractions
	static public val Boolean REMOVE_ALL_QUANTS = true
}