package org.xtext.example.ipl.interfaces

/**
 * Captures the result of verification
 */
class VerificationResult { 
	
	private boolean isValid
	private boolean isError
	private String message   
	
	public def boolean isValid() { 
		isValid
	}
	
	public def boolean isError() { 
		isError
	}
	
	public def String getMessage() { 
		message
	}
	
	/** Returned if the formula is valid */
	static public def VerificationResult valid() { 
		val vr = new VerificationResult 
		vr.isValid = true
		vr.isError = false
		vr.message = 'Valid'   
		vr
	} 
	
	/** Returned if the formula is invalid */
	static public def VerificationResult invalid() { 
		val vr = new VerificationResult 
		vr.isValid = false
		vr.isError = false
		vr.message = 'Invalid'   
		vr
	} 
	
	/** Returned if there was an error during verification */
	static public def VerificationResult error(String errorMsg) { 
		val vr = new VerificationResult 
		vr.isValid = false
		vr.isError = false
		vr.message = errorMsg
		vr
	} 
	
}
