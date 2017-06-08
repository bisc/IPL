package org.xtext.example.ipl.validation

class RealType extends IPLType {
		
	public override equals(Object o) {
		return o instanceof RealType
	}
	
	public override toString() {
		"real"
	}
}