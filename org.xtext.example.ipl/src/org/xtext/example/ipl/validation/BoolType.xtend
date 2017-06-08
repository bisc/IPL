package org.xtext.example.ipl.validation

class BoolType extends IPLType {
		
	public override equals(Object o) {
		return o instanceof BoolType
	}
	
	public override toString() {
		"bool"
	}
}