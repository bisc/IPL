package org.xtext.example.ipl.validation

class IntType extends IPLType {
	
	public override equals(Object o) {
		return o instanceof IntType
	}
	
	public override toString() {
		"int"
	}
}