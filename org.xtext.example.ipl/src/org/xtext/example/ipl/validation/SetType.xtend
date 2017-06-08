package org.xtext.example.ipl.validation

import org.xtext.example.ipl.validation.IPLType

class SetType extends IPLType {
	
	val IPLType elemType;
	
	new(IPLType elemType) {
		this.elemType = elemType
	} 
	
	public override equals(Object o) {
		return o instanceof SetType && (o as SetType).elemType == elemType
	}
	
	def getElemType() {
		elemType
	}
	
	public override toString() {
		"{" + elemType.toString + "}"
	}
}