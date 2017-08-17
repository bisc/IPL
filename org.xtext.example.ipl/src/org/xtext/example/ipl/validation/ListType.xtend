package org.xtext.example.ipl.validation

import org.xtext.example.ipl.validation.IPLType

class ListType extends IPLType {
	
	val IPLType elemType;
	
	new(IPLType elemType) {
		this.elemType = elemType
	} 
	
	public override equals(Object o) {
		return o instanceof ListType && (o as ListType).elemType == elemType
	}
	
	def getElemType() {
		elemType
	}
	
	public override toString() {
		"<" + elemType.toString + ">"
	}
}