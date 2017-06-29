package org.xtext.example.ipl.validation

import org.xtext.example.ipl.validation.IPLType
import java.util.HashMap

class ComponentType extends IPLType {
	
	String name;
	ComponentType superType = null;
	HashMap<String, IPLType> members = new HashMap;
	
	new (String name) {
		this.name = name
	}
	
	new (String name, ComponentType superType) {
		this(name)
		this.superType = superType
	}
	
	def getName() { 
		name
	}
	
	def getSuperType() {
		superType
	}
	
	def getMemberType(String member) {
		members.get(member)
	}
	
	def addMember(String member, IPLType type) {
		if (!members.containsKey(member)) {
			members.put(member, type)
		}
	}
	
	override equals(Object that) {
		switch (that) {
			ComponentType: name == that.name
			default: false
		}
	}
	
	override toString() {
		"ComponentType(" + this.name + ": " + members + ")" 
	}

}