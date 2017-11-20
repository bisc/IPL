package org.xtext.example.ipl.validation

import org.xtext.example.ipl.validation.IPLType
import java.util.HashMap

class ComponentType extends IPLType {
	
	private String name;
	private ComponentType superType = null;
	private HashMap<String, IPLType> members = new HashMap;
	
	// the value of name when it's declared as an architectural element
	// results in equality checks passing (because it can be a reference to any component type)
	public static final String DECLARATION_NAME = 'DECLARATION' 
	// name when the component's object wasn't found in an aadl model
	public static final String NOT_FOUND_NAME = 'NOT_FOUND' 
	
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
			ComponentType: name == that.name || name == DECLARATION_NAME || that.name == DECLARATION_NAME
			default: false
		}
	}
	
	override toString() {
		"ComponentType("+ this.name + ")"
	}

}