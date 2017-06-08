package org.xtext.example.ipl.validation

import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.TermFormula
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.Property
import org.xtext.example.ipl.iPL.Type
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeReal
import org.xtext.example.ipl.iPL.TypeSet
import org.xtext.example.ipl.iPL.Spec

import static extension org.eclipse.xtext.EcoreUtil2.*
import org.xtext.example.ipl.iPL.VarDec

class IPLTypeProvider {
	
	def IPLType fromType(Type t) {
		switch (t) {
			TypeInt: new IntType
			TypeReal: new RealType
			TypeBool: new BoolType
			TypeSet: new SetType(fromType((t as TypeSet).elem))
		}
	}
	
	def dispatch IPLType typeOf(ID e) {
		// TODO: Resolve id here
		val name = e.id
		
		val decls = e.getContainerOfType(Spec).decls
		
		val decl = decls.findLast[it instanceof VarDec && it.name == name] as VarDec
		
		if (decl != null) 
			return fromType(decl.type) 
		else {
			for (c : (e.allContainers.filter[it instanceof QAtom])) {
				val q = c as QAtom
				if (q != null && q.^var == name)
					return (typeOf(q.set) as SetType).elemType
			}
			return null
		}
	}
	
	def dispatch IPLType typeOf(Const c) {
		switch (c) {
			Int: new IntType
			Real: new RealType
			Bool: new BoolType
			//String: new StringType
		}
	}
	
	def dispatch IPLType typeOf(Formula f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(TAtom f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(QAtom f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(TermFormula f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(Fun f) {
		fromType(f.name.retType)
	}
	
	def dispatch IPLType typeOf(ExprOperation e) {
		if (e.left.typeOf instanceof RealType || e.right.typeOf instanceof RealType)
			new RealType
		else
			new IntType
	}
	
	def dispatch IPLType typeOf(Property p) {
		new IntType
	}
	
	def getParamTypes(Fun fun) {		
		fun.name.paramTypes.map[fromType]
	}
	
	
}