/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.validation

import org.xtext.example.ipl.iPL.FormulaOperation
import org.eclipse.xtext.validation.Check
import org.xtext.example.ipl.iPL.IPLPackage
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Fun

/**
 * This class contains custom validation rules. 
 *
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#validation
 */
class IPLValidator extends AbstractIPLValidator {
	
	val typeProvider = new IPLTypeProvider
	
	public static val WRONG_TYPE = 'wrongType'

	def IPLType getType(Formula f) {
		val type = typeProvider.typeOf(f)
	
//		// Apparently we can't have a StructRef to a child of a container?	
//		if (type == null && f instanceof ID)
//			error("Undefined symbol " + (f as ID).id,
//						IPLPackage.Literals.ID__ID, WRONG_TYPE)
			
		type
	}

	@Check
	def checkTypes(FormulaOperation op) {
		
		val leftType = getType(op.left)
		
		if (!(leftType instanceof BoolType)) {
			error("expected bool type, but was " + leftType,
				IPLPackage.Literals.FORMULA_OPERATION__LEFT, WRONG_TYPE)
		}
		
		val rightType = getType(op.right)
		
		if (!(rightType instanceof BoolType)) {
			error("expected bool type, but was " + rightType,
				IPLPackage.Literals.FORMULA_OPERATION__RIGHT, WRONG_TYPE)
		}
		
	}
	
	@Check
	def checkTypes(QAtom q) {
		
		val expType = getType(q.exp)
		
		if (!(expType instanceof BoolType)) {
			error("expected bool type, but was " + expType,
				IPLPackage.Literals.QATOM__EXP, WRONG_TYPE)
		}
		
		val setType = getType(q.set);
		
		if (!(setType instanceof SetType)) {
			error("expected set type, but was " + setType,
				IPLPackage.Literals.QATOM__SET, WRONG_TYPE)
		}
		
	}
	
	@Check
	def checkTypes(TAtom t) {
		
		val expType = getType(t.exp)
		
		if (!(expType instanceof BoolType)) {
			error("expected bool type, but was " + expType,
				IPLPackage.Literals.QATOM__EXP, WRONG_TYPE)
		}
	}
	
	@Check
	def checkTypes(TermOperation op) {
		
		val leftType = getType(op.left)
		val rightType = getType(op.left)
		
		switch (op.op) {
			case "<",
			case ">",
			case "<=",
			case ">=": {		
				if (!(leftType instanceof IntType || leftType instanceof RealType)) {
					error("expected numeric type, but was " + leftType,
						IPLPackage.Literals.TERM_OPERATION__LEFT, WRONG_TYPE)
				}
				
				if (!(leftType instanceof IntType || leftType instanceof RealType)) {
					error("expected numeric type, but was " + rightType,
						IPLPackage.Literals.TERM_OPERATION__RIGHT, WRONG_TYPE)
				}
			}
			
			case "=",
			case "!=": {
				if (leftType != rightType) {
					error("expected equal types, but left was " + leftType +
						" and right was " + rightType,
						IPLPackage.Literals.TERM_OPERATION__RIGHT, WRONG_TYPE)
				}
			}
		}
	}
	
	@Check
	def checkTypes(ExprOperation op) {
		
		val leftType = getType(op.left)
		val rightType = getType(op.left)
		
		if (!(leftType instanceof IntType || leftType instanceof RealType)) {
			error("expected numeric type, but was " + leftType,
				IPLPackage.Literals.EXPR_OPERATION__LEFT, WRONG_TYPE)
		}
		
		if (!(leftType instanceof IntType || leftType instanceof RealType)) {
			error("expected numeric type, but was " + rightType,
				IPLPackage.Literals.EXPR_OPERATION__RIGHT, WRONG_TYPE)
		}
	}
	
	@Check
	def checkTypes(Fun f) {
		val paramTypesIt = typeProvider.getParamTypes(f).iterator()
		
		for (a : f.args) {
			
			if (!paramTypesIt.hasNext) {
				error("wrong number of arguments to function",
					IPLPackage.Literals.FUN__ARGS, WRONG_TYPE)
			} else {
				val expType = paramTypesIt.next
				val actType = getType(a)
				if (actType != expType) {
					error("expected " + expType + " type, but was " + actType,
						IPLPackage.Literals.FUN__ARGS, WRONG_TYPE)
				}
			}
		}
	}
	
	
}
