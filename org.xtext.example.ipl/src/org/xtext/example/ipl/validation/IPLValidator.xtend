/*
 * generated by Xtext 2.10.0
 */
package org.xtext.example.ipl.validation

import java.util.HashMap
import org.eclipse.xtext.validation.Check
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLPackage
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation

import static extension org.eclipse.xtext.EcoreUtil2.*
import static extension org.xtext.example.ipl.validation.IPLRigidityProvider.*

/**
 * This class contains custom validation rules. 
 * 
 * Be careful with using class variables: this validator is run on many programs. 
 * 
 * See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#validation
 */
class IPLValidator extends AbstractIPLValidator {

	public static val WRONG_TYPE = 'wrongType'
	public static val UNDEFINED = 'undefined'
	public static val INV_FLEXIBLE = 'invalidFlexible'

	// FIXME this cache doesn't really work because formula objects aren't the same in consecutive invocations
	private static val cache = new HashMap<Formula, IPLType>

	// DO NOT reuse a type provider across many sessions because it saves the names in a cache

	def IPLType getType(Formula f) {

		// this cache doesn't work well because new formula objects are created every time
		var type = cache.get(f)

		if (type === null) {
			type = (new IPLTypeProvider).typeOf(f)
			cache.put(f, type);
		}

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
			error("expected bool type, but was " + leftType, IPLPackage.Literals.FORMULA_OPERATION__LEFT, WRONG_TYPE)
		}

		val rightType = getType(op.right)

		if (!(rightType instanceof BoolType)) {
			error("expected bool type, but was " + rightType, IPLPackage.Literals.FORMULA_OPERATION__RIGHT, WRONG_TYPE)
		}

	}

	@Check
	def checkTypes(QAtom q) {

		val expType = getType(q.exp)

		if (!(expType instanceof BoolType)) {
			error("expected bool type, but was " + expType, IPLPackage.Literals.QATOM__EXP, WRONG_TYPE)
		}

		val domType = (new IPLTypeProvider).getQdomType(q.dom);

		if (!(domType instanceof SetType || domType instanceof IntType || 
			domType instanceof BoolType || domType instanceof RealType || domType instanceof ElementType
		)) {
			error("expected set or base type, but was " + domType, IPLPackage.Literals.QATOM__DOM, WRONG_TYPE)
		}

	}

	@Check
	def checkTypes(TAtomBinary t) {
		if (t === null || t.op === null)
			return;

		val expType1 = getType(t.left)
		val expType2 = getType(t.right)

		if (!(expType1 instanceof BoolType)) {
			error("expected bool type, but was " + expType1, IPLPackage.Literals.TATOM_BINARY__LEFT, WRONG_TYPE)
		}

		if (!(expType2 instanceof BoolType)) {
			error("expected bool type, but was " + expType2, IPLPackage.Literals.TATOM_BINARY__RIGHT, WRONG_TYPE)
		}

	}

	@Check
	def checkTypes(TAtomUnary t) {
		val expType = getType(t.exp)

		if (!(expType instanceof BoolType)) {
			error("expected bool type, but was " + expType, IPLPackage.Literals.TATOM_UNARY__EXP, WRONG_TYPE)
		}
	}

	@Check
	def checkTypes(TermOperation op) {

		val leftType = getType(op.left)
		val rightType = getType(op.right)

		switch (op.op) {
			case "<",
			case ">",
			case "<=",
			case ">=": {
				if (!(leftType instanceof IntType || leftType instanceof RealType)) {
					error("expected numeric type, but was " + leftType, IPLPackage.Literals.TERM_OPERATION__LEFT,
						WRONG_TYPE)
				}

				if (!(rightType instanceof IntType || rightType instanceof RealType)) {
					error("expected numeric type, but was " + rightType, IPLPackage.Literals.TERM_OPERATION__RIGHT,
						WRONG_TYPE)
				}
			}
			case "=",
			case "!=": {
				// if not numeric
				if (! ((leftType instanceof IntType || leftType instanceof RealType) &&
						(rightType instanceof IntType || rightType instanceof RealType)	))
					// then types have to be equal
					if (leftType != rightType) {
						error("expected equal types, but left was " + leftType + " and right was " + rightType,
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
			error("expected numeric type, but was " + leftType, IPLPackage.Literals.EXPR_OPERATION__LEFT, WRONG_TYPE)
		}

		if (!(rightType instanceof IntType || rightType instanceof RealType)) {
			error("expected numeric type, but was " + rightType, IPLPackage.Literals.EXPR_OPERATION__RIGHT, WRONG_TYPE)
		}
	}

	@Check
	def checkTypes(Fun f) {
		val paramTypesIt = (new IPLTypeProvider).getDeclaredParamTypes(f).iterator()

		for (a : f.args) {
			if (!paramTypesIt.hasNext) {
				// FIXME detects mismatch correctly if args > formal params, but not if formal params > args 
				error("wrong number of arguments to function", IPLPackage.Literals.FUN__ARGS, WRONG_TYPE)
			} else {
				val expType = paramTypesIt.next
				val actType = getType(a)
				if (actType != expType) {
					error("expected " + expType + " type, but was " + actType, IPLPackage.Literals.FUN__ARGS,
						WRONG_TYPE)
				}
			}
		}
	}

	@Check
	def checkTypes(PropertyExpression p) {
		val type = getType(p.left)

		switch (type) { 
			ComponentType:
				if (type.getMemberType(p.right.id) === null) {
					error("Not a property: " + p.right.id, IPLPackage.Literals.PROPERTY_EXPRESSION__RIGHT, UNDEFINED)
				}
			default:
				error("Not an archelem", IPLPackage.Literals.PROPERTY_EXPRESSION__LEFT, WRONG_TYPE)
		}
	}

	@Check
	def checkDefined(ID id) {
		// reusing the type-fetching to determine definition
//		if ((new IPLTypeProvider).typeOf(id) === null) {
		if (getType(id) === null) {	
			// old version
			//if (!(new IPLTypeProvider).isDef(id)) {
			error("Undefined symbol " + id.id, IPLPackage.Literals.ID__ID, UNDEFINED)
		}
	}

	@Check
	def checkFlexibleQuant(QAtom t) {
		val inModality = t.getContainerOfType(TAtomUnary) !== null ||
			 t.getContainerOfType(TAtomBinary) !== null
		val rp = new IPLRigidityProvider
	
		if (inModality && !rp.isRigid(t.exp)) {
			error("Flexible quantification used inside modality", IPLPackage.Literals.QATOM__EXP, INV_FLEXIBLE)
		}

		if (inModality && !rp.isRigid(t.dom)) {
			error("Flexible quantification used inside modality", IPLPackage.Literals.QATOM__DOM, INV_FLEXIBLE)
		}
	}

	// @Check
	// TODO rethink this validation
	/*def checkModality(TAtom t) {
		val missingModelExpr = t.getContainerOfType(ModelExpr) === null

		if (missingModelExpr) {
			error("Modality used outside behavioral model expression", IPLPackage.Literals.TATOM__OP, INV_FLEXIBLE)
		}
	}*/

	@Check
	def checkModelExpr(ModelExpr t) {
		val inModelExpr = t.allContainers.findFirst[it instanceof ModelExpr] !== null

		if (inModelExpr) {
			error("Nested model expressions", IPLPackage.Literals.PRISM_EXPR__EXPR, INV_FLEXIBLE)
		}
	}

// TODO check that no more than one model 
// TODO check that declared and passed model parameters match 	
// TODO check for name duplicates in declarations
}
