package org.xtext.example.ipl.transform

import java.util.Map
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.PrismExpr
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.validation.IPLType

/** Transforms arbitrary clauses (subformulas) into their provided values 
 * Does not touch any other clauses. */  
class Clause2ValueTransformer {

	private Map<Formula, IPLType> formulaTypes
	private Map<Formula, Object> formulaValues

	/** Replaces all occurrences of _values.keys in f with _values.values */
	def public EObject replaceClausesWithValues(Formula f, Map<Formula, Object> _values, Map<Formula, IPLType> _types) {
		formulaValues = _values
		formulaTypes = _types

		return replace(f)
	}

	private dispatch def EObject replace(QAtom f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.exp)
			return f
		}
	}

	private dispatch def EObject replace(FormulaOperation f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.left)
			replace(f.right)
			return f
		}

	}

	private dispatch def EObject replace(ExprOperation f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.left)
			replace(f.right)
			return f
		}
	}

	private dispatch def EObject replace(Fun f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			f.args.forEach [
				replace(it)
			]
			return f
		}
	}

	private dispatch def EObject replace(TermOperation f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.left)
			replace(f.right)
			return f
		}
	}

	private dispatch def EObject replace(Negation f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.child)
			return f
		}
	}

	private dispatch def EObject replace(TAtomUnary f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.exp)
			return f
		}
	}
	
	private dispatch def EObject replace(TAtomBinary f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.left)
			replace(f.right)
			return f
		}
	}

	private dispatch def EObject replace(Const f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else 
			return f
	}

	private dispatch def EObject replace(ID f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else 
			return f
	}

	private dispatch def EObject replace(PropertyExpression f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.left)
			// transform(f.right) -- Prop is not a Formula
			return f
		}
	}
	
	private dispatch def EObject replace(ModelExpr f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.expr)
			replace(f.params)
			return f
		}
	}
	
	private dispatch def EObject replace(PrismExpr f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			replace(f.expr)
			return f
		}
	}
	
	private dispatch def EObject replace(ModelParamExpr f) {
		if (formulaValues.containsKey(f))
			return valueForFormula(f)
		else {
			f.vals.forEach[replace(it)] 
			return f
		}
	}

	private def EObject valueForFormula(EObject f) {
		val value = IPLUtils::createEcoreValueFromIPL(formulaTypes.get(f), formulaValues.get(f)) 
		EcoreUtil::replace(f, value)
		return value
	}

}
