package org.xtext.example.ipl.transform

import java.rmi.UnexpectedException
import java.util.Map
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.validation.IPLType

/** Replaces rigid variables/constants with provided values 
* Useful inside flexible subformulas
*/
class Var2ValueTransformer {

	var Map<String, Object> vals
	var Map<String, IPLType> decls
	//var Map<Pair<String, IPLType>, Map<Integer, String>> propMap
	var Map<String, IPLType> propTypeMap
	var Map<String, Map<Integer, Object>> propValueMap

	/**  Replaces all occurrences of variables with their valuations
	 * Returns the next object (potentially changed if on top*/
	public def EObject replaceVarsWithValues(EObject f, Map<String, Object> valuation, 
		Map<String, IPLType> declarations, Map propertyTypeMap, Map propertyValueMap
	) {
		if (valuation.size == 0 )
			return f;
		
		vals = valuation
		decls = declarations
		propTypeMap = propertyTypeMap
		propValueMap = propertyValueMap
		return replaceVars(f)
	}

	private dispatch def EObject replaceVars(FormulaOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}
	
	private dispatch def EObject replaceVars(Negation f) {
		replaceVars(f.child)
		return f
	}

	private dispatch def EObject replaceVars(QAtom f) {
		val exp = replaceVars(f.exp)

		// eliminate quantification
		if (vals.containsKey(f.^var))
			EcoreUtil::replace(f, f.exp)
		
		return exp
	}

	private dispatch def EObject replaceVars(TAtomUnary f) {
		replaceVars(f.exp)
		return f
	}
	
	private dispatch def EObject replaceVars(TAtomBinary f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(Const f) {
		// do nothing?
		return f
	}

	private dispatch def EObject replaceVars(ExprOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(Fun f) {
		f.args.forEach[replaceVars(it)]
		return f
	}

	private dispatch def EObject replaceVars(ID f) {
		// the actual replacement 
		if (vals.containsKey(f.id)) {
			// replace with a value from switch, depending on the type
			val v = IPLUtils::createEcoreValueFromIPL(decls.get(f.id), vals.get(f.id))
				
			// TODO not sure if need to delete f here
			EcoreUtil::replace(f, v)
			return v
		} else 
			return f
	}

	private dispatch def EObject replaceVars(PropertyExpression f) {
		// replace the name into a value
		replaceVars(f.left)
		
		val propName = f.right.id
		val propType = propTypeMap.get(propName)
		
		if(propType === null)
			throw new UnexpectedException('Cannot find property ' + propName + ' in property map ' + propTypeMap)
		
		// map: elemId -> val
		val elemValueMap = propValueMap.get(propName)
		
		if(!(f.left instanceof Int))
			throw new UnsupportedOperationException('Property ' + propName + ' has a non-integer left side: ' + f.left)
		
		val elemId = (f.left as Int).value
		
		if(!elemValueMap.containsKey(elemId)) 
			throw new UnexpectedException('Cannot find element ' + elemId + ' in property map ' + propValueMap)
		
		// make a value 
		val v = IPLUtils::createEcoreValueFromIPL(propType, elemValueMap.get(elemId))
		EcoreUtil::replace(f, v)
		
		return v
	}

	private dispatch def EObject replaceVars(TermOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(ModelExpr f) {
		replaceVars(f.expr)
		replaceVars(f.params)
		return f
	}

	private dispatch def EObject replaceVars(ModelParamExpr f) {
		f.vals.forEach[replaceVars(it)]
		return f
	}

	private dispatch def EObject replaceVars(ProbQuery f) {
		replaceVars(f.expr)
		return f
	}

	private dispatch def EObject replaceVars(RewardQuery f) {
		replaceVars(f.expr)
		return f
	}


}
