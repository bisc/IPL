package org.xtext.example.ipl.transform

import java.util.Map
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.EReference
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLPackage
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

// replaces indicated vars with free constants
// eliminates their quantifiers, leaving others intact
class Var2FreeVarPartialTransformer {
	
	private var Map<String, String> var2FreeVar  
	
	def EObject replaceVarsWithTerms(Formula f, Map _var2FreeVar) { 
		var2FreeVar =  _var2FreeVar
		
		replaceVars(f)
	}
	
		
	private dispatch def EObject replaceVars(FormulaOperation f){ 
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}
	
	private dispatch def EObject replaceVars(Negation f){
		return replaceVars(f.child)
	}
	
	private dispatch def EObject replaceVars(TAtomUnary f){ 
		return replaceVars(f.exp)
	}
	
	private dispatch def EObject replaceVars(TAtomBinary f){
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}
	
	private dispatch def EObject replaceVars(QAtom f){ 
		val exp = f.exp
		val parent = f.eContainer

		// eliminate quantification, slightly more nuanced than in the full case
		if (var2FreeVar.containsKey(f.^var)) { // removing quantification
			EcoreUtil::replace(f, exp)
			// if the parent is null, it still needs to be assigned, which is not done by Ecore
			if (parent === null) {
				EcoreUtil::remove(exp) // removes the argument from its container (doesn't delete the arg)
				// other attempts 
//				val EReference feature = exp.eContainmentFeature //	exp.eContainingFeature
//				EcoreUtil::remove(exp, exp.eContainingFeature, f)
//				exp.eSet(feature, null)
			}
			// 
			EcoreUtil::delete(f, false) // non-recursive, looks for usages and containments to remove refs
			return replaceVars(exp)
//			if (parent !== null) { // deeper into the tree, returning parent
//				replaceVars(exp)
//				return parent 
//			} else { // if top of the tree, then returning itself 
//				return replaceVars(exp)
//			}
		} else { // not removing quantification, returning itself
			replaceVars(exp)
			return f
		}
	}
	
	private dispatch def EObject replaceVars(Const f){ 
		return f
	}
	
	private dispatch def EObject replaceVars(ExprOperation f){ 
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}
	
	private dispatch def EObject replaceVars(Fun f){ 
		f.args.forEach[replaceVars(it)]
		return f
	}
	
	private dispatch def EObject replaceVars(ID f){ 
		// replace var with a free const
		if(var2FreeVar.containsKey(f.id)) {
			
			val EClass ei = IPLPackage.eINSTANCE.ID
			val ID i = EcoreUtil::create(ei) as ID
			i.id = var2FreeVar.get(f.id)
			EcoreUtil::replace(f, i)
			EcoreUtil::delete(f, false) // non-recursive
			return i
		} else 
			return f
	}
	
	private dispatch def EObject replaceVars(PropertyExpression f){
		replaceVars(f.left) 
		return f
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
