package org.xtext.example.ipl.transform

import java.util.Map
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
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
import org.xtext.example.ipl.validation.IPLType

// replaces vars with free constants
class VarFreeVarTransformer {
	
	private var Map<String, String> var2Term  
	private var Map<String, IPLType> termTypes 
	
	def EObject replaceVarsWithTerms(Formula f, Map _var2Term, Map _termTypes) { 
		var2Term =  _var2Term
		termTypes = _termTypes // FIXME not needed? 
		
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

		// eliminate quantification
		if (var2Term.containsKey(f.^var))
			EcoreUtil::replace(f, f.exp)
		
		// TODO not sure whether to delete f
		return replaceVars(exp)
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
		if(var2Term.containsKey(f.id)) {
			
			val EClass ei = IPLPackage.eINSTANCE.ID
			val ID i = EcoreUtil::create(ei) as ID
			i.id = var2Term.get(f.id)
			EcoreUtil::replace(f, i)
			EcoreUtil::delete(f)
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
