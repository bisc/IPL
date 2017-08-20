package org.xtext.example.ipl.generator

import java.rmi.UnexpectedException
import java.util.Map
import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.PrismExpr
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation

// replaces values of rigid variables/constants in IPL formulas
class IPLTransformerValueReplacer {
	public def replaceQvarsWithValues (EObject f, Map<String, Object> valuation) { 
		replaceQvars(f, valuation)
	}
	
	/*private dispatch def replaceQvars(Formula f, Map<String, Object> valuation){ 
		throw new UnexpectedException("Shouldn't this be casted down to a specific class?")	
	}*/
	
	private dispatch def replaceQvars(FormulaOperation f, Map<String, Object> valuation){ 
		replaceQvars(f.left, valuation)
		replaceQvars(f.right, valuation)
	}
	
	private dispatch def replaceQvars(QAtom f, Map<String, Object> valuation){ 
		replaceQvars(f.exp, valuation)
		
		// eliminate quantification
		if(valuation.containsKey(f.^var)) 
			(new IPLTransformerDadUpdater).updateDad(f.eContainer, f.exp)
		
	}
	
	private dispatch def replaceQvars(TAtom f, Map<String, Object> valuation){ 
		replaceQvars(f.exp, valuation)
	}
	
	private dispatch def replaceQvars(Const f, Map<String, Object> valuation){ 
		// do nothing?
	}
	
	private dispatch def replaceQvars(ExprOperation f, Map<String, Object> valuation){ 
		replaceQvars(f.left, valuation)
		replaceQvars(f.right, valuation)
	}
	
	private dispatch def replaceQvars(Fun f, Map<String, Object> valuation){ 
		f.args.forEach[replaceQvars(it, valuation)]
	}
	
	private dispatch def replaceQvars(ID f, Map<String, Object> valuation){ 
		// TODO: difficult case 
		throw new UnexpectedException("TO IMPLEMENT")	
	}
	
	private dispatch def replaceQvars(PropertyExpression f, Map<String, Object> valuation){ 
		replaceQvars(f.left, valuation)
	}
	
	private dispatch def replaceQvars(TermOperation f, Map<String, Object> valuation){ 
		replaceQvars(f.left, valuation)
		replaceQvars(f.right, valuation)
	}
	
	private dispatch def replaceQvars(ModelParamExpr f, Map<String, Object> valuation){
		f.vals.forEach[replaceQvars(it, valuation)]
	}	
	
	private dispatch def replaceQvars(PrismExpr f, Map<String, Object> valuation){ 
		replaceQvars(f.expr, valuation)
	}
	
	private dispatch def replaceQvars(ProbQuery f, Map<String, Object> valuation){ 
		replaceQvars(f.expr, valuation)
	}
	
	private dispatch def replaceQvars(RewardQuery f, Map<String, Object> valuation){ 
		replaceQvars(f.expr, valuation)
	}
	
}