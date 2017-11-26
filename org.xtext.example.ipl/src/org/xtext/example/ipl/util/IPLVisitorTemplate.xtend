package org.xtext.example.ipl.util

import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.Prop
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation

/**
 * An unused template to simplify creation of new transformations/visitors by copy-paste. 
 */
class IPLVisitorTemplate {
	dispatch def visit(Formula f) { 
		
	}
		
	dispatch def visit(FormulaOperation f){ 
	}
	
	dispatch def visit(Negation f){
		
	}
	
	dispatch def visit(QAtom f){ 
		
	}
	
	dispatch def visit(TAtomUnary f){ 
	}
	
	dispatch def visit(TAtomBinary f){ 
	}
	
	dispatch def visit(Const f){ 
	}
	
	dispatch def visit(ExprOperation f){ 
	}
	
	dispatch def visit(Fun f){ 
	}
	
	dispatch def visit(ID f){ 
	}
	
	dispatch def visit(PropertyExpression f){ 
	}
	
	dispatch def visit(Prop f){
	}
	
	dispatch def visit(TermOperation f){ 
	}
	
	dispatch def visit(ModelParamExpr f){
	}	
	
	dispatch def visit(ModelExpr f){
	}
	
	dispatch def visit(ProbQuery f){ 
	}
	
	dispatch def visit(RewardQuery f){ 
	}
}
