package org.xtext.example.ipl.transform

import java.rmi.UnexpectedException
import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Expression
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.PrismExpr
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation


// TODO: not being used, using EcoreUtils instead
class IPLTransformerDadUpdater {
	
	dispatch def updateDad(FormulaOperation f, EObject son){
		 // TODO: left or right?? 
	}
	
	dispatch def updateDad(QAtom f, EObject son){ 
		f.exp = son as Formula
	}
	
	dispatch def updateDad(TAtom f, EObject son){ 
		f.exp = son as Formula
	}
	
	dispatch def updateDad(Const f, EObject son){ 
		throw new IllegalArgumentException("Constant cannot have children")
	}
	
	dispatch def updateDad(ExprOperation f, EObject son){ 
		// TODO: left or right??
	}
	
	dispatch def updateDad(Fun f, EObject son){ 
		// TODO: which argument? 
	}
	
	dispatch def updateDad(ID f, EObject son){ 
		throw new IllegalArgumentException("IDs cannot have children")
	}
	
	dispatch def updateDad(PropertyExpression f, EObject son){ 
		//TODO assuming left 
		f.left = son as Expression
	}
	
	dispatch def updateDad(TermOperation f, EObject son){ 
		// TODO: left or right
	}
	
	dispatch def updateDad(PrismExpr f, EObject son){ 
		f.expr = son as Formula
		//TODO: not sure, maybe we're updating parameters? ugh
	}
	
	dispatch def updateDad(ProbQuery f, EObject son){ 
		f.expr = son as Formula
	} 
	
	dispatch def updateDad(RewardQuery f, EObject son){ 
		f.expr = son as Formula
	}
	
	dispatch def updateDad(IPLSpec s, EObject son) {
		throw new UnexpectedException("Didn't know it could go so high up")	
	}
}
