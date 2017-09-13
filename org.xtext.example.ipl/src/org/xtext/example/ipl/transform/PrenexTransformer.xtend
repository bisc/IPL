package org.xtext.example.ipl.transform

import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
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

// transforms a formula into its prenex normal form
class PrenexTransformer {
	
	private QAtom curQuant
	
	def Formula toPrenexNormalForm(Formula f) { 
		// flow:
		// find the insertion point  
		// find the outermost quantifier
		// propagate it out, path guided by econtainers 
		// repeat for the next quant
		var formulaTop = f
		var QAtom insertionPt = null // the deepest qatom in the prenex part
		
		// locate the insertion point, if it exists; otherwise leave as null
		var EObject iter = f
		while(iter instanceof QAtom)
			iter = iter.exp
		if (iter !== f)
			insertionPt = iter.eContainer as QAtom
		
		do {
			curQuant = null
			findOutmostQuant(if (insertionPt !== null) insertionPt.exp else f )
			
			if (curQuant !== null) {
				
				// count negations before curQuant
				iter = curQuant
				var int negCount = 0
				
				while(iter !== null && iter !== formulaTop && !(iter instanceof IPLSpec)) { 
					val iterUp = iter.eContainer // step up one level
					
					if (iterUp instanceof Negation) //negation
						negCount++ 
					else if (iterUp instanceof FormulaOperation) // premise of implication
						if (iterUp.op == '->' && iterUp.left === iter)
							negCount++ 
						
					iter = iterUp
				} 
				
				// remove quantification from its place, update formula top as needed
				if (formulaTop === curQuant)
					formulaTop = curQuant.exp 
				EcoreUtil::replace(curQuant, curQuant.exp) // this makes curQuant.exp = null, curQuant.eContainer = null
				
				// propagate the quantifier back
				if(insertionPt !== null) { 
					// insert curQuant between insertionPt and its exp  
					curQuant.exp = insertionPt.exp // this reassigns insertionPt.exp.eContainer
					insertionPt.exp = curQuant // this reassigns curQuant.eContainer
					// move insertion point to curQuant
					insertionPt = curQuant
				} else { // the first discovered QAtom is placed at the top of the formula
					curQuant.exp = formulaTop // this reassigns formulaTop.eContainer
					formulaTop = curQuant
					insertionPt = curQuant
				} 
				
				// invert the quantifier as needed
				if(negCount % 2 != 0)
					if (curQuant.op == 'forall')
						curQuant.op = 'exists'
					else 
						curQuant.op = 'forall'
				
			}
		} while(curQuant !== null)
		
		return formulaTop
	} 
	
	private dispatch def EObject findOutmostQuant(QAtom f){ 
		curQuant = f // found!
	}
	
	private dispatch def EObject findOutmostQuant(FormulaOperation f){ 
		findOutmostQuant(f.left)
		
		if(curQuant === null)
			findOutmostQuant(f.right)
	}
		private dispatch def EObject findOutmostQuant(ExprOperation f){ 
		findOutmostQuant(f.left)
		if(curQuant === null)
			findOutmostQuant(f.right)
	}
	
	private dispatch def EObject findOutmostQuant(Fun f){ 
		f.args.forEach[
			if (curQuant === null) 
				findOutmostQuant(it)
		]
		f
	}
		private dispatch def EObject findOutmostQuant(TermOperation f) {
		findOutmostQuant(f.left)
		if (curQuant === null) 
			findOutmostQuant(f.right)
	}

	private dispatch def EObject findOutmostQuant(ModelExpr f) {
		findOutmostQuant(f.expr)
		if (curQuant === null) 
			findOutmostQuant(f.params)
	}

	private dispatch def EObject findOutmostQuant(ModelParamExpr f) {
		f.vals.forEach[
			if (curQuant === null) 
				findOutmostQuant(it)
		]
		f
	}
	private dispatch def EObject findOutmostQuant(Negation f){
		findOutmostQuant(f.child)
	}
	
	private dispatch def EObject findOutmostQuant(TAtomUnary f){ 
		findOutmostQuant(f.exp)
	}
	
	private dispatch def EObject findOutmostQuant(TAtomBinary f){ 
		findOutmostQuant(f.left)
		if(curQuant === null)
			findOutmostQuant(f.right)
	}

	private dispatch def EObject findOutmostQuant(Const f){ 
		
	}
	
	private dispatch def EObject findOutmostQuant(ID f){ 
		
	}
	
	private dispatch def EObject findOutmostQuant(PropertyExpression f){
		findOutmostQuant(f.left) 
	}

	private dispatch def EObject findOutmostQuant(ProbQuery f) {
		findOutmostQuant(f.expr)
	}

	private dispatch def EObject findOutmostQuant(RewardQuery f) {
		findOutmostQuant(f.expr)
	}

}
