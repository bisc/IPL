package org.xtext.example.ipl.transform

import java.util.List
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
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.impl.FunImpl
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.iPL.IPLSpec

// transforms a formula into its prenex normal form
class PrenexTransformer {
	
	private QAtom curQuant
	
	def Formula toPrenexNormalForm(Formula f) { 
		// flow:  
		// find the outermost quantifier
		// propagate it out, path guided by econtainers 
		// repeat for the next quant
		var formulaTop = f
		var QAtom insertionPt = null
		
		do {
			curQuant = null
			findOutmostQuant(if (insertionPt !== null) insertionPt.exp else f )
			
			if (curQuant !== null) {
				
				// count negations
				var EObject iter = curQuant 
				var int negCount = 0
				
				while(iter !== null && !(iter instanceof IPLSpec)) { 
					val iterUp = iter.eContainer // step up one level
					
					if (iterUp instanceof Negation) //negation
						negCount++ 
					else if (iterUp instanceof FormulaOperation) // premise of implication
						if (iterUp.op == '->' && iterUp.left === iterUp)
							negCount++ 
						
					iter = iterUp
				} 
				
				// remove quantification from its place
				EcoreUtil::replace(curQuant, curQuant.exp)
				
				// propagate the quantifier back
				if(insertionPt !== null) { // insert into a sequence of qatoms
					curQuant.exp = insertionPt.exp
					insertionPt.exp = curQuant
				} else { // the first discovered QAtom is placed at the top of the formula
					curQuant.exp = formulaTop
					insertionPt = curQuant
					formulaTop = curQuant
				} 
				
				// invert the quantifier as needed
				if(negCount % 2 != 0)
					if (curQuant.op == 'forall')
						curQuant.op = 'exists'
					else 
						curQuant.op = 'forall'
				
				/*val EClass ei = IPLPackage.eINSTANCE.QAtom
				val QAtom qa = EcoreUtil::create(ei) as QAtom
				qa.op = 'forall'*/				
			}
		} while(curQuant !== null)
		
		return formulaTop
	} 
	
	private dispatch def EObject findOutmostQuant(QAtom f){ 
		curQuant = f
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
		findOutmostQuant(f)
	}
	
	private dispatch def EObject findOutmostQuant(TAtom f){ 
		findOutmostQuant(f.exp)
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
