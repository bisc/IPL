package org.xtext.example.ipl.transform

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
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
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.util.IPLUtils
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.IPLTypeProviderSpec


import static extension org.eclipse.emf.ecore.util.EcoreUtil.*

// replaces the topmost flexible formula with a propositional constant
class PropAbstTransformer {
	
	private var IPLTypeProviderSpec tp
	
	private List<String> propAbsts = new ArrayList 
	private int propAbstCt = 0 
	private Map<Formula, Formula> replacedFormulas = new HashMap 
	
	public def Formula performPropAbst(Formula f, IPLTypeProviderSpec _tp) {
		tp = _tp 
		visit(f)
	}
	
	public def getPropAbstNames (){
		propAbsts
	}
	
	private dispatch def Formula visit(FormulaOperation f){ 
		visit(f.left)
		visit(f.right)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		}
	}
	
	private dispatch def Formula visit(Negation f){
		visit(f.child)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		} 
	}
	
	private dispatch def Formula visit(QAtom f){ 
		visit(f.exp)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		}
	}
	
	private dispatch def Formula visit (TAtomUnary f){
		visit(f.exp)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		} 
	}
	
	private dispatch def Formula visit(TAtomBinary f){ 
		visit(f.left)
		visit(f.right)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		} 
	}
	
	private dispatch def Formula visit(Const f){ 
		f
	}
	
	private dispatch def Formula visit(ExprOperation f){ 
		visit(f.left)
		visit(f.right)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		} 
	}
	
	private dispatch def Formula visit(Fun f){ 
		f.args.forEach[
			visit(it)
		]
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		}
	}
	
	private dispatch def Formula visit(ID f){
		f 
	}
	
	private dispatch def Formula visit(PropertyExpression f){
		visit(f.left)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		} 
	}
	
	private dispatch def Formula visit(TermOperation f){
 		visit(f.left)
		visit(f.right)
		
		val repl = replacedFormulas.get(f)
		if (repl === null)
			f
		else {
			f.delete(true);
			repl
		}
	}
	
	private dispatch def Formula visit(ModelExpr f){
		// find the closest enclosing formula
		var EObject iter = f
		while(!(tp.typeOf(iter) instanceof BoolType) && iter !== null)
			iter = iter.eContainer
			
		if (iter === null)
			throw new UnexpectedException('Failed to find the enclosing formula of ' + f) 
		
		val Formula formulaToReplace = iter as Formula
		
		// replace the formula with a propositional ID 
		val EClass ei = IPLPackage.eINSTANCE.ID
		val ID i = EcoreUtil::create(ei) as ID
		i.id = IPLUtils::propAbst('') + (propAbstCt++)
		propAbsts.add(i.id)
		replacedFormulas.put(formulaToReplace, i)
		EcoreUtil::replace(formulaToReplace, i)
		
		if (formulaToReplace !== f)
			f
		else {
			formulaToReplace.delete(true);
			i
		}
	}
}
