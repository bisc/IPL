package org.xtext.example.ipl

import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Lst
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.QM
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation

class IPLPrettyPrinter {
	/*dispatch def print(Formula f) { 
		
	}*/
	
	public static def String print_formula(EObject f) { 
		(new IPLPrettyPrinter).print(f) as String
	}
		
	dispatch def String print(FormulaOperation f){ 
		'''«print(f.left)» «f.op» «print(f.right)»'''
	}
	
	dispatch def String print(Negation f){
		'''!«print(f.child)»'''
	}
	
	dispatch def String print(QAtom f){ 
		'''«f.op» «f.^var»: «print(f.set)» | «print(f.exp)»'''
	}
	
	dispatch def String print(TAtom f){ 
		'''«f.op» «print(f.exp)»'''
	}
	
	/*dispatch def print(Const f){
		'''«f.»''' 
	}*/
	dispatch def String print(Set f){
		'''{«f.members.map[print(it)].join(', ')»}'''
	}
	
	dispatch def String print(Lst f){
		'''<<«f.members.map[print(it)].join(', ')»>>'''
	}
	
	dispatch def String print(Int f){
		f.getValue.toString
	}
	
	dispatch def String print(Real f){
		f.getValue.toString
	}
	
	dispatch def String print(Bool f){
		f.getValue.toString
	}
	
	dispatch def String print(ExprOperation f){
		'''«print(f.left)» «f.op» «print(f.right)»''' 
	}
	
	dispatch def String print(Fun f){ 
		'''«f.name»(«f.args.map[print(it)].join(' ')»)'''
	}
	
	dispatch def String print(ID f){ 
		f.id
	}
	
	dispatch def String print(PropertyExpression f){
		'''«print(f.left)»::«print(f.right)»''' 
	}
	
	dispatch def String print(TermOperation f){ 
		'''«print(f.left)» «f.op» «print(f.right)»''' 
	}
	
	dispatch def String print(ModelParamExpr f){
		'''{|«f.vals.map[print(it)].join(', ')»|}'''
	}	
	
	dispatch def String print(ModelExpr f){
		 // intentionally not printing the parameters
		 print(f.expr)
	}
	
	dispatch def String print(QM f){
		 '?'
	}
	
	dispatch def String print(ProbQuery f){
		val mm = f.minmax?.^val ?: ''
		//var mm = if (f.minmax !== null)	f.minmax.^val else ''
			
		'''P«mm»«f.comp»«print(f.value)»[«print(f.expr)»]'''
	}
	
	dispatch def String print(RewardQuery f){ 
		val mm = f.minmax?.^val ?: ''
		'''R{«f.rewardName»}«mm»«f.comp»«print(f.value)» [«print(f.expr)»]'''
	}
	
	/*dispatch def print(PrismValue f){
		print(f)	 
	}*/
}