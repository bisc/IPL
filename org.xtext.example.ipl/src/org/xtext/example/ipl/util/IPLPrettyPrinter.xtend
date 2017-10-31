package org.xtext.example.ipl.util

import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Lst
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.Prop
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.QM
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeElem
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeReal

class IPLPrettyPrinter {
	/*dispatch def print(Formula f) { 
		
	}*/
	
	public static def String print_formula(EObject f) { 
		(new IPLPrettyPrinter).print(f) as String
	}
		
	dispatch def String print(FormulaOperation f){ 
		val left = if (f.left instanceof Formula) '(' + print(f.left) + ')' else print(f.left)
		val right = if (f.right instanceof Formula) '(' + print(f.right) + ')' else print(f.right)
			
		'''«left» «f.op» «right»'''
	}
	
	dispatch def String print(Negation f){
		'''!(«print(f.child)»)'''
	}
	
	dispatch def String print(QAtom f){ 
		'''«f.op» «f.^var»: «print(f.dom)» | «print(f.exp)»'''
	}
	
	dispatch def String print(TAtomUnary f){ 
		'''«f.op» («print(f.exp)»)''' // extra parentheses for prism
	}
	
	dispatch def String print(TAtomBinary f){ 
		'''(«print(f.left)») «f.op» («print(f.right)»)''' // extra parentheses for prism
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
	
	dispatch def String print(TypeInt f){
		'int'
	}
	
	dispatch def String print(TypeReal f){
		'real'
	}
	
	dispatch def String print(TypeBool f){
		'bool'
	}
	
	dispatch def String print(TypeElem f){
		'elem'
	}
	
	dispatch def String print(ExprOperation f){
		'''«print(f.left)» «f.op» «print(f.right)»''' 
	}
	
	dispatch def String print(Fun f){ 
		'''«f.decl.name»(«f.args.map[print(it)].join(', ')»)'''
	}
	
	dispatch def String print(ID f){ 
		f.id
	}
	
	dispatch def String print(PropertyExpression f){
		'''«print(f.left)»::«print(f.right)»''' 
	}
	
	dispatch def String print(Prop f){
		'''«f.id»''' 
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
