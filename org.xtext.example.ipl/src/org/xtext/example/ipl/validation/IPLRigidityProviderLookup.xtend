package org.xtext.example.ipl.validation

import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.MFunDecl
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.Negation
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.SortDecl
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.iPL.Type
import org.xtext.example.ipl.iPL.TypedDecl
import org.xtext.example.ipl.iPL.VarDecl

import static extension org.eclipse.xtext.EcoreUtil2.*

class IPLRigidityProviderLookup {
	
	static def dispatch boolean isRigid(QAtom q) {
		q.dom.rigid && q.exp.rigid
	}
	
	static def dispatch boolean isRigid(TAtomUnary t) {
		false
	}
	
	static def dispatch boolean isRigid(TAtomBinary t) {
		false
	}
	
	static def dispatch boolean isRigid(ModelExpr r) {
		false
	}	
	
	static def dispatch boolean isRigid(ProbQuery p) {
		false
	}
	
	static def dispatch boolean isRigid(RewardQuery r) {
		false
	}	
	
	static def dispatch boolean isRigid(Const c) {
		true
	}
	
	static def dispatch boolean isRigid(Type t) { // for when e.g. int inside quantification
		true
	}
	
	static def dispatch boolean isRigid(PropertyExpression p) {
		true
	}
	
	static def dispatch boolean isRigid(Fun f) {
		!(f.decl instanceof MFunDecl)
	}

	static def dispatch boolean isRigid(ID e) {
		val name = e.id
		
		val decls = e.getContainerOfType(IPLSpec).decls
		
		val decl = decls.filter[it instanceof TypedDecl].findLast[(it as TypedDecl).name == name]
		
		if (decl !== null) 
			return (decl instanceof VarDecl || decl instanceof SortDecl)
		else 
			return true
	}
	
	static def dispatch boolean isRigid(FormulaOperation op) {
		op.left.rigid && op.right.rigid
	}
	
	
	static def dispatch boolean isRigid(ExprOperation op){
		 op.left.rigid && op.right.rigid
	}
	
	static def dispatch boolean isRigid(Negation op){
		 op.child.rigid
	}
	
	static def dispatch boolean isRigid(TermOperation op){
	 	op.left.rigid && op.right.rigid
	}
	
	// a questionable function that expands each eobject
//	static def dispatch boolean isRigid(EObject o) {
//		o.eAllContentsAsList.forall[rigid]
//	}
//	
}