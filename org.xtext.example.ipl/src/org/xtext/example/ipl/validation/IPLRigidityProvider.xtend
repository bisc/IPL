package org.xtext.example.ipl.validation

import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.MFunDecl
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.SortDecl
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TypedDecl
import org.xtext.example.ipl.iPL.VarDecl

import static extension org.eclipse.xtext.EcoreUtil2.*

class IPLRigidityProvider {
	
	static def dispatch boolean isRigid(QAtom q) {
		q.set.rigid && q.exp.rigid
	}
	
	static def dispatch boolean isRigid(TAtom t) {
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

	static def dispatch boolean isRigid(EObject o) {
		o.eAllContentsAsList.forall[rigid]
	}
	
}