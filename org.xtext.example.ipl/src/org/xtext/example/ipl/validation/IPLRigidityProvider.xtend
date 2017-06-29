package org.xtext.example.ipl.validation

import org.eclipse.emf.ecore.EObject
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.MFunDec
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.Spec
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.VarDec

import static extension org.eclipse.xtext.EcoreUtil2.*
import org.xtext.example.ipl.iPL.TypedDec
import org.xtext.example.ipl.iPL.SortDec

class IPLRigidityProvider {
	
	static def dispatch boolean isRigid(QAtom q) {
		q.set.rigid && q.exp.rigid
	}
	
	static def dispatch boolean isRigid(TAtom t) {
		false
	}
	
	static def dispatch boolean isRigid(Const c) {
		true
	}
	
	static def dispatch boolean isRigid(PropertyExpression p) {
		true
	}
	
	static def dispatch boolean isRigid(Fun f) {
		!(f.name instanceof MFunDec)
	}

	static def dispatch boolean isRigid(ID e) {
		val name = e.id
		
		val decls = e.getContainerOfType(Spec).decls
		
		val decl = decls.filter[it instanceof TypedDec].findLast[(it as TypedDec).name == name]
		
		if (decl !== null) 
			return (decl instanceof VarDec || decl instanceof SortDec)
		else 
			return true
	}

	static def dispatch boolean isRigid(EObject o) {
		o.eAllContentsAsList.forall[rigid]
	}
	
}