package org.xtext.example.ipl.generator

import java.rmi.UnexpectedException
import java.util.Map
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.Utils
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.FormulaOperation
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLPackage
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.ModelParamExpr
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.validation.IPLType

// replaces values of rigid variables/constants in IPL formulas
class IPLTransformerProbeReplacer {

	var Map<String, IPLType> scopeDecls

	// replaces all occurences of variables with their valuations
	// returns the next object (potentially changed if on top
	public def EObject replaceVarsWithProbes(EObject f, Map<String, IPLType> scopeDeclarations) {
		
		scopeDecls = scopeDeclarations
		return replaceVars(f)
	}

	private dispatch def EObject replaceVars(FormulaOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(QAtom f) {
		throw new UnexpectedException("Was not supposed to be run on QAtoms")
		
		/*replaceVars(f.exp)

		// eliminate quantification
		if (vals.containsKey(f.^var))
			EcoreUtil::replace(f, f.exp)
		
		return f.exp*/
	}

	private dispatch def EObject replaceVars(TAtom f) {
		replaceVars(f.exp)
		return f
	}

	private dispatch def EObject replaceVars(Const f) {
		// do nothing?
		return f
	}

	private dispatch def EObject replaceVars(ExprOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(Fun f) {
		f.args.forEach[replaceVars(it)]
		return f
	}

	private dispatch def EObject replaceVars(ID f) {
		// the actual replacement 
		if (scopeDecls.containsKey(f.id)) {
			// create an ID element with probe name 
			val EClass eb = IPLPackage.eINSTANCE.ID
			val ID probeId = EcoreUtil::create(eb) as ID
			probeId.id = Utils::probe(f.id)
				
			// TODO not sure if need to delete f here
			EcoreUtil::replace(f, probeId)
			return probeId
		} else 
			return f
	}

	private dispatch def EObject replaceVars(PropertyExpression f) {
		// replace the name into a value
		replaceVars(f.left)
		
		return f
	}

	private dispatch def EObject replaceVars(TermOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
		return f
	}

	private dispatch def EObject replaceVars(ModelExpr f) {
		replaceVars(f.expr)
		replaceVars(f.params)
		return f
	}

	private dispatch def EObject replaceVars(ModelParamExpr f) {
		f.vals.forEach[replaceVars(it)]
		return f
	}

	private dispatch def EObject replaceVars(ProbQuery f) {
		replaceVars(f.expr)
		return f
	}

	private dispatch def EObject replaceVars(RewardQuery f) {
		replaceVars(f.expr)
		return f
	}


}
