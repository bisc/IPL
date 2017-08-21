package org.xtext.example.ipl.generator

import java.util.Map
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.util.EcoreUtil
import org.xtext.example.ipl.iPL.Bool
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
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.RewardQuery
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermOperation
import org.xtext.example.ipl.validation.BoolType
import org.xtext.example.ipl.validation.IPLType
import org.xtext.example.ipl.validation.IntType
import org.xtext.example.ipl.validation.RealType
import java.rmi.UnexpectedException

// replaces values of rigid variables/constants in IPL formulas
class IPLTransformerValueReplacer {

	var Map<String, Object> vals
	var Map<String, IPLType> decls

	// replaces all occurences of variables with their valuations
	public def replaceVarsWithValues(EObject f, Map<String, Object> valuation, Map<String, IPLType> declarations) {
		if (valuation.size == 0 )
			return
		
		vals = valuation
		decls = declarations
		replaceVars(f)
	}

	private dispatch def replaceVars(FormulaOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
	}

	private dispatch def replaceVars(QAtom f) {
		replaceVars(f.exp)

		// eliminate quantification
		if (vals.containsKey(f.^var))
			EcoreUtil::replace(f, f.exp)
	}

	private dispatch def replaceVars(TAtom f) {
		replaceVars(f.exp)
	}

	private dispatch def replaceVars(Const f) {
		// do nothing?
	}

	private dispatch def replaceVars(ExprOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
	}

	private dispatch def replaceVars(Fun f) {
		f.args.forEach[replaceVars(it)]
	}

	private dispatch def replaceVars(ID f) {
		// the actual replacement 
		if (vals.containsKey(f.id)) {
			// replace with a value from switch, depending on the type
			val v = switch (decls.get(f.id)) {
				BoolType: {
					val EClass eb = IPLPackage.eINSTANCE.bool
					val Bool i = EcoreUtil::create(eb) as Bool
					i.value = vals.get(f.id).toString
					i
				}
				IntType: {
					val EClass ei = IPLPackage.eINSTANCE.int
					val Int i = EcoreUtil::create(ei) as Int
					i.value = vals.get(f.id) as Integer
					i
				}
				RealType:{
					val EClass er = IPLPackage.eINSTANCE.real
					val Real i = EcoreUtil::create(er) as Real
					i.value = vals.get(f.id) as Float
					i
				}
				default: throw new UnexpectedException("Unknown type")
			}
			
			// TODO not sure if need to delete f here
			EcoreUtil::replace(f, v)
		}
	}

	private dispatch def replaceVars(PropertyExpression f) {
		replaceVars(f.left)
	}

	private dispatch def replaceVars(TermOperation f) {
		replaceVars(f.left)
		replaceVars(f.right)
	}

	private dispatch def replaceVars(ModelExpr f) {
		replaceVars(f.expr)
		replaceVars(f.params)
	}

	private dispatch def replaceVars(ModelParamExpr f) {
		f.vals.forEach[replaceVars(it)]
	}

	private dispatch def replaceVars(ProbQuery f) {
		replaceVars(f.expr)
	}

	private dispatch def replaceVars(RewardQuery f) {
		replaceVars(f.expr)
	}

}
