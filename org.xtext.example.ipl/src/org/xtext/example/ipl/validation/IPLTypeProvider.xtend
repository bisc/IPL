package org.xtext.example.ipl.validation

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
import org.eclipse.emf.ecore.EObject
import org.eclipse.xtext.resource.IEObjectDescription
import org.osate.aadl2.AadlBoolean
import org.osate.aadl2.AadlInteger
import org.osate.aadl2.AadlPackage
import org.osate.aadl2.AadlReal
import org.osate.aadl2.ComponentClassifier
import org.osate.aadl2.ComponentImplementation
import org.osate.aadl2.Property
import org.osate.aadl2.PropertySet
import org.osate.aadl2.SubprogramGroupImplementation
import org.osate.aadl2.SubprogramImplementation
import org.osate.aadl2.instance.ComponentInstance
import org.osate.aadl2.instance.util.InstanceUtil
import org.osate.aadl2.instantiation.InstantiateModel
import org.osate.aadl2.modelsupport.resources.OsateResourceUtil
import org.osate.xtext.aadl2.properties.util.EMFIndexRetrieval
import org.xtext.example.ipl.iPL.Bool
import org.xtext.example.ipl.iPL.Const
import org.xtext.example.ipl.iPL.ExprOperation
import org.xtext.example.ipl.iPL.Expression
import org.xtext.example.ipl.iPL.Formula
import org.xtext.example.ipl.iPL.Fun
import org.xtext.example.ipl.iPL.ID
import org.xtext.example.ipl.iPL.IPLSpec
import org.xtext.example.ipl.iPL.Int
import org.xtext.example.ipl.iPL.Lst
import org.xtext.example.ipl.iPL.ModelExpr
import org.xtext.example.ipl.iPL.PrismExpr
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.QM
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.STVarDecl
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.SortDecl
import org.xtext.example.ipl.iPL.TAtomBinary
import org.xtext.example.ipl.iPL.TAtomUnary
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeElem
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeReal
import org.xtext.example.ipl.iPL.TypedDecl
import org.xtext.example.ipl.iPL.VarDecl
import org.xtext.example.ipl.iPL.ViewDecl
import org.xtext.example.ipl.util.IPLUtils

import static extension org.eclipse.xtext.EcoreUtil2.*

// a version of the type provider combines looking up and setting IPL spec up front
// creates IPL types: 
// - from component instance
// - from component classifier (used for aadl mdls)
// - from component implementation (deprecated)
class IPLTypeProvider {
	
	HashMap<ComponentClassifier, List<Property>> classifierPropCache = new HashMap
	IPLSpec spec = null
	Map<String, IPLType> freeVarTypes = null
	
	
	new(){ // spec lookup happens later
	}

	new(IPLSpec _spec){
		spec = _spec
	}
	
	new(IPLSpec _spec, Map<String, IPLType> _freeVarTypes){
		spec = _spec
		freeVarTypes = _freeVarTypes
	}
	
	def setFreeVarTypes(Map<String, IPLType> _freeVarTypes) {
		freeVarTypes = _freeVarTypes
	}

	// accepts a reference to the topmost element 
	def populatePropCache(ComponentImplementation ref) { 
		// TODO: do for all components and all properties at once? 
	}
	
	def IPLType createTypeFromComponentImpl(ComponentImplementation ref) {
		if (true)
			throw new UnexpectedException("This function is not supposed to be called")
			 
		// this function never seems to be called...
		if (ref instanceof SubprogramImplementation
			|| ref instanceof SubprogramGroupImplementation) {
			//Fail...
			return null			
		}
	
		// a BIG bottleneck here, maybe
		val inst = InstantiateModel::buildInstanceModelFile(ref)
		
		val prop_cache = new ArrayList<Property>


		val allPropSets = EMFIndexRetrieval::getAllPropertySetsInWorkspace(inst);
		println(allPropSets)
		// cache all applicable properties 		
		for (IEObjectDescription ieo: EMFIndexRetrieval::getAllPropertySetsInWorkspace(inst.getComponentClassifier())) { 
			val ps = OsateResourceUtil.getResourceSet().getEObject(ieo.getEObjectURI(), true) as PropertySet;
			for (prop : ps.ownedProperties) {
				if (inst.acceptsProperty(prop) && IPLUtils::typeFromPropType(prop.propertyType) !== null) {
					prop_cache.add(prop);
				}
			}
		}
		
		createTypeFromComponentInst(inst, prop_cache)
	}
	
	def IPLType createTypeFromComponentInst(ComponentInstance inst, List<Property> prop_cache) {
//		System::out.println(inst.children.map[switch (it) {
//			ComponentInstance: it.name
//			PropertyAssociationInstance: it.property.name
//			default: "N/A"
//		}])
		
		val impl = InstanceUtil::getComponentImplementation(inst, 0, null)
		val ct = new ComponentType(if (impl === null) inst.name else impl.name)
		
		// add subcomponent instances as members
		inst.children.forEach[switch (it) {ComponentInstance: ct.addMember(it.name, createTypeFromComponentInst(it, prop_cache))}]

		for (prop : prop_cache) {
			val propType = IPLUtils::typeFromPropType(prop.propertyType)
			if (inst.acceptsProperty(prop) && propType !== null) {
				ct.addMember(prop.name, propType);
			}
		}
		 
		ct
	}
	
	def IPLType createTypeFromComponentClassifier(ComponentClassifier ref) {
		
		val ct = new ComponentType(
			if (ref.name === null) 
				ComponentType.NOT_FOUND_NAME
			else 
				ref.name
		) 
		
		// populate the cache if needed
		if (classifierPropCache.get(ref) === null) {
			classifierPropCache.put(ref, newArrayList())
			// get all imported property definitions
			val List<PropertySet> propsets = ref.getContainerOfType(AadlPackage).publicSection.importedUnits.filter[
				it instanceof PropertySet
			].toList as List
			for (PropertySet ps : propsets) { 
			//for (IEObjectDescription ieo : EMFIndexRetrieval::getAllPropertySetsInWorkspace(ref)) {
				//val ps = OsateResourceUtil.getResourceSet().getEObject(ieo.getEObjectURI(), true) as PropertySet;
				for (prop : ps.ownedProperties) { // iterate through owned properties
					val propType = IPLUtils::typeFromPropType(prop.propertyType)
					if (propType !== null) {
						val metaclasses = prop.appliesToMetaclasses
						metaclasses.forEach [
							it.metaclass.name
							// val owningClassifier = it.containingClassifier
							if (it.metaclass.name.equalsIgnoreCase(ref.category.getName())) // if (ref.isDescendentOf(owningClassifier))
								classifierPropCache.get(ref).add(prop) 
								//ct.addMember(prop.name, propType);
						]
					/*val classifiers = prop.appliesToClassifiers

					 * classifiers.forEach[
					 * 	if (ref.isDescendentOf(it) || ref == it) 
					 * 		ct.addMember(prop.name, propType);					
					 ]*/
					}
				// val applies = ref.checkAppliesToClassifier(prop)
				// if (applies && propType !== null) 
				// ct.addMember(prop.name, fromPropType(prop));
				}
			}
		}
		
		// use cache
		classifierPropCache.get(ref).forEach[ct.addMember(it.name, 
			IPLUtils::typeFromPropType(it.propertyType))]
		
		ct
	}
	
		
	// declarations and IDs
	def dispatch IPLType typeOf(ID e) {
		// Resolve id here
		val name = e.id
		
//		System::out.println("####<" + e.id + ">####")
		
		if (spec === null )
			spec = e.getContainerOfType(IPLSpec)
		val decls = spec.decls

		val decl = decls.findLast[
			it instanceof TypedDecl && (it as TypedDecl).name == name
		] as TypedDecl
		
		// first check in declarations. Works for state vars, declared functions, and sorts
		if (decl !== null) { 
			return switch (decl) {
				VarDecl: IPLUtils::typesDecl2IPL(decl.type)
				STVarDecl: IPLUtils::typesDecl2IPL(decl.type)
				SortDecl: new SetType(createTypeFromComponentClassifier(decl.ref)) //used to be from ComponentImpl
				ViewDecl: createTypeFromComponentImpl(decl.ref)
			}
		// then check in free variable declarations, works when quantifiers are removed
		} else if (freeVarTypes !== null && freeVarTypes.containsKey(name)) { 
			return freeVarTypes.get(name)
		// then check in quantified variables, works for vars whose quantifiers have not been removed
		} else { 
			for (c : (e.allContainers.filter[it instanceof QAtom])) {
				val q = c as QAtom
						
				// this is a bit hacky, so maybe FIXME 
				// sometimes this gets called with variable names, and sometimes with their free version
				// trying for either, assuming that free vars have unique names
				if (q !== null && (q.^var == name || IPLUtils::freeVar(q.^var) == name)) {
//					System::out.println("****<" + q.set + ">****")
					val type = getQdomType(q.dom)
					if (type instanceof SetType) // if it's a set of components, return component type
						return (type as SetType).elemType
					else
					// This is an error, but assume this is what the user meant
						return type
				}
			}
			return null
		}
	}
	
	def dispatch IPLType typeOf(Const c) {
		switch (c) {
			Int: new IntType
			Real: new RealType
			Bool: new BoolType
			//String: new StringType
		}
	}
	
	// for null - incomplete and incorrect parsing results
	def dispatch IPLType typeOf(Void x) {
		println('Null typing results - possible error')
		null
	}
	
	def dispatch IPLType typeOf(Set s) {
		if (s.members.size != 0)
			new SetType(typeOf(s.members.get(0))) 
		else 
			new SetType(null)
	}
	
	def dispatch IPLType typeOf(Lst s) {
		if (s.members.size != 0)
			new ListType(typeOf(s.members.get(0))) 
		else 
			new ListType(null)
	}
	
	def dispatch IPLType typeOf(Formula f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(TAtomUnary f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(TAtomBinary f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(QAtom f) {
		new BoolType
	}
	
	/*def dispatch IPLType typeOf(TermFormula f) {
		new BoolType
	}*/
	
	def dispatch IPLType typeOf(Fun f) {
		IPLUtils::typesDecl2IPL(f.decl.retType)
	}
	
	def dispatch IPLType typeOf(ExprOperation e) {
		if (e.left.typeOf instanceof RealType || e.right.typeOf instanceof RealType)
			new RealType
		else
			new IntType
	}
	
	def dispatch IPLType typeOf(PropertyExpression p) {
		val type = typeOf(p.left)
		
		switch (type) {
			ComponentType: type.getMemberType(p.right.id)
			default: null
		}
	}
	
	def dispatch IPLType typeOf(ModelExpr me) {
		typeOf(me.expr)
	}
	
	def dispatch IPLType typeOf(PrismExpr pq) {//used to be ProbQuery
		if(pq.value instanceof QM)
			new RealType
		else 
			new BoolType
	}
	
	// returns a type of a given quantification domain
	public def IPLType getQdomType(EObject qdom){ 
		switch(qdom) { 
			Expression:
				typeOf(qdom)
			TypeInt:
				new IntType
			TypeReal: 
				new RealType
			TypeBool:
				new BoolType
			TypeElem: 
			  	new ElementType
		}
	}
	
	def getParamTypes(Fun fun) {		
		fun.decl.paramTypes.map[IPLUtils::typesDecl2IPL(it)]
	}
	
	// Duplicate code: 
	// Resolve id here -- whether it has been defined
//	def isDef(ID e) {
//		val name = e.id
//		
//		if (spec === null )
//			spec = e.getContainerOfType(IPLSpec)
//		val decls = spec.decls
//		
//		val decl = decls.findLast[it instanceof TypedDecl && (it as TypedDecl).name == name] as TypedDecl
//		
//		if (decl !== null) {
//			true
//		} else {
//			for (c : (e.allContainers.filter[it instanceof QAtom])) {
//				val q = c as QAtom
//				if (q !== null && q.^var == name)
//					return true
//						
//			}
//			return false
//		}
//	}

	
}