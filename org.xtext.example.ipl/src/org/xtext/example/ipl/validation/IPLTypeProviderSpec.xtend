package org.xtext.example.ipl.validation

import java.rmi.UnexpectedException
import java.util.ArrayList
import java.util.HashMap
import java.util.List
import java.util.Map
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
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermFormula
import org.xtext.example.ipl.iPL.Type
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeLst
import org.xtext.example.ipl.iPL.TypeReal
import org.xtext.example.ipl.iPL.TypeSet
import org.xtext.example.ipl.iPL.TypedDecl
import org.xtext.example.ipl.iPL.VarDecl
import org.xtext.example.ipl.iPL.ViewDecl

import static extension org.eclipse.xtext.EcoreUtil2.*

// a version of the type provider working for a given spec
class IPLTypeProviderSpec {
	
	HashMap<ComponentClassifier, List<Property>> classifierPropCache = new HashMap
	IPLSpec spec 
	Map<String, IPLType> freeVarTypes = null
	
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
	
	private def IPLType fromType(Type t) {
		switch (t) {
			TypeInt: new IntType
			TypeReal: new RealType
			TypeBool: new BoolType
			TypeSet: new SetType(fromType((t as TypeSet).elem))
			TypeLst: new ListType(fromType((t as TypeLst).elem))
		}
	}

	private def IPLType fromComponentImpl(ComponentImplementation ref) {
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
				if (inst.acceptsProperty(prop) && fromPropType(prop) !== null) {
					prop_cache.add(prop);
				}
			}
		}
		
		fromComponentInst(inst, prop_cache)
	}
	
	private def IPLType fromComponentInst(ComponentInstance inst, List<Property> prop_cache) {
//		System::out.println(inst.children.map[switch (it) {
//			ComponentInstance: it.name
//			PropertyAssociationInstance: it.property.name 
//			default: "N/A"
//		}])
		
		val impl = InstanceUtil::getComponentImplementation(inst, 0, null)
		val ct = new ComponentType(if (impl === null) inst.name else impl.name)
		
		// add subcomponent instances as members
		inst.children.forEach[switch (it) {ComponentInstance: ct.addMember(it.name, fromComponentInst(it, prop_cache))}]

		for (prop : prop_cache) {
			if (inst.acceptsProperty(prop) && fromPropType(prop) !== null) {
				ct.addMember(prop.name, fromPropType(prop));
			}
		}
		 
		ct
	}
	
	private def IPLType fromComponentClassifier(ComponentClassifier ref) {
		
		val ct = new ComponentType(ref.name) 
		
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
				for (prop : ps.ownedProperties) {

					val propType = fromPropType(prop)
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
		classifierPropCache.get(ref).forEach[ct.addMember(it.name, fromPropType(it))]
		
		ct

	}
	
	private def IPLType fromPropType(Property property) {
		switch (property.propertyType) {
			AadlBoolean: new BoolType
			AadlInteger: new IntType
			AadlReal: new RealType
			default: null
		}
	}
	
		
	// declarations and IDs
	public def dispatch IPLType typeOf(ID e) {
		// Resolve id here
		val name = e.id
		
		val decls = spec.decls
		
		val decl = decls.findLast[it instanceof TypedDecl && (it as TypedDecl).name == name] as TypedDecl
		
		// try finding a declaration of the variable
		if (decl !== null) {
			return switch (decl) {
				VarDecl: fromType(decl.type)
				STVarDecl: fromType(decl.type)
				SortDecl: new SetType(fromComponentClassifier(decl.ref)) //used to be from ComponentImpl
				ViewDecl: fromComponentImpl(decl.ref)
			}
		} else { 
			if(freeVarTypes !== null)
				if (freeVarTypes.containsKey(name))
					return freeVarTypes.get(name)
			
			// without declaration, try finding a QAtom declaring a variable
			for (c : (e.allContainers.filter[it instanceof QAtom])) {
				val q = c as QAtom
				if (q !== null && q.^var == name) {
//					System::out.println("****<" + q.set + ">****")
					val type = typeOf(q.set)
					if (type instanceof SetType)
						return (type as SetType).elemType
					else
					// This is an error, but assume this is what the user meant
						return type
				}
			}
			
			
			
			// giving up, haven't found anything
			return null
		}
	}
	
	public def dispatch IPLType typeOf(Const c) {
		switch (c) {
			Int: new IntType
			Real: new RealType
			Bool: new BoolType
			//String: new StringType
		}
	}
	
	// for null - incomplete and incorrect parsing results
	public def dispatch IPLType typeOf(Void x) {
		println('Null typing results - possible error')
		null
	}
	
	public def dispatch IPLType typeOf(Set s) {
		if (s.members.size != 0)
			new SetType(typeOf(s.members.get(0))) 
		else 
			new SetType(null)
	}
	
	public def dispatch IPLType typeOf(Lst s) {
		if (s.members.size != 0)
			new ListType(typeOf(s.members.get(0))) 
		else 
			new ListType(null)
	}
	
	public def dispatch IPLType typeOf(Formula f) {
		new BoolType
	}
	
	public def dispatch IPLType typeOf(TAtom f) {
		new BoolType
	}
	
	public def dispatch IPLType typeOf(QAtom f) {
		new BoolType
	}
	
	public def dispatch IPLType typeOf(TermFormula f) {
		new BoolType
	}
	
	public def dispatch IPLType typeOf(Fun f) {
		fromType(f.decl.retType)
	}
	
	public def dispatch IPLType typeOf(ExprOperation e) {
		if (e.left.typeOf instanceof RealType || e.right.typeOf instanceof RealType)
			new RealType
		else
			new IntType
	}
	
	public def dispatch IPLType typeOf(PropertyExpression p) {
		val type = typeOf(p.left)
		
		switch (type) {
			ComponentType: type.getMemberType(p.right.id)
			default: null
		}
	}
	
	public def dispatch IPLType typeOf(ModelExpr me) {
		typeOf(me.expr)
	}
	
	public def dispatch IPLType typeOf(PrismExpr pq) {//used to be ProbQuery
		if(pq.value instanceof QM)
			new RealType
		else 
			new BoolType
	}
	
	public def getParamTypes(Fun fun) {		
		fun.decl.paramTypes.map[fromType]
	}
	
	public def isDef(ID e) {
		// Resolve id here
		val name = e.id
		
		val decl = spec.decls.findLast[it instanceof TypedDecl && (it as TypedDecl).name == name] as TypedDecl
		
		if (decl !== null) {
			true
		} else {
			for (c : (e.allContainers.filter[it instanceof QAtom])) {
				val q = c as QAtom
				if (q !== null && q.^var == name)
					return true
						
			}
			return false
		}
	}
	
	
}