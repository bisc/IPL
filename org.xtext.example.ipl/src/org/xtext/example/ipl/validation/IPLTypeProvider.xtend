package org.xtext.example.ipl.validation

import java.util.ArrayList
import java.util.HashMap
import java.util.List
import org.eclipse.xtext.resource.IEObjectDescription
import org.osate.aadl2.AadlBoolean
import org.osate.aadl2.AadlInteger
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
import org.xtext.example.ipl.iPL.ProbQuery
import org.xtext.example.ipl.iPL.PropertyExpression
import org.xtext.example.ipl.iPL.QAtom
import org.xtext.example.ipl.iPL.Real
import org.xtext.example.ipl.iPL.STVarDec
import org.xtext.example.ipl.iPL.Set
import org.xtext.example.ipl.iPL.SortDec
import org.xtext.example.ipl.iPL.TAtom
import org.xtext.example.ipl.iPL.TermFormula
import org.xtext.example.ipl.iPL.Type
import org.xtext.example.ipl.iPL.TypeBool
import org.xtext.example.ipl.iPL.TypeInt
import org.xtext.example.ipl.iPL.TypeLst
import org.xtext.example.ipl.iPL.TypeReal
import org.xtext.example.ipl.iPL.TypeSet
import org.xtext.example.ipl.iPL.TypedDec
import org.xtext.example.ipl.iPL.VarDec
import org.xtext.example.ipl.iPL.ViewDec

import static extension org.eclipse.xtext.EcoreUtil2.*

class IPLTypeProvider {
	
	HashMap<ComponentInstance, List<Property>> instPropCache = new HashMap
	HashMap<ComponentClassifier, List<Property>> classifierPropCache = new HashMap
	
	def IPLType fromType(Type t) {
		switch (t) {
			TypeInt: new IntType
			TypeReal: new RealType
			TypeBool: new BoolType
			TypeSet: new SetType(fromType((t as TypeSet).elem))
			TypeLst: new ListType(fromType((t as TypeLst).elem))
		}
	}
	
	// declarations and IDs
	def dispatch IPLType typeOf(ID e) {
		// Resolve id here
		val name = e.id
		
//		System::out.println("####<" + e.id + ">####")
		
		val decls = e.getContainerOfType(IPLSpec).decls
		
		val decl = decls.findLast[it instanceof TypedDec && (it as TypedDec).name == name] as TypedDec
		
		if (decl !== null) {
			return switch (decl) {
				VarDec: fromType(decl.type)
				STVarDec: fromType(decl.type)
				SortDec: new SetType(fromComponentClassifier(decl.ref)) //used to be from ComponentImpl
				ViewDec: fromComponentImpl(decl.ref)
			}
		} else {
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
			return null
		}
	}
	
	// accepts a reference to the topmost element 
	def populatePropCache(ComponentImplementation ref) { 
		// TODO: do for all components and all properties at once? 
	}
	
	def IPLType fromComponentImpl(ComponentImplementation ref) {
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
	
	def IPLType fromComponentInst(ComponentInstance inst, List<Property> prop_cache) {
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
	
	def IPLType fromComponentClassifier(ComponentClassifier ref) {
		
		val ct = new ComponentType(ref.name) 
		
		// populate the cache if needed
		if (classifierPropCache.get(ref) === null) {
			classifierPropCache.put(ref, newArrayList())
			for (IEObjectDescription ieo : EMFIndexRetrieval::getAllPropertySetsInWorkspace(ref)) {
				val ps = OsateResourceUtil.getResourceSet().getEObject(ieo.getEObjectURI(), true) as PropertySet;
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
	
	def IPLType fromPropType(Property property) {
		switch (property.propertyType) {
			AadlBoolean: new BoolType
			AadlInteger: new IntType
			AadlReal: new RealType
			default: null
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
	
	def dispatch IPLType typeOf(TAtom f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(QAtom f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(TermFormula f) {
		new BoolType
	}
	
	def dispatch IPLType typeOf(Fun f) {
		fromType(f.name.retType)
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
	
	def dispatch IPLType typeOf(ProbQuery pq) { 
		new BoolType
	}
	
	def getParamTypes(Fun fun) {		
		fun.name.paramTypes.map[fromType]
	}
	
	def isDef(ID e) {
		// Resolve id here
		val name = e.id
		
		val decls = e.getContainerOfType(IPLSpec).decls
		
		val decl = decls.findLast[it instanceof TypedDec && (it as TypedDec).name == name] as TypedDec
		
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