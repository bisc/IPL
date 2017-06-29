package org.xtext.example.ipl

import com.google.inject.Inject
import com.google.inject.Provider
import java.util.Collections
import org.apache.log4j.Logger
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.EReference
import org.eclipse.xtext.linking.LinkingScopeProviderBinding
import org.eclipse.xtext.linking.impl.AbstractLinkingService
import org.eclipse.xtext.linking.impl.IllegalNodeException
import org.eclipse.xtext.linking.impl.ImportedNamesAdapter
import org.eclipse.xtext.linking.impl.LinkingHelper
import org.eclipse.xtext.naming.IQualifiedNameConverter
import org.eclipse.xtext.naming.QualifiedName
import org.eclipse.xtext.nodemodel.INode
import org.eclipse.xtext.resource.IEObjectDescription
import org.eclipse.xtext.scoping.IScope
import org.eclipse.xtext.scoping.IScopeProvider
import org.eclipse.xtext.scoping.impl.AbstractGlobalScopeDelegatingScopeProvider
import org.eclipse.xtext.scoping.impl.IDelegatingScopeProvider

class IPLLinkingService extends AbstractLinkingService {
	
	val logger = Logger.getLogger(IPLLinkingService)
	
	@Inject
	@LinkingScopeProviderBinding
	var IScopeProvider scopeProvider
	
	@Inject
	var Provider<ImportedNamesAdapter> importedNamesAdapterProvider
	
	@Inject 
	var LinkingHelper linkingHelper
	
	//@Inject
	var IQualifiedNameConverter qualifiedNameConverter = new IQualifiedNameConverter.DefaultImpl() {
		
		override getDelimiter() {
			"::"
		}
			
	}
	
	/**
	 * @return the first element returned from the injected {@link IScopeProvider} which matches the text of the passed
	 *         {@link INode node}
	 */
	override getLinkedObjects(EObject context, EReference ref, INode node) throws IllegalNodeException {
		
		val EClass requiredType = ref.getEReferenceType()
		if (requiredType === null)
			return Collections.<EObject> emptyList()

		val String crossRefString = getCrossRefNodeAsString(node)
		if (crossRefString !== null && crossRefString != "") {
			if (logger.isDebugEnabled()) {
				logger.debug("before getLinkedObjects: node: '" + crossRefString + "'")
			}
			
//			System::out.println("before getLinkedObjects: node: '" + crossRefString + "'")
			
			val IScope scope = getScope(context, ref)
			val QualifiedName qualifiedLinkName =  qualifiedNameConverter.toQualifiedName(crossRefString)
			
//			System::out.println("QN: " + qualifiedLinkName + " : " + qualifiedLinkName.segments)
			
			val IEObjectDescription eObjectDescription = scope.getSingleElement(qualifiedLinkName)
			
//			System::out.println("Searching scope:")
//			
//			for (e : scope.allElements) {
//				System::out.println(e.qualifiedName.segments)
//			}
		
			if (logger.isDebugEnabled()) {
				logger.debug("after getLinkedObjects: node: '" + crossRefString + "' result: " + eObjectDescription)
			}
	
//			System::out.println("after getLinkedObjects: node: '" + crossRefString + "' result: " + eObjectDescription)
//			System::out.println()
//			System::out.println()
			
			if (eObjectDescription !== null) 
				return Collections.singletonList(eObjectDescription.getEObjectOrProxy())
		}
		return Collections.emptyList()
		
	}
	
	protected def IScope getScope(EObject context, EReference reference) {
		if (getScopeProvider() === null)
			throw new IllegalStateException("scopeProvider must not be null.")
		try {
			registerImportedNamesAdapter(context)
			return getScopeProvider().getScope(context, reference)
		} catch (Exception e) {
			throw e
		} finally {
			unRegisterImportedNamesAdapter()
		}
	}
	
	protected def void unRegisterImportedNamesAdapter() {
		unRegisterImportedNamesAdapter(getScopeProvider())
	}
	
	protected def void unRegisterImportedNamesAdapter(IScopeProvider scopeProvider) {
		if (scopeProvider instanceof AbstractGlobalScopeDelegatingScopeProvider) {
			val AbstractGlobalScopeDelegatingScopeProvider provider = scopeProvider as AbstractGlobalScopeDelegatingScopeProvider
			provider.setWrapper(null)
		} else if (scopeProvider instanceof IDelegatingScopeProvider) {
			val IDelegatingScopeProvider delegatingScopeProvider = scopeProvider as IDelegatingScopeProvider
			unRegisterImportedNamesAdapter(delegatingScopeProvider.getDelegate())
		}
	}

	protected def void registerImportedNamesAdapter(EObject context) {
		registerImportedNamesAdapter(getScopeProvider(), context)
	}
	
	protected def void registerImportedNamesAdapter(IScopeProvider scopeProvider, EObject context) {
		if (scopeProvider instanceof AbstractGlobalScopeDelegatingScopeProvider) {
			val AbstractGlobalScopeDelegatingScopeProvider provider = scopeProvider as AbstractGlobalScopeDelegatingScopeProvider
			val ImportedNamesAdapter adapter = getImportedNamesAdapter(context)
			provider.setWrapper(adapter)
		} else if (scopeProvider instanceof IDelegatingScopeProvider) {
			val IDelegatingScopeProvider delegatingScopeProvider = scopeProvider as IDelegatingScopeProvider
			registerImportedNamesAdapter(delegatingScopeProvider.getDelegate(), context)
		}
	}

	protected def ImportedNamesAdapter getImportedNamesAdapter(EObject context) {
		val ImportedNamesAdapter adapter = ImportedNamesAdapter.find(context.eResource())
		if (adapter !== null)
			return adapter
		val ImportedNamesAdapter importedNamesAdapter = importedNamesAdapterProvider.get()
		context.eResource().eAdapters().add(importedNamesAdapter)
		return importedNamesAdapter
	}
	
	def String getCrossRefNodeAsString(INode node) throws IllegalNodeException {
		linkingHelper.getCrossRefNodeAsString(node, true)
	}

	def void setScopeProvider(IScopeProvider scopeProvider) {
		this.scopeProvider = scopeProvider
	}

	def IScopeProvider getScopeProvider() {
		scopeProvider
	}

	def LinkingHelper getLinkingHelper() {
		linkingHelper
	}
}
