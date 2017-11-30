package org.xtext.example.ipl.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.ICoreRunnable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.xtext.builder.EclipseResourceFileSystemAccess2;
import org.eclipse.xtext.generator.GeneratorContext;
import org.eclipse.xtext.generator.IGenerator2;
import org.eclipse.xtext.resource.IResourceDescriptions;
import org.eclipse.xtext.ui.resource.IResourceSetProvider;

import com.google.inject.Inject;
import com.google.inject.Provider;

/**
 * A handler for the IPL verification command from menu/toolbar button.  
 */
public class IPLVerifyHandler extends AbstractHandler {
	@Inject
	private IGenerator2 generator;

	@Inject
	private Provider<EclipseResourceFileSystemAccess2> fileAccessProvider;

	@Inject
	IResourceDescriptions resourceDescriptions;

	@Inject
	IResourceSetProvider resourceSetProvider;

	@Override
	/**
	 * Execute the command. 
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
		MessageDialog.openInformation(window.getShell(), "org.xtext.example.ipl", "Start IPL Verification");

		// find the project's src-gen folder to populate file system access
		ISelection selection = HandlerUtil.getCurrentSelection(event);
		if (selection instanceof IStructuredSelection) {
			IStructuredSelection structuredSelection = (IStructuredSelection) selection;
			Object firstElement = structuredSelection.getFirstElement(); // pick the first file of the selection
			if (firstElement instanceof IFile) {
				IFile file = (IFile) firstElement;
				IProject project = file.getProject();
				IFolder srcGenFolder = project.getFolder("src-gen");
				if (!srcGenFolder.exists()) {
					try {
						srcGenFolder.create(true, true, new NullProgressMonitor());
					} catch (CoreException e) {
						return null;
					}
				}

				// create file system access object
				final EclipseResourceFileSystemAccess2 fsa = fileAccessProvider.get();
				fsa.setProject(project);
				fsa.setOutputPath(srcGenFolder.getFullPath().toString());
				fsa.setMonitor(new NullProgressMonitor());
				fsa.setOutputPath("DEFAULT_OUTPUT", "src-gen");

				// get the selected file's resource 
				URI uri = URI.createPlatformResourceURI(file.getFullPath().toString(), true);
				ResourceSet rs = resourceSetProvider.get(project);
				Resource r = rs.getResource(uri, true);
				
				
				Job job = Job.create("Update table", (ICoreRunnable) monitor -> {
					// run the IPL generator
					GeneratorContext ctx = new GeneratorContext();
					generator.beforeGenerate(r, fsa, ctx);
					generator.doGenerate(r, fsa, ctx);
					generator.afterGenerate(r, fsa, ctx);
				
				});
				job.schedule();
				

			}
		}

		// ANOTHER WAY TO DO THIS:
		// IEditorPart editor =
		// PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
		// IProject currentProject =
		// editor.getEditorInput().getAdapter(IProject.class);
		//
		// EclipseResourceFileSystemAccess2 fsa = new
		// EclipseResourceFileSystemAccess2();//fileSystemAccessProvider.get();
		// fsa.setProject(currentProject);
		// fsa.setMonitor(new NullProgressMonitor());
		// Map<String, OutputConfiguration> outputs = new HashMap<String,
		// OutputConfiguration>();
		// for (OutputConfiguration conf :
		// outputConfigurationProvider.getOutputConfigurations(targetProject)) {
		// outputs.put(conf.getName(), conf);
		// }
		// fsa.setOutputConfigurations(outputs);

		return null;
	}
}
