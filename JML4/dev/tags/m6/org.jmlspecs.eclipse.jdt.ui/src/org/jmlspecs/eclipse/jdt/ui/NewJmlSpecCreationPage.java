package org.jmlspecs.eclipse.jdt.ui;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.net.URI;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.viewers.IStructuredSelection;

import org.eclipse.ui.PlatformUI;

import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.IBuffer;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IImportDeclaration;
import org.eclipse.jdt.core.IInitializer;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.formatter.CodeFormatter;

import org.eclipse.jdt.ui.CodeGeneration;
import org.eclipse.jdt.ui.wizards.NewTypeWizardPage;
import org.eclipse.jdt.ui.wizards.NewTypeWizardPage.ImportsManager;

import org.eclipse.jdt.internal.corext.codemanipulation.StubUtility;
import org.eclipse.jdt.internal.corext.util.CodeFormatterUtil;
import org.eclipse.jdt.internal.corext.util.JavaModelUtil;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.corext.util.Resources;
import org.eclipse.jdt.internal.corext.util.Strings;
import org.eclipse.jdt.internal.ui.IJavaHelpContextIds;
import org.eclipse.jdt.internal.ui.dialogs.StatusInfo;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;
import org.eclipse.jdt.internal.ui.wizards.dialogfields.DialogField;
import org.eclipse.jdt.internal.ui.wizards.dialogfields.LayoutUtil;
import org.eclipse.jdt.internal.ui.wizards.dialogfields.SelectionButtonDialogFieldGroup;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;

// This was started from NewClassCreationPage

public class NewJmlSpecCreationPage extends NewTypeWizardPage {
        
        private final static String PAGE_NAME= "NewJmlSpecCreationPage"; //$NON-NLS-1$
        
        private final static String SETTINGS_CREATEMETHODS = "create_methods"; //$NON-NLS-1$
        
        private final static String pageTitle = "New JML Specification";
        private final static String pageDescription = "Creates a new JML specification file";
        
        private SelectionButtonDialogFieldGroup fMethodStubsButtons;
        
        /**
         * Creates a new <code>NewClassWizardPage</code>
         */
        public NewJmlSpecCreationPage() {
            super(true, PAGE_NAME);
            
            setTitle(pageTitle); 
            setDescription(pageDescription); 
            
            String[] buttonNames3= new String[] { "Populate specification from its type" };
            fMethodStubsButtons= new SelectionButtonDialogFieldGroup(SWT.CHECK, buttonNames3, 1);
            fMethodStubsButtons.setLabelText("PAGE METHODS");        
        }
        
        // -------- Initialization ---------
        
        /**
         * The wizard owning this page is responsible for calling this method with the
         * current selection. The selection is used to initialize the fields of the wizard 
         * page.
         * 
         * @param selection used to initialize the fields
         */
        public void init(IStructuredSelection selection) {
            IJavaElement jelem= getInitialJavaElement(selection);
            initContainerPage(jelem);
            initTypePage(jelem);
            doStatusUpdate();
            
            boolean createMethods= false;
            IDialogSettings dialogSettings= getDialogSettings();
            if (dialogSettings != null) {
                IDialogSettings section= dialogSettings.getSection(PAGE_NAME);
                if (section != null) {
                    createMethods = section.getBoolean(SETTINGS_CREATEMETHODS);
                }
            }
            
            setMethodStubSelection(createMethods, false, false, true);
        }
        
        // ------ validation --------
        private void doStatusUpdate() {
            // status of all used components
            IStatus[] status= new IStatus[] {
                fContainerStatus,
                isEnclosingTypeSelected() ? fEnclosingTypeStatus : fPackageStatus,
                fTypeNameStatus,
                fModifierStatus,
                fSuperClassStatus,
                fSuperInterfacesStatus
            };
            
            // the mode severe status will be displayed and the OK button enabled/disabled.
            updateStatus(status);
        }
        
        
        /*
         * @see NewContainerWizardPage#handleFieldChanged
         */
        protected void handleFieldChanged(String fieldName) {
            super.handleFieldChanged(fieldName);
            
            doStatusUpdate();
        }
        
        
        // ------ UI --------
        
        /*
         * @see WizardPage#createControl
         */
        public void createControl(Composite parent) {
            initializeDialogUnits(parent);
            
            Composite composite= new Composite(parent, SWT.NONE);
            composite.setFont(parent.getFont());
            
            int nColumns= 4;
            
            GridLayout layout= new GridLayout();
            layout.numColumns= nColumns;        
            composite.setLayout(layout);
            
            // pick & choose the wanted UI components
            
            createContainerControls(composite, nColumns);   
            createPackageControls(composite, nColumns); 
            createEnclosingTypeControls(composite, nColumns);
                    
            createSeparator(composite, nColumns);
            
            createTypeNameControls(composite, nColumns);
            createModifierControls(composite, nColumns);
                
            createSuperClassControls(composite, nColumns);
            createSuperInterfacesControls(composite, nColumns);
                    
            createMethodStubSelectionControls(composite, nColumns);
            
            createCommentControls(composite, nColumns);
            enableCommentControl(true);
            
            setControl(composite);
                
            Dialog.applyDialogFont(composite);
            // FIXME PlatformUI.getWorkbench().getHelpSystem().setHelp(composite, IJavaHelpContextIds.NEW_CLASS_WIZARD_PAGE);    
        }
        
        /*
         * @see WizardPage#becomesVisible
         */
        public void setVisible(boolean visible) {
            super.setVisible(visible);
            if (visible) {
                setFocus();
            } else {
                IDialogSettings dialogSettings= getDialogSettings();
                if (dialogSettings != null) {
                    IDialogSettings section= dialogSettings.getSection(PAGE_NAME);
                    if (section == null) {
                        section= dialogSettings.addNewSection(PAGE_NAME);
                    }
                    section.put(SETTINGS_CREATEMETHODS, isCreateMethods());
                }
            }
        }   
        
        private void createMethodStubSelectionControls(Composite composite, int nColumns) {
            Control labelControl= fMethodStubsButtons.getLabelControl(composite);
            LayoutUtil.setHorizontalSpan(labelControl, nColumns);
            
            DialogField.createEmptySpace(composite);
            
            Control buttonGroup= fMethodStubsButtons.getSelectionButtonsGroup(composite);
            LayoutUtil.setHorizontalSpan(buttonGroup, nColumns - 1);    
        }
        
        /**
         * Returns the current selection state of the 'Create Main' checkbox.
         * 
         * @return the selection state of the 'Create Main' checkbox
         */
        public boolean isCreateMethods() {
            return fMethodStubsButtons.isSelected(0);
        }

         /**
         * Sets the selection state of the method stub checkboxes.
         * 
         * @param createMain initial selection state of the 'Create Main' checkbox.
         * @param createConstructors initial selection state of the 'Create Constructors' checkbox.
         * @param createInherited initial selection state of the 'Create inherited abstract methods' checkbox.
         * @param canBeModified if <code>true</code> the method stub checkboxes can be changed by 
         * the user. If <code>false</code> the buttons are "read-only"
         */
        public void setMethodStubSelection(boolean createMethods, boolean createConstructors, boolean createInherited, boolean canBeModified) {
            fMethodStubsButtons.setSelection(0, createMethods);
            
            fMethodStubsButtons.setEnabled(canBeModified);
        }   
        
        // ---- creation ----------------
          // FIXME - complete implementatino here
        /*
         * @see NewTypeWizardPage#createTypeMembers
         */
        protected void createTypeMembers(IType type, ImportsManager imports, IProgressMonitor monitor) throws CoreException {
            boolean doMethods = isCreateMethods();
            createInheritedMethods(type, false, false, imports, new SubProgressMonitor(monitor, 1));

            if (doMethods) {
                StringBuffer buf= new StringBuffer();
                final String lineDelim= "\n"; // OK, since content is formatted afterwards //$NON-NLS-1$
                String comment= CodeGeneration.getMethodComment(type.getCompilationUnit(), type.getTypeQualifiedName('.'), "main", new String[] {"args"}, new String[0], Signature.createTypeSignature("void", true), null, lineDelim); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
                if (comment != null) {
                    buf.append(comment);
                    buf.append(lineDelim);
                }
                buf.append("public static void main("); //$NON-NLS-1$
                buf.append(imports.addImport("java.lang.String")); //$NON-NLS-1$
                buf.append("[] args) {"); //$NON-NLS-1$
                buf.append(lineDelim);
                final String content= CodeGeneration.getMethodBodyContent(type.getCompilationUnit(), type.getTypeQualifiedName('.'), "main", false, "", lineDelim); //$NON-NLS-1$ //$NON-NLS-2$
                if (content != null && content.length() != 0)
                    buf.append(content);
                buf.append(lineDelim);
                buf.append("}"); //$NON-NLS-1$
                type.createMethod(buf.toString(), null, false, null);
            }
            
            if (monitor != null) {
                monitor.done();
            }   
        }
 
        private String getTypeNameWithoutParameters() {
            String typeNameWithParameters= getTypeName();
            int angleBracketOffset= typeNameWithParameters.indexOf('<');
            if (angleBracketOffset == -1) {
                return typeNameWithParameters;
            } else {
                return typeNameWithParameters.substring(0, angleBracketOffset);
            }
        }
        
        public void insertType(IType ty, StringBuffer s, String indent, String eol) throws JavaModelException {
            s.append(eol+indent);
            int fl = ty.getFlags();
            if (fl != 0) s.append(Flags.toString(fl) + " ");
            if (ty.isInterface()) {
                s.append("interface ");
            } else if (ty.isEnum()) {
                s.append("enum "); // FIXME - implement this; also Annotatino
            } else {
                s.append("class ");
            }
            s.append(ty.getElementName());
            String sn = ty.getSuperclassName();
            if (sn != null) s.append(" extends " + sn);
            String[] a = ty.getSuperInterfaceNames();
            if (a != null && a.length != 0) {
                if (ty.isInterface()) s.append(" extends " + a[0]);
                else s.append(" implements " + a[0]);
                for (int ii=1; ii<a.length; ++ii) {
                    s.append(", " + a[ii]);
                }
            }
            s.append(" {" + eol);
            IJavaElement[] jj = ty.getChildren();
            String tabbed = indent+tabamount;
            for (int i=0; i<jj.length; i++) {
                IJavaElement j = jj[i];
                if (j instanceof IType) {
                    insertType((IType)j,s,tabbed,eol);
                } else if (j instanceof IMethod) {
                    insertMethod((IMethod)j,s,tabbed,eol);
                } else if (j instanceof IField) {
                    insertField((IField)j,s,tabbed,eol);
                } else if (j instanceof IInitializer) {
                    insertInitializer((IInitializer)j,s,tabbed,eol);
                } else { // FIXME 
                    s.append(" // MISSING a " + j.getClass() + " " + j.getElementName() + eol);
                }
            }
            s.append(eol+indent+ "}"+eol);
        }
        
        final public String tabamount = "  ";

        public void insertInitializer(IInitializer i, StringBuffer s, String indent, String eol) throws JavaModelException {
            s.append(eol + indent);
            // FIXME _ put in specs
            if (Flags.isStatic(i.getFlags())) s.append("//@ static_initializer");
            else s.append("//@ initializer");
            s.append(eol);
        }
        public void insertMethod(IMethod m, StringBuffer s, String indent, String eol) throws JavaModelException {
            s.append(eol + indent);
            // FIXME _ put in specs
            int fl = m.getFlags();
            if (fl != 0) s.append(Flags.toString(fl) + " ");
            if (!m.isConstructor()) s.append("TBDTYPE");
            s.append(" ");
            s.append(m.getElementName());
            s.append("( TBDTYPES ) TBD EXCEPTIONS;" + eol);
        }

        public void insertField(IField f, StringBuffer s, String indent, String eol) throws JavaModelException {
            s.append(eol + indent);
            // FIXME _ put in specs
            int fl = f.getFlags();
            if (fl != 0) s.append(Flags.toString(fl) + " ");
            s.append("TBDTYPE ");
            s.append(f.getElementName());
            s.append(";" + eol);
        }
        
        public void insertCompUnit(ICompilationUnit cu, StringBuffer s, String eol, IPackageFragment pack) throws JavaModelException {
            s.append("package ");
            s.append(pack.getElementName());
            s.append(";");
            s.append(eol);
            s.append(eol);
            IImportDeclaration[] imports = cu.getImports();
            for (int i=0; i<imports.length; i++) {
                IImportDeclaration im = imports[i];
                s.append("import ");
                if (Flags.isStatic(im.getFlags())) s.append("static ");
                s.append(im.getElementName());
                if (im.isOnDemand()) s.append(".*");
                s.append(";"+eol);
            }
            s.append(eol);
            IType[] types = cu.getAllTypes();
            for (int i=0; i<types.length; i++) {
                IType ty = types[i];
                insertType(ty,s,"",eol);
            }

        }

        /**
         * Creates the new type using the entered field values.
         * 
         * @param monitor a progress monitor to report progress.
         * @throws CoreException Thrown when the creation failed.
         * @throws InterruptedException Thrown when the operation was canceled.
         */
        public void createType(IProgressMonitor monitor) throws CoreException, InterruptedException {       
            if (monitor == null) {
                monitor= new NullProgressMonitor();
            }

            monitor.beginTask(NewWizardMessages.NewTypeWizardPage_operationdesc, 8); 
            
            IPackageFragmentRoot root= getPackageFragmentRoot();
            IPackageFragment pack= getPackageFragment();
            if (pack == null) {
                pack= root.getPackageFragment(""); //$NON-NLS-1$
            }
            
            if (!pack.exists()) {
                String packName= pack.getElementName();
                pack= root.createPackageFragment(packName, true, new SubProgressMonitor(monitor, 1));
            } else {
                monitor.worked(1);
            }
            
            boolean needsSave;
            ICompilationUnit connectedCU= null;
            
            // FIXME - complete implementation here
            try {
                String typeName= getTypeNameWithoutParameters();
                IFolder f = (IFolder)pack.getResource();
                IFile file = f.getFile(typeName + ".jml");
                StringBuffer s = new StringBuffer();
                //String eol = StubUtility.getLineDelimiterUsed(pack.getJavaProject()); // FIXME - use this?
                String eol = System.getProperty("line.separator", "\n");
                if (fCurrType != null && fCurrType.exists() && isCreateMethods()) {
                    // Add all contents
                    insertCompUnit(fCurrType.getCompilationUnit(),s,eol,pack);
                } else {
                    s.append("package ");
                    s.append(pack.getElementName());
                    s.append(";");
                    s.append(eol);
                    s.append(eol);
                    s.append("class " + typeName); // FIXME - interface?
                    String sn = getSuperClass();
                    if (sn != null) s.append(" extends " + sn);
                    Iterator i = getSuperInterfaces().iterator();
                    if (i.hasNext()) {
                        s.append(" implements ");
                        s.append(i.next());
                        while (i.hasNext()) s.append(", " + i.next());
                    }
                    s.append(" {" + eol);
                    s.append("}");
                }
                
                InputStream i = new ByteArrayInputStream(s.toString().getBytes("UTF-8")); // FIXME - what charset?
                file.create(i,false,monitor);
                
                
            } catch (Exception e) {
                Log.errorlog("FAILED ",e);
                // FIXME
            }
//            try {   
//                String typeName= getTypeNameWithoutParameters();
//                
//                boolean isInnerClass= isEnclosingTypeSelected();
//            
//                IType createdType;
//                ImportsManager imports;
//                int indent= 0;
//
//                Set /* String (import names) */ existingImports;
//                
//                String lineDelimiter= null; 
//                if (!isInnerClass) {
//                   lineDelimiter= StubUtility.getLineDelimiterUsed(pack.getJavaProject());
//                    
//                    String cuName= getCompilationUnitName(typeName);
//                    ICompilationUnit parentCU= pack.createCompilationUnit(cuName, "", false, new SubProgressMonitor(monitor, 2)); //$NON-NLS-1$
//                    // create a working copy with a new owner
//                    
//                    needsSave= true;
//                    parentCU.becomeWorkingCopy(new SubProgressMonitor(monitor, 1)); // cu is now a (primary) working copy
//                    connectedCU= parentCU;
//                    
//                    IBuffer buffer= parentCU.getBuffer();
//                    
//                    String simpleTypeStub= constructSimpleTypeStub();
//                    String cuContent= constructCUContent(parentCU, simpleTypeStub, lineDelimiter);
//                    buffer.setContents(cuContent);
//                    
//                    CompilationUnit astRoot= createASTForImports(parentCU);
//                    existingImports= getExistingImports(astRoot);
//                                
//                    imports= new ImportsManager(astRoot);
//                    // add an import that will be removed again. Having this import solves 14661
//                    imports.addImport(JavaModelUtil.concatenateName(pack.getElementName(), typeName));
//                    
//                    String typeContent= constructTypeStub(parentCU, imports, lineDelimiter);
//                    
//                    int index= cuContent.lastIndexOf(simpleTypeStub);
//                    if (index == -1) {
//                        AbstractTypeDeclaration typeNode= (AbstractTypeDeclaration) astRoot.types().get(0);
//                        int start= ((ASTNode) typeNode.modifiers().get(0)).getStartPosition();
//                        int end= typeNode.getStartPosition() + typeNode.getLength();
//                        buffer.replace(start, end - start, typeContent);
//                    } else {
//                        buffer.replace(index, simpleTypeStub.length(), typeContent);
//                    }
//                    
//                    createdType= parentCU.getType(typeName);
//                } else {
//                    IType enclosingType= getEnclosingType();
//                    
//                    ICompilationUnit parentCU= enclosingType.getCompilationUnit();
//                    
//                    needsSave= !parentCU.isWorkingCopy();
//                    parentCU.becomeWorkingCopy(new SubProgressMonitor(monitor, 1)); // cu is now for sure (primary) a working copy
//                    connectedCU= parentCU;
//                    
//                    CompilationUnit astRoot= createASTForImports(parentCU);
//                    imports= new ImportsManager(astRoot);
//                    existingImports= getExistingImports(astRoot);
//
//        
//                    // add imports that will be removed again. Having the imports solves 14661
//                    IType[] topLevelTypes= parentCU.getTypes();
//                    for (int i= 0; i < topLevelTypes.length; i++) {
//                        imports.addImport(topLevelTypes[i].getFullyQualifiedName('.'));
//                    }
//                    
//                    lineDelimiter= StubUtility.getLineDelimiterUsed(enclosingType);
//                    StringBuffer content= new StringBuffer();
//                    
//                    String comment= getTypeComment(parentCU, lineDelimiter);
//                    if (comment != null) {
//                        content.append(comment);
//                        content.append(lineDelimiter);
//                    }
//
//                    content.append(constructTypeStub(parentCU, imports, lineDelimiter));
//                    IJavaElement sibling= null;
//                    if (enclosingType.isEnum()) {
//                        IField[] fields = enclosingType.getFields();
//                        if (fields.length > 0) {
//                            for (int i = 0, max = fields.length; i < max; i++) {
//                                if (!fields[i].isEnumConstant()) {
//                                    sibling = fields[i];
//                                    break;
//                                }
//                            }
//                        }
//                    } else {
//                        IJavaElement[] elems= enclosingType.getChildren();
//                        sibling = elems.length > 0 ? elems[0] : null;
//                    }
//                    
//                    createdType= enclosingType.createType(content.toString(), sibling, false, new SubProgressMonitor(monitor, 2));
//                
//                    indent= StubUtility.getIndentUsed(enclosingType) + 1;
//                }
//                if (monitor.isCanceled()) {
//                    throw new InterruptedException();
//                }
//                
//                // add imports for superclass/interfaces, so types can be resolved correctly
//                
//                ICompilationUnit cu= createdType.getCompilationUnit();  
//                
//                imports.create(false, new SubProgressMonitor(monitor, 1));
//                    
//                JavaModelUtil.reconcile(cu);
//
//                if (monitor.isCanceled()) {
//                    throw new InterruptedException();
//                }
//                
//                // set up again
//                CompilationUnit astRoot= createASTForImports(imports.getCompilationUnit());
//                imports= new ImportsManager(astRoot);
//                
//                createTypeMembers(createdType, imports, new SubProgressMonitor(monitor, 1));
//        
//                // add imports
//                imports.create(false, new SubProgressMonitor(monitor, 1));
//                
//                removeUnusedImports(cu, existingImports, false);
//                
//                JavaModelUtil.reconcile(cu);
//                
//                ISourceRange range= createdType.getSourceRange();
//                
//                IBuffer buf= cu.getBuffer();
//                String originalContent= buf.getText(range.getOffset(), range.getLength());
//                
//                String formattedContent= CodeFormatterUtil.format(CodeFormatter.K_CLASS_BODY_DECLARATIONS, originalContent, indent, null, lineDelimiter, pack.getJavaProject());
//                formattedContent= Strings.trimLeadingTabsAndSpaces(formattedContent);
//                buf.replace(range.getOffset(), range.getLength(), formattedContent);
//                if (!isInnerClass) {
//                    String fileComment= getFileComment(cu);
//                    if (fileComment != null && fileComment.length() > 0) {
//                        buf.replace(0, 0, fileComment + lineDelimiter);
//                    }
//                }
//                fCreatedType= createdType;
//
//                if (needsSave) {
//                    cu.commitWorkingCopy(true, new SubProgressMonitor(monitor, 1));
//                } else {
//                    monitor.worked(1);
//                }
//                
//            } finally {
//                if (connectedCU != null) {
//                    connectedCU.discardWorkingCopy();
//                }
//                monitor.done();
//            }
        } 

        private IType fCurrType;

        /**
         * Hook method that gets called when the type name has changed. The method validates the 
         * type name and returns the status of the validation.
         * <p>
         * Subclasses may extend this method to perform their own validation.
         * </p>
         * 
         * @return the status of the validation
         */
        protected IStatus typeNameChanged() {
            StatusInfo status= new StatusInfo();
            fCurrType= null;
            String typeNameWithParameters= getTypeName();
            // must not be empty
            if (typeNameWithParameters.length() == 0) {
                status.setError(NewWizardMessages.NewTypeWizardPage_error_EnterTypeName); 
                return status;
            }
            
            String typeName= getTypeNameWithoutParameters();
            if (typeName.indexOf('.') != -1) {
                status.setError(NewWizardMessages.NewTypeWizardPage_error_QualifiedName); 
                return status;
            }
            
            IJavaProject project= getJavaProject(); 
            IStatus val= validateJavaTypeName(typeName, project);
            if (val.getSeverity() == IStatus.ERROR) {
                status.setError(Messages.format(NewWizardMessages.NewTypeWizardPage_error_InvalidTypeName, val.getMessage())); 
                return status;
            } else if (val.getSeverity() == IStatus.WARNING) {
                status.setWarning(Messages.format(NewWizardMessages.NewTypeWizardPage_warning_TypeNameDiscouraged, val.getMessage())); 
                // continue checking
            }       

            // must not exist
            if (!isEnclosingTypeSelected()) {
                IPackageFragment pack= getPackageFragment();
                if (pack != null) {
                    ICompilationUnit cu= pack.getCompilationUnit(getCompilationUnitName(typeName));
                    fCurrType= cu.getType(typeName);
                    IResource resource= cu.getResource();
                    // FIXME - if type name already exists, we can fill in the methods from it.
//                  if (resource.exists()) {
//                  status.setError(NewWizardMessages.NewTypeWizardPage_error_TypeNameExists); 
//                  return status;
//              }
                    String nameExt = typeName + ".jml";
                    IFile file = ((IFolder)pack.getResource()).getFile(nameExt);
                    if (file.exists()) {
                        status.setError("Specification file already exists: " + nameExt); 
                        return status;
                    }
                    
                    // FIXME - enable the following check??
//                    URI location= resource.getLocationURI();
//                    if (location != null) {
//                        try {
//                            IFileStore store= EFS.getStore(location);
//                            if (store.fetchInfo().exists()) {
//                                status.setError(NewWizardMessages.NewTypeWizardPage_error_TypeNameExistsDifferentCase); 
//                                return status;
//                            }
//                        } catch (CoreException e) {
//                            status.setError(Messages.format(
//                                NewWizardMessages.NewTypeWizardPage_error_uri_location_unkown, 
//                                Resources.getLocationString(resource)));
//                        }
//                    }
                }
            } else {
                // FIXME - probably do not want to handle enclosed types
                IType type= getEnclosingType();
                if (type != null) {
                    fCurrType= type.getType(typeName);
                    if (fCurrType.exists()) {
                        status.setError(NewWizardMessages.NewTypeWizardPage_error_TypeNameExists); 
                        return status;
                    }
                }
            }
            
            if (!typeNameWithParameters.equals(typeName) && project != null) {
                if (!JavaModelUtil.is50OrHigher(project)) {
                    status.setError(NewWizardMessages.NewTypeWizardPage_error_TypeParameters); 
                    return status;
                }
                String typeDeclaration= "class " + typeNameWithParameters + " {}"; //$NON-NLS-1$//$NON-NLS-2$
                ASTParser parser= ASTParser.newParser(AST.JLS3);
                parser.setSource(typeDeclaration.toCharArray());
                parser.setProject(project);
                CompilationUnit compilationUnit= (CompilationUnit) parser.createAST(null);
                IProblem[] problems= compilationUnit.getProblems();
                if (problems.length > 0) {
                    status.setError(Messages.format(NewWizardMessages.NewTypeWizardPage_error_InvalidTypeName, problems[0].getMessage())); 
                    return status;
                }
            }
            return status;
        }

 

        private static IStatus validateJavaTypeName(String text, IJavaProject project) {
            if (project == null || !project.exists()) {
                return JavaConventions.validateJavaTypeName(text, JavaCore.VERSION_1_3, JavaCore.VERSION_1_3);
            }
            String sourceLevel= project.getOption(JavaCore.COMPILER_SOURCE, true);
            String compliance= project.getOption(JavaCore.COMPILER_COMPLIANCE, true);
            return JavaConventions.validateJavaTypeName(text, sourceLevel, compliance);
        }

}

