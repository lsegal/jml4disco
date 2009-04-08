package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ClassFile;
import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.ExceptionHandlingFlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.flow.InitializationFlowContext;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlConstructorDeclaration extends ConstructorDeclaration implements JmlAbstractMethodDeclaration {

	public static final boolean DEBUG = false;
	public JmlMethodSpecification specification;
	private boolean jmlModifiersHaveBeenInit = false;
	private long jmlModifiers = 0;
	private /*@nullable*/Result[] escResults;
	private boolean previousRacState;

	public JmlConstructorDeclaration(CompilationResult compilationResult) {
		super(compilationResult);
	}

	public void resolve(ClassScope upperScope) {
		initJmlModifiersFromAnnotations();
		super.resolve(upperScope);
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE)
			return;
		if (this.specification != null)
			this.specification.resolve(this.scope);
	}

	public void resolveStatements() {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE
			&& this.isModel())
			return;
		super.resolveStatements();
	}

	public void initJmlModifiersFromAnnotations() {
		jmlModifiers |= JmlModifier.getFromAnnotations(this.annotations);
		this.jmlModifiersHaveBeenInit = true;
	}

	public void analyseCode(ClassScope classScope,
			InitializationFlowContext initializerFlowContext,
			FlowInfo flowInfo, int initialReachMode) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_ANALYSIS) {
			if (!this.isModel())
				super.analyseCode(classScope, initializerFlowContext, flowInfo, initialReachMode);
			return;
		}
		// TODO uncomment the following line
		// checkNullityOfSupers(classScope);
		// TODO: remove the following test once we fix the parser to only use Jml AST Nodes when EnabledJml.
		if (classScope.compilerOptions().useNonNullTypeSystem()) {
			JmlMethodDeclaration.tagParametersWithNullities(this, flowInfo);
		}
		ExceptionHandlingFlowContext constructorContext =
			new ExceptionHandlingFlowContext(
				initializerFlowContext,
				this,
				this.binding.thrownExceptions,
				this.scope,
				FlowInfo.DEAD_END);

		if (classScope.compilerOptions().jmlDbcEnabled && this.specification != null) {
			this.specification.analysePrecondition(this.scope, constructorContext, flowInfo);
		}
		JmlMethodDeclaration.handleArgumentsAnnotations(this.arguments, classScope);

		super.analyseCode(classScope, initializerFlowContext, flowInfo, initialReachMode);

		if (classScope.compilerOptions().jmlDbcEnabled && this.specification != null) {
			//TODO: the call to super uses a different flowInfo when analysing the statements. Is this a problem?
			this.specification.analysePostcondition(this.scope, constructorContext, flowInfo);
		}
		if (isPure())
			checkPurity();
	}
	private void checkPurity() {
		// TODO: implement purity check
	}
	
	public boolean isPure() {
		if (!this.jmlModifiersHaveBeenInit)
			initJmlModifiersFromAnnotations();
		return JmlModifier.isPure(this.jmlModifiers);
	}

	public boolean isModel() {
		if (!this.jmlModifiersHaveBeenInit)
			initJmlModifiersFromAnnotations();
		return JmlModifier.isModel(this.jmlModifiers);
	}

	protected void checkMissingBlankFieldNullity(FieldBinding field, ClassScope classScope, FlowInfo flowInfo) {
		if (!classScope.compilerOptions().useNonNullTypeSystem())
			return;
		if ((!field.isStatic())
				&& (field.fieldDeclaration != null 
				   && field.fieldDeclaration.type != null
				   && field.fieldDeclaration.type.isDeclaredNonNull()
				   && ! Nullity.isPrimitiveType(field.type))
				&& (!flowInfo.isDefinitelyAssigned(field))) {
				this.scope.problemReporter().uninitializedBlankNonNullField(
					field,
					((this.bits & ASTNode.IsDefaultConstructor) != 0) ? (ASTNode)field.fieldDeclaration : this);
			}
	}

	public void generateCode(ClassFile classFile) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION
				&& this.isModel()) // if this is not a model method we still want to generate code for the method body.
			return;
		super.generateCode(classFile);
		if (this.scope.compilerOptions().jmlEscGovernsRac) {
			this.scope.compilerOptions().jmlRacEnabled = this.previousRacState;
		}
	}

	protected void generateChecksForPrecondition(MethodScope initializerScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		if (this.specification != null) {
			this.specification.generateCheckOfRequires(initializerScope, this, codeStream);
		}
		JmlMethodDeclaration.generateChecksForNonNullParametersStatic(this, codeStream);
		if (initializerScope.compilerOptions().jmlEscGovernsRac) {
			this.previousRacState = initializerScope.compilerOptions().jmlRacEnabled;
			if (JmlMethodDeclaration.escSayNoNeedToCheck(this.escResults)) {
				initializerScope.compilerOptions().jmlRacEnabled = false;
			}
		}
	}

	protected void generateChecksForPostcondition(MethodScope methodScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		generateCheckForInitiallys(methodScope, codeStream);
		if (this.specification != null) {
			this.specification.generateCheckOfEnsures(methodScope, this, codeStream);
		}
	}
	
	protected void generateCheckForInitiallys(MethodScope mScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
				return;
		// assert initiallys for non-helper constructors
		if (!JmlModifier.isHelper(jmlModifiers)) {
			TypeDeclaration typeDecl = mScope.classScope().referenceContext;
			if (typeDecl instanceof JmlTypeDeclaration) {
				((JmlTypeDeclaration) typeDecl).generateCheckForInitiallys(mScope, this, codeStream);
			}
		}
	}

	public void traverse(ASTVisitor visitor,	ClassScope classScope) {
		if (visitor.visit(this, classScope)) {
			super.traverse(visitor, classScope);
		}
		visitor.endVisit(this, classScope);
	}

	public JmlMethodSpecification getSpecification() {
		return this.specification;
	}

	public void setEscResults(Result[] results) {
		this.escResults = results;
	}

}
