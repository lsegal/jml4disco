package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.BranchLabel;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.codegen.ConstantPool;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

/** An abstraction of a JML clause which can be either a:
 * - type body clause,
 * - method spec clause,
 * - statement body clause.
 * While we could create subclasses for each of the categories mentioned above
 * we have currently chosen not to do so (keeping the type hierarchy a bit
 * flatter and simpler).
 * 
 * Most JML clauses contain a predicate and can be marked as redundant, 
 * hence this characteristics are captured here.
 */
public abstract class JmlClause extends JmlAstNode {

	protected static final boolean DEBUG = false;
	//@ public static final String REDUNDANTLY_SUFFIX = "_redundantly"; //$NON-NLS-1$
	// FIXME: eventually throw a JML specific runtime exception.
	public static final char[] JML_RUNTIME_EXCEPTION = "java/lang/Error".toCharArray(); //$NON-NLS-1$

	public final String clauseKeyword;
	private final boolean isRedundant;
	public final /*@nullable*/ Expression pred;

	//@ ensures this.clauseKeyword == clauseKeyword;
	//@ ensures this.pred == pred;
	//@ ensures this.notSpecifiedLexeme == notSpecifiedLexeme;
	private JmlClause(String clauseKeyword, boolean isRedundant, Expression pred, String keywordGivenInsteadOfPred) {
		this.clauseKeyword = clauseKeyword.intern();
		this.isRedundant = isRedundant;
		this.pred = pred;
	}

	//@ ensures this.clauseKeyword == clauseKeyword;
	//@ ensures this.pred == pred;
	//@ ensures "".equals(this.notSpecifiedLexeme);
	public JmlClause(String clauseKeyword, boolean isRedundant, Expression pred) {
		this(clauseKeyword, isRedundant, pred, EMPTY_STRING);
	}

	//@ ensures this.clauseKeyword == clauseKeyword;
	//@ ensures this.pred == null;
	//@ ensures this.notSpecifiedLexeme == notSpecifiedLexeme;
	public JmlClause(String clauseKeyword, boolean isRedundant) {
		this(clauseKeyword, isRedundant, null, EMPTY_STRING);
	}

	public StringBuffer print(int indent, StringBuffer output) {
		printIndent(indent, output).append(this.clauseKeyword + SPACE);
		if (hasPred())
			this.pred.print(0, output);
		return output.append(SEMICOLON);
	}

	public void resolve(BlockScope scope) {
		if (hasPred()) {
			TypeBinding type = pred.resolveTypeExpecting(scope, TypeBinding.BOOLEAN);
			pred.computeConversion(scope, type, type);	
		}
		else if (this.isRedundant()) {
			// FIXME: ensure hasPred() for redundant clauses.
			// Report a problem!
			System.err.println("FIXME: report a problem -- redundant clause must have a predicate."); //$NON-NLS-1$
		}
	}

	public void analyseCode(BlockScope scope, FlowContext context, FlowInfo flowInfo) {
		if (hasPred())
			this.pred.analyseCode(scope, context, flowInfo);
	}

	public abstract void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream);

	//@ ensures \result <==> expr != null;
	//@ pure
	public boolean hasPred() {
		return pred != null;
	}
	
	/**
	 * Returns the kind of this clause as a String for the purpose of error
	 * reporting -- e.g. "precondition".
	 */
	public String kind() {
		return this.clauseKeyword + " clause"; //$NON-NLS-1$
	}

	protected void generateEvaluateAndThrowIfFalse(BlockScope currentScope,	CodeStream codeStream) {
		String msg = kind() + " failed ('"+(this.pred.toString())+"')";  //$NON-NLS-1$//$NON-NLS-2$
		generateEvaluateAndThrowIfFalse(currentScope, codeStream, msg);
	}

	private void generateEvaluateAndThrowIfFalse(BlockScope currentScope,
			CodeStream codeStream, String msg) {
		pred.generateCode(currentScope, codeStream, true);
		BranchLabel trueLabel = new BranchLabel(codeStream);
		codeStream.ifne(trueLabel);
		codeStream.newClassFromName(JML_RUNTIME_EXCEPTION, msg);
		codeStream.athrow();
		trueLabel.place();
	}

	protected void generateInvariantCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		TypeDeclaration enclosingType = currentScope.classScope().referenceContext;
		if (enclosingType instanceof JmlTypeDeclaration) {
			JmlTypeDeclaration jmlType = (JmlTypeDeclaration) enclosingType;
			jmlType.generateCheck(currentScope, methodDecl, codeStream);
		}
	}

	protected void generatePrintValue(BlockScope currentScope, CodeStream codeStream) {
		generatePrintValue(currentScope, codeStream, "<unknown>"); //$NON-NLS-1$
	}
	protected void generatePrintValue(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		generatePrintValue(currentScope, codeStream, new String(methodDecl.selector));
	}
	private void generatePrintValue(BlockScope currentScope,
			CodeStream codeStream, String where) {
		if (pred == null || pred.resolvedType == null)
			return;
		String msg = kind() + " of " +  where //$NON-NLS-1$
		           + " is '" + pred + "' and evaluated to "; //$NON-NLS-1$ //$NON-NLS-2$
		codeStream.getSystemDotOut();
		codeStream.newClassFromName(ConstantPool.JavaLangStringBufferConstantPoolName);
		codeStream.ldc(msg);
		codeStream.invokeStringBufferAppend(ConstantPool.JavaLangStringSignature);
		pred.generateCode(currentScope, codeStream, true);
		codeStream.invokeStringBufferAppend(pred.resolvedType.signature());
		codeStream.invokeStringConcatenationToString();
		codeStream.invokeSystemOutPrintln();
	}

	protected void generatePrintValue(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream,
			LocalVariableBinding localBinding, String what) {
		codeStream.getSystemDotOut();
		codeStream.newClassFromName(ConstantPool.JavaLangStringBufferConstantPoolName);
		String msg = what + " of " + (new String(methodDecl.selector)); //$NON-NLS-1$
		msg += " is '" + localBinding + "' and evaluated to "; //$NON-NLS-1$ //$NON-NLS-2$
		codeStream.ldc(msg);
		codeStream.invokeStringBufferAppend(ConstantPool.JavaLangStringSignature);
		codeStream.load(localBinding);
		codeStream.invokeStringBufferAppend(localBinding.type.signature());
		codeStream.invokeStringConcatenationToString();
		codeStream.invokeSystemOutPrintln();
	}

	public boolean isRedundant() {
		return this.isRedundant;
	}

	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if(visitor.visit(this, scope)) {
			if(this.pred != null)
				this.pred.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}
}
