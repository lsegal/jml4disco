package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
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
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

/** An abstraction of a JML clause which can be either a:
 * - type body clause,
 * - method spec clause,
 * - statement body clause.
 * While we could create subclasses for each of the categories mentioned above
 * we have currently chosen not to do so (keeping the type hierarchy a bit
 * flatter and simpler).
 * 
 * Features of instance of this class:
 * - clause has a keyword
 * - argument to the clause is either a single expression and/or
 *   a non-empty array of expressions. The type of the single expression is assumed to be
 *   a boolean (since it is generally a predicate). No assumption is made about the type
 *   of the expression array. 
 */
public abstract class JmlClause extends ASTNode implements JmlConstants {

	protected static final boolean DEBUG = false;
	// FIXME: eventually throw a JML specific runtime exception.
	// FIXME: the following should be with other type name decls.
	public static final char[] JML_RUNTIME_EXCEPTION = "java/lang/Error".toCharArray(); //$NON-NLS-1$

	public static final Expression NULL_EXPR = null;
	public static final Expression[] EMPTY_EXPR_LIST = new Expression[0];
	
	private final char[] clauseKeyword;
	private final boolean isRedundant;
	public final /*@nullable*/ Expression expr;

	protected JmlClause(JmlIdentifier keyword, /*@nullable*/Expression expr) {
		this.clauseKeyword = keyword.token();
		this.isRedundant = keyword.hasRedundantSuffix();
		this.expr = expr;
		
		this.sourceStart = keyword.sourceStart();
	}

	protected JmlClause(JmlIdentifier keyword) {
		this(keyword, NULL_EXPR);
	}

	public StringBuffer print(int indent, StringBuffer output) {
		printIndent(indent, output).append(this.clauseKeyword).append(SPACE);
		return printClauseContent(output).append(SEMICOLON);
	}

	protected StringBuffer printClauseContent(StringBuffer output) {
		if(hasExpr())
			this.expr.print(0, output);
		return output;
	}

	public void resolve(BlockScope scope) {
		if (hasNonKeywordExpr()) {
			resolveType(scope);
		} else if (this.isRedundant() ) {
			String msg = "A redundant " + kind() + " must be followed by an expression"; //$NON-NLS-1$ //$NON-NLS-2$
			// FIXME: define a real error.
			scope.problemReporter().jmlEsc2Error(msg, sourceStart, sourceEnd);
		}
	}

	// Resolve type of this.expr.
	//@ requires hasNonKeywordExpr();
	protected TypeBinding resolveType(BlockScope scope) {
		return expr.resolveTypeExpecting(scope, TypeBinding.BOOLEAN);
	}

	public void analyseCode(BlockScope scope, FlowContext context, FlowInfo flowInfo) {
		if (hasExpr())
			this.expr.analyseCode(scope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		// do nothing
	}

	//@ ensures \result == (expr != null);
	//@ pure
	public boolean hasExpr() {
		return expr != null;
	}
	
	public boolean hasNonKeywordExpr() {
		return expr != null && !(expr instanceof JmlKeywordExpression);
	}
	/**
	 * Returns the kind of this clause as a String for the purpose of error
	 * reporting -- e.g. "precondition".
	 */
	public String kind() {
		return this.clauseKeyword() + " clause"; //$NON-NLS-1$
	}

	public String clauseKeyword() {
		return new String(this.clauseKeyword).intern();
	}

	protected void generateEvaluateAndThrowIfFalse(BlockScope currentScope,	CodeStream codeStream) {
		String msg = kind() + " failed ('"+(this.expr.toString())+"')";  //$NON-NLS-1$//$NON-NLS-2$
		generateEvaluateAndThrowIfFalse(currentScope, codeStream, msg);
	}

	private void generateEvaluateAndThrowIfFalse(BlockScope currentScope,
			CodeStream codeStream, String msg) {
		expr.generateCode(currentScope, codeStream, true);
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
		if (expr == null || expr.resolvedType == null)
			return;
		String msg = kind() + " of " +  where //$NON-NLS-1$
		           + " is '" + expr + "' and evaluated to "; //$NON-NLS-1$ //$NON-NLS-2$
		codeStream.getSystemDotOut();
		codeStream.newClassFromName(ConstantPool.JavaLangStringBufferConstantPoolName);
		codeStream.ldc(msg);
		codeStream.invokeStringBufferAppend(ConstantPool.JavaLangStringSignature);
		expr.generateCode(currentScope, codeStream, true);
		codeStream.invokeStringBufferAppend(expr.resolvedType.signature());
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
			if(this.expr != null)
				this.expr.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}
}
