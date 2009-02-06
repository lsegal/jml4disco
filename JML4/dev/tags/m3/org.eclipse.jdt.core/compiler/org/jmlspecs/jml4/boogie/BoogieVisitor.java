package org.jmlspecs.jml4.boogie;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.lookup.*;
import org.jmlspecs.jml4.ast.*;

public class BoogieVisitor extends ASTVisitor {
	private static final boolean DEBUG = true;
	private int indent = 0;
	private boolean newLine = true;
	private StringBuffer implBody = new StringBuffer();

	private void debug(ASTNode term, Object scope) {
		if (!DEBUG)
			return;
		System.out.println("Visiting " //$NON-NLS-1$
				+ term.getClass() + " on line " //$NON-NLS-1$
				+ term.sourceStart + (scope != null ? (" from scope " //$NON-NLS-1$
				+ scope.getClass().getSimpleName())
						: " from class scope")); //$NON-NLS-1$
	}

	public String getResults() {
		return implBody.toString();
	}

	private void append(Object o) {
		if (newLine && indent > 0) {
			for (int i = 0; i < indent; i++) {
				implBody.append("\t"); //$NON-NLS-1$
			}
		}
		implBody.append(o);
		newLine = false;
	}

	private void appendLine(Object o) {
		append(o);
		implBody.append("\n"); //$NON-NLS-1$
		newLine = true;
	}

	// TODO priority=2 group=expr
	public boolean visit(AllocationExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(AND_AND_Expression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=decl
	public boolean visit(AnnotationMethodDeclaration term, ClassScope classScope) {
		debug(term, classScope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(Argument term, BlockScope scope) {
		debug(term, scope);

		append(new String(term.name) + ": "); //$NON-NLS-1$
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(Argument term, ClassScope scope) {
		debug(term, scope);

		append(new String(term.name) + ": "); //$NON-NLS-1$
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ArrayAllocationExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ArrayInitializer term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=array
	public boolean visit(ArrayQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=array
	public boolean visit(ArrayQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=array
	public boolean visit(ArrayReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=array
	public boolean visit(ArrayTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=array
	public boolean visit(ArrayTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=misc
	public boolean visit(AssertStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(Assignment term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(BinaryExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(Block term, BlockScope scope) {
		debug(term, scope);
		appendLine("{"); //$NON-NLS-1$
		indent++;
		return true;
	}

	public void endVisit(Block term, BlockScope scope) {
		indent--;
		appendLine("}"); //$NON-NLS-1$
	}

	// TODO priority=3 group=stmt
	public boolean visit(BreakStatement term, BlockScope scope) {
		debug(term, scope);
		append("break;"); //$NON-NLS-1$
		return true;
	}

	// TODO priority=2 group=stmt
	public boolean visit(CaseStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(CastExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=lit
	public boolean visit(CharLiteral term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(ClassLiteralAccess term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(Clinit term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=decl
	public boolean visit(CompilationUnitDeclaration term, CompilationUnitScope scope) {
		debug(term, scope);
		// implemented
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(CompoundAssignment term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(ConditionalExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=decl
	public boolean visit(ConstructorDeclaration term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(ContinueStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=stmt
	public boolean visit(DoStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(DoubleLiteral term, BlockScope scope) {
		debug(term, scope);
		append(new String(term.source()));
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(EmptyStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(EqualExpression term, BlockScope scope) {
		if (DEBUG) {
			debug(term, scope);
		}

		term.left.traverse(this, scope);
		append(" == "); //$NON-NLS-1$
		term.right.traverse(this, scope);

		return false;
	}

	// TODO priority=1 group=expr
	public boolean visit(ExplicitConstructorCall term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=lit
	public boolean visit(ExtendedStringLiteral term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(FalseLiteral term, BlockScope scope) {
		debug(term, scope);
		append("false"); //$NON-NLS-1$
		return true;
	}

	// TODO priority=3 group=field
	public boolean visit(FieldDeclaration term, MethodScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=field
	public boolean visit(FieldReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=field
	public boolean visit(FieldReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(FloatLiteral term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(ForeachStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(ForStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(IfStatement term, BlockScope scope) {
		debug(term, scope);

		append("if ("); //$NON-NLS-1$
		term.condition.traverse(this, scope);
		append(") "); //$NON-NLS-1$
		term.thenStatement.traverse(this, scope);
		append("else "); //$NON-NLS-1$
		term.elseStatement.traverse(this, scope);

		return false;
	}

	// TODO priority=0 group=misc
	public boolean visit(ImportReference term, CompilationUnitScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=misc 
	public boolean visit(Initializer term, MethodScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(InstanceOfExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(IntLiteral term, BlockScope scope) {
		debug(term, scope);
		append(new String(term.source()));
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(Javadoc term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(Javadoc term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocAllocationExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocAllocationExpression term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArgumentExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArgumentExpression term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArrayQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArrayQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArraySingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocArraySingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocFieldReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocFieldReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocImplicitTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocImplicitTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocMessageSend term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocMessageSend term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocReturnStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocReturnStatement term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocSingleNameReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocSingleNameReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocSingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=javadoc
	public boolean visit(JavadocSingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlArrayQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlArrayQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlArrayReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlArrayTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlArrayTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlAssertStatement term, BlockScope scope) {
		debug(term, scope);
		append("assert "); //$NON-NLS-1$
		return true;
	}

	public void endVisit(JmlAssertStatement term, BlockScope scope) {
		appendLine(";"); //$NON-NLS-1$
	}

	// TODO priority=? group=jml
	public boolean visit(JmlAssignment term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlAssumeStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlCastExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlCastExpressionWithoutType term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlClause term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlCompilationUnitDeclaration term, CompilationUnitScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlConstructorDeclaration term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlEnsuresClause term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlFieldDeclaration term, MethodScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlFieldReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlFieldReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlLocalDeclaration term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlLoopAnnotations term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlLoopInvariant term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlLoopVariant term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlMessageSend term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlMethodDeclaration term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlMethodSpecification term, ClassScope classScope) {
		debug(term, classScope);
		return true;
	}

	// TODO priority=2 group=jml
	public boolean visit(JmlOldExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlParameterizedQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlParameterizedQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlParameterizedSingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlParameterizedSingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlQualifiedNameReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlQualifiedNameReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlQuantifiedExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlRequiresClause term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlResultReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlReturnStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlSingleNameReference term, BlockScope scope) {
		append(new String(term.toString()));
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlSingleNameReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlSingleTypeReference term, BlockScope scope) {
		append(new String(term.token));
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlSingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlWhileStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=jml
	public boolean visit(JmlWildcard term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=jml
	public boolean visit(JmlWildcard term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(LabeledStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=decl
	public boolean visit(LocalDeclaration term, BlockScope scope) {
		debug(term, scope);
		String name = new String(term.name);
		append("var " + name + " : "); //$NON-NLS-1$//$NON-NLS-2$
		term.type.traverse(this, scope);
		appendLine(";"); //$NON-NLS-1$
		append(name + " := "); //$NON-NLS-1$
		term.initialization.traverse(this, scope);
		appendLine(";"); //$NON-NLS-1$
		return false;
	}

	// TODO priority=3 group=lit
	public boolean visit(LongLiteral term, BlockScope scope) {
		debug(term, scope);
		append(new String(term.source()));
		return true;
	}

	// TODO priority=? group=decl
	public boolean visit(MarkerAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(MemberValuePair term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(MessageSend term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=decl
	public boolean visit(MethodDeclaration term, ClassScope scope) {
		debug(term, scope);

		append("procedure "); //$NON-NLS-1$
		append(new String(term.binding.declaringClass.readableName()) + "."); //$NON-NLS-1$
		append(new String(term.selector));
		append("("); //$NON-NLS-1$
		if (term.arguments != null) {
			for (int i = 0; i < term.arguments.length; i++) {
				term.arguments[i].traverse(this, scope);
				if (i < term.arguments.length - 1) {
					append(", "); //$NON-NLS-1$
				}
			}
		}
		append(")"); //$NON-NLS-1$
		if (term.returnType.resolveType(scope) != TypeBinding.VOID) {
			append(" returns (__result__ : "); //$NON-NLS-1$
			term.returnType.traverse(this, scope);
			append(")"); //$NON-NLS-1$
		}
		appendLine(" {"); //$NON-NLS-1$
		indent++;

		for (int i = 0; i < term.statements.length; i++) {
			term.statements[i].traverse(this, term.scope);
		}

		indent--;
		appendLine("}"); //$NON-NLS-1$

		return false;
	}

	// TODO priority=? group=decl
	public boolean visit(NormalAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(NullLiteral term, BlockScope scope) {
		debug(term, scope);
		append("null"); //$NON-NLS-1$
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(OR_OR_Expression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ParameterizedQualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ParameterizedQualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ParameterizedSingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ParameterizedSingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(PostfixExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(PrefixExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(QualifiedAllocationExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(QualifiedNameReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=? group=expr
	public boolean visit(QualifiedNameReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedSuperReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedSuperReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedThisReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedThisReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedTypeReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(QualifiedTypeReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(ReturnStatement term, BlockScope scope) {
		debug(term, scope);
		append("return "); //$NON-NLS-1$
		return true;
	}

	public void endVisit(ReturnStatement term, BlockScope scope) {
		appendLine(";"); //$NON-NLS-1$
	}

	// TODO priority=? group=expr
	public boolean visit(SingleMemberAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(SingleNameReference term, BlockScope scope) {
		append(new String(term.token));
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(SingleNameReference term, ClassScope scope) {
		debug(term, scope);
		append(new String(term.token));
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(SingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		// TODO print passified variable name
		append(new String(term.token));
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(SingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		append(new String(term.resolveType(scope).readableName()));
		return true;
	}

	// TODO priority=2 group=lit
	public boolean visit(StringLiteral term, BlockScope scope) {
		debug(term, scope);
		String name = new String(term.source());
		// TODO can this be improved? declare these at the top
		append("string_lit_" + new Integer(name.hashCode())); //$NON-NLS-1$
		return true;
	}

	// TODO priority=1 group=lit
	public boolean visit(StringLiteralConcatenation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(SuperReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(SwitchStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(SynchronizedStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ThisReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(ThisReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(ThrowStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=lit
	public boolean visit(TrueLiteral term, BlockScope scope) {
		debug(term, scope);
		append("true"); //$NON-NLS-1$
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(TryStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=decl
	public boolean visit(TypeDeclaration term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=decl
	public boolean visit(TypeDeclaration term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=decl
	public boolean visit(TypeDeclaration term, CompilationUnitScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(TypeParameter term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(TypeParameter term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(UnaryExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=stmt
	public boolean visit(WhileStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=misc
	public boolean visit(Wildcard term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=0 group=misc
	public boolean visit(Wildcard term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

}
