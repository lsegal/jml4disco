package org.jmlspecs.jml4.boogie;

import java.util.List;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.lookup.*;
import org.jmlspecs.jml4.ast.*;

public class BoogieVisitor extends ASTVisitor {
	private static final boolean DEBUG = true;
	private BlockScope methodScope;
	private BoogieSource output;
	
	private static final String BLOCK_OPEN = "{"; //$NON-NLS-1$
	private static final String BLOCK_CLOSE = "}"; //$NON-NLS-1$
	private static final String STMT_END = ";"; //$NON-NLS-1$
	
	public BoogieVisitor(BoogieSource output) {
		this.output = output;
	}
	
	public static BoogieSource visit(CompilationUnitDeclaration unit) {
		return visit(unit, new BoogieSource());
	}

	public static BoogieSource visit(CompilationUnitDeclaration unit, BoogieSource output) {
		BoogieVisitor visitor = new BoogieVisitor(output);
		unit.traverse(visitor, unit.scope);
		return output;
	}

	public void appendLine(Object o) { output.appendLine(o); }
	
	public void append(Object o) { output.append(o); }

	public void append(Object o, ASTNode linePointTerm) {
		output.append(o, linePointTerm);
	}

	private void debug(ASTNode term, Object scope) {
		if (!DEBUG)
			return;
		System.out.println("Visiting " //$NON-NLS-1$
				+ term.getClass() + " on line " //$NON-NLS-1$
				+ term.sourceStart + (scope != null ? (" from scope " //$NON-NLS-1$
				+ scope.getClass().getSimpleName())
						: " from class scope")); //$NON-NLS-1$
	}

	// TODO priority=2 group=expr
	public boolean visit(AllocationExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=expr
	public boolean visit(AND_AND_Expression term, BlockScope scope) {
		debug(term, scope);
		term.left.traverse(this, scope);
		append(" && "); //$NON-NLS-1$
		term.right.traverse(this, scope);
		return false;
	}

	// priority=0 group=decl
	public boolean visit(AnnotationMethodDeclaration term, ClassScope classScope) {
		debug(term, classScope);
		return true;
	}

	// priority=3 group=expr
	public boolean visit(Argument term, BlockScope scope) {
		debug(term, scope);

		append(new String(term.name) + ": "); //$NON-NLS-1$
		return true;
	}

	// priority=3 group=expr
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

	// TODO priority=3 group=misc
	public boolean visit(AssertStatement term, BlockScope scope) {
		debug(term, scope);
		JmlAssertStatement stmt = 
			new JmlAssertStatement("assert", term.assertExpression, term.sourceStart); //$NON-NLS-1$
		stmt.traverse(this, scope);
		return false;
	}

	// priority=3 group=expr
	public boolean visit(Assignment term, BlockScope scope) {
		debug(term, scope);
		term.lhs.traverse(this, scope);
		append(" := "); //$NON-NLS-1$
		term.expression.traverse(this, scope);
		return false;
	}

	// TODO priority=2 group=expr
	public boolean visit(BinaryExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=stmt
	public boolean visit(Block term, BlockScope scope) {
		debug(term, scope);
		appendLine(BLOCK_OPEN);
		output.increaseIndent();
		return true;
	}

	public void endVisit(Block term, BlockScope scope) {
		output.decreaseIndent();
		appendLine(BLOCK_CLOSE);
	}

	// priority=3 group=stmt
	public boolean visit(BreakStatement term, BlockScope scope) {
		debug(term, scope);
		if (term.label == null)  
			appendLine("break" + STMT_END); //$NON-NLS-1$
		else
			appendLine("break " + new String(term.label) + STMT_END);  //$NON-NLS-1$
			
		return true;
	}

	// TODO priority=2 group=stmt
	public boolean visit(CaseStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
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

	// priority=3 group=decl
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

	// TODO priority=3 group=stmt
	public boolean visit(DoStatement term, BlockScope scope) {
		debug(term, scope);		
		if (term.action instanceof Block) {
			Block block = (Block) term.action;
			for (int i = 0; i < block.statements.length; i++) {
				block.statements[i].traverse(this, scope);
			}
		} else {
			appendLine(term.action);
		}
		WhileStatement whl = new WhileStatement(term.condition, term.action, term.sourceStart, term.sourceEnd);  
		whl.traverse(this, scope); 
		return false;
	}

	// priority=3 group=lit
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

	// priority=3 group=expr
	public boolean visit(EqualExpression term, BlockScope scope) {
		debug(term, scope);

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

	// priority=3 group=lit
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

	// priority=3 group=stmt
	public boolean visit(IfStatement term, BlockScope scope) {
		debug(term, scope);

		append("if ("); //$NON-NLS-1$
		term.condition.traverse(this, scope);
		append(") "); //$NON-NLS-1$
		if (term.thenStatement!= null)
			if (!(term.thenStatement instanceof Block )) {
				output.increaseIndent();
				appendLine(BLOCK_OPEN); 
			}							
			term.thenStatement.traverse(this, scope);
			if (!(term.thenStatement instanceof Block )) {				
				output.decreaseIndent();
				appendLine(BLOCK_CLOSE);
			}			
		if (term.elseStatement != null) {
			append("else "); //$NON-NLS-1$
			if (!(term.elseStatement instanceof Block )) {				
				appendLine(BLOCK_OPEN);
				output.increaseIndent();
			}			
			term.elseStatement.traverse(this, scope);
			if (!(term.elseStatement instanceof Block )) {
				output.decreaseIndent();
				appendLine(BLOCK_CLOSE);
			}		
		}
		return false;
	}

	// priority=0 group=misc
	public boolean visit(ImportReference term, CompilationUnitScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=misc 
	public boolean visit(Initializer term, MethodScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(InstanceOfExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=lit
	public boolean visit(IntLiteral term, BlockScope scope) {
		debug(term, scope);
		append(new String(term.source()));
		return true;
	}

	// priority=3 group=jml
	public boolean visit(JmlAssertStatement term, BlockScope scope) {
		debug(term, scope);
		append("assert ", term.assertExpression); //$NON-NLS-1$
		term.assertExpression.traverse(this, scope);
		appendLine(STMT_END);
		return false;
	}

	// TODO priority=? group=jml
	public boolean visit(JmlAssignment term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=jml
	public boolean visit(JmlAssumeStatement term, BlockScope scope) {
		debug(term, scope);
		append("assume ", term.assertExpression); //$NON-NLS-1$
		term.assertExpression.traverse(this, scope);
		appendLine(STMT_END);
		return false;
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

	// priority=0 group=jml
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

	// TODO priority=3 group=jml
	public boolean visit(JmlMethodSpecification term, ClassScope scope) {
		debug(term, scope);

		// TODO ensures
		for (int i = 0; i < term.specCases.length; i++) {
			append(" "); //$NON-NLS-1$
			append("ensures ", term); //$NON-NLS-1$
			List exprs = term.specCases[i].getEnsuresExpressions();
			for (int j = 0; j < exprs.size(); j++) {
				Expression expr = (Expression)exprs.get(j);
				expr.traverse(this, methodScope);
			}
			append(STMT_END);
		}

		return true;
	}

	// TODO priority=2 group=jml
	public boolean visit(JmlOldExpression term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=jml
	public boolean visit(JmlRequiresClause term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=1 group=jml
	public boolean visit(JmlResultReference term, BlockScope scope) {
		debug(term, scope);
		append("__result__"); //$NON-NLS-1$
		return true;
	}

	// priority=1 group=stmt
	public boolean visit(LabeledStatement term, BlockScope scope) {
		debug(term, scope);
		appendLine(new String (term.label) + ":"); //$NON-NLS-1$
		return true;
	}

	// priority=3 group=decl
	public boolean visit(LocalDeclaration term, BlockScope scope) {
		debug(term, scope);
		String name = new String(term.name);
		append("var " + name + " : "); //$NON-NLS-1$//$NON-NLS-2$
		term.type.traverse(this, scope);
		appendLine(STMT_END);
		
		if (term.initialization != null) {
			Assignment a = 
				new Assignment(new SingleNameReference(term.name, term.sourceStart), 
					term.initialization, term.sourceEnd);
			a.traverse(this, scope);
			appendLine(STMT_END);
		}
		return false;
	}
	
	// TODO priority=3 group=lit
	public boolean visit(LongLiteral term, BlockScope scope) {
		debug(term, scope);
		append(new String(term.source()));
		return true;
	}

	// priority=0 group=decl
	public boolean visit(MarkerAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=expr
	public boolean visit(MemberValuePair term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=expr
	public boolean visit(MessageSend term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=decl
	public boolean visit(MethodDeclaration term, ClassScope scope) {
		JmlMethodDeclaration jmlTerm = (JmlMethodDeclaration)term;
		methodScope = term.scope; // used by #visit(JmlMethodSpecification, ClassScope)
		
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
		
		// ensures & requires clause
		if (jmlTerm.getSpecification() != null) {
			visit(jmlTerm.getSpecification(), scope);
		}
		
		appendLine(" {"); //$NON-NLS-1$
		output.increaseIndent();

		if (term.statements != null) {
			for (int i = 0; i < term.statements.length; i++) {
				term.statements[i].traverse(this, term.scope);
				//appendLine(";"); //$NON-NLS-1$
			}
		}

		output.decreaseIndent();
		appendLine("}"); //$NON-NLS-1$

		return false;
	}

	// priority=0 group=decl
	public boolean visit(NormalAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=lit
	public boolean visit(NullLiteral term, BlockScope scope) {
		debug(term, scope);
		append("null"); //$NON-NLS-1$
		return true;
	}

	// priority=1 group=expr
	public boolean visit(OR_OR_Expression term, BlockScope scope) {
		debug(term, scope);
		append("("); //$NON-NLS-1$
		term.left.traverse(this, scope);
		append(" || "); //$NON-NLS-1$
		term.right.traverse(this, scope);
		append(")"); //$NON-NLS-1$
		return false;
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

	// priority=3 group=expr
	public boolean visit(ReturnStatement term, BlockScope scope) {
		debug(term, scope);
		if (term.expression != null) {
			char result[] = "__result__".toCharArray(); //$NON-NLS-1$
			Assignment m = new Assignment(
					new SingleTypeReference(result,  term.sourceStart),
						term.expression, term.sourceEnd);
			m.traverse(this, scope);
		}
		appendLine(STMT_END);
		append("return", term.expression); //$NON-NLS-1$
		appendLine(STMT_END); 
		return false;
	}

	// priority=0 group=expr
	public boolean visit(SingleMemberAnnotation term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=expr
	public boolean visit(SingleNameReference term, BlockScope scope) {
		append(new String(term.token));
		return true;
	}

	// priority=3 group=expr
	public boolean visit(SingleNameReference term, ClassScope scope) {
		debug(term, scope);
		append(new String(term.token));
		return true;
	}

	// priority=3 group=expr
	public boolean visit(SingleTypeReference term, BlockScope scope) {
		debug(term, scope);
		// TODO print passified variable name
		if (term.resolvedType == TypeBinding.BOOLEAN) {
			append("bool"); //$NON-NLS-1$
		}
		else {
			append(new String(term.token));
		}
		return true;
	}

	// priority=3 group=expr
	public boolean visit(SingleTypeReference term, ClassScope scope) {
		debug(term, scope);
		
		TypeBinding binding = term.resolveType(scope);
		if (binding == TypeBinding.BOOLEAN) {
			append("bool"); //$NON-NLS-1$
		}
		else {
			append(new String(binding.readableName()));
		}
		
		return true;
	}

	// priority=2 group=lit
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

	// TODO priority=2 group=expr
	public boolean visit(SuperReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=2 group=stmt
	public boolean visit(SwitchStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=1 group=stmt
	public boolean visit(SynchronizedStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(ThisReference term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// TODO priority=3 group=expr
	public boolean visit(ThisReference term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=0 group=stmt
	public boolean visit(ThrowStatement term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=3 group=lit
	public boolean visit(TrueLiteral term, BlockScope scope) {
		debug(term, scope);
		append("true"); //$NON-NLS-1$
		return true;
	}

	// priority=0 group=stmt
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

	// priority=3 group=stmt
	public boolean visit(WhileStatement term, BlockScope scope) {
		debug(term, scope);
		append("while ("); //$NON-NLS-1$
		term.condition.traverse(this, scope);
		append(") "); //$NON-NLS-1$
		if (!(term.action instanceof Block)){
			appendLine(BLOCK_OPEN);
			output.increaseIndent();			
		}
		
		term.action.traverse(this, scope);
		
		if (!(term.action instanceof Block)){
			output.decreaseIndent();				
			appendLine(BLOCK_CLOSE);
		}		
		return false;
	}

	// priority=0 group=misc
	public boolean visit(Wildcard term, BlockScope scope) {
		debug(term, scope);
		return true;
	}

	// priority=0 group=misc
	public boolean visit(Wildcard term, ClassScope scope) {
		debug(term, scope);
		return true;
	}

}
