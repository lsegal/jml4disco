package org.jmlspecs.jml4.fspv;

import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.AND_AND_Expression;
import org.eclipse.jdt.internal.compiler.ast.AllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.AnnotationMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.ArrayAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.ArrayInitializer;
import org.eclipse.jdt.internal.compiler.ast.ArrayQualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.ArrayTypeReference;
import org.eclipse.jdt.internal.compiler.ast.AssertStatement;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.BreakStatement;
import org.eclipse.jdt.internal.compiler.ast.CaseStatement;
import org.eclipse.jdt.internal.compiler.ast.CastExpression;
import org.eclipse.jdt.internal.compiler.ast.CharLiteral;
import org.eclipse.jdt.internal.compiler.ast.ClassLiteralAccess;
import org.eclipse.jdt.internal.compiler.ast.Clinit;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.ConditionalExpression;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ContinueStatement;
import org.eclipse.jdt.internal.compiler.ast.DoStatement;
import org.eclipse.jdt.internal.compiler.ast.DoubleLiteral;
import org.eclipse.jdt.internal.compiler.ast.EmptyStatement;
import org.eclipse.jdt.internal.compiler.ast.EqualExpression;
import org.eclipse.jdt.internal.compiler.ast.ExplicitConstructorCall;
import org.eclipse.jdt.internal.compiler.ast.ExtendedStringLiteral;
import org.eclipse.jdt.internal.compiler.ast.FalseLiteral;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.FloatLiteral;
import org.eclipse.jdt.internal.compiler.ast.ForStatement;
import org.eclipse.jdt.internal.compiler.ast.ForeachStatement;
import org.eclipse.jdt.internal.compiler.ast.IfStatement;
import org.eclipse.jdt.internal.compiler.ast.ImportReference;
import org.eclipse.jdt.internal.compiler.ast.Initializer;
import org.eclipse.jdt.internal.compiler.ast.InstanceOfExpression;
import org.eclipse.jdt.internal.compiler.ast.IntLiteral;
import org.eclipse.jdt.internal.compiler.ast.Javadoc;
import org.eclipse.jdt.internal.compiler.ast.JavadocAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.JavadocArgumentExpression;
import org.eclipse.jdt.internal.compiler.ast.JavadocArrayQualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocArraySingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocFieldReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocImplicitTypeReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocMessageSend;
import org.eclipse.jdt.internal.compiler.ast.JavadocQualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.JavadocSingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.JavadocSingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.LabeledStatement;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.LongLiteral;
import org.eclipse.jdt.internal.compiler.ast.MarkerAnnotation;
import org.eclipse.jdt.internal.compiler.ast.MemberValuePair;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.NormalAnnotation;
import org.eclipse.jdt.internal.compiler.ast.NullLiteral;
import org.eclipse.jdt.internal.compiler.ast.OR_OR_Expression;
import org.eclipse.jdt.internal.compiler.ast.ParameterizedQualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.ParameterizedSingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ast.PrefixExpression;
import org.eclipse.jdt.internal.compiler.ast.QualifiedAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedSuperReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedThisReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.ReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.SingleMemberAnnotation;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.StringLiteral;
import org.eclipse.jdt.internal.compiler.ast.StringLiteralConcatenation;
import org.eclipse.jdt.internal.compiler.ast.SuperReference;
import org.eclipse.jdt.internal.compiler.ast.SwitchStatement;
import org.eclipse.jdt.internal.compiler.ast.SynchronizedStatement;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.eclipse.jdt.internal.compiler.ast.ThrowStatement;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.ast.TryStatement;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeParameter;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;
import org.eclipse.jdt.internal.compiler.ast.WhileStatement;
import org.eclipse.jdt.internal.compiler.ast.Wildcard;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.ast.JmlArrayQualifiedTypeReference;
import org.jmlspecs.jml4.ast.JmlArrayReference;
import org.jmlspecs.jml4.ast.JmlArrayTypeReference;
import org.jmlspecs.jml4.ast.JmlAssertStatement;
import org.jmlspecs.jml4.ast.JmlAssignment;
import org.jmlspecs.jml4.ast.JmlAssumeStatement;
import org.jmlspecs.jml4.ast.JmlCastExpression;
import org.jmlspecs.jml4.ast.JmlCastExpressionWithoutType;
import org.jmlspecs.jml4.ast.JmlClause;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlEnsuresClause;
import org.jmlspecs.jml4.ast.JmlFieldDeclaration;
import org.jmlspecs.jml4.ast.JmlFieldReference;
import org.jmlspecs.jml4.ast.JmlLocalDeclaration;
import org.jmlspecs.jml4.ast.JmlLoopAnnotations;
import org.jmlspecs.jml4.ast.JmlLoopInvariant;
import org.jmlspecs.jml4.ast.JmlLoopVariant;
import org.jmlspecs.jml4.ast.JmlMessageSend;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodSpecification;
import org.jmlspecs.jml4.ast.JmlOldExpression;
import org.jmlspecs.jml4.ast.JmlParameterizedQualifiedTypeReference;
import org.jmlspecs.jml4.ast.JmlParameterizedSingleTypeReference;
import org.jmlspecs.jml4.ast.JmlQualifiedNameReference;
import org.jmlspecs.jml4.ast.JmlQualifiedTypeReference;
import org.jmlspecs.jml4.ast.JmlQuantifiedExpression;
import org.jmlspecs.jml4.ast.JmlRequiresClause;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlReturnStatement;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;
import org.jmlspecs.jml4.ast.JmlSingleTypeReference;
import org.jmlspecs.jml4.ast.JmlWhileStatement;
import org.jmlspecs.jml4.ast.JmlWildcard;
import org.jmlspecs.jml4.util.Logger;

public class TraceAstVisitor extends ASTVisitor {
	public void acceptProblem(IProblem problem) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			AllocationExpression allocationExpression,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			AnnotationMethodDeclaration annotationTypeDeclaration,
			ClassScope classScope) {
		Logger.printlnWithTrace(0, this.toString());
	}	
	public void endVisit(Argument argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Argument argument,ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ArrayAllocationExpression arrayAllocationExpression,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ArrayInitializer arrayInitializer, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ArrayReference arrayReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ArrayTypeReference arrayTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ArrayTypeReference arrayTypeReference, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(AssertStatement assertStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Assignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(BinaryExpression binaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Block block, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(BreakStatement breakStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(CaseStatement caseStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(CastExpression castExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(CharLiteral charLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ClassLiteralAccess classLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Clinit clinit, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			CompilationUnitDeclaration compilationUnitDeclaration,
			CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(CompoundAssignment compoundAssignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ConditionalExpression conditionalExpression,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ConstructorDeclaration constructorDeclaration,
			ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ContinueStatement continueStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(DoStatement doStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(DoubleLiteral doubleLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(EmptyStatement emptyStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(EqualExpression equalExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ExplicitConstructorCall explicitConstructor,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			ExtendedStringLiteral extendedStringLiteral,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(FalseLiteral falseLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(FieldReference fieldReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(FieldReference fieldReference, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(FloatLiteral floatLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ForeachStatement forStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ForStatement forStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(IfStatement ifStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(ImportReference importRef, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Initializer initializer, MethodScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(
			InstanceOfExpression instanceOfExpression,
			BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(IntLiteral intLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Javadoc javadoc, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(Javadoc javadoc, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocAllocationExpression expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocAllocationExpression expression, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArgumentExpression expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArgumentExpression expression, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArrayQualifiedTypeReference typeRef, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArrayQualifiedTypeReference typeRef, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArraySingleTypeReference typeRef, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocArraySingleTypeReference typeRef, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocFieldReference fieldRef, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocFieldReference fieldRef, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocImplicitTypeReference implicitTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocImplicitTypeReference implicitTypeReference, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocMessageSend messageSend, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocMessageSend messageSend, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocQualifiedTypeReference typeRef, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocQualifiedTypeReference typeRef, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocReturnStatement statement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocReturnStatement statement, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocSingleNameReference argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocSingleNameReference argument, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocSingleTypeReference typeRef, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(JavadocSingleTypeReference typeRef, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(LabeledStatement labeledStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(LocalDeclaration localDeclaration, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public void endVisit(LongLiteral longLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	/**
	 * @param annotation
	 * @param scope
	 * @since 3.1
	 */
	 public void endVisit(MarkerAnnotation annotation, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	/**
	 * @param pair
	 * @param scope
	 */
	 public void endVisit(MemberValuePair pair, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(MessageSend messageSend, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(MethodDeclaration methodDeclaration, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(StringLiteralConcatenation literal, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 /**
	  * @param annotation
	  * @param scope
	  * @since 3.1
	  */
	 public void endVisit(NormalAnnotation annotation, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(NullLiteral nullLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(PostfixExpression postfixExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(PrefixExpression prefixExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedAllocationExpression qualifiedAllocationExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedNameReference qualifiedNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedNameReference qualifiedNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedSuperReference qualifiedSuperReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedSuperReference qualifiedSuperReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedThisReference qualifiedThisReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedThisReference qualifiedThisReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedTypeReference qualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 QualifiedTypeReference qualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ReturnStatement returnStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 /**
	  * @param annotation
	  * @param scope
	  * @since 3.1
	  */
	 public void endVisit(SingleMemberAnnotation annotation, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 SingleNameReference singleNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 SingleNameReference singleNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 SingleTypeReference singleTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 SingleTypeReference singleTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(StringLiteral stringLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(SuperReference superReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(SwitchStatement switchStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 SynchronizedStatement synchronizedStatement,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ThisReference thisReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ThisReference thisReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(ThrowStatement throwStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(TrueLiteral trueLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(TryStatement tryStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 TypeDeclaration localTypeDeclaration,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }	
	 public void endVisit(
			 TypeDeclaration memberTypeDeclaration,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 TypeDeclaration typeDeclaration,
			 CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(TypeParameter typeParameter, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(TypeParameter typeParameter, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(UnaryExpression unaryExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(WhileStatement whileStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(Wildcard wildcard, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(Wildcard wildcard, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(
			 AllocationExpression allocationExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 AnnotationMethodDeclaration annotationTypeDeclaration,
			 ClassScope classScope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }	
	 public boolean visit(Argument argument, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Argument argument, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ArrayAllocationExpression arrayAllocationExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ArrayInitializer arrayInitializer, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ArrayReference arrayReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ArrayTypeReference arrayTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ArrayTypeReference arrayTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(AssertStatement assertStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Assignment assignment, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(BinaryExpression binaryExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Block block, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(BreakStatement breakStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(CaseStatement caseStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(CastExpression castExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(CharLiteral charLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ClassLiteralAccess classLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Clinit clinit, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 CompilationUnitDeclaration compilationUnitDeclaration,
			 CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(CompoundAssignment compoundAssignment, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ConditionalExpression conditionalExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ConstructorDeclaration constructorDeclaration,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ContinueStatement continueStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(DoStatement doStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(DoubleLiteral doubleLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(EmptyStatement emptyStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(EqualExpression equalExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ExplicitConstructorCall explicitConstructor,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 ExtendedStringLiteral extendedStringLiteral,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(FalseLiteral falseLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(FieldReference fieldReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(FieldReference fieldReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(FloatLiteral floatLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ForeachStatement forStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ForStatement forStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(IfStatement ifStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ImportReference importRef, CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Initializer initializer, MethodScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 InstanceOfExpression instanceOfExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(IntLiteral intLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Javadoc javadoc, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Javadoc javadoc, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocAllocationExpression expression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocAllocationExpression expression, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArgumentExpression expression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArgumentExpression expression, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArrayQualifiedTypeReference typeRef, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArrayQualifiedTypeReference typeRef, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArraySingleTypeReference typeRef, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocArraySingleTypeReference typeRef, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocFieldReference fieldRef, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocFieldReference fieldRef, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocImplicitTypeReference implicitTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocImplicitTypeReference implicitTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocMessageSend messageSend, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocMessageSend messageSend, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocQualifiedTypeReference typeRef, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocQualifiedTypeReference typeRef, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocReturnStatement statement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocReturnStatement statement, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocSingleNameReference argument, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocSingleNameReference argument, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocSingleTypeReference typeRef, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JavadocSingleTypeReference typeRef, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(LabeledStatement labeledStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(LocalDeclaration localDeclaration, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(LongLiteral longLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 /**
	  * @param annotation
	  * @param scope
	  * @since 3.1
	  */
	 public boolean visit(MarkerAnnotation annotation, BlockScope scope) {
		 return false;
	 }
	 /**
	  * @param pair
	  * @param scope
	  * @since 3.1
	  */
	 public boolean visit(MemberValuePair pair, BlockScope scope) {
		 return false;
	 }
	 public boolean visit(MessageSend messageSend, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 StringLiteralConcatenation literal,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 /**
	  * @param annotation
	  * @param scope
	  * @since 3.1
	  */
	 public boolean visit(NormalAnnotation annotation, BlockScope scope) {
		 return false;
	 }
	 public boolean visit(NullLiteral nullLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(PostfixExpression postfixExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(PrefixExpression prefixExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedAllocationExpression qualifiedAllocationExpression,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedNameReference qualifiedNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedNameReference qualifiedNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedSuperReference qualifiedSuperReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedSuperReference qualifiedSuperReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedThisReference qualifiedThisReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedThisReference qualifiedThisReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedTypeReference qualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 QualifiedTypeReference qualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ReturnStatement returnStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 /**
	  * @param annotation
	  * @param scope
	  * @since 3.1
	  */
	 public boolean visit(SingleMemberAnnotation annotation, BlockScope scope) {
		 return false;
	 }
	 public boolean visit(
			 SingleNameReference singleNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 SingleNameReference singleNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 SingleTypeReference singleTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 SingleTypeReference singleTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(StringLiteral stringLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(SuperReference superReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(SwitchStatement switchStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 SynchronizedStatement synchronizedStatement,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ThisReference thisReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ThisReference thisReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(ThrowStatement throwStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(TrueLiteral trueLiteral, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(TryStatement tryStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 TypeDeclaration localTypeDeclaration,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 TypeDeclaration memberTypeDeclaration,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }	
	 public boolean visit(
			 TypeDeclaration typeDeclaration,
			 CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(TypeParameter typeParameter, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(TypeParameter typeParameter, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(UnaryExpression unaryExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(WhileStatement whileStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Wildcard wildcard, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(Wildcard wildcard, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }


	 // <jml-start="jml-ast"/>
	 public void endVisit(
			 JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlArrayReference arrayReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlArrayTypeReference arrayTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(JmlArrayTypeReference arrayTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlAssertStatement assertStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlAssumeStatement assertStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlAssignment assignment, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlCastExpression castExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlCastExpressionWithoutType castExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlCompilationUnitDeclaration compilationUnitDeclaration,
			 CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlConstructorDeclaration constructorDeclaration,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlEnsuresClause ensuresClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlFieldDeclaration fieldDeclaration, MethodScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlFieldReference fieldReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(JmlFieldReference fieldReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlLocalDeclaration localDeclaration, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlMessageSend messageSend, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlQualifiedNameReference qualifiedNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 JmlQualifiedNameReference qualifiedNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlQualifiedTypeReference qualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 JmlQualifiedTypeReference qualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlRequiresClause requiresClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlResultReference resultReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlReturnStatement returnStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlSingleNameReference singleNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 JmlSingleNameReference singleNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(
			 JmlSingleTypeReference singleTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(
			 JmlSingleTypeReference singleTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 public void endVisit(JmlWildcard wildcard, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public void endVisit(JmlWildcard wildcard, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(
			 JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlArrayReference arrayReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlArrayTypeReference arrayTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlArrayTypeReference arrayTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlAssertStatement assertStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlAssignment assignment, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlAssumeStatement assertStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlCastExpression castExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlCastExpressionWithoutType castExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlCompilationUnitDeclaration compilationUnitDeclaration,
			 CompilationUnitScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlConstructorDeclaration constructorDeclaration,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlEnsuresClause ensuresClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlFieldDeclaration fieldDeclaration, MethodScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlFieldReference fieldReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlFieldReference fieldReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlLocalDeclaration localDeclaration, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlMessageSend messageSend, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlQualifiedNameReference qualifiedNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 JmlQualifiedNameReference qualifiedNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlQualifiedTypeReference qualifiedTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 JmlQualifiedTypeReference qualifiedTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlRequiresClause requiresClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlResultReference resultReference, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlReturnStatement returnStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlSingleNameReference singleNameReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 JmlSingleNameReference singleNameReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(
			 JmlSingleTypeReference singleTypeReference,
			 BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(
			 JmlSingleTypeReference singleTypeReference,
			 ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }

	 public boolean visit(JmlWildcard wildcard, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlWildcard wildcard, ClassScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public boolean visit(JmlWhileStatement whileStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlWhileStatement whileStatement, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(JmlLoopAnnotations jmlLoopAnnotations, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlLoopAnnotations jmlLoopAnnotations, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(JmlLoopInvariant jmlLoopInvariant, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlLoopInvariant jmlLoopInvariant, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(JmlLoopVariant jmlLoopVariant, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlLoopVariant jmlLoopVariant, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(JmlQuantifiedExpression expr, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlQuantifiedExpression expr, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 
	 public boolean visit(JmlMethodSpecification jmlMethodSpecification,
			 ClassScope classScope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlMethodSpecification jmlMethodSpecification,
			 ClassScope classScope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	 public boolean visit(JmlOldExpression jmlOldExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString()); return false;
	 }
	 public void endVisit(JmlOldExpression jmlOldExpression, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());		
	 }
	 public boolean visit(JmlClause jmlClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());return false;
	 }
	 public void endVisit(JmlClause jmlClause, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }

	 // <jml-end="jml-ast"/>

}