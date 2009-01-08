/**
 * 
 */
package org.jmlspecs.eclipse.jdt.internal.esc2;

import org.eclipse.jdt.core.compiler.IProblem;
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
// TODO import org.jmlspecs.jml4.ast.JmlAstVisitor;
import org.jmlspecs.jml4.ast.JmlCastExpression;
import org.jmlspecs.jml4.ast.JmlCastExpressionWithoutType;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlEnsuresClause;
import org.jmlspecs.jml4.ast.JmlFieldDeclaration;
import org.jmlspecs.jml4.ast.JmlFieldReference;
import org.jmlspecs.jml4.ast.JmlLocalDeclaration;
import org.jmlspecs.jml4.ast.JmlMessageSend;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlParameterizedQualifiedTypeReference;
import org.jmlspecs.jml4.ast.JmlParameterizedSingleTypeReference;
import org.jmlspecs.jml4.ast.JmlQualifiedNameReference;
import org.jmlspecs.jml4.ast.JmlQualifiedTypeReference;
import org.jmlspecs.jml4.ast.JmlRequiresClause;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlReturnStatement;
import org.jmlspecs.jml4.ast.JmlSingleNameReference;
import org.jmlspecs.jml4.ast.JmlSingleTypeReference;
import org.jmlspecs.jml4.ast.JmlWildcard;

/**
 * @author karabot
 * @deprecated because it is very unlikely that we will try to map between JML4 and ESC/Java2 ASTs.
 */
public class PrintVisitor { // TODO extends JmlAstVisitor {
	public void acceptProblem(IProblem problem) {
		// do nothing by default
		System.out.println("PrintVisitor: " + problem); //$NON-NLS-1$
	}
	public boolean visit(
			AllocationExpression allocationExpression,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + allocationExpression.getClass() + " ==> " + allocationExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		System.out.println("PrintVisitor: " + and_and_Expression.getClass() + " ==> " + and_and_Expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			AnnotationMethodDeclaration annotationTypeDeclaration,
			ClassScope classScope) {
		System.out.println("PrintVisitor: " + annotationTypeDeclaration.getClass() + " ==> " + annotationTypeDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}	
	public boolean visit(Argument argument, BlockScope scope) {
		System.out.println("PrintVisitor: " + argument.getClass() + " ==> " + argument + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Argument argument, ClassScope scope) {
		System.out.println("PrintVisitor: " + argument.getClass() + " ==> " + argument + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ArrayAllocationExpression arrayAllocationExpression,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayAllocationExpression.getClass() + " ==> " + arrayAllocationExpression  + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ArrayInitializer arrayInitializer, BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayInitializer.getClass() + " ==> " + arrayInitializer + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayQualifiedTypeReference.getClass() + " ==> " + arrayQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ArrayQualifiedTypeReference arrayQualifiedTypeReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + arrayQualifiedTypeReference.getClass() + " ==> " + arrayQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ArrayReference arrayReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayReference.getClass() + " ==> " + arrayReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ArrayTypeReference arrayTypeReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayTypeReference.getClass() + " ==> " + arrayTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ArrayTypeReference arrayTypeReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + arrayTypeReference.getClass() + " ==> " + arrayTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(AssertStatement assertStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + assertStatement.getClass() + " ==> " + assertStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Assignment assignment, BlockScope scope) {
		System.out.println("PrintVisitor: " + assignment.getClass() + " ==> " + assignment + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(BinaryExpression binaryExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + binaryExpression.getClass() + " ==> " + binaryExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Block block, BlockScope scope) {
		System.out.println("PrintVisitor: " + block.getClass() + " ==> " + block + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(BreakStatement breakStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + breakStatement.getClass() + " ==> " + breakStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(CaseStatement caseStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + caseStatement.getClass() + " ==> " + caseStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(CastExpression castExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + castExpression.getClass() + " ==> " + castExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(CharLiteral charLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + charLiteral.getClass() + " ==> " + charLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ClassLiteralAccess classLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + classLiteral.getClass() + " ==> " + classLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Clinit clinit, ClassScope scope) {
		System.out.println("PrintVisitor: " + clinit.getClass() + " ==> " + clinit + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			CompilationUnitDeclaration compilationUnitDeclaration,
			CompilationUnitScope scope) {
		System.out.println("PrintVisitor: " + compilationUnitDeclaration.getClass() + " ==> " + compilationUnitDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(CompoundAssignment compoundAssignment, BlockScope scope) {
		System.out.println("PrintVisitor: " + compoundAssignment.getClass() + " ==> " + compoundAssignment + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ConditionalExpression conditionalExpression,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + conditionalExpression.getClass() + " ==> " + conditionalExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ConstructorDeclaration constructorDeclaration,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + constructorDeclaration.getClass() + " ==> " + constructorDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ContinueStatement continueStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + continueStatement.getClass() + " ==> " + continueStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(DoStatement doStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + doStatement.getClass() + " ==> " + doStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(DoubleLiteral doubleLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + doubleLiteral.getClass() + " ==> " + doubleLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(EmptyStatement emptyStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + emptyStatement.getClass() + " ==> " + emptyStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(EqualExpression equalExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + equalExpression.getClass() + " ==> " + equalExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ExplicitConstructorCall explicitConstructor,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + explicitConstructor.getClass() + " ==> " + explicitConstructor + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			ExtendedStringLiteral extendedStringLiteral,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + extendedStringLiteral.getClass() + " ==> " + extendedStringLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(FalseLiteral falseLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + falseLiteral.getClass() + " ==> " + falseLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		System.out.println("PrintVisitor: " + fieldDeclaration.getClass() + " ==> " + fieldDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(FieldReference fieldReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + fieldReference.getClass() + " ==> " + fieldReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(FieldReference fieldReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + fieldReference.getClass() + " ==> " + fieldReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(FloatLiteral floatLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + floatLiteral.getClass() + " ==> " + floatLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ForeachStatement forStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + forStatement.getClass() + " ==> " + forStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ForStatement forStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + forStatement.getClass() + " ==> " + forStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(IfStatement ifStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + ifStatement.getClass() + " ==> " + ifStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ImportReference importRef, CompilationUnitScope scope) {
		System.out.println("PrintVisitor: " + importRef.getClass() + " ==> " + importRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Initializer initializer, MethodScope scope) {
		System.out.println("PrintVisitor: " + initializer.getClass() + " ==> " + initializer + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			InstanceOfExpression instanceOfExpression,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + instanceOfExpression.getClass() + " ==> " + instanceOfExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(IntLiteral intLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + intLiteral.getClass() + " ==> " + intLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Javadoc javadoc, BlockScope scope) {
		System.out.println("PrintVisitor: " + javadoc.getClass() + " ==> " + javadoc + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Javadoc javadoc, ClassScope scope) {
		System.out.println("PrintVisitor: " + javadoc.getClass() + " ==> " + javadoc + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocAllocationExpression expression, BlockScope scope) {
		System.out.println("PrintVisitor: " + expression.getClass() + " ==> " + expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocAllocationExpression expression, ClassScope scope) {
		System.out.println("PrintVisitor: " + expression.getClass() + " ==> " + expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArgumentExpression expression, BlockScope scope) {
		System.out.println("PrintVisitor: " + expression.getClass() + " ==> " + expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArgumentExpression expression, ClassScope scope) {
		System.out.println("PrintVisitor: " + expression.getClass() + " ==> " + expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArrayQualifiedTypeReference typeRef, BlockScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArrayQualifiedTypeReference typeRef, ClassScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArraySingleTypeReference typeRef, BlockScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocArraySingleTypeReference typeRef, ClassScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocFieldReference fieldRef, BlockScope scope) {
		System.out.println("PrintVisitor: " + fieldRef.getClass() + " ==> " + fieldRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocFieldReference fieldRef, ClassScope scope) {
		System.out.println("PrintVisitor: " + fieldRef.getClass() + " ==> " + fieldRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocImplicitTypeReference implicitTypeReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + implicitTypeReference.getClass() + " ==> " + implicitTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocImplicitTypeReference implicitTypeReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + implicitTypeReference.getClass() + " ==> " + implicitTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocMessageSend messageSend, BlockScope scope) {
		System.out.println("PrintVisitor: " + messageSend.getClass() + " ==> " + messageSend + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocMessageSend messageSend, ClassScope scope) {
		System.out.println("PrintVisitor: " + messageSend.getClass() + " ==> " + messageSend + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocQualifiedTypeReference typeRef, BlockScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocQualifiedTypeReference typeRef, ClassScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocReturnStatement statement, BlockScope scope) {
		System.out.println("PrintVisitor: " + statement.getClass() + " ==> " + statement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocReturnStatement statement, ClassScope scope) {
		System.out.println("PrintVisitor: " + statement.getClass() + " ==> " + statement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocSingleNameReference argument, BlockScope scope) {
		System.out.println("PrintVisitor: " + argument.getClass() + " ==> " + argument + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocSingleNameReference argument, ClassScope scope) {
		System.out.println("PrintVisitor: " + argument.getClass() + " ==> " + argument + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocSingleTypeReference typeRef, BlockScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(JavadocSingleTypeReference typeRef, ClassScope scope) {
		System.out.println("PrintVisitor: " + typeRef.getClass() + " ==> " + typeRef + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(LabeledStatement labeledStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + labeledStatement.getClass() + " ==> " + labeledStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(LocalDeclaration localDeclaration, BlockScope scope) {
		System.out.println("PrintVisitor: " + localDeclaration.getClass() + " ==> " + localDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(LongLiteral longLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + longLiteral.getClass() + " ==> " + longLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	/**
	 * @param annotation
	 * @param scope
	 * @since 3.1
	 */
	public boolean visit(MarkerAnnotation annotation, BlockScope scope) {
		System.out.println("PrintVisitor: " + annotation.getClass() + " ==> " + annotation + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true;
	}
	/**
	 * @param pair
	 * @param scope
	 * @since 3.1
	 */
	public boolean visit(MemberValuePair pair, BlockScope scope) {
		System.out.println("PrintVisitor: " + pair.getClass() + " ==> " + pair + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true;
	}
	public boolean visit(MessageSend messageSend, BlockScope scope) {
		System.out.println("PrintVisitor: " + messageSend.getClass() + " ==> " + messageSend + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		System.out.println("PrintVisitor: " + methodDeclaration.getClass() + " ==> " + methodDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			StringLiteralConcatenation literal,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + literal.getClass() + " ==> " + literal + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	/**
	 * @param annotation
	 * @param scope
	 * @since 3.1
	 */
	public boolean visit(NormalAnnotation annotation, BlockScope scope) {
		System.out.println("PrintVisitor: " + annotation.getClass() + " ==> " + annotation + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true;
	}
	public boolean visit(NullLiteral nullLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + nullLiteral.getClass() + " ==> " + nullLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		System.out.println("PrintVisitor: " + or_or_Expression.getClass() + " ==> " + or_or_Expression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + parameterizedQualifiedTypeReference.getClass() + " ==> " + parameterizedQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + parameterizedQualifiedTypeReference.getClass() + " ==> " + parameterizedQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + parameterizedSingleTypeReference.getClass() + " ==> " + parameterizedSingleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + parameterizedSingleTypeReference.getClass() + " ==> " + parameterizedSingleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(PostfixExpression postfixExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + postfixExpression.getClass() + " ==> " + postfixExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(PrefixExpression prefixExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + prefixExpression.getClass() + " ==> " + prefixExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedAllocationExpression qualifiedAllocationExpression,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + qualifiedAllocationExpression.getClass() + " ==> " + qualifiedAllocationExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedNameReference qualifiedNameReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + qualifiedNameReference.getClass() + " ==> " + qualifiedNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedNameReference qualifiedNameReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + qualifiedNameReference.getClass() + " ==> " + qualifiedNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedSuperReference qualifiedSuperReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + qualifiedSuperReference.getClass() + " ==> " + qualifiedSuperReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedSuperReference qualifiedSuperReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + qualifiedSuperReference.getClass() + " ==> " + qualifiedSuperReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedThisReference qualifiedThisReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + qualifiedThisReference.getClass() + " ==> " + qualifiedThisReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedThisReference qualifiedThisReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + qualifiedThisReference.getClass() + " ==> " + qualifiedThisReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedTypeReference qualifiedTypeReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + qualifiedTypeReference.getClass() + " ==> " + qualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			QualifiedTypeReference qualifiedTypeReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + qualifiedTypeReference.getClass() + " ==> " + qualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ReturnStatement returnStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + returnStatement.getClass() + " ==> " + returnStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	/**
	 * @param annotation
	 * @param scope
	 * @since 3.1
	 */
	public boolean visit(SingleMemberAnnotation annotation, BlockScope scope) {
		System.out.println("PrintVisitor: " + annotation.getClass() + " ==> " + annotation + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true;
	}
	public boolean visit(
			SingleNameReference singleNameReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + singleNameReference.getClass() + " ==> " + singleNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			SingleNameReference singleNameReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + singleNameReference.getClass() + " ==> " + singleNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			SingleTypeReference singleTypeReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + singleTypeReference.getClass() + " ==> " + singleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			SingleTypeReference singleTypeReference,
			ClassScope scope) {
		System.out.println("PrintVisitor: " + singleTypeReference.getClass() + " ==> " + singleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(StringLiteral stringLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + stringLiteral.getClass() + " ==> " + stringLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(SuperReference superReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + superReference.getClass() + " ==> " + superReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(SwitchStatement switchStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + switchStatement.getClass() + " ==> " + switchStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			SynchronizedStatement synchronizedStatement,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + synchronizedStatement.getClass() + " ==> " + synchronizedStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ThisReference thisReference, BlockScope scope) {
		System.out.println("PrintVisitor: " + thisReference.getClass() + " ==> " + thisReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ThisReference thisReference, ClassScope scope) {
		System.out.println("PrintVisitor: " + thisReference.getClass() + " ==> " + thisReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(ThrowStatement throwStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + throwStatement.getClass() + " ==> " + throwStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(TrueLiteral trueLiteral, BlockScope scope) {
		System.out.println("PrintVisitor: " + trueLiteral.getClass() + " ==> " + trueLiteral + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(TryStatement tryStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + tryStatement.getClass() + " ==> " + tryStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			TypeDeclaration localTypeDeclaration,
			BlockScope scope) {
		System.out.println("PrintVisitor: local: " + localTypeDeclaration.getClass() + " ==> " + localTypeDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(
			TypeDeclaration memberTypeDeclaration,
			ClassScope scope) {
		System.out.println("PrintVisitor: member: " + memberTypeDeclaration.getClass() + " ==> " + memberTypeDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}	
	public boolean visit(
			TypeDeclaration typeDeclaration,
			CompilationUnitScope scope) {
		System.out.println("PrintVisitor: " + typeDeclaration.getClass() + " ==> " + typeDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(TypeParameter typeParameter, BlockScope scope) {
		System.out.println("PrintVisitor: " + typeParameter.getClass() + " ==> " + typeParameter + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(TypeParameter typeParameter, ClassScope scope) {
		System.out.println("PrintVisitor: " + typeParameter.getClass() + " ==> " + typeParameter + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(UnaryExpression unaryExpression, BlockScope scope) {
		System.out.println("PrintVisitor: " + unaryExpression.getClass() + " ==> " + unaryExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(WhileStatement whileStatement, BlockScope scope) {
		System.out.println("PrintVisitor: " + whileStatement.getClass() + " ==> " + whileStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Wildcard wildcard, BlockScope scope) {
		System.out.println("PrintVisitor: " + wildcard.getClass() + " ==> " + wildcard + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}
	public boolean visit(Wildcard wildcard, ClassScope scope) {
		System.out.println("PrintVisitor: " + wildcard.getClass() + " ==> " + wildcard + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return true; // do nothing by default, keep traversing
	}

	
	public boolean visit(
			JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			BlockScope scope) {
		System.out.println("PrintVisitor: " + arrayQualifiedTypeReference.getClass() + " ==> " + arrayQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(
			JmlArrayQualifiedTypeReference arrayQualifiedTypeReference,
			ClassScope scope) {
			System.out.println("PrintVisitor: " + arrayQualifiedTypeReference.getClass() + " ==> " + arrayQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlArrayReference arrayReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + arrayReference.getClass() + " ==> " + arrayReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlArrayTypeReference arrayTypeReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + arrayTypeReference.getClass() + " ==> " + arrayTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(JmlArrayTypeReference arrayTypeReference, ClassScope scope) {
			System.out.println("PrintVisitor: " + arrayTypeReference.getClass() + " ==> " + arrayTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlAssertStatement assertStatement, BlockScope scope) {
			System.out.println("PrintVisitor: " + assertStatement.getClass() + " ==> " + assertStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlAssignment assignment, BlockScope scope) {
			System.out.println("PrintVisitor: " + assignment.getClass() + " ==> " + assignment + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlCastExpression castExpression, BlockScope scope) {
			System.out.println("PrintVisitor: " + castExpression.getClass() + " ==> " + castExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		
		public boolean visit(JmlCastExpressionWithoutType castExpression, BlockScope scope) {
			System.out.println("PrintVisitor: " + castExpression.getClass() + " ==> " + castExpression + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		
		public boolean visit(
				JmlCompilationUnitDeclaration compilationUnitDeclaration,
				CompilationUnitScope scope) {
			System.out.println("PrintVisitor: " + compilationUnitDeclaration.getClass() + " ==> " + compilationUnitDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}
		
		public boolean visit(
				JmlConstructorDeclaration constructorDeclaration,
				ClassScope scope) {
			System.out.println("PrintVisitor: " + constructorDeclaration.getClass() + " ==> " + constructorDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}

		public boolean visit(JmlEnsuresClause ensuresClause, BlockScope scope) {
			System.out.println("PrintVisitor: " + ensuresClause.getClass() + " ==> " + ensuresClause + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}
		
		public boolean visit(JmlFieldDeclaration fieldDeclaration, MethodScope scope) {
			System.out.println("PrintVisitor: " + fieldDeclaration.getClass() + " ==> " + fieldDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlFieldReference fieldReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + fieldReference.getClass() + " ==> " + fieldReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(JmlFieldReference fieldReference, ClassScope scope) {
			System.out.println("PrintVisitor: " + fieldReference.getClass() + " ==> " + fieldReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		
		public boolean visit(JmlLocalDeclaration localDeclaration, BlockScope scope) {
			System.out.println("PrintVisitor: " + localDeclaration.getClass() + " ==> " + localDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlMessageSend messageSend, BlockScope scope) {
			System.out.println("PrintVisitor: " + messageSend.getClass() + " ==> " + messageSend + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
			System.out.println("PrintVisitor: " + methodDeclaration.getClass() + " ==> " + methodDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + parameterizedQualifiedTypeReference.getClass() + " ==> " + parameterizedQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(JmlParameterizedQualifiedTypeReference parameterizedQualifiedTypeReference, ClassScope scope) {
			System.out.println("PrintVisitor: " + parameterizedQualifiedTypeReference.getClass() + " ==> " + parameterizedQualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + parameterizedSingleTypeReference.getClass() + " ==> " + parameterizedSingleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(JmlParameterizedSingleTypeReference parameterizedSingleTypeReference, ClassScope scope) {
			System.out.println("PrintVisitor: " + parameterizedSingleTypeReference.getClass() + " ==> " + parameterizedSingleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(
				JmlQualifiedNameReference qualifiedNameReference,
				BlockScope scope) {
			System.out.println("PrintVisitor: " + qualifiedNameReference.getClass() + " ==> " + qualifiedNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(
				JmlQualifiedNameReference qualifiedNameReference,
				ClassScope scope) {
			System.out.println("PrintVisitor: " + qualifiedNameReference.getClass() + " ==> " + qualifiedNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(
	    		JmlQualifiedTypeReference qualifiedTypeReference,
	    		BlockScope scope) {
			System.out.println("PrintVisitor: " + qualifiedTypeReference.getClass() + " ==> " + qualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}
		public boolean visit(
	    		JmlQualifiedTypeReference qualifiedTypeReference,
	    		ClassScope scope) {
			System.out.println("PrintVisitor: " + qualifiedTypeReference.getClass() + " ==> " + qualifiedTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlRequiresClause requiresClause, BlockScope scope) {
			System.out.println("PrintVisitor: " + requiresClause.getClass() + " ==> " + requiresClause + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}

		public boolean visit(JmlResultReference resultReference, BlockScope scope) {
			System.out.println("PrintVisitor: " + resultReference.getClass() + " ==> " + resultReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(JmlReturnStatement returnStatement, BlockScope scope) {
			System.out.println("PrintVisitor: " + returnStatement.getClass() + " ==> " + returnStatement + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return true; // do nothing by default, keep traversing
		}

		public boolean visit(
				JmlSingleNameReference singleNameReference,
				BlockScope scope) {
			System.out.println("PrintVisitor: " + singleNameReference.getClass() + " ==> " + singleNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}
			public boolean visit(
					JmlSingleNameReference singleNameReference,
					ClassScope scope) {
				System.out.println("PrintVisitor: " + singleNameReference.getClass() + " ==> " + singleNameReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}

			public boolean visit(
		    		JmlSingleTypeReference singleTypeReference,
		    		BlockScope scope) {
				System.out.println("PrintVisitor: " + singleTypeReference.getClass() + " ==> " + singleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}
			public boolean visit(
		    		JmlSingleTypeReference singleTypeReference,
		    		ClassScope scope) {
				System.out.println("PrintVisitor: " + singleTypeReference.getClass() + " ==> " + singleTypeReference + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}

			public boolean visit(JmlWildcard wildcard, BlockScope scope) {
				System.out.println("PrintVisitor: " + wildcard.getClass() + " ==> " + wildcard + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}
			public boolean visit(JmlWildcard wildcard, ClassScope scope) {
				System.out.println("PrintVisitor: " + wildcard.getClass() + " ==> " + wildcard + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				return true; // do nothing by default, keep traversing
			}

	
}
