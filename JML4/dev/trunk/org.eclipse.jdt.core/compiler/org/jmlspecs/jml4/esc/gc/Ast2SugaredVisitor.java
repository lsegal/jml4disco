package org.jmlspecs.jml4.esc.gc;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.AND_AND_Expression;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.AllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.ArrayAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.AssertStatement;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.BreakStatement;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.ConditionalExpression;
import org.eclipse.jdt.internal.compiler.ast.ContinueStatement;
import org.eclipse.jdt.internal.compiler.ast.DoStatement;
import org.eclipse.jdt.internal.compiler.ast.EmptyStatement;
import org.eclipse.jdt.internal.compiler.ast.EqualExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FalseLiteral;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.ForStatement;
import org.eclipse.jdt.internal.compiler.ast.IfStatement;
import org.eclipse.jdt.internal.compiler.ast.IntLiteral;
import org.eclipse.jdt.internal.compiler.ast.LabeledStatement;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.OR_OR_Expression;
import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.eclipse.jdt.internal.compiler.ast.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ast.PrefixExpression;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.ReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.ast.SwitchStatement;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;
import org.eclipse.jdt.internal.compiler.ast.WhileStatement;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlAbstractMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlAssertStatement;
import org.jmlspecs.jml4.ast.JmlAssumeStatement;
import org.jmlspecs.jml4.ast.JmlLoopInvariant;
import org.jmlspecs.jml4.ast.JmlLoopVariant;
import org.jmlspecs.jml4.ast.JmlMessageSend;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodSpecification;
import org.jmlspecs.jml4.ast.JmlQuantifiedExpression;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlWhileStatement;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredIfStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredLoopAnnotations;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignable;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignment;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMethodSpecification;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredPostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredQuantifier;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredThisReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;
import org.jmlspecs.jml4.esc.util.Counter;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.util.Logger;

public class Ast2SugaredVisitor extends ASTVisitor {

	private static final String RETURN = "return"; //$NON-NLS-1$
	private /*@nullable*/ SugaredStatement  stmt;
	private /*@nullable*/ SugaredExpression expr;
	private final List/*<SugaredExpression>*/ loopVariants = new ArrayList/*<SugaredExpression>*/();
	private final List/*<SugaredExpression>*/ loopInvariants = new ArrayList/*<SugaredExpression>*/();
	private final Stack/*<String>*/ continueLabels = new Stack/*<String>*/();
	private final Stack/*<String>*/ breakLabels = new Stack/*<String>*/();
	private final Counter counter = new Counter();
	private TypeBinding returnType;

	public Ast2SugaredVisitor(AbstractMethodDeclaration method) {
		this.returnType = method.binding.returnType;
	}
	
	public SugaredStatement getResult() {
		SugaredStatement result;
		result = (this.stmt == null 
				  ? (this.expr == null 
				     ? SugaredAssert.SKIP
				     : new SugaredExprStatement(this.expr))
				  : this.stmt);
		this.stmt = null;
		this.expr = null;
		return result;
	}

	public boolean visit(JmlAssumeStatement assumeStatement, BlockScope scope) {
		assumeStatement.assertExpression.traverse(this, scope);
		this.stmt = new SugaredAssume(this.expr, assumeStatement.sourceStart);
		this.expr = null;
		return false;
	}

	public boolean visit(JmlAssertStatement assertStatement, BlockScope scope) {
		assertStatement.assertExpression.traverse(this, scope);
		KindOfAssertion kind = KindOfAssertion.ASSERT;
		this.stmt = new SugaredAssert(this.expr, kind, assertStatement.sourceStart);
		this.expr = null;
		return false;
	}

	public boolean visit(AssertStatement assertStatement, BlockScope scope) {
		assertStatement.assertExpression.traverse(this, scope);
		KindOfAssertion kind = KindOfAssertion.ASSERT;
		this.stmt = new SugaredAssert(this.expr, kind, assertStatement.sourceStart);
		this.expr = null;
		return false;
	}

	public boolean visit(Assignment assignment, BlockScope scope) {
		assignment.lhs.traverse(this, scope);
		Utils.assertTrue(this.expr instanceof SugaredAssignable, "lhs should resolve to an assignable"); //$NON-NLS-1$
		SugaredAssignable lhs = (SugaredAssignable) this.expr;
		assignment.expression.traverse(this, scope);
		SugaredExpression rhs = this.expr;
		this.expr = new SugaredAssignment(lhs, rhs, assignment.sourceStart, rhs.sourceEnd);
		return false;
	}

	public boolean visit(CompoundAssignment assignment, BlockScope scope) {
		assignment.lhs.traverse(this, scope);
		Utils.assertTrue(this.expr instanceof SugaredAssignable, "lhs should resolve to an assignable"); //$NON-NLS-1$
		SugaredAssignable lhs = (SugaredAssignable) this.expr;
		assignment.expression.traverse(this, scope);
		SugaredExpression rhs = this.expr;
		//TODO: cast result of operation to type of lhs
		SugaredOperator operator = getOperatorFromId(assignment.operator);
		SugaredBinaryExpression newRhs = new SugaredBinaryExpression(operator, lhs, rhs, lhs.type, assignment.sourceStart, assignment.sourceEnd);
		this.expr = new SugaredAssignment(lhs, newRhs, assignment.sourceStart, assignment.sourceEnd);
		return false;
	}

	private SugaredOperator getOperatorFromId(int operatorId) {
		switch (operatorId) {
			case OperatorIds.AND       : return SugaredOperator.AND;
			case OperatorIds.OR        : return SugaredOperator.OR;
			case OperatorIds.PLUS      : return SugaredOperator.PLUS;
			case OperatorIds.MINUS     : return SugaredOperator.MINUS;
			case OperatorIds.MULTIPLY  : return SugaredOperator.TIMES;
			case OperatorIds.DIVIDE    : return SugaredOperator.DIVIDE;
			case OperatorIds.REMAINDER : return SugaredOperator.REMAINDER;
			case OperatorIds.JML_IMPLIES     : return SugaredOperator.IMPLIES;
			case OperatorIds.JML_REV_IMPLIES : return SugaredOperator.REV_IMPLIES;
			case OperatorIds.JML_EQUIV       : return SugaredOperator.EQUIV;
			case OperatorIds.JML_NOT_EQUIV   : return SugaredOperator.NOT_EQUIV;
			default : throw new RuntimeException("operator not supported"); //$NON-NLS-1$
		}
	}

	public boolean visit(PrefixExpression prefixExpr, BlockScope scope) {
		if (prefixExpr.lhs.resolvedType.isArrayType()) {
			// we don't handle arrays yet
			throw new RuntimeException("arrays not supported in visit(Assignment)"); //$NON-NLS-1$
		} else {
			prefixExpr.lhs.traverse(this, scope);
			if (! (this.expr instanceof SugaredAssignable)) throw new RuntimeException("lhs should resolve to an assignable"); //$NON-NLS-1$
			SugaredAssignable lhs = (SugaredAssignable) this.expr;
			SugaredExpression rhs = SugaredIntegerConstant.ONE;
			SugaredOperator operator = getOperatorFromId(prefixExpr.operator);
			SugaredBinaryExpression newRhs = new SugaredBinaryExpression(operator, lhs, rhs, lhs.type, prefixExpr.sourceStart, prefixExpr.sourceEnd);
			this.expr = new SugaredAssignment(lhs, newRhs, prefixExpr.sourceStart, prefixExpr.sourceEnd);
		}
		return false;
	}

	public boolean visit(PostfixExpression postfixExpr, BlockScope scope) {
		postfixExpr.lhs.traverse(this, scope);
		Utils.assertTrue(this.expr instanceof SugaredAssignable, "lhs should resolve to an assignable"); //$NON-NLS-1$
		SugaredAssignable lhs = (SugaredAssignable) this.expr;
		SugaredOperator operator = getOperatorFromId(postfixExpr.operator);
		this.expr = new SugaredPostfixExpression(lhs, operator, postfixExpr.sourceStart, postfixExpr.sourceEnd);
		return false;
	}

	public boolean visit(IntLiteral intConst, BlockScope scope) {
		this.expr = new SugaredIntegerConstant(intConst.value, intConst.sourceStart, intConst.sourceEnd);
		return false;
	}

	public boolean visit(FalseLiteral falseLiteral, BlockScope scope) {
		this.expr = new SugaredBooleanConstant(false, falseLiteral.sourceStart, falseLiteral.sourceEnd);
		return false;
	}

	public boolean visit(ArrayReference arrayReference, BlockScope scope) {
		arrayReference.receiver.traverse(this, scope);
		SugaredExpression receiver = this.expr;
		this.expr = null;
		arrayReference.position.traverse(this, scope);
		SugaredExpression position = this.expr;
		this.expr = null;
		SugaredArrayReference arrayRef = new SugaredArrayReference(receiver, position, arrayReference.resolvedType, arrayReference.sourceStart, arrayReference.sourceEnd);
		this.expr = arrayRef;
		return false;
	}

	public boolean visit(SingleNameReference var, BlockScope scope) {
		String name = new String(var.token);
		int pos = -1;
		LocalVariableBinding localVarBinding = var.localVariableBinding();
		if (localVarBinding != null) {
			pos = localVarBinding.declaration.sourceStart;
			this.expr = new SugaredVariable(name, pos, var.resolvedType, var.sourceStart, var.sourceEnd);
		} else {
			FieldBinding fieldBinding = var.fieldBinding();
			Utils.assertNotNull(fieldBinding, "'"+var.toString()+"' is neither a local nor a field"); //$NON-NLS-1$ //$NON-NLS-2$
			pos = fieldBinding.sourceField().sourceStart;
			SugaredThisReference thiz = SugaredThisReference.getImplicit(fieldBinding.declaringClass);
			String declaringClass = fieldBinding.declaringClass.debugName();
			if (fieldBinding.isStatic()) {
				this.expr = new SugaredVariable(name + declaringClass, 0, var.resolvedType, var.sourceStart, var.sourceEnd, true);
			} else {
				this.expr = new SugaredFieldReference(thiz, name, declaringClass, var.resolvedType, var.sourceStart, var.sourceEnd);
			}
		}
		Utils.assertTrue(pos >= 0, "pos is negative"); //$NON-NLS-1$
		return false;
	}

	public boolean visit(ThisReference thisReference, BlockScope scope) {
		this.expr = SugaredThisReference.getImplicit(thisReference.resolvedType);
		return false;
	}

	public boolean visit(QualifiedNameReference var, BlockScope scope) {
		SugaredExpression receiver = getReceiver(var);
		SugaredExpression fieldExpr = null;
		Utils.assertNotNull(var.otherBindings, "var.otherBindings is null"); //$NON-NLS-1$
		int length = var.otherBindings.length;
		Utils.assertTrue(length > 0, "there are no other bindings"); //$NON-NLS-1$
		for (int i=0; i<length; i++) {
			FieldBinding fieldBinding = var.otherBindings[i];
			ReferenceBinding declaringClass = fieldBinding.declaringClass;
			String declaringClassName = declaringClass == null 
			                          ? "<internal>" //$NON-NLS-1$
					                  : declaringClass.debugName();
			String fieldName = new String(var.tokens[var.indexOfFirstFieldBinding+i]);
			if (fieldBinding.isStatic()) {
				fieldExpr = new SugaredVariable(fieldName + declaringClassName, 0, fieldBinding.type, var.sourceStart, var.sourceEnd, true);
			} else {
				fieldExpr = new SugaredFieldReference(receiver, fieldName, declaringClassName, fieldBinding.type, var.sourceStart, var.sourceEnd);
			}
			receiver = fieldExpr;
        }
        Utils.assertNotNull(fieldExpr);
		this.expr = fieldExpr;
		return false;
	}

	private SugaredExpression getReceiver(QualifiedNameReference var) {
		SugaredExpression result;
		if (var.binding instanceof FieldBinding) {
			FieldBinding fieldBinding = (FieldBinding) var.binding;
			ReferenceBinding declaringClass = fieldBinding.declaringClass;
			String declaringClassName = declaringClass == null 
			                          ? "<internal>" //$NON-NLS-1$
					                  : declaringClass.debugName();
			String fieldName = getReceveiverName(var);
			if (fieldBinding.isStatic()) {
				result = new SugaredVariable(fieldName + declaringClassName, 0, fieldBinding.type, var.sourceStart, var.sourceEnd, true);
			} else {
		        SugaredExpression receiver = new SugaredThisReference(fieldBinding.declaringClass, 0, 0);
				result = new SugaredFieldReference(receiver, fieldName, declaringClassName, fieldBinding.type, var.sourceStart, var.sourceEnd);
			}
		} else if (var.binding instanceof LocalVariableBinding) {
			LocalVariableBinding localBinding = (LocalVariableBinding)var.binding;
			LocalDeclaration localDeclaration = localBinding.declaration;
			String name = new String(localDeclaration.name);
			int pos = localDeclaration.sourceStart;
			TypeBinding type = localBinding.type;
			Utils.assertNotNull(localDeclaration, "localDeclaration is null"); //$NON-NLS-1$
			result = new SugaredVariable(name, pos, type, localDeclaration.sourceStart, localDeclaration.sourceEnd);
		} else {
			Utils.assertTrue(false, "can't handle '" + var + "'"); //$NON-NLS-1$ //$NON-NLS-2$
			result = null;
		}
		return result;
	}

	private String getReceveiverName(QualifiedNameReference var) {
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < var.indexOfFirstFieldBinding; i++) {
			if (i>0)
				buffer.append('.');
			buffer.append(new String(var.tokens[i]));
		}
		String result = buffer.toString();
		return result;
	}

	public boolean visit(FieldReference fieldRef, BlockScope scope) {
		String field = new String(fieldRef.token);
		fieldRef.receiver.traverse(this, scope);
		SugaredExpression receiver = this.expr;
		String declaringClass = fieldRef.binding.declaringClass.debugName();
		TypeBinding type = fieldRef.binding.type;
		if (fieldRef.binding.isStatic()) {
			this.expr = new SugaredVariable(field + declaringClass, 0, type, fieldRef.sourceStart, fieldRef.sourceEnd);
		} else {
			this.expr = new SugaredFieldReference(receiver, field, declaringClass, type, fieldRef.sourceStart, fieldRef.sourceEnd);
		}
		return false;
	}

	public boolean visit(TrueLiteral trueLiteral, BlockScope scope) {
		this.expr = new SugaredBooleanConstant(true, trueLiteral.sourceStart, trueLiteral.sourceEnd);
		return false;
	}

	public boolean visit(UnaryExpression unaryExpression, BlockScope scope) {
		unaryExpression.expression.traverse(this, scope);
		int operatorId = (unaryExpression.bits & ASTNode.OperatorMASK) >> ASTNode.OperatorSHIFT;
		if (operatorId == OperatorIds.NOT) {
			this.expr = new SugaredNotExpression(this.expr, unaryExpression.sourceStart, unaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.PLUS) {
			// do nothing: this.expr is already set
		} else if (operatorId == OperatorIds.MINUS) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.MINUS, SugaredIntegerConstant.ZERO, this.expr, this.expr.type, unaryExpression.sourceStart, unaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.TWIDDLE) {
			// jls_15.15.5:  note that, in all cases, ~x equals (-x)-1.
			SugaredExpression left = new SugaredBinaryExpression(SugaredOperator.MINUS, SugaredIntegerConstant.ZERO, this.expr, this.expr.type, unaryExpression.sourceStart, unaryExpression.sourceEnd);
			this.expr = new SugaredBinaryExpression(SugaredOperator.MINUS, left, SugaredIntegerConstant.MINUS_ONE, this.expr.type, unaryExpression.sourceStart, unaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.JML_OLD
				|| operatorId == OperatorIds.JML_PRE) {
			this.expr = new SugaredOldExpression(this.expr, unaryExpression.sourceStart, unaryExpression.sourceEnd);
		} else {
			Logger.print("not implemented"); //$NON-NLS-1$
			this.expr = null;
		}
		return false;
	}

	public boolean visit(BinaryExpression binaryExpression, BlockScope scope) {
		binaryExpression.left.traverse(this, scope);
		SugaredExpression left = this.expr;
		this.expr = null;
		Utils.assertNotNull(left, "left is null"); //$NON-NLS-1$
		binaryExpression.right.traverse(this, scope);
		SugaredExpression right = this.expr;
		this.expr = null;
		Utils.assertNotNull(right, "right is null"); //$NON-NLS-1$
		int operatorId = (binaryExpression.bits & ASTNode.OperatorMASK) >> ASTNode.OperatorSHIFT;
		if (operatorId == OperatorIds.AND_AND) {
			this.expr = new SugaredConditionalExpression(left, right, new SugaredBooleanConstant(false, 0, 0), TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.OR_OR) {
			this.expr = new SugaredConditionalExpression(left, new SugaredBooleanConstant(true, 0, 0), right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.AND) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.AND, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.OR) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.OR, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.EQUAL_EQUAL) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.EQUALS, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.NOT_EQUAL) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.NOT_EQUALS, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.LESS) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.LESS, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.LESS_EQUAL) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.LESS_EQUALS, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.GREATER) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.GREATER, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.GREATER_EQUAL) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.GREATER_EQUALS, left, right, TypeBinding.BOOLEAN, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.PLUS) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.PLUS, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.MINUS) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.MINUS, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.MULTIPLY) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.TIMES, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.DIVIDE) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.DIVIDE, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.REMAINDER) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.REMAINDER, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.JML_IMPLIES) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.IMPLIES, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.JML_REV_IMPLIES) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.REV_IMPLIES, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.JML_EQUIV) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.EQUIV, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else if (operatorId == OperatorIds.JML_NOT_EQUIV) {
			this.expr = new SugaredBinaryExpression(SugaredOperator.NOT_EQUIV, left, right, left.type, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		} else {
			Logger.println(binaryExpression.toString() + " not supported by astExpr2cfgExpr.UnaryExpression"); //$NON-NLS-1$
			this.expr = new SugaredBooleanConstant(false, binaryExpression.sourceStart, binaryExpression.sourceEnd);
		}
		return false;
	}

	public boolean visit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		return visit((BinaryExpression) or_or_Expression, scope);
	}

	public boolean visit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		return visit((BinaryExpression) and_and_Expression, scope);
	}

	public boolean visit(EqualExpression eqExpr, BlockScope scope) {
		return visit((BinaryExpression) eqExpr, scope);
	}

	public boolean visit(ConditionalExpression condExpression, BlockScope scope) {
		condExpression.condition.traverse(this, scope);
		SugaredExpression condition = this.expr;
		condExpression.valueIfTrue.traverse(this, scope);
		SugaredExpression valueIfTrue = this.expr;
		condExpression.valueIfFalse.traverse(this, scope);
		SugaredExpression valueIfFalse = this.expr;
		this.expr = new SugaredConditionalExpression(condition, valueIfTrue, valueIfFalse, condExpression.resolvedType, condExpression.sourceStart, condExpression.sourceEnd);
		return false;
	}

	public boolean visit(LocalDeclaration localDeclaration, BlockScope scope) {
		int sourceStart = localDeclaration.sourceStart;
		int sourceEnd = localDeclaration.sourceEnd;
		String name = new String(localDeclaration.name);
        int pos = sourceStart;
		TypeBinding type = localDeclaration.binding.type;
		this.stmt = new SugaredVarDecl(name, pos, type, sourceStart);
		this.expr = null;

		Expression initialization = localDeclaration.initialization;
		if (initialization != null) {
			initialization.traverse(this, scope);
			SugaredExpression init = this.expr;
			SugaredVariable var = new SugaredVariable(name, pos, type, sourceStart, sourceEnd);
			Utils.assertNotNull(init);
			SugaredAssignment assignment = new SugaredAssignment(var, init, sourceStart, sourceEnd);
			SugaredExprStatement exprStmt = new SugaredExprStatement(assignment);
			this.stmt = new SugaredSequence(this.getResult(), exprStmt);
			this.expr = null;
		}

		return false;
	}

	public boolean visit(ArrayAllocationExpression arrayAlloc, BlockScope scope) {
		int length = arrayAlloc.dimensions.length;
		SugaredExpression[] dims = new SugaredExpression[length];
		int counts[] = new int[length];
		for (int i = 0; i < dims.length; i++) {
			if (arrayAlloc.dimensions[i] == null)
				this.expr = new SugaredIntegerConstant(-1, 0, 0);
			else
				arrayAlloc.dimensions[i].traverse(this, scope);
			dims[i] = this.expr;
			this.expr = null;
		}
		for (int i = 0; i < dims.length; i++) {
			counts[i] = this.counter.getAndIncCounter();
		}
		TypeBinding type = arrayAlloc.resolvedType;
		int sourceStart = arrayAlloc.sourceStart;
		int sourceEnd = arrayAlloc.sourceEnd;
		this.expr = new SugaredArrayAllocationExpression(counts, dims, type, sourceStart, sourceEnd);
		return false;
	}

	public boolean visit(IfStatement ifStatement, BlockScope scope) {
		ifStatement.condition.traverse(this, scope);
		SugaredExpression condition = this.expr;
		ifStatement.thenStatement.traverse(this, scope);
		SugaredStatement thenStatement = this.getResult();
		SugaredStatement elseStatement;
		if (ifStatement.elseStatement == null) {
			elseStatement = SugaredAssert.SKIP;
		} else {
			ifStatement.elseStatement.traverse(this, scope);
			elseStatement = this.getResult();
		}
		Utils.assertNotNull(elseStatement, "elseStatement is null"); //$NON-NLS-1$
		this.stmt = new SugaredIfStatement(condition, thenStatement, elseStatement, ifStatement.sourceStart);
		this.expr = null;
		return false;
	}

	public boolean visit(JmlWhileStatement whileStatement, BlockScope scope) {
		String label = "jmlWhile$" + this.counter.getAndIncCounter(); //$NON-NLS-1$
		this.visit(whileStatement, scope, label);
		return false;
	}

	public boolean visit(WhileStatement whileStatement, BlockScope scope) {
		String label = "while$" + this.counter.getAndIncCounter(); //$NON-NLS-1$
		this.visit(whileStatement, scope, label);
		return false;
	}

	public boolean visit(LabeledStatement labeledStatement, BlockScope scope) {
		String label = new String(labeledStatement.label)+"$"+this.counter.getAndIncCounter(); //$NON-NLS-1$
		Statement labeled = labeledStatement.statement;
		if (labeled instanceof WhileStatement) {
			this.visit((WhileStatement)labeled, scope, label);
		} else if (labeled instanceof ForStatement) {
			Logger.print("implement me"); //$NON-NLS-1$
		} else if (labeled instanceof DoStatement) {
			Logger.print("implement me"); //$NON-NLS-1$
		} else if (labeled instanceof SwitchStatement) {
			Logger.print("implement me"); //$NON-NLS-1$
		} else {
			labeled.traverse(this, scope);
		}
		return false;
	}

	// whileStatement may or may not be a JmlWhileStatement
	private void visit(WhileStatement whileStatement, BlockScope scope, String label) {
		whileStatement.condition.traverse(this, scope);
		SugaredExpression condition = this.expr;
		if (whileStatement instanceof JmlWhileStatement) {
		   ((JmlWhileStatement)whileStatement).annotations.traverse(this, scope);
		} else {
			Utils.assertTrue(this.loopInvariants.size() == 0, "leftover loop invariants..."); //$NON-NLS-1$
			Utils.assertTrue(this.loopVariants.size() == 0, "leftover loop variants..."); //$NON-NLS-1$
		}
		SugaredLoopAnnotations annotations = this.gatherLoopAnnotations();

		String breakTargetName = label + "$break"; //$NON-NLS-1$
		String headerName      = label + "$header"; //$NON-NLS-1$
		this.breakLabels.push(breakTargetName);
		this.continueLabels.push(headerName);
		whileStatement.action.traverse(this, scope);

		String lbl = (String)this.breakLabels.pop();
		Utils.assertTrue(lbl.equals(breakTargetName), "break label not as expected"); //$NON-NLS-1$
		lbl = (String)this.continueLabels.pop();
		Utils.assertTrue(lbl.equals(headerName), "continue label not as expected"); //$NON-NLS-1$

		SugaredStatement action = this.getResult();
		this.stmt = new SugaredWhileStatement(label, condition, annotations, action, whileStatement.sourceStart);
		this.expr = null;
	}

	private SugaredLoopAnnotations gatherLoopAnnotations() {
		SugaredExpression[] variants   = (SugaredExpression[])this.loopVariants.toArray(SugaredExpression.EMPTY);
		SugaredExpression[] invariants = (SugaredExpression[])this.loopInvariants.toArray(SugaredExpression.EMPTY);
		SugaredLoopAnnotations result = new SugaredLoopAnnotations(invariants, variants);
		this.loopInvariants.clear();
		this.loopVariants.clear();
		return result;
	}

	public boolean visit(BreakStatement breakStatement, BlockScope scope) {
		String label = (breakStatement.label == null 
			     ? (String)this.breakLabels.peek() 
			     : new String(breakStatement.label));
		this.stmt = new SugaredBreakStatement(label, breakStatement.sourceStart);
		return false;
	}

	public boolean visit(ContinueStatement continueStatement, BlockScope scope) {
		String label = (continueStatement.label == null 
				     ? (String)this.continueLabels.peek() 
				     : new String(continueStatement.label));
		this.stmt = new SugaredContinueStatement(label, continueStatement.sourceStart);
		return false;
	}

	public boolean visit(JmlLoopInvariant jmlLoopInvariant, BlockScope scope) {
		jmlLoopInvariant.expr.traverse(this, scope);
		this.loopInvariants.add(this.expr);
		this.expr = null;
		return false;
	}

	public boolean visit(JmlLoopVariant jmlLoopVariant, BlockScope scope) {
		jmlLoopVariant.expr.traverse(this, scope);
		this.loopVariants.add(this.expr);
		this.expr = null;
		return false;
	}

	public boolean visit(Block block, BlockScope scope) {
		/*@nullable*/ Statement[] statements = block.statements;
		if (statements == null) {
			this.stmt = SugaredAssert.SKIP;
		} else {
			SugaredStatement[] sugared = new SugaredStatement[statements.length];
			for (int i = 0; i < statements.length; i++) {
				statements[i].traverse(this, scope);
				sugared[i] = this.getResult();
			}
			this.stmt = SugaredSequence.fold(sugared);
		}
		return false;
	}

	public boolean visit(EmptyStatement empty, BlockScope scope) {
		this.stmt = SugaredAssert.SKIP;
		return false;
	}

	public boolean visit(JmlQuantifiedExpression quantExpr, BlockScope scope) {
		SugaredQuantifier quantifier = new SugaredQuantifier(quantExpr.quantifier.lexeme, quantExpr.quantifier.type);
		quantExpr.range.traverse(this, scope);
		SugaredExpression range = this.expr;
		quantExpr.body.traverse(this, scope);
		SugaredExpression body = this.expr;
		int length = quantExpr.boundVariables.length;
		SugaredVarDecl[] boundVariables = new SugaredVarDecl[length]; 
		for (int i = 0; i < length; i++) {
			LocalDeclaration boundVariable = quantExpr.boundVariables[i];
			boundVariable.traverse(this, scope);
			SugaredStatement result = this.getResult();
			Utils.assertTrue(result instanceof SugaredVarDecl, "result is a '" + result.getClass() + "', expecting a SugaredVarDecl");  //$NON-NLS-1$//$NON-NLS-2$
			boundVariables[i] = (SugaredVarDecl) result;
		}
		this.expr = new SugaredQuantifiedExpression(quantifier, range, body, boundVariables, quantExpr.resolvedType, quantExpr.sourceStart, quantExpr.sourceEnd);
		return false;
	}

	public boolean visit(ReturnStatement retStmt, BlockScope scope) {
		TypeBinding type = this.returnType;
		SugaredExpression retExpr;
		if (retStmt.expression == null) {
			retExpr = null;
		} else {
			retStmt.expression.traverse(this, scope);
			retExpr = this.expr;
			this.expr = null;
		}
		this.stmt = new SugaredReturnStatement(retExpr, type, retStmt.sourceStart);
		return false;
	}

	public boolean visit(JmlResultReference resRef, BlockScope scope) {
		SugaredVariable retVar = new SugaredVariable(RETURN, 0, this.returnType, 0, 0);
		this.expr = retVar;
		return false;
	}

	public boolean visit(MessageSend messageSend, BlockScope scope) {
		Utils.assertTrue(messageSend instanceof JmlMessageSend, "messageSend isn't a JmlMessageSend"); //$NON-NLS-1$
		AbstractMethodDeclaration methodDecl = ((JmlMessageSend) messageSend).binding.methodDeclaration;
		Utils.assertTrue(methodDecl instanceof JmlMethodDeclaration, "methodDecl('"+new String(methodDecl.selector)+"') isn't a JmlMethodDeclaration"); //$NON-NLS-1$ //$NON-NLS-2$
		JmlMethodDeclaration jmlMethodDecl = (JmlMethodDeclaration) methodDecl;

		SugaredVarDecl[] formalParams = new SugaredVarDecl[messageSend.arguments.length];
		for (int i = 0; i < formalParams.length; i++) {
			Argument formal = methodDecl.arguments[i];
			String name = new String(formal.name);
			int pos = formal.sourceStart;
			TypeBinding type = formal.binding.type; 
			formalParams[i] = new SugaredVarDecl(name, pos, type, pos);
		}
		
		SugaredExpression[] actualParams = new SugaredExpression[messageSend.arguments.length];
		Utils.assertNotNull(messageSend.receiver, "messageSend.receiver is null"); //$NON-NLS-1$
		messageSend.receiver.traverse(this, scope);
		SugaredExpression receiver = this.expr;
		Utils.assertNotNull(receiver, "receiver is null"); //$NON-NLS-1$
		this.expr = null;
		String selector = new String(messageSend.selector);
		for (int i = 0; i < messageSend.arguments.length; i++) {
			messageSend.arguments[i].traverse(this, scope);
			actualParams[i] = this.expr;
			this.expr = null;
		}
		TypeBinding previousReturnType = this.returnType;
		TypeBinding type = messageSend.resolvedType;
		this.returnType = type;
		JmlMethodSpecification specification = jmlMethodDecl.specification;
		SugaredExpression pre;
		SugaredExpression post;
		if (specification == null) {
			pre  = SugaredBooleanConstant.TRUE;
			post = SugaredBooleanConstant.TRUE;
		} else {
			Expression exPre  = specification.getPrecondition();
			exPre.traverse(this, scope);
			pre = this.expr;
			this.expr = null;
			
			Expression exPost = specification.getPostcondition();
			exPost.traverse(this, scope);
			post = this.expr;
			this.expr = null;
		} 

		this.returnType = previousReturnType;
		
		int count = this.counter.getAndIncCounter();
		this.expr = new SugaredMessageSend(count, receiver, selector, formalParams, actualParams, type, pre, post, messageSend.sourceStart, messageSend.sourceEnd);
		return false;
	}

	public SugaredMethodSpecification getSpec(JmlAbstractMethodDeclaration method) {
		SugaredExpression prevExpr = this.expr;
		Utils.assertTrue(prevExpr == null, "prevExpr isn't null"); //$NON-NLS-1$
		BlockScope scope = null;
		JmlMethodSpecification spec = method.getSpecification();
		if (spec == null) {
			return SugaredMethodSpecification.DEFAULT;
		} else {
			Expression preExpr = spec.getPrecondition();
			preExpr.traverse(this, scope);
			SugaredExpression pre = this.expr;
			this.expr = null;
			Expression postExpr = spec.getPostcondition();
			postExpr.traverse(this, scope);
			SugaredExpression post = this.expr;
			this.expr = prevExpr;
			return new SugaredMethodSpecification(pre, post, null);
		}
	}

	public String toString() {
		return super.toString() + "[stmt = "+this.stmt+", expr = "+this.expr+"]";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
	}

	public SugaredExpression getInvariant(Expression invariant) {
		invariant.traverse(this, (BlockScope)null);
		SugaredExpression result = this.expr;
		this.expr = null;
		return result;
	}
	public boolean visit(AllocationExpression allocationExpression, BlockScope scope) {
		String name = allocationExpression.type.toString();
		TypeBinding type = allocationExpression.resolvedType;
		int sourceStart  = allocationExpression.sourceStart;
		int sourceEnd    = allocationExpression.sourceEnd;
		this.expr = new SugaredVariable(name, 0, type, sourceStart, sourceEnd);
		return true;
	}
}
