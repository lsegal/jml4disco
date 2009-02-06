package org.jmlspecs.jml4.esc.gc;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssert;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssignment;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssume;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleBlock;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleGoto;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleHavoc;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleProgram;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleSequence;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleAssignable;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleOperator;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimplePostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleQuantifier;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleThisReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBlock;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredGoto;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredHavoc;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredIfStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignment;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredPostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredThisReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class DesugaringVisitor {
	
	public DesugaringVisitor() {/*empty*/}

	public SimpleProgram visit(SugaredProgram sugaredProgram) {
		SugaredBlock[] sugaredBlocks = sugaredProgram.blocks;
		SimpleBlock[] block = new SimpleBlock[sugaredBlocks.length];
		for (int i = 0; i < sugaredBlocks.length; i++) {
			block[i] = sugaredBlocks[i].accept(this);
		}
		return new SimpleProgram(block, sugaredProgram.startName, sugaredProgram.methodIndicator);
	}

	public SimpleBlock visit(SugaredBlock sugared) {
		SimpleStatement simples = sugared.stmt.accept(this);
		return new SimpleBlock(sugared.blockId, simples, sugared.gotos);
	}

	public SimpleStatement visit(SugaredSequence sugaredSequence) {
		SimpleStatement stmt1 = sugaredSequence.stmt1.accept(this);
		SimpleStatement stmt2 = sugaredSequence.stmt2().accept(this);
		return new SimpleSequence(stmt1, stmt2);
	}

	public SimpleStatement visit(SugaredAssert sugaredAssert) {
		SimpleExpression expr = sugaredAssert.pred.accept(this);
		return new SimpleAssert(expr, sugaredAssert.kind, sugaredAssert.sourceStart);
	}

	public SimpleStatement visit(SugaredAssume sugaredAssume) {
		SimpleExpression expr = sugaredAssume.pred.accept(this);
		return new SimpleAssume(expr, sugaredAssume.sourceStart);
	}

	public SimpleExpression visit(SugaredAssignment sugaredAssignment) {
		SimpleExpression lhs =  sugaredAssignment.lhs.accept(this);
		Utils.assertTrue(lhs instanceof SimpleAssignable, "'"+lhs+"' is not an SugaredAssignable but a '"+lhs.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		SimpleExpression expr = sugaredAssignment.expr.accept(this);
		return new SimpleAssignment((SimpleAssignable)lhs, expr, sugaredAssignment.sourceStart, sugaredAssignment.sourceEnd);
	}

	public SimpleStatement visit(SugaredVarDecl var) {
		return new SimpleVarDecl(var.name, var.pos, var.type, var.sourceStart);
	}

	public SimpleExpression visit(SugaredBooleanConstant bool) {
		return new SimpleBooleanConstant(bool.value, bool.sourceStart, bool.sourceEnd);
	}

	public SimpleExpression visit(SugaredIntegerConstant intConst) {
		return new SimpleIntegerConstant(intConst.value, intConst.sourceStart, intConst.sourceEnd);
	}

	public SimpleExpression visit(SugaredVariable var) {
		return new SimpleVariable(var.name, var.pos, var.type, var.sourceStart, var.sourceEnd, var.isStaticField);
	}

	public SimpleExpression visit(SugaredNotExpression notExpr) {
		SimpleExpression expr = notExpr.expr.accept(this);
		return new SimpleNotExpression(expr, notExpr.sourceStart, notExpr.sourceEnd);
	}

	public SimpleExpression visit(SugaredBinaryExpression binExpr) {
		SimpleExpression left = binExpr.left.accept(this);
		SimpleExpression right = binExpr.right.accept(this);
		SimpleOperator operator;
		TypeBinding type;
		if (binExpr.operator == SugaredOperator.AND) {
			operator = SimpleOperator.AND;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.OR) {
			operator = SimpleOperator.OR;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.EQUALS) {
			operator = SimpleOperator.EQUALS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.NOT_EQUALS) {
			operator = SimpleOperator.NOT_EQUALS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.GREATER) {
			operator = SimpleOperator.GREATER;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.GREATER_EQUALS) {
			operator = SimpleOperator.GREATER_EQUALS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.LESS) {
			operator = SimpleOperator.LESS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.LESS_EQUALS) {
			operator = SimpleOperator.LESS_EQUALS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.PLUS) {
			operator = SimpleOperator.PLUS;
			type = left.type;
		} else if (binExpr.operator == SugaredOperator.MINUS) {
			operator = SimpleOperator.MINUS;
			type = left.type;
		} else if (binExpr.operator == SugaredOperator.TIMES) {
			operator = SimpleOperator.TIMES;
			type = left.type;
		} else if (binExpr.operator == SugaredOperator.DIVIDE) {
			operator = SimpleOperator.DIVIDE;
			type = left.type;
		} else if (binExpr.operator == SugaredOperator.REMAINDER) {
			operator = SimpleOperator.REMAINDER;
			type = left.type;
		} else if (binExpr.operator == SugaredOperator.IMPLIES) {
			operator = SimpleOperator.IMPLIES;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.REV_IMPLIES) {
			operator = SimpleOperator.REV_IMPLIES;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.EQUIV) {
			operator = SimpleOperator.EQUIV;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SugaredOperator.NOT_EQUIV) {
			operator = SimpleOperator.NOT_EQUIV;
			type = TypeBinding.BOOLEAN;
		} else {
			operator = null;
			type = null;
			Utils.assertTrue(false, "operator (" + binExpr + ") not translated correctly"); //$NON-NLS-1$//$NON-NLS-2$
		}
		return new SimpleBinaryExpression(operator, left, right, type, binExpr.sourceStart, binExpr.sourceEnd);
	}

	public SimpleExpression visit(SugaredConditionalExpression condExpr) {
		SimpleExpression condition = condExpr.condition.accept(this);
		SimpleExpression valueIfTrue = condExpr.valueIfTrue.accept(this);
		SimpleExpression valueIfFalse = condExpr.valueIfFalse.accept(this);
		return new SimpleConditionalExpression(condition, valueIfTrue, valueIfFalse, condExpr.type, condExpr.sourceStart, condExpr.sourceEnd);
	}

	public SimpleStatement visit(SugaredIfStatement sugaredIfStatement) {
		throw new RuntimeException("shouldn't be trying to desugar an if..."); //$NON-NLS-1$
	}

	public SimpleStatement visit(SugaredWhileStatement sugaredWhileStatement) {
		throw new RuntimeException("shouldn't be trying to desugar a while..."); //$NON-NLS-1$
	}
	public SimpleStatement visit(SugaredContinueStatement sugaredContinueStatement) {
		throw new RuntimeException("shouldn't be trying to desugar a continue..."); //$NON-NLS-1$
	}
	public SimpleStatement visit(SugaredBreakStatement sugaredBreakStatement) {
		throw new RuntimeException("shouldn't be trying to desugar a break..."); //$NON-NLS-1$
	}
	public SimpleStatement visit(SugaredReturnStatement sugaredReturn) {
		throw new RuntimeException("shouldn't be trying to desugar a return..."); //$NON-NLS-1$
	}
	public SimpleStatement visit(SugaredPrecondition sugaredPrecondition) {
		throw new RuntimeException("shouldn't be trying to desugar a precondition..."); //$NON-NLS-1$
	}
	public SimpleStatement visit(SugaredPostcondition sugaredPostcondition) {
		throw new RuntimeException("shouldn't be trying to desugar a postcondition..."); //$NON-NLS-1$
	}

	public SimpleStatement visit(SugaredGoto sugaredGoto) {
		return new SimpleGoto(sugaredGoto.gotos);
	}

	public SimpleExpression visit(SugaredPostfixExpression post) {
		SimpleExpression lhsExpr = post.lhs.accept(this);
		Utils.assertTrue(lhsExpr instanceof SimpleAssignable, "varExpr isn't a SimpleVariable but a "+lhsExpr.getClass().getName()); //$NON-NLS-1$
		SimpleAssignable lhs = (SimpleAssignable)lhsExpr;
		SimpleOperator operator = (post.operator == SugaredOperator.PLUS)
								?  SimpleOperator.PLUS
								:  SimpleOperator.MINUS;
		return new SimplePostfixExpression(lhs, operator, post.sourceStart, post.sourceEnd);
	}

	public SimpleStatement visit(SugaredHavoc sugaredHavoc) {
		SimpleExpression varExpr = sugaredHavoc.var.accept(this);
		Utils.assertTrue(varExpr instanceof SimpleVariable, "varExpr isn't a SimpleVariable but a "+varExpr.getClass().getName()); //$NON-NLS-1$
		SimpleVariable var = (SimpleVariable)varExpr;
		return new SimpleHavoc(var, sugaredHavoc.sourceStart);
	}

	public SimpleExpression visit(SugaredQuantifiedExpression quantExpr) {
		SimpleQuantifier quantifier = new SimpleQuantifier(quantExpr.quantifier.lexeme, quantExpr.quantifier.type);
		SimpleExpression range = quantExpr.range.accept(this);
		SimpleExpression body = quantExpr.body.accept(this);
		int length = quantExpr.boundVariables.length;
		SimpleVarDecl[] boundVariables = new SimpleVarDecl[length]; 
		for (int i = 0; i < length; i++) {
			SugaredVarDecl boundVariable = quantExpr.boundVariables[i];
			SimpleStatement result = boundVariable.accept(this);
			Utils.assertTrue(result instanceof SimpleVarDecl, "result is a '" + result.getClass() + "', expecting a SimpleVarDecl");  //$NON-NLS-1$//$NON-NLS-2$
			boundVariables[i] = (SimpleVarDecl)result;
		}
		return new SimpleQuantifiedExpression(quantifier, range, body, boundVariables, quantExpr.type, quantExpr.sourceStart, quantExpr.sourceEnd);
	}

	public SimpleExpression visit(SugaredOldExpression oldExpr) {
		SimpleExpression expr = oldExpr.expr.accept(this);
		return new SimpleOldExpression(expr, oldExpr.type, oldExpr.sourceStart, oldExpr.sourceEnd);
	}

	public SimpleExpression visit(SugaredMessageSend msgSend) {
		SimpleExpression receiver = msgSend.receiver == null
								  ? null
								  : msgSend.receiver.accept(this);
		String selector = msgSend.selector;
		TypeBinding type = msgSend.type;
		int length = msgSend.formalParams.length;
		SimpleVarDecl[] formalParams = new SimpleVarDecl[length];
		SimpleExpression[] actualParams = new SimpleExpression[length];
		for (int i = 0; i < actualParams.length; i++) {
			SimpleStatement formal = msgSend.formalParams[i].accept(this);
			Utils.assertTrue(formal instanceof SimpleVarDecl, "formal isn't a SimpleVarDecl"); //$NON-NLS-1$
			formalParams[i] = (SimpleVarDecl) formal;
			actualParams[i] = msgSend.actualParams[i].accept(this);
		}
		SimpleExpression pre = msgSend.pre.accept(this);
		SimpleExpression post = msgSend.post.accept(this);
		int count = msgSend.countForLabels;
		return new SimpleMessageSend(count, receiver, selector, formalParams, actualParams, type, pre, post, msgSend.sourceStart, msgSend.sourceEnd);
	}

	public SimpleExpression visit(SugaredThisReference thisRef) {
		return new SimpleThisReference(thisRef.type, thisRef.sourceStart, thisRef.sourceEnd);
	}

	public SimpleExpression visit(SugaredSuperReference superRef) {
		return new SimpleSuperReference(superRef.type, superRef.sourceStart, superRef.sourceEnd);
	}

	public SimpleExpression visit(SugaredFieldReference fieldRef) {
		SimpleExpression receiver = fieldRef.receiver.accept(this);
		return new SimpleFieldReference(receiver, fieldRef.field, fieldRef.declaringClass, fieldRef.type, fieldRef.sourceStart, fieldRef.sourceEnd);
	}

	public SimpleExpression visit(SugaredArrayReference arrayRef) {
		SimpleExpression receiver = arrayRef.receiver.accept(this);
		SimpleExpression position = arrayRef.position.accept(this);
		SimpleArrayReference result = new SimpleArrayReference(receiver, position, arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
		return result;
	}

	public SimpleExpression visit(SugaredArrayAllocationExpression arrayAlloc) {
		int length = arrayAlloc.dims.length;
		SimpleExpression[] dims = new SimpleExpression[length];
		for (int i = 0; i < dims.length; i++) {
			dims[i] = arrayAlloc.dims[i].accept(this);
		}
		return new SimpleArrayAllocationExpression(arrayAlloc.ids, dims, arrayAlloc.type, arrayAlloc.sourceStart, arrayAlloc.sourceEnd);
	}
}
