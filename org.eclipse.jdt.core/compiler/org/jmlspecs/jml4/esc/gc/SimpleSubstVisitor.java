package org.jmlspecs.jml4.esc.gc;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssignment;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimplePostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleQuantifier;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleThisReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleSubstVisitor implements SimpleExprVisitor {

	private final Map/*<Pair, Pair>*/ subst = new HashMap/*<Pair, Pair>*/();
	private String result;
	public SimpleSubstVisitor(String result, SimpleVarDecl[] bindings, SimpleVarDecl[] formalParams) {
		Utils.assertTrue(bindings.length == formalParams.length, "sizes don't match"); //$NON-NLS-1$
		for (int i = 0; i < bindings.length; i++) {
			Pair binding = new Pair(bindings[i].name, bindings[i].pos);
			Pair formal  = new Pair(formalParams[i].name, formalParams[i].pos);
			this.subst.put(formal, binding);
		}
		this.result = result;
	}

	public SimpleExpression visit(SimpleAssignment expr) {
		Utils.assertTrue(false, "shouldn't be called"); //$NON-NLS-1$
		return null;
	}

	public SimpleExpression visit(SimpleBinaryExpression expr) {
		SimpleExpression left  = expr.left.accept(this);
		SimpleExpression right = expr.right.accept(this);
		return left == expr.left && right == expr.right
			 ? expr
			 : new SimpleBinaryExpression(expr.operator, left, right, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleBooleanConstant expr) {
		return expr;
	}

	public SimpleExpression visit(SimpleConditionalExpression expr) {
		SimpleExpression cond = expr.condition.accept(this);
		SimpleExpression ifTrue = expr.valueIfTrue.accept(this);
		SimpleExpression ifFalse = expr.valueIfFalse.accept(this);
		return cond == expr.condition && ifTrue == expr.valueIfTrue && ifFalse == expr.valueIfFalse
		     ? expr
		     : new SimpleConditionalExpression(cond, ifTrue, ifFalse, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleIntegerConstant expr) {
		return expr;
	}

	public SimpleExpression visit(SimpleMessageSend expr) {
		SimpleExpression receiver = expr.receiver.accept(this);
		String selector = expr.selector;
		SimpleVarDecl[] formalParams = expr.formalParams;
		int length = expr.actualParams.length;
		SimpleExpression[] actualParams = new SimpleExpression[length];
		for (int i = 0; i < length; i++) {
			SimpleExpression actualParam = expr.actualParams[i].accept(this);
			Utils.assertTrue(actualParam instanceof SimpleVariable
					      || actualParam instanceof SimpleOldExpression, "'"+actualParam.toString()+"' isn't a SimpleVariable but a '"+actualParam.getClass().getName()+"'"); //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
			actualParams[i] = actualParam;
		}
		SimpleExpression pre = expr.pre.accept(this);
		String prevResult = this.result;
		this.result = null;
		SimpleExpression post = expr.post.accept(this);
		this.result = prevResult;
		int countForLabels = expr.countForLabels;
		TypeBinding type = expr.type;
		int sourceStart = expr.sourceStart;
		int sourceEnd = expr.sourceEnd;
		return new SimpleMessageSend(countForLabels, receiver, selector, formalParams, actualParams, type, pre, post, sourceStart, sourceEnd);
	}

	public SimpleExpression visit(SimpleOldExpression expr) {
		SimpleExpression oldExpr = expr.expr.accept(this);
		return oldExpr == expr.expr
			 ? expr
			 : new SimpleOldExpression(oldExpr, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimplePostfixExpression expr) {
		Utils.assertTrue(false, "shouldn't be called"); //$NON-NLS-1$
		return null;
	}

	public SimpleExpression visit(SimpleQuantifiedExpression expr) {
		SimpleQuantifier quantifier = expr.quantifier;
		SimpleExpression range = expr.range.accept(this);
		SimpleExpression body = expr.body.accept(this);
		SimpleVarDecl[] boundVariables = expr.boundVariables;
		return range == expr.range && body == expr.body 
		 	 ? expr
		 	 : new SimpleQuantifiedExpression(quantifier, range, body, boundVariables, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleNotExpression expr) {
		SimpleExpression notExpr = expr.expr.accept(this);
		return notExpr == expr.expr
			 ? expr
			 : new SimpleNotExpression(notExpr, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleVariable expr) {
		Pair replacement = (Pair) subst.get(new Pair(expr.name, expr.pos));
		SimpleExpression result;
		if (replacement == null) {
			if (this.result != null && expr.name.equals("return")) {//$NON-NLS-1$
				result = new SimpleVariable(this.result, 0, expr.type, expr.sourceStart, expr.sourceEnd, expr.isStaticField);
			} else {
				result = expr;
			}
		} else {
			String name = replacement.name;
			int pos = replacement.pos;
			result = new SimpleVariable(name, pos, expr.type, expr.sourceStart, expr.sourceEnd, expr.isStaticField);
		}
		return result;
	}

	public SimpleExpression visit(SimpleFieldReference expr) {
		SimpleExpression receiver = expr.receiver.accept(this);
		return receiver == expr.receiver
		     ? expr
		     : new SimpleFieldReference(receiver, expr.field, expr.declaringClass, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleSuperReference superRef) {
		return superRef;
	}

	public SimpleExpression visit(SimpleThisReference thisRef) {
		return thisRef;
	}

	public SimpleExpression visit(SimpleArrayReference expr) {
		SimpleExpression receiver = expr.receiver.accept(this);
		SimpleExpression position = expr.receiver.accept(this);
		return receiver == expr.receiver && position == expr.position
	         ? expr
	         : new SimpleArrayReference(receiver, position, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SimpleExpression visit(SimpleArrayAllocationExpression arrayAlloc) {
		int length = arrayAlloc.dims.length;
		SimpleExpression[] dims = new SimpleExpression[length];
		for (int i = 0; i < dims.length; i++) {
			dims[i] = arrayAlloc.dims[i].accept(this);
		}
		return new SimpleArrayAllocationExpression(arrayAlloc.ids, dims, arrayAlloc.type, arrayAlloc.sourceStart, arrayAlloc.sourceEnd);
	}

	public String toString() {
		return this.result + " " + this.subst.toString(); //$NON-NLS-1$
	}

	private static class Pair {
		
		public final String name;
		public final int pos;

		public Pair(String name, int pos) {
			this.name = name;
			this.pos = pos;
		}
		
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + name.hashCode();
			result = prime * result + pos;
			return result;
		}
		
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null || getClass() != obj.getClass())
				return false;
			Pair other = (Pair) obj;
			return pos == other.pos && name.equals(other.name);
		}
		
		public String toString() {
			return "("+this.name+"@"+this.pos+")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
		}
		
	}

}
