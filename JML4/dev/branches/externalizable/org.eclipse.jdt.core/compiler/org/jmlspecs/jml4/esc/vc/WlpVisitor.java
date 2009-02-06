package org.jmlspecs.jml4.esc.vc;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.CfgAssert;
import org.jmlspecs.jml4.esc.gc.lang.CfgAssume;
import org.jmlspecs.jml4.esc.gc.lang.CfgBlock;
import org.jmlspecs.jml4.esc.gc.lang.CfgGoto;
import org.jmlspecs.jml4.esc.gc.lang.CfgSequence;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatementBlock;
import org.jmlspecs.jml4.esc.gc.lang.CfgVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.GcProgram;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldStore;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgOperator;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgThisReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgVariable;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcAnd;
import org.jmlspecs.jml4.esc.vc.lang.VcArithExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcArrayAllocationExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcArrayReference;
import org.jmlspecs.jml4.esc.vc.lang.VcBooleanConstant;
import org.jmlspecs.jml4.esc.vc.lang.VcConditionalExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcFieldReference;
import org.jmlspecs.jml4.esc.vc.lang.VcFieldStore;
import org.jmlspecs.jml4.esc.vc.lang.VcIntegerConstant;
import org.jmlspecs.jml4.esc.vc.lang.VcLogicalExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcNot;
import org.jmlspecs.jml4.esc.vc.lang.VcOperator;
import org.jmlspecs.jml4.esc.vc.lang.VcOr;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;
import org.jmlspecs.jml4.esc.vc.lang.VcQuantifiedExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcQuantifier;
import org.jmlspecs.jml4.esc.vc.lang.VcRelativeExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcSuperReference;
import org.jmlspecs.jml4.esc.vc.lang.VcThisReference;
import org.jmlspecs.jml4.esc.vc.lang.VcVarDecl;
import org.jmlspecs.jml4.esc.vc.lang.VcVariable;

public class WlpVisitor {

	private static final String LENGTH = "length"; //$NON-NLS-1$
	private final List/*<VcFieldReference>*/ lengthRefs = new ArrayList();

	public VcProgram visit(GcProgram gcProgram) {
		int numBlocks = gcProgram.blocks.length;
		VC[] vcs = new VC[numBlocks];
		for (int i = 0; i < numBlocks; i++) {
			Utils.assertTrue(this.lengthRefs.isEmpty(), "lengthsRefs not empty ("+this.lengthRefs.toString()+")");  //$NON-NLS-1$//$NON-NLS-2$
			VC N = new VcBooleanConstant(true, 0, 0);
			CfgBlock block = gcProgram.blocks[i];
			VC wlp = block.accept(this, N);
			
			VC lengthImps = getLengthImps();
			if (lengthImps != null) {
				wlp = new VcLogicalExpression(VcOperator.IMPLIES, lengthImps, wlp, 0, 0);
			}

			String beqName = block.blockId;
			wlp.setName(beqName);
			vcs[i] = wlp;
		}
		return new VcProgram(vcs, gcProgram.startName, gcProgram.incarnations.toStringIntegerMap(), gcProgram.methodIndicator);
	}

	private /*nullable*/ VC getLengthImps() {
		VC result = null;
		Set/*<String>*/ seen = new HashSet/*<String>*/();
		if (! this.lengthRefs.isEmpty()) {
			for (Iterator iterator = this.lengthRefs.iterator(); iterator.hasNext();) {
				VcFieldReference lenRef = (VcFieldReference) iterator.next();
				if (! seen.contains(lenRef.toString())) {
					VcRelativeExpression geZero = new VcRelativeExpression(VcOperator.GREATER_EQUALS, lenRef, VcIntegerConstant.ZERO, 0, 0);
					result = (result == null)
					       ? (VC) geZero
					       : new VcLogicalExpression(VcOperator.IMPLIES, result, geZero, 0, 0);
					seen.add(lenRef.toString());
				}
			}
			this.lengthRefs.clear();
		}
		Utils.assertTrue(this.lengthRefs.isEmpty(), "lengthRefs not empty ("+this.lengthRefs+")"); //$NON-NLS-1$ //$NON-NLS-2$
		return result;
	}

	public VC visit(CfgBlock cfgBlock, VC N) {
		return cfgBlock.stmt().accept(this, N);
	}

	public VC visit(CfgAssert cfgAssert, VC N) {
		VC expr = cfgAssert.pred.accept(this);
		expr.setLabel(cfgAssert.kind, VC.NEGLBL, cfgAssert.sourceStart);
		VC result = new VcAnd(expr, N, cfgAssert.sourceStart, cfgAssert.pred.sourceEnd);
		if (cfgAssert.sourceStart != 0)
		   result.setLabel(cfgAssert.kind, VC.NEGLBL, cfgAssert.sourceStart);
		return result;
	}

	public VC visit(CfgAssume cfgAssume, VC N) {
		Utils.assertTrue(N.type.equals(TypeBinding.BOOLEAN), "N not a boolean but a '"+N.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(cfgAssume.pred.type.equals(TypeBinding.BOOLEAN), "cfgAssume.pred not a boolean but a '"+cfgAssume.pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		VC expr = cfgAssume.pred.accept(this);
		Utils.assertTrue(expr.type.equals(TypeBinding.BOOLEAN), "expr not a boolean but a '"+expr.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		VC result = new VcLogicalExpression(VcOperator.IMPLIES, expr, N, cfgAssume.sourceStart, cfgAssume.pred.sourceEnd);
		return result;
	}

	public VC visit(CfgSequence cfgSequence, VC N) {
		CfgStatement s = cfgSequence.stmt1;
		CfgStatement t = cfgSequence.stmt2;
		VC vcT = t.accept(this, N);
		VC result = s.accept(this, vcT);
		return result;
	}

	public VC visit(CfgStatementBlock cfgStatementBlock, VC N) {
		VC stmt = cfgStatementBlock.stmt.accept(this, N);
//		VC stmt = cfgStatementBlock.stmt.accept(this, VcBooleanConstant.TRUE);
		int length = cfgStatementBlock.boundVarDecls.length;
		VcVarDecl[] varDecls = new VcVarDecl[length];
		for (int i = 0; i < varDecls.length; i++) {
			VC vcVarDecl = this.visit(cfgStatementBlock.boundVarDecls[i]);
			Utils.assertTrue(vcVarDecl instanceof VcVarDecl, "vcVarDecl isn't a varDecl but a '"+vcVarDecl.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			varDecls[i] = (VcVarDecl) vcVarDecl;
		}
		VC block = new VcQuantifiedExpression(VcQuantifier.FORALL, varDecls, stmt);
//		VC result = new VcLogicalExpression(VcOperator.IMPLIES, block, N, 0, 0);
		VC result = block;
		return result;
	}

	public VC visit(CfgVarDecl cfgVarDecl) {
		int sourceStart = cfgVarDecl.sourceStart;
		int sourceEnd = sourceStart + cfgVarDecl.name.length() + cfgVarDecl.type.debugName().length() + 2;
		return new VcVarDecl(cfgVarDecl.name, cfgVarDecl.pos, cfgVarDecl.type, sourceStart, sourceEnd);
	}

    public VC visit(CfgQuantifiedExpression expr) {
		VcQuantifier quantifier = new VcQuantifier(expr.quantifier.lexeme, expr.quantifier.type);
		VC range = expr.range.accept(this);
		VC body = expr.body.accept(this);
		int length = expr.boundVariables.length;
		for (int i = 0; i < length; i++) {
			CfgVarDecl boundVariable = expr.boundVariables[i];
			VC result = boundVariable.accept(this, range);
			Utils.assertTrue(result.equals(range), "result isn't range");  //$NON-NLS-1$
		}
		return new VcQuantifiedExpression(quantifier, range, body, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public VC visit(CfgVariable var) {
		return new VcVariable(var.name, var.pos, var.type, var.incarnation(), var.sourceStart, var.sourceEnd);
	}

	public VC visit(CfgBooleanConstant bool) {
		return new VcBooleanConstant(bool.value, bool.sourceStart, bool.sourceEnd);
	}

	public VC visit(CfgIntegerConstant intConst) {
		return new VcIntegerConstant(intConst.value, intConst.sourceStart, intConst.sourceEnd);
	}

	public VC visit(CfgNotExpression notRef) {
		VC expr = notRef.expr.accept(this);
		return new VcNot(expr, notRef.sourceStart, notRef.sourceEnd);
	}

	public VC visit(CfgBinaryExpression binExpr) {
		VC left = binExpr.left.accept(this);
		VC right = binExpr.right.accept(this);
	    if (binExpr.operator == CfgOperator.AND)
	    	 return new VcAnd(left, right, binExpr.sourceStart, binExpr.sourceEnd);
		if (binExpr.operator == CfgOperator.OR)
			return new VcOr(left, right, binExpr.sourceStart, binExpr.sourceEnd);

		VcOperator operator = null;
	    if (binExpr.operator == CfgOperator.EQUALS) {        
			operator = VcOperator.EQUALS;
		} else if (binExpr.operator == CfgOperator.NOT_EQUALS) {     
			operator = VcOperator.NOT_EQUALS;
		} else if (binExpr.operator == CfgOperator.GREATER) {   
			operator = VcOperator.GREATER;
		} else if (binExpr.operator == CfgOperator.GREATER_EQUALS) { 
			operator = VcOperator.GREATER_EQUALS;
		} else if (binExpr.operator == CfgOperator.LESS) {
			operator = VcOperator.LESS;
		} else if (binExpr.operator == CfgOperator.LESS_EQUALS) {    
			operator = VcOperator.LESS_EQUALS;
		}
	    if (operator != null) {
		     return new VcRelativeExpression(operator, left, right, binExpr.sourceStart, binExpr.sourceEnd);
	    }

	    if (binExpr.operator == CfgOperator.IMPLIES) {        
			operator = VcOperator.IMPLIES;
		} else if (binExpr.operator == CfgOperator.REV_IMPLIES) {     
			operator = VcOperator.IMPLIES;
			VC temp = left;
			left = right;
			right = temp;
		} else if (binExpr.operator == CfgOperator.EQUIV) {     
			operator = VcOperator.EQUIV;
		} else if (binExpr.operator == CfgOperator.NOT_EQUIV) {     
			operator = VcOperator.NOT_EQUIV;
		}
	    if (operator != null) {
		    VC result = new VcLogicalExpression(operator, left, right, binExpr.sourceStart, binExpr.sourceEnd);
		    result.markAsImplication();
		    return result;
	    }

	    if (binExpr.operator == CfgOperator.PLUS) {
			operator = VcOperator.PLUS;
		} else if (binExpr.operator == CfgOperator.MINUS) {
			operator = VcOperator.MINUS;
		} else if (binExpr.operator == CfgOperator.TIMES) {
			operator = VcOperator.TIMES;
		} else if (binExpr.operator == CfgOperator.DIVIDE) {
			operator = VcOperator.DIVIDE;
		} else if (binExpr.operator == CfgOperator.REMAINDER) {
			operator = VcOperator.REMAINDER;
		} 
		Utils.assertNotNull(operator, "operator ("+binExpr+") not translated correctly");  //$NON-NLS-1$//$NON-NLS-2$
	    return new VcArithExpression(operator, left, right, left.type, binExpr.sourceStart, binExpr.sourceEnd);
	}

	public VC visit(CfgConditionalExpression condExpr) {
		VC condition = condExpr.condition.accept(this);
		VC valueIfTrue = condExpr.valueIfTrue.accept(this);
		VC valueIfFalse = condExpr.valueIfFalse.accept(this);
		return new VcConditionalExpression(condition, valueIfTrue,
				valueIfFalse, condExpr.type, condExpr.sourceStart, condExpr.sourceEnd);
	}

	public VC visit(CfgGoto cfgGoto, VC N) {
		String[] gotos = cfgGoto.gotos;
		VC result = N;
		for (int i = gotos.length-1; i >= 0; i--) {
			String varName = gotos[i]+"$ok"; //$NON-NLS-1$
			VcVariable var = new VcVariable(varName, 0, TypeBinding.BOOLEAN, 0, 0, 0);
			result = new VcAnd(var, result, 0, 0);
		}
		return result;
	}

	public VC visit(CfgSuperReference superRef) {
		return new VcSuperReference(superRef.type, superRef.sourceStart, superRef.sourceEnd);
	}

	public VC visit(CfgThisReference thisRef) {
		return new VcThisReference(thisRef.type, thisRef.sourceStart, thisRef.sourceEnd);
	}

	public VC visit(CfgFieldReference fieldRef) {
		VC receiver = fieldRef.receiver.accept(this);
		VcFieldReference result = new VcFieldReference(receiver, fieldRef.field, fieldRef.incarnation(), fieldRef.type, fieldRef.sourceStart, fieldRef.sourceEnd);
		if (receiver.type.isArrayType() && fieldRef.field.equals(LENGTH)) {
			this.lengthRefs.add(result);
		}
		return result;
	}

	public VC visit(CfgFieldStore fieldStore) {
		VC visitedField = fieldStore.field.accept(this);
		Utils.assertTrue(visitedField instanceof VcFieldReference, "'"+visitedField+"' isn't a VcFieldReference but a '"+visitedField.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		VcFieldReference field = (VcFieldReference) visitedField;
		VC value = fieldStore.value.accept(this);
		return new VcFieldStore(field, fieldStore.oldIncarnation, fieldStore.newIncarnation, value);
	}

	public VC visit(CfgArrayReference arrayRef) {
		VC receiver = arrayRef.receiver.accept(this);
		VC position = arrayRef.receiver.accept(this);
		return new VcArrayReference(receiver, position, arrayRef.incarnation(), arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
	}

	public VC visit(CfgArrayAllocationExpression arrayAlloc) {
		int length = arrayAlloc.dims.length;
		VC[] dims = new VC[length];
		for (int i = 0; i < dims.length; i++) {
			dims[i] = arrayAlloc.dims[i].accept(this);
		}
		return new VcArrayAllocationExpression(arrayAlloc.ids, dims, arrayAlloc.type, arrayAlloc.sourceStart, arrayAlloc.sourceEnd);
	}

}
