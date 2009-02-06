package org.jmlspecs.jml4.esc.gc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBlock;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredGoto;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredHavoc;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredIfStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredLoopAnnotations;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignment;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;
import org.jmlspecs.jml4.esc.util.Counter;
import org.jmlspecs.jml4.esc.util.Utils;

public class DesugarLoopVisitor implements SugaredStatementVisitor {

	public static final boolean useNewLoopSemantics = false;
	static class NewBlocks {
		private final List/*<SugaredBlock>*/ blockList = new ArrayList/*<SugaredBlock>*/();

		public String toString() {
			List result = new ArrayList();
			for (Iterator iterator = this.blockList.iterator(); iterator.hasNext();) {
				SugaredBlock block = (SugaredBlock) iterator.next();
				result.add(block.blockId);
			}
			return result.toString();
		}
		public void add(SugaredBlock block) {
			SugaredBlock[] existing = this.toArray();
			for (int i = 0; i < existing.length; i++) {
				SugaredBlock existingBlock = existing[i];
				if (existingBlock.blockId.equals(block.blockId))
					throw new RuntimeException("block '"+block.blockId+"' already exists"); //$NON-NLS-1$ //$NON-NLS-2$
			}
			this.blockList.add(block);
		}

		public SugaredBlock[] toArray() {
			return (SugaredBlock[])this.blockList.toArray(SugaredBlock.EMPTY);
		}

		public int size() {
			return this.blockList.size();
		}

		public void clear() {
			this.blockList.clear();
		}

		public void addAll(SugaredBlock[] blocks) {
			for (int i = 0; i < blocks.length; i++) {
				this.blockList.add(blocks[i]);
			}
		}
	}
	NewBlocks newlyCreatedBlocks = new NewBlocks();
	private final Counter counter = new Counter();
	private final Map/*<String, SugaredLoopAnnotations>*/ annotations = new HashMap/*<String, SugaredLoopAnnotations>*/();
	private final Map/*<String, SugaredWhileStatement>*/ loops = new HashMap/*<String, SugaredWhileStatement>*/();

	public DesugarLoopVisitor() {/*empty*/}

	public SugaredProgram visit(SugaredProgram origProgram) {
		NewBlocks blocks = new NewBlocks();
		SugaredBlock[] sugaredBlocks = origProgram.blocks;
		for (int i = 0; i < sugaredBlocks.length; i++) {
			SugaredBlock[] modBlocks = sugaredBlocks[i].accept(this);
			blocks.addAll(modBlocks);
		}
		return new SugaredProgram(blocks.toArray(), origProgram.startName, origProgram.methodIndicator);
	}

	public SugaredBlock[] /*<SugaredBlock>*/ visit(SugaredBlock origBlock) {
		NewBlocks result = new NewBlocks();
		SugaredStatement modStmt = origBlock.stmt.accept(this, null);
		SugaredBlock modBlock = new SugaredBlock(origBlock.blockId, modStmt);
		result.add(modBlock);
		if (this.newlyCreatedBlocks.size() > 0) {
			SugaredBlock[] newBlocks = this.newlyCreatedBlocks.toArray();
			this.newlyCreatedBlocks.clear();
			for (int i = 0; i < newBlocks.length; i++) {
				SugaredBlock[] newOnes = newBlocks[i].accept(this);
				result.addAll(newOnes);
			}
		}
		if (this.newlyCreatedBlocks.size() > 0) {
			throw new RuntimeException("previous if should be a while..."); //$NON-NLS-1$
		}
		return result.toArray();
	}

	public SugaredStatement visit(SugaredAssert sugaredAssert, SugaredStatement rest) {
		return (rest == null
			 ? (SugaredStatement) sugaredAssert
			 : new SugaredSequence(sugaredAssert.accept(this, null), rest.accept(this, null)));
	}
	public SugaredStatement visit(SugaredAssume sugaredAssume, SugaredStatement rest) {
		return (rest == null
			 ? (SugaredStatement) sugaredAssume
			 : new SugaredSequence(sugaredAssume.accept(this, null), rest.accept(this, null)));
	}
	public SugaredStatement visit(SugaredPrecondition sugaredPrecondition, SugaredStatement rest) {
		if (rest == null) {
			SugaredExpression pred = sugaredPrecondition.pred;
			SugaredAssume result = new SugaredAssume(pred, sugaredPrecondition.sourceStart);
			return result;
		}
		else
			return new SugaredSequence(sugaredPrecondition.accept(this, null), rest.accept(this, null));
	}
	public SugaredStatement visit(SugaredPostcondition sugaredPostcondition, SugaredStatement rest) {
		if (rest == null) {
			SugaredExpressionVisitor visitor = new VarToOldVisitor();
			SugaredExpression pred = sugaredPostcondition.pred.accept(visitor);
			SugaredAssert result = new SugaredAssert(pred, KindOfAssertion.POST, sugaredPostcondition.methodStart);
			return result;
		}
		else
			return new SugaredSequence(sugaredPostcondition.accept(this, null), rest.accept(this, null));
	}
	public SugaredStatement visit(SugaredVarDecl sugaredVarDecl, SugaredStatement rest) {
		return (rest == null
			 ? (SugaredStatement) sugaredVarDecl
			 : new SugaredSequence(sugaredVarDecl.accept(this, null), rest.accept(this, null)));
	}
	public SugaredStatement visit(SugaredGoto sugaredGoto, SugaredStatement rest) {
		return (rest == null
			 ? (SugaredStatement) sugaredGoto
			 : new SugaredSequence(sugaredGoto.accept(this, null), rest.accept(this, null)));
	}
	public SugaredStatement visit(SugaredExprStatement sugaredExprStatement, SugaredStatement rest) {
		return (rest == null
			 ? (SugaredStatement) sugaredExprStatement
			 : new SugaredSequence(sugaredExprStatement.accept(this, null), rest.accept(this, null)));
	}

	public SugaredStatement visit(SugaredSequence sugaredSequence, SugaredStatement rest) {
		if (sugaredSequence.stmt1 instanceof SugaredIfStatement) {
			int count = this.counter.getAndIncCounter();
			String afterBlockName = "afterIf$"+count; //$NON-NLS-1$
			SugaredStatement stmt2 = sugaredSequence.stmt2().accept(this, rest);
			SugaredBlock afterBlock = new SugaredBlock(afterBlockName, stmt2);
			this.newlyCreatedBlocks.add(afterBlock);
			return visit((SugaredIfStatement)sugaredSequence.stmt1, afterBlockName, count);
		} else if (sugaredSequence.stmt1 instanceof SugaredWhileStatement) {
			SugaredWhileStatement whileStmt = (SugaredWhileStatement)sugaredSequence.stmt1;
			String label = whileStmt.label;
			//this string is duplicated at Ast2SugaredVisitor.visit(WhileStatement whileStatement, BlockScope scope, String label)
			String breakTargetName = label + "$break"; //$NON-NLS-1$
			SugaredStatement result = (useNewLoopSemantics
					                ? visit_new(whileStmt, breakTargetName)
            						: visit_old(whileStmt, breakTargetName));
			SugaredStatement stmt2 = sugaredSequence.stmt2().accept(this, rest);
			SugaredBlock breakToHereBlock = new SugaredBlock(breakTargetName, stmt2);
			this.newlyCreatedBlocks.add(breakToHereBlock);
			return result;
		} else if (sugaredSequence.stmt1 instanceof SugaredBreakStatement) {
//			Utils.assertTrue(sugaredSequence.stmt2() instanceof SugaredGoto, "something other than goto after break"); //$NON-NLS-1$
			return sugaredSequence.stmt1.accept(this, null);
		} else if (sugaredSequence.stmt1 instanceof SugaredContinueStatement) {
//			Utils.assertTrue(sugaredSequence.stmt2() instanceof SugaredGoto, "something other than goto after continue"); //$NON-NLS-1$
			return sugaredSequence.stmt1.accept(this, null);
		} else if (sugaredSequence.stmt1 instanceof SugaredReturnStatement) {
//			Utils.assertTrue(sugaredSequence.stmt2() instanceof SugaredGoto, "something other than goto after continue"); //$NON-NLS-1$
			return sugaredSequence.stmt1.accept(this, null);
		} else {
			SugaredStatement newRest = (rest == null
					                ? sugaredSequence.stmt2()
					                : new SugaredSequence(sugaredSequence.stmt2(), rest));
			return sugaredSequence.stmt1.accept(this, newRest);
		}
	}

	private SugaredStatement visit(SugaredIfStatement sugaredIfStatement, String afterBlockName, int count) {
		String thenBlockName = "then$" + count; //$NON-NLS-1$
		String elseBlockName = "else$" + count; //$NON-NLS-1$
		String[] newBlockNames = new String[] {thenBlockName, elseBlockName};

		SugaredStatement gotoAfter = new SugaredGoto(new String[]{afterBlockName});
		SugaredExpression condition = sugaredIfStatement.condition;
		condition.clearSourcePosition();
		SugaredStatement assumeCondition = new SugaredAssume(condition, condition.sourceStart);
		SugaredStatement assumeNotCondition = new SugaredAssume(new SugaredNotExpression(condition, 0, 0), condition.sourceStart);

		SugaredStatement thenGotoAfter = new SugaredSequence(sugaredIfStatement.thenStatement, gotoAfter);
		SugaredStatement condThenAfter = new SugaredSequence(assumeCondition, thenGotoAfter);
		SugaredBlock thenBlock = new SugaredBlock(thenBlockName, condThenAfter);
		this.newlyCreatedBlocks.add(thenBlock);

		SugaredStatement elseGotoAfter = new SugaredSequence(sugaredIfStatement.elseStatement, gotoAfter);
		SugaredStatement notCondElseAfter = new SugaredSequence(assumeNotCondition, elseGotoAfter);
		SugaredBlock elseBlock = new SugaredBlock(elseBlockName, notCondElseAfter);
		this.newlyCreatedBlocks.add(elseBlock);

		return new SugaredGoto(newBlockNames);
	}

	private SugaredStatement visit_old(SugaredWhileStatement whileStmt, String breakTargetName) {
		//these strings are duplicated at Ast2SugaredVisitor.visit(WhileStatement whileStatement, BlockScope scope, String label)
		String headerName = whileStmt.label + "$header"; //$NON-NLS-1$
		String   bodyName = whileStmt.label + "$body";   //$NON-NLS-1$
		String  afterName = whileStmt.label + "$after";  //$NON-NLS-1$

		SugaredExpression cond = whileStmt.condition;
		this.annotations.put(headerName, whileStmt.annotations);
		this.loops.put(headerName, whileStmt);

		SugaredExpression inv = whileStmt.annotations.foldInvariants();
		SugaredExpression[] loopTargets = gatherTargets(whileStmt);
		SugaredStatement havocTargets = havocTargets(loopTargets);

		// result goes in place of the while statement in the original block
		// result : assert inv ; goto header
		SugaredStatement assertInvPre = new SugaredAssert(inv, KindOfAssertion.LOOP_INVAR_PRE, whileStmt.sourceStart);
		SugaredStatement gotoHeader = new SugaredGoto(new String[]{headerName});
		SugaredStatement result = new SugaredSequence(assertInvPre, gotoHeader);

		// header : havoc targets ; assume inv; goto body, after;
		SugaredStatement assumeInv = new SugaredAssume(inv, inv.sourceStart);
		SugaredStatement gotoBodyAfter = new SugaredGoto(new String[]{bodyName, afterName});
		SugaredStatement assumeGoto = new SugaredSequence(assumeInv, gotoBodyAfter);
		SugaredStatement havocAssumeGoto = new SugaredSequence(havocTargets, assumeGoto);
		SugaredStatement headerStmt = havocAssumeGoto;
		SugaredBlock headerBlock = new SugaredBlock(headerName, headerStmt);
		this.newlyCreatedBlocks.add(headerBlock);

		// body : store variants; assume cond; action; assert inv; check variants; goto;
		SugaredStatement assertInvPost = new SugaredAssert(inv, KindOfAssertion.LOOP_INVAR, whileStmt.sourceStart);
		SugaredStatement cyclicActionAssertInv = 
		    ( whileStmt.annotations.invariants.length == 0
		    ? whileStmt.action
		    : new SugaredSequence(whileStmt.action, assertInvPost));

		SugaredStatement cyclicActionInvVar =
		    ( whileStmt.annotations.variants.length == 0
		    ? cyclicActionAssertInv
		    : new SugaredSequence(cyclicActionAssertInv, getCheckVariants(whileStmt)));

		SugaredStatement goNowhere = new SugaredGoto(new String[0]);
		SugaredStatement cyclicActionAndRest = new SugaredSequence(cyclicActionInvVar, goNowhere);

		SugaredStatement action = cyclicActionAndRest.accept(this, null);
		SugaredStatement assumeCond = new SugaredAssume(cond, cond.sourceStart);
		
		SugaredStatement storeVariantsAssumeCond =
		    ( whileStmt.annotations.variants.length == 0
		    ? assumeCond
		    : new SugaredSequence(storeVariants(whileStmt), assumeCond));

		SugaredStatement bodyStmt = new SugaredSequence(storeVariantsAssumeCond, action);

		SugaredBlock bodyBlock = new SugaredBlock(bodyName, bodyStmt);
		this.newlyCreatedBlocks.add(bodyBlock);

		// after : assume ~ cond; goto breakTarget;
		SugaredStatement gotoBreakTarget = new SugaredGoto(new String[]{breakTargetName});
		SugaredExpression notCondition = new SugaredNotExpression(cond, cond.sourceStart, cond.sourceEnd);
		SugaredStatement assumeNotCond = new SugaredAssume(notCondition, cond.sourceStart);
		SugaredStatement afterStmt = new SugaredSequence(assumeNotCond, gotoBreakTarget);
		SugaredBlock afterBlock = new SugaredBlock(afterName, afterStmt);
		this.newlyCreatedBlocks.add(afterBlock);

		return result;
	}
	private SugaredStatement visit_new(SugaredWhileStatement whileStmt, String breakTargetName) {
		//these strings are duplicated at Ast2SugaredVisitor.visit(WhileStatement whileStatement, BlockScope scope, String label)
		String headerName = whileStmt.label + "$header"; //$NON-NLS-1$
		String   bodyName = whileStmt.label + "$body";   //$NON-NLS-1$
		String  afterName = whileStmt.label + "$after";  //$NON-NLS-1$

		SugaredVarDecl condTempDecl = getCondDeclaration(whileStmt.label);
		SugaredStatement condAssignment = getCondAssignment(whileStmt);

		SugaredExpression cond = whileStmt.condition;
		this.annotations.put(headerName, whileStmt.annotations);
		this.loops.put(headerName, whileStmt);

		SugaredExpression inv = whileStmt.annotations.foldInvariants();
		SugaredExpression[] loopTargets = gatherTargets(whileStmt);
		SugaredStatement havocTargets = havocTargets(loopTargets);

		// result goes in place of the while statement in the original block
		// result : boolean condTemp = cond; assert inv ; goto header
		SugaredStatement assertInvPre = new SugaredAssert(inv, KindOfAssertion.LOOP_INVAR_PRE, whileStmt.sourceStart);
		SugaredStatement gotoHeader = new SugaredGoto(new String[]{headerName});
		SugaredStatement result = new SugaredSequence(condTempDecl,
				  				  new SugaredSequence(condAssignment,
								  new SugaredSequence(assertInvPre, gotoHeader)));

		// header : havoc targets ; goto body, after;
		SugaredStatement gotoBodyAfter = new SugaredGoto(new String[]{bodyName, afterName});
		SugaredStatement havocGoto = new SugaredSequence(havocTargets, gotoBodyAfter);
		SugaredStatement headerStmt = havocGoto;
		SugaredBlock headerBlock = new SugaredBlock(headerName, headerStmt);
		this.newlyCreatedBlocks.add(headerBlock);

		// body : assume cond; assume inv; store variants; action; condTemp = cond; assert inv; check variants; goto;
		SugaredStatement assertInvAfter = new SugaredAssert(inv, KindOfAssertion.LOOP_INVAR, whileStmt.sourceStart);
		SugaredStatement cyclicActionAssertInv = new SugaredSequence(whileStmt.action, 
				                                 new SugaredSequence(condAssignment, assertInvAfter));
		SugaredStatement cyclicActionInvVar = (whileStmt.annotations.variants.length == 0
				? cyclicActionAssertInv
				: new SugaredSequence(cyclicActionAssertInv, getCheckVariants(whileStmt)));

		SugaredStatement goNowhere = new SugaredGoto(new String[0]);
		SugaredStatement cyclicActionAndRest = new SugaredSequence(cyclicActionInvVar, goNowhere);

		SugaredStatement actionAndRest = cyclicActionAndRest.accept(this, null);
		SugaredStatement assumeInv = new SugaredAssume(inv, inv.sourceStart);
		SugaredStatement assumeCondAssumeInv = new SugaredSequence(new SugaredAssume(cond, cond.sourceStart), assumeInv);
		
		SugaredStatement assumeCondInvStoreVariants =
		    ( whileStmt.annotations.variants.length == 0
		    ? assumeCondAssumeInv
		    : new SugaredSequence(assumeCondAssumeInv, storeVariants(whileStmt)));

		SugaredStatement bodyStmt = new SugaredSequence(assumeCondInvStoreVariants, actionAndRest);

		SugaredBlock bodyBlock = new SugaredBlock(bodyName, bodyStmt);
		this.newlyCreatedBlocks.add(bodyBlock);

		// after : assume ~ cond ; assume inv ; goto breakTarget;
		SugaredStatement gotoBreakTarget = new SugaredGoto(new String[]{breakTargetName});
		SugaredExpression notCondition = new SugaredNotExpression(cond, cond.sourceStart, cond.sourceEnd);
		SugaredStatement assumeNotCond = new SugaredAssume(notCondition, cond.sourceStart);
		SugaredStatement afterStmt = new SugaredSequence(assumeNotCond,
								     new SugaredSequence(assumeInv,
								    		 	         gotoBreakTarget));
		SugaredBlock afterBlock = new SugaredBlock(afterName, afterStmt);
		this.newlyCreatedBlocks.add(afterBlock);

		return result;
	}

	private SugaredVariable getCondTemp(String label) {
		String condTempName = getCondTempName(label);
		SugaredVariable condTemp = new SugaredVariable(condTempName, 0, TypeBinding.BOOLEAN, 0, 0);
		return condTemp;
	}

	private SugaredVarDecl getCondDeclaration(String label) {
		String condTempName = getCondTempName(label);
		return new SugaredVarDecl(condTempName, 0, TypeBinding.BOOLEAN, 0);
	}

	private String getCondTempName(String label) {
		String condTempName = label + "$condTemp";  //$NON-NLS-1$
		return condTempName;
	}

	private SugaredStatement getCondAssignment(SugaredWhileStatement whileStmt) {
		SugaredVariable condTemp = getCondTemp(whileStmt.label);
		SugaredExpression condAssignmentExpr = new SugaredAssignment(condTemp, whileStmt.condition, 0, 0);
		SugaredStatement condAssignment = new SugaredExprStatement(condAssignmentExpr);
		return condAssignment;
	}

	private SugaredStatement storeVariants(SugaredWhileStatement whileStmt) {
		Utils.assertTrue(whileStmt.annotations.variants.length > 0, "no variants to store"); //$NON-NLS-1$
		SugaredExpression[] variants = whileStmt.annotations.variants;
		String label = whileStmt.label;
		SugaredStatement result = getStoreVariantAsStatement(variants[variants.length-1], variants.length - 1, label);
		for (int i = variants.length - 2; i >= 0; i--) {
			SugaredStatement variant = getStoreVariantAsStatement(variants[i], i, label);
			result = new SugaredSequence(variant, result); 
		}
		return result;
	}

	private SugaredStatement getCheckVariants(SugaredWhileStatement whileStmt) {
		Utils.assertTrue(useNewLoopSemantics || whileStmt.annotations.variants.length > 0, "no variants to store"); //$NON-NLS-1$
		return getCheckVariants(whileStmt.annotations.variants, whileStmt.label, whileStmt.condition);
	}
	private SugaredStatement getCheckVariants(String label) {
		SugaredWhileStatement whileStmt = findLoopForLabel(label);
		return getCheckVariants(whileStmt);
	}

	private SugaredStatement getCheckVariants(SugaredExpression[] variants, String label, SugaredExpression condition) {
		SugaredStatement result = getCheckVariantAsStatement(variants[variants.length - 1], variants.length - 1, label, condition);
		for (int i = variants.length - 2; i >= 0; i--) {
			SugaredStatement variant = getCheckVariantAsStatement(variants[i], i, label, condition);
			result = new SugaredSequence(variant, result); 
		}
		return result;
	}

	// creates a variable declaration to store each loop variant
	// and initializes it with the value of the variant function
	private SugaredStatement getStoreVariantAsStatement(SugaredExpression variant, int index, String label) {
		String name = label + "$var$" + index; //$NON-NLS-1$
		BaseTypeBinding type = TypeBinding.INT;
		SugaredVarDecl varDecl = new SugaredVarDecl(name, variant.sourceStart, type, variant.sourceStart);
		SugaredVariable var = new SugaredVariable(name, variant.sourceStart, type, variant.sourceStart, variant.sourceEnd);
		SugaredExpression assignmentExpr = new SugaredAssignment(var, variant, variant.sourceStart, variant.sourceEnd);
		SugaredExprStatement assignmentStmt = new SugaredExprStatement(assignmentExpr);
		SugaredStatement result = new SugaredSequence(varDecl, assignmentStmt);
		return result;
	}

	// for each loop variant, assert that the value of the variant function
	// is less than the corresponding variable stored at the top of the loop
	// also, for each variant, check that its value being zero implies
	// the negation of the loop condition
	private SugaredStatement getCheckVariantAsStatement(SugaredExpression variant, int index, String label, SugaredExpression condition) {
		return useNewLoopSemantics
		     ? getCheckVariantAsStatement_new(variant, index, label, condition)
	     	 : getCheckVariantAsStatement_old(variant, index, label, condition);
	}
	private SugaredStatement getCheckVariantAsStatement_old(SugaredExpression variant, int index, String label, SugaredExpression condition) {
		String name = label + "$var$" + index; //$NON-NLS-1$
		SugaredVariable var = new SugaredVariable(name, variant.sourceStart, TypeBinding.INT, variant.sourceStart, variant.sourceEnd);
		SugaredExpression decreasesCheck = new SugaredBinaryExpression(SugaredOperator.LESS, variant, var, TypeBinding.BOOLEAN, variant.sourceStart, variant.sourceEnd);
		SugaredStatement decreases = new SugaredAssert(decreasesCheck, KindOfAssertion.LOOP_VAR, decreasesCheck.sourceStart);

		SugaredStatement result = decreases;
		return result;

		// if the following lines aren't needed, remove them
//		SugaredExpression variantEqZero = new SugaredBinaryExpression(SugaredOperator.EQUALS, variant, SugaredIntegerConstant.ZERO, TypeBinding.BOOLEAN, variant.sourceStart, variant.sourceEnd);
//		SugaredExpression notVariantEqZero = new SugaredNotExpression(variantEqZero, variant.sourceStart, variant.sourceEnd);
//		SugaredExpression notCondition = new SugaredNotExpression(condition, variantEqZero.sourceStart, variantEqZero.sourceEnd);
//
//		// a=>b == ~a|b
//		SugaredExpression Eq0impliesNotCond = new SugaredBinaryExpression(SugaredOperator.OR, notVariantEqZero, notCondition, TypeBinding.BOOLEAN, variant.sourceStart, variant.sourceEnd);
//		SugaredStatement exits = new SugaredAssert(Eq0impliesNotCond, Eq0impliesNotCond.sourceStart);
//
//		SugaredStatement result = new SugaredSequence(decreases, exits);
//		return result;
	}
	private SugaredStatement getCheckVariantAsStatement_new(SugaredExpression variant, int index, String label, SugaredExpression condition) {
		String name = label + "$var$" + index; //$NON-NLS-1$
		BaseTypeBinding type = TypeBinding.INT;
		SugaredVariable var = new SugaredVariable(name, variant.sourceStart, type, variant.sourceStart, variant.sourceEnd);
		SugaredExpression decreasesCheck = new SugaredBinaryExpression(SugaredOperator.LESS, variant, var, type, variant.sourceStart, variant.sourceEnd);
		SugaredStatement decreases = new SugaredAssert(decreasesCheck, KindOfAssertion.LOOP_VAR, decreasesCheck.sourceStart);
		return decreases;
	}

	//@ requires (* forall i . loopTargets[i] instanceof SugaredVariable*);
	private SugaredStatement havocTargets(SugaredExpression[] loopTargets) {
		if (loopTargets.length == 0)
			return SugaredAssert.SKIP;
		int length = loopTargets.length;
		SugaredStatement result = new SugaredHavoc((SugaredVariable)loopTargets[length-1], 0);
		for (int i = length - 2; i >= 0; i--) {
			SugaredHavoc havoc = new SugaredHavoc((SugaredVariable)loopTargets[i], 0);
			result = new SugaredSequence(havoc, result);
		}
		return result;
	}

	private SugaredExpression[] gatherTargets(SugaredWhileStatement whileStmt) {
		TargetGatheringVisitor targetGatheringVisitor = new TargetGatheringVisitor();
		whileStmt.condition.accept(targetGatheringVisitor);
		whileStmt.action.accept(targetGatheringVisitor);
		SugaredExpression[] loopTargets = targetGatheringVisitor.getResult();
		return loopTargets;
	}

	public SugaredStatement visit(SugaredIfStatement sugaredIfStatement, SugaredStatement rest) {
		if (rest == null) {
			int count = this.counter.getAndIncCounter();
			String afterBlockName = "afterIf$"+count; //$NON-NLS-1$
			SugaredStatement stmt2 = new SugaredGoto(SugaredGoto.NOWHERE);
			SugaredBlock afterBlock = new SugaredBlock(afterBlockName, stmt2);
			this.newlyCreatedBlocks.add(afterBlock);
			return visit(sugaredIfStatement, afterBlockName, count);
		} else {
			return new SugaredSequence(sugaredIfStatement.accept(this, null), rest.accept(this, null));
		}
	}

	public SugaredStatement visit(SugaredWhileStatement whileStmt, SugaredStatement rest) {
		if (rest == null) {
			String label = whileStmt.label;
			String breakTargetName = label + "$break"; //$NON-NLS-1$
			SugaredStatement result = (useNewLoopSemantics
	                				? visit_new(whileStmt, breakTargetName)
	                				: visit_old(whileStmt, breakTargetName));
			SugaredStatement stmt2 = new SugaredGoto(SugaredGoto.NOWHERE);
			SugaredBlock breakToHereBlock = new SugaredBlock(breakTargetName, stmt2);
			this.newlyCreatedBlocks.add(breakToHereBlock);
			return result;
		} else {
			return new SugaredSequence(whileStmt.accept(this, null), rest.accept(this, null));
		}
	}

	public SugaredStatement visit(SugaredBreakStatement breakStmt, SugaredStatement rest) {
		return useNewLoopSemantics
			 ? visit_new(breakStmt, rest)
			 : visit_old(breakStmt, rest);
	}
	private SugaredStatement visit_old(SugaredBreakStatement breakStmt, SugaredStatement rest) {
		Utils.assertTrue(rest == null, "rest isn't null"); //$NON-NLS-1$
		String label = breakStmt.label;
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		Utils.assertTrue(label.indexOf("break") >= 0, "break label is "+label); //$NON-NLS-1$ //$NON-NLS-2$
		return new SugaredGoto(new String[]{label});
	}
	private SugaredStatement visit_new(SugaredBreakStatement breakStmt, SugaredStatement rest) {
		Utils.assertTrue(rest == null, "rest isn't null"); //$NON-NLS-1$
		String label = breakStmt.label;
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		Utils.assertTrue(label.indexOf("break") >= 0, "break label is "+label); //$NON-NLS-1$ //$NON-NLS-2$
		// assert inv; goto breakTarget;
		SugaredExpression assertExpr = findInvariantForLoop(label);
		SugaredAssert assertInv = new SugaredAssert(assertExpr, KindOfAssertion.LOOP_INVAR, breakStmt.sourceStart);
		SugaredGoto gotoBreak = new SugaredGoto(new String[]{label});
		return new SugaredSequence(assertInv, gotoBreak);
	}
	public SugaredStatement visit(SugaredContinueStatement continueStmt, SugaredStatement rest) {
		return useNewLoopSemantics
			 ? visit_new(continueStmt, rest)
			 : visit_old(continueStmt, rest);
	}
	private SugaredStatement visit_old(SugaredContinueStatement sugaredContinueStatement, SugaredStatement rest) {
		Utils.assertTrue(rest == null, "rest isn't null"); //$NON-NLS-1$
		String label = sugaredContinueStatement.label;
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		Utils.assertTrue(label.indexOf("header") >= 0, "continuelabel is "+label); //$NON-NLS-1$ //$NON-NLS-2$
		SugaredExpression assertExpr = findInvariantForLoop(label);
		SugaredAssert assertInv = new SugaredAssert(assertExpr, KindOfAssertion.LOOP_INVAR, sugaredContinueStatement.sourceStart);
		SugaredStatement checkVariants = getCheckVariants(label);
		SugaredGoto goNowhere = new SugaredGoto(new String[0]);
		return new SugaredSequence(assertInv, new SugaredSequence(checkVariants, goNowhere));
	}
	private SugaredStatement visit_new(SugaredContinueStatement sugaredContinueStatement, SugaredStatement rest) {
		Utils.assertTrue(rest == null, "rest isn't null"); //$NON-NLS-1$
		String label = sugaredContinueStatement.label;
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		Utils.assertTrue(label.indexOf("header") >= 0, "continuelabel is "+label); //$NON-NLS-1$ //$NON-NLS-2$
		// condTemp = c; assert I; check variants; goto;
		SugaredWhileStatement whileStmt = findLoopForLabel(label);
		Utils.assertNotNull(whileStmt, "while statement is null for "+label); //$NON-NLS-1$
		Utils.assertNotNull(whileStmt.annotations, "annotations is null for "+label); //$NON-NLS-1$
		SugaredExpression assertExpr = whileStmt.annotations.foldInvariants();
		SugaredAssert assertInv = new SugaredAssert(assertExpr, KindOfAssertion.LOOP_INVAR, sugaredContinueStatement.sourceStart);
		SugaredStatement checkVariants = getCheckVariants(label);
		SugaredGoto goNowhere = new SugaredGoto(new String[0]);
		
		SugaredSequence result = new SugaredSequence(assertInv, 
								 new SugaredSequence(getCondAssignment(whileStmt),
				                 new SugaredSequence(checkVariants, goNowhere)));
		return result;
	}

	private SugaredExpression findInvariantForLoop(String label) {
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		SugaredLoopAnnotations ann = (SugaredLoopAnnotations)this.annotations.get(label);
		if (useNewLoopSemantics) {
			if (ann == null) {
				return new SugaredBooleanConstant(true, 0, 0);
			}
		} else {
			Utils.assertNotNull(ann, "should be unreachable"); //$NON-NLS-1$
		}
		return ann.foldInvariants();
	}
	private SugaredWhileStatement findLoopForLabel(String label) {
		Utils.assertNotNull(label, "label is null"); //$NON-NLS-1$
		SugaredWhileStatement loopStmt = (SugaredWhileStatement)this.loops.get(label);
		Utils.assertNotNull(loopStmt, "should be unreachable"); //$NON-NLS-1$
		return loopStmt;
	}

	public SugaredStatement visit(SugaredHavoc sugaredHavoc, SugaredStatement rest) {
		if (rest == null)
			return sugaredHavoc;
		else
			return new SugaredSequence(sugaredHavoc.accept(this, null), rest.accept(this, null));
	}

	public SugaredStatement visit(SugaredReturnStatement returnStmt, SugaredStatement rest) {
		Utils.assertTrue(rest == null, "rest isn't null"); //$NON-NLS-1$
		SugaredExpression expr = returnStmt.expr;
		SugaredGoto gotoReturn = new SugaredGoto(new String[]{SugaredReturnStatement.RETURN_BLOCK});
		SugaredStatement result;
		if (expr == null) {
			result = gotoReturn;
		} else {
			TypeBinding type = returnStmt.type;
			SugaredVariable resultVar = new SugaredVariable("return", 0, type, expr.sourceStart, expr.sourceEnd); //$NON-NLS-1$
			SugaredBinaryExpression resultEq = new SugaredBinaryExpression(SugaredOperator.EQUALS, resultVar, expr, TypeBinding.BOOLEAN, expr.sourceStart, expr.sourceEnd);
			SugaredAssume retExpr = new SugaredAssume(resultEq, resultEq.sourceStart);
			result = new SugaredSequence(retExpr, gotoReturn);
		}
		return result;
	}

}
