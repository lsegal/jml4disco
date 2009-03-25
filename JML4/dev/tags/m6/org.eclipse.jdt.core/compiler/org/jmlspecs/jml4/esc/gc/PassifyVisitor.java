package org.jmlspecs.jml4.esc.gc;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

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
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgAssignable;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldStore;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgOperator;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgQuantifier;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgThisReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgVariable;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssert;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssignment;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleAssume;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleBlock;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleExprStatement;
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
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleThisReference;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class PassifyVisitor {

	private static final String SEP = "$"; //$NON-NLS-1$
	private static final boolean useCfgSubstitutionVisitor = false;
	private boolean translatedAMethodCall = false;
	//* used to store assignments and method pre&posts
	private final StmtsFromExprs stmtsFromExprs = new StmtsFromExprs();
	static class StmtsFromExprs {
		private final List/*<CfgStatements>*/ stmts = new ArrayList/*<CfgStatement>*/();
		public void add(CfgStatement stmt) {
			this.stmts.add(stmt);
		}
		public void addAll(List/*<CfgStatement>*/ condList) {
			this.stmts.addAll(condList);
		}
		public void clear() {
			this.stmts.clear();
		}
		public boolean isEmpty() {
			return this.stmts.isEmpty();
		}
		public int size() {
			return this.stmts.size();
		}
		public List/*<CfgStatement>*/ asList() {
			CfgStatement[] asArray = toArray();
			List/*<CfgStatement>*/ asList = Arrays.asList(asArray);
			List/*<CfgStatement>*/ result = new ArrayList/*<CfgStatement>*/();
			result.addAll(asList);
			return result;
		}
		public CfgStatement[] toArray() {
			return (CfgStatement[])this.stmts.toArray(CfgStatement.EMPTY);
		}
		public String toString() {
			return this.stmts.toString();
		}
	}
	private final FieldReceiverCache passifiedReceiverCache = new FieldReceiverCache();
	private boolean processingContract = false;
	public final Map/*<CfgVariable, CfgExpression>*/ map = new HashMap/*<CfgVariable, CfgExpression>*/();
	private final Set/*<CfgVarDecl>*/ paramAndResultDecls = new HashSet/*<CfgVarDecl>*/();
	private boolean isInQuantifiedExpression = false;
	
	static class FieldReceiverCache {
		private Map/*<SimpleFieldReference, CfgExpression>*/ cache = new HashMap/*<SimpleFieldReference, CfgExpression>*/();

		public void put(SimpleFieldReference fieldRef, CfgExpression receiver) {
			this.cache.put(fieldRef, receiver);
		}

		public CfgExpression get(SimpleFieldReference fieldRef) {
			Object result = this.cache.get(fieldRef);
			Utils.assertNotNull(result, "no value cached for '"+fieldRef.getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			Utils.assertTrue(result instanceof CfgExpression, "'"+fieldRef.getName()+"' isn't a CfgExpression but a '"+result.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return (CfgExpression) result;
		}
	}
	
	public GcProgram visit(SimpleProgram simpleProgram) {
		CfgBlock[] passified = new CfgBlock[simpleProgram.blocks.length];
		SimpleBlock[] sorted = simpleProgram.getSortedParentsFirst();
		simpleProgram.findParentsOfBlocks();
		Utils.assertTrue(sorted.length == passified.length, "arrays not equal length"); //$NON-NLS-1$
		HashMap/*<String, CfgBlock>*/ idToBlockMap = new HashMap/*<String, CfgBlock>*/();
		IncarnationMap allMap = new IncarnationMap();
		for (int i = 0; i < sorted.length; i++) {
			SimpleBlock block = sorted[i];

			// parents should be CfgBlocks...
			SimpleBlock[] simpleParents = block.getParents();
			CfgBlock[] parents = toCfgBlocks(simpleParents, idToBlockMap);
			if (parents.length > 1)
				handleJoinFromParents(parents);
			IncarnationMap incMap = getIncarnationMap(parents);
			CfgBlock passifiedBlock = block.accept(this, incMap);
			addIncMapToAllMap(incMap, allMap);
			Utils.assertTrue(passifiedBlock.blockId.equals(block.blockId), "blockIds don't match: passified '"+passifiedBlock.blockId+"' vs simple '"+block.blockId+"'");  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
			idToBlockMap.put(passifiedBlock.blockId, passifiedBlock);
			passified[i] = passifiedBlock;
		}
		return new GcProgram(passified, simpleProgram.startName, allMap, simpleProgram.methodIndicator);
	}

	private void addIncMapToAllMap(IncarnationMap incMap, IncarnationMap allMap) {
		Entry[] entries = (Entry[])incMap.entrySet().toArray(new Entry[0]);
		for (int i = 0; i < entries.length; i++) {
			SimpleAssignable var = (SimpleAssignable) entries[i].getKey();
			Set/*<Integer>*/ newSet = (Set) entries[i].getValue();
			Integer[] ints = (Integer[])newSet.toArray(new Integer[0]);
			for (int j = 0; j < ints.length; j++) {
				allMap.add(var, ints[j].intValue());
			}
		}
	}

	private static CfgBlock[] toCfgBlocks(SimpleBlock[] simpleParents, HashMap/*<String, CfgBlock>*/ map) {
		int length = simpleParents.length;
		CfgBlock[] result = new CfgBlock[length];
		for (int i = 0; i < result.length; i++) {
			Object value = map.get(simpleParents[i].blockId);
			Utils.assertNotNull(value, "value is null for "+simpleParents[i].blockId); //$NON-NLS-1$
			result[i] = (CfgBlock)(value);
		}
		return result;
	}

	private void handleJoinFromParents(CfgBlock[] parents) {
		SimpleAssignable[] assignables = getAssignablesFromParents(parents);
		for (int i = 0; i < assignables.length; i++) {
			SimpleAssignable assignable = assignables[i];
			Set/*<Integer>*/[] incarnations = getParentsIncarnations(assignable, parents);
			int newIncarnation = findMaxOfIntersection(incarnations);
			if (newIncarnation == -1) {
				newIncarnation = findMaxOfUnion(incarnations);
				for (int j = 0; j < parents.length; j++) {
					CfgBlock parent = parents[j];
					CfgAssignable lhs = getAssignable(assignable, newIncarnation);
					IncarnationMap parentIncarnationMap = parent.getIncarnationMap();
					int oldIncarnation = parentIncarnationMap.getMax(assignable);
					Utils.assertTrue(newIncarnation >= oldIncarnation, "newIncarnation("+newIncarnation+") < oldInc("+oldIncarnation+")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
					if (newIncarnation != oldIncarnation) {
						CfgExpression rhs = getAssignable(assignable, oldIncarnation);
						CfgExpression assignment = new CfgBinaryExpression(CfgOperator.EQUALS, lhs, rhs, TypeBinding.BOOLEAN, 0, 0);
						parent.addAssume(assignment);
						if (lhs.isField()) {
							Utils.assertTrue(lhs instanceof CfgFieldReference, "'"+lhs+"' isn't a field reference but a '"+lhs.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
							CfgFieldReference fieldRef = (CfgFieldReference) lhs;
							CfgExpression store = new CfgFieldStore(fieldRef, oldIncarnation, newIncarnation, rhs);
							parent.addAssume(store);
						}
						parentIncarnationMap.add(assignable, newIncarnation);
					}
				}
			}
		}
	}

	private CfgAssignable getAssignable(SimpleAssignable assignable, int incarnation) {
		CfgAssignable result;
		if (assignable.isVariable()) {
			SimpleVariable var = (SimpleVariable) assignable;
			result = new CfgVariable(var.name, var.pos, var.type, incarnation, 0, 0, var.isStaticField);
		} else {
			Utils.assertTrue(assignable.isField(), "'"+assignable.getName()+"' isn't a variable or a field"); //$NON-NLS-1$ //$NON-NLS-2$
			SimpleFieldReference field = (SimpleFieldReference) assignable;
			CfgExpression receiver = this.passifiedReceiverCache.get(field);
			result = new CfgFieldReference(receiver, field.field, incarnation, field.type, 0, 0);
		}
		Utils.assertTrue(result.incarnation() == incarnation, "'"+result.incarnation()+"' != '"+incarnation+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return result;
	}

	private IncarnationMap getIncarnationMap(CfgBlock[] parents) {
		SimpleAssignable[] vars = getAssignablesFromParents(parents);
		IncarnationMap result = new IncarnationMap();
		for (int i = 0; i < vars.length; i++) {
			SimpleAssignable var = vars[i];
			Set/*<Integer>*/[] incarnations = getParentsIncarnations(var, parents);
			int max = findMaxOfIntersection(incarnations);
			Utils.assertTrue(max >= 0, "max should be non-negative"); //$NON-NLS-1$
			result.put(var, max);
		}
		return result;
	}

	private Set/*<Integer>*/[] getParentsIncarnations(SimpleAssignable var, CfgBlock[] parents) {
		Set/*<Integer>*/[] result = new Set/*<Integer>*/[parents.length];
		for (int i = 0; i < parents.length; i++) {
			CfgBlock parent = parents[i];
			result[i] = parent.getIncarnationMap().get(var);
		}
		return result;
	}

	private SimpleAssignable[] getAssignablesFromParents(CfgBlock[] parents) {
		Set/*<SimpleVariable>*/ result = new HashSet();
		for (int i = 0; i < parents.length; i++) {
			CfgBlock parent = parents[i];
			Utils.assertNotNull(parent, "parent is null, probably because there's a cycle in the cfg..."); //$NON-NLS-1$
			IncarnationMap incarnationMap = parent.getIncarnationMap();
			Set keySet = incarnationMap.keySet();
			result.addAll(keySet);
		}
		return (SimpleAssignable[])result.toArray(new SimpleAssignable[0]);
	}

	// if the intersection of the incarnation sets is not empty, returns the largest element from the intersection
	// otherwise return -1;
	private int findMaxOfIntersection(Set/*<Integer>*/[] incarnations) {
		int result = 0;
		if (incarnations.length > 0) {
			Set/*<Integer>*/ intersection = new HashSet();
			intersection.addAll(nonempty(incarnations[0]));
			for (int i = 1; i < incarnations.length; i++) {
				intersection.retainAll(nonempty(incarnations[i]));
			}
			if (intersection.size() > 0) {
				result = Utils.max((Integer[])intersection.toArray(new Integer[0]));
			} else {
				result = -1;
			}
		}
		return result;
	}
	
	// is set is empty, return a new collection containing 0
	// otherwise, return set
	private Collection nonempty(Set set) {
		return (set.isEmpty()
			 ? Arrays.asList(new Integer[]{Utils.valueOf(0)})
			 : (Collection) set);
	}

	// returns the largest element from the union of the incarnation sets 
	private int findMaxOfUnion(Set/*<Integer>*/[] incarnations) {
		int result = 0;
		if (incarnations.length > 0) {
			Set/*<Integer>*/ union = new HashSet();
			for (int i = 0; i < incarnations.length; i++) {
				union.addAll(incarnations[i]);
			}
			result = Utils.max((Integer[])union.toArray(new Integer[0]));
		}
		return result;
	}

	public CfgBlock visit(SimpleBlock simpleBlock, IncarnationMap incarnationMap) {
		CfgStatement  cfgStmt = simpleBlock.stmt.accept(this, incarnationMap);
		return new CfgBlock(simpleBlock.blockId, cfgStmt, incarnationMap);
	}

	public CfgStatement visit(SimpleAssert simpleAssert, IncarnationMap incarnationMap) {
		List previousStmtsFromExprs = new ArrayList(this.stmtsFromExprs.asList());
		this.stmtsFromExprs.clear();

		CfgExpression expr = simpleAssert.pred.accept(this, incarnationMap);
		CfgStatement asrt = new CfgAssert(expr, simpleAssert.kind, simpleAssert.sourceStart);
		CfgStatement block = handlePossibleMethodCall(asrt);
		this.stmtsFromExprs.addAll(previousStmtsFromExprs);
		this.stmtsFromExprs.add(block);
		return this.getAssignmentsAsStatement();
	}

	public CfgStatement visit(SimpleAssume simpleAssume, IncarnationMap incarnationMap) {
		List previousStmtsFromExprs = new ArrayList(this.stmtsFromExprs.asList());
		this.stmtsFromExprs.clear();

		CfgExpression expr = simpleAssume.pred.accept(this, incarnationMap);
		CfgStatement assumes = new CfgAssume(expr, simpleAssume.sourceStart);
		CfgStatement block = handlePossibleMethodCall(assumes);
		
		this.stmtsFromExprs.addAll(previousStmtsFromExprs);
		this.stmtsFromExprs.add(block);
		return this.getAssignmentsAsStatement();
	}

	private CfgStatement handlePossibleMethodCall(CfgStatement stmt) {
		this.stmtsFromExprs.add(stmt);
		CfgStatement assignments = this.getAssignmentsAsStatement();
		CfgVarDecl[] varDecls = (CfgVarDecl[]) this.paramAndResultDecls.toArray(CfgVarDecl.EMPTY);
		this.paramAndResultDecls.clear();
		CfgStatement block = (this.translatedAMethodCall) 
		                   ? new CfgStatementBlock(assignments, varDecls)
		                   : assignments;
		this.translatedAMethodCall = false;
		return block;
	}

	private CfgExpression handlePossibleMethodCall(CfgExpression expr) {
		if (! (this.isInQuantifiedExpression && translatedAMethodCall))
			return expr;
		CfgStatement assignments = this.getAssignmentsAsStatement();
		CfgVarDecl[] varDecls = (CfgVarDecl[]) this.paramAndResultDecls.toArray(CfgVarDecl.EMPTY);
		this.paramAndResultDecls.clear();
		CfgExpression body = getHypotheseFromStatements(assignments, expr);
		CfgExpression result = CfgQuantifiedExpression.asBlock(body, varDecls);
		this.translatedAMethodCall = false;
		return result;
	}

	public CfgStatement visit(SimpleSequence simpleSequence, IncarnationMap incarnationMap) {
		CfgStatement stmt1 = simpleSequence.stmt1.accept(this, incarnationMap);
		CfgStatement stmt2 = simpleSequence.stmt2().accept(this, incarnationMap);
		return new CfgSequence(stmt1, stmt2);
	}

	public CfgStatement visit(SimpleHavoc simpleHavoc, IncarnationMap incarnationMap) {
		SimpleVariable simpleVar = simpleHavoc.var;
		CfgVariable var = (CfgVariable) simpleVar.accept(this, incarnationMap);
		int newIncarnation = 1 + incarnationMap.getMax(simpleVar);
		var.setIncarnation(newIncarnation);
		incarnationMap.put(simpleVar, newIncarnation);
		CfgExpression expr = new CfgBinaryExpression(CfgOperator.EQUALS, var, var, TypeBinding.BOOLEAN, simpleHavoc.sourceStart, simpleVar.sourceEnd);
		this.stmtsFromExprs.add(new CfgAssume(expr, expr.sourceStart));
		return this.getAssignmentsAsStatement();
	}

	public CfgStatement visit(SimpleVarDecl var, IncarnationMap incarnationMap) {
		CfgStatement result = new CfgVarDecl(var.name, var.pos, var.type, var.sourceStart);
		return result;
	}

	public CfgStatement visit(SimpleExprStatement simpleExprStatement, IncarnationMap incarnationMap) {
		CfgExpression expr = simpleExprStatement.expr.accept(this, incarnationMap);
		boolean typeTest = expr instanceof CfgAssignable
		                || expr instanceof CfgBooleanConstant;
		Utils.assertTrue(typeTest, "expr '"+expr.toString()+"' should be a CfgAssignable but is a '"+expr.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		//@ assert expr instanceof CfgVariable;
		return this.getAssignmentsAsStatement();
	}

	public CfgStatement visit(SimpleGoto simpleGoto, IncarnationMap incarnationMap) {
		Utils.assertTrue(this.stmtsFromExprs.isEmpty(), "stmtsFromExprs isn't empty"); //$NON-NLS-1$
		return new CfgGoto(simpleGoto.gotos);
	}

	public CfgExpression visit(SimpleAssignment simpleAssignment, IncarnationMap incarnationMap) {
		SimpleAssignable simpleLhs = simpleAssignment.lhs;
		boolean lhsIsNew = ! incarnationMap.containsKey(simpleLhs);
		CfgAssignable lhs = (CfgAssignable) simpleLhs.accept(this, incarnationMap);
		CfgExpression rhs = simpleAssignment.expr.accept(this, incarnationMap);
		int newIncarnation = lhsIsNew && simpleLhs.isVariable()
		                   ? 0
			               : 1 + incarnationMap.getMax(simpleLhs);
		int oldIncarnation = lhs.incarnation();
		lhs.setIncarnation(newIncarnation);
		incarnationMap.put(simpleLhs, newIncarnation);
		CfgExpression expr = new CfgBinaryExpression(CfgOperator.EQUALS, lhs, rhs, TypeBinding.BOOLEAN, simpleAssignment.sourceStart, rhs.sourceEnd);
		this.stmtsFromExprs.add(new CfgAssume(expr, expr.sourceStart));

		if (lhs.isField()) {
			CfgFieldReference field = (CfgFieldReference)lhs;
			CfgExpression store = new CfgFieldStore(field, oldIncarnation, newIncarnation, rhs);
			this.stmtsFromExprs.add(new CfgAssume(store, store.sourceStart));
		}
		
		return lhs;
	}

	public CfgExpression visit(SimpleBooleanConstant bool, IncarnationMap incarnationMap) {
		return new CfgBooleanConstant(bool.value, bool.sourceStart, bool.sourceEnd);
	}

	public CfgExpression visit(SimpleIntegerConstant intConst, IncarnationMap incarnationMap) {
		return new CfgIntegerConstant(intConst.value, intConst.sourceStart, intConst.sourceEnd);
	}

	public CfgExpression visit(SimpleVariable var, IncarnationMap incarnationMap) {
		return new CfgVariable(var.name, var.pos, var.type, incarnationMap.getMax(var), var.sourceStart, var.sourceEnd, var.isStaticField);
	}

	public CfgExpression visit(SimpleNotExpression notExpr, IncarnationMap incarnationMap) {
		CfgExpression expr = notExpr.expr.accept(this, incarnationMap);
		return new CfgNotExpression(expr, notExpr.sourceStart, notExpr.sourceEnd);
	}

	public CfgExpression visit(SimpleConditionalExpression condExpr, IncarnationMap incarnationMap) {
		CfgExpression condition = condExpr.condition.accept(this, incarnationMap);
		
		IncarnationMap ifTrueMap = incarnationMap.copy();
		IncarnationMap ifFalseMap = incarnationMap.copy();

		List/*<CfgStatement>*/ condList = this.getAndClearAssignments();

		CfgExpression valueIfTrue = condExpr.valueIfTrue.accept(this, ifTrueMap);
		List/*<CfgStatement>*/ ifTrueList = this.getAndClearAssignments();

		CfgExpression valueIfFalse = condExpr.valueIfFalse.accept(this, ifFalseMap);
		List/*<CfgStatement>*/ ifFalseList = this.getAndClearAssignments();

		this.stmtsFromExprs.addAll(condList);
		
		// at this point, ifTrueMap has the incarnation after evaluating valueIfTrue
		//                ifTrueList has the assignments created when passifying valueIfTrue
		// Mutatis mutandis for ifFalse
		// incarnationMap has the incarnation after evaluating condition
		if (ifTrueList.size() > 0 || ifFalseList.size() > 0) {
			reconcileMaps(incarnationMap, ifTrueMap, ifFalseMap, ifTrueList, ifFalseList);
			handleNewAssignmentsAndAsserts(condition, ifTrueList, ifFalseList);
		}
		return new CfgConditionalExpression(condition, valueIfTrue, valueIfFalse, condExpr.type, condExpr.sourceStart, condExpr.sourceEnd);
	}

	public String toString() {
		return this.stmtsFromExprs.toString();
	}

	private void handleNewAssignmentsAndAsserts(CfgExpression cond, List/*<CfgStatement>*/ ifTrueList, List/*<CfgStatement>*/ ifFalseList) {
		CfgExpression assumeIfTrue  = foldAssumes(ifTrueList);
		CfgExpression assumeIfFalse = foldAssumes(ifFalseList);
		CfgStatement assertIfTrue   = foldAsserts(cond, ifTrueList);
		CfgNotExpression notCond = new CfgNotExpression(cond, cond.sourceStart, cond.sourceEnd);
		CfgStatement assertIfFalse  = foldAsserts(notCond, ifFalseList);

		CfgStatement assumes = null;
		if (assumeIfTrue != CfgBooleanConstant.TRUE || assumeIfFalse != CfgBooleanConstant.TRUE) {
			CfgExpression pred = new CfgConditionalExpression(cond, assumeIfTrue, assumeIfFalse, TypeBinding.BOOLEAN, 0, 0);
			assumes = new CfgAssume(pred, 0);
		}
		if (assumes != null)
			this.stmtsFromExprs.add(assumes);
		if (assertIfTrue != CfgAssert.SKIP)
			this.stmtsFromExprs.add(assertIfTrue);
		if (assertIfFalse != CfgAssert.SKIP)
			this.stmtsFromExprs.add(assertIfFalse);
	}

	private CfgExpression foldAssumes(List/*<CfgStatement>*/ ifXList) {
		List/*<CfgStatement>*/ unfolded = CfgStatement.unfold(ifXList);
		CfgStatement[] stmts = (CfgStatement[]) unfolded.toArray(CfgStatement.EMPTY);
		List/*<CfgExpression>*/ assumes = new ArrayList/*<CfgExpression>*/();
		for (int i = stmts.length-1; i >= 0; i--) {
			CfgStatement stmt = stmts[i];
			if (stmt instanceof CfgAssume) {
				assumes.add(((CfgAssume) stmt).pred);
			} else {
				Utils.assertTrue(stmt instanceof CfgAssert
						      || stmt instanceof CfgVarDecl, "stmt('"+stmt+"') not an varDecl or assert"); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
		CfgExpression result = foldWithConjunction(assumes);
		return result;
	}

	private CfgStatement foldAsserts(CfgExpression cond, List/*<CfgStatement>*/ ifXList) {
		List/*<CfgStatement>*/ unfolded = CfgStatement.unfold(ifXList);
		CfgStatement[] stmts = (CfgStatement[]) unfolded.toArray(CfgStatement.EMPTY);
		List/*<CfgStatement>*/ asserts = new ArrayList/*<CfgStatement>*/();
		for (int i = stmts.length-1; i >= 0; i--) {
			CfgStatement stmt = stmts[i];
			if (stmt instanceof CfgAssert) {
				CfgAssert assertion = (CfgAssert) stmt;
				CfgExpression pred = assertion.pred;
				CfgExpression newPred = new CfgBinaryExpression(CfgOperator.IMPLIES, cond, pred, pred.type, pred.sourceStart, pred.sourceEnd);
				KindOfAssertion kind = assertion.kind;
				CfgAssert newAssertion = new CfgAssert(newPred, kind, stmt.sourceStart);
				asserts.add(newAssertion);
			} else {
				Utils.assertTrue(stmt instanceof CfgVarDecl
						      || stmt instanceof CfgAssume, "stmt('"+stmt+"') not an assume or varDecl"); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
		CfgStatement result = CfgSequence.fold(asserts);
		return result;
	}
	private CfgExpression foldWithConjunction(List/*<CfgExpression>*/ ifXList) {
		if (ifXList.size() == 0) return CfgBooleanConstant.TRUE;

		CfgExpression result=null;
		boolean first = true;
		for (Iterator iterator = ifXList.iterator(); iterator.hasNext();) {
			CfgExpression expr = (CfgExpression) iterator.next();
			if (first) {
				first = false;
				result = expr;
			} else {
				Utils.assertNotNull(result, "result is null"); //$NON-NLS-1$
				result = new CfgBinaryExpression(CfgOperator.AND, result, expr, TypeBinding.BOOLEAN, 0, 0);
			}
		}
		return result;
	}

	private void reconcileMaps(IncarnationMap incarnationMap, IncarnationMap ifTrueMap, IncarnationMap ifFalseMap, 
			List ifTrueList, List ifFalseList) {
		SimpleVariable[] vars = getVars(ifTrueMap, ifFalseMap);
		for (int i = 0; i < vars.length; i++) {
			SimpleVariable var = vars[i];
			Set/*<Integer>*/[] incarnations = getIncarnations(var, ifTrueMap, ifFalseMap);
			int max = findMaxOfIntersection(incarnations);
			if (max == -1) {
				max = findMaxOfUnion(incarnations);
				reconcile(var, max, incarnationMap, ifTrueMap,  ifTrueList);
				reconcile(var, max, incarnationMap, ifFalseMap, ifFalseList);
			}
		}
		setNewMap(vars, incarnationMap, ifTrueMap, ifFalseMap);
	}

	private void setNewMap(SimpleVariable[] vars, IncarnationMap finalMap, IncarnationMap ifTrueMap, IncarnationMap ifFalseMap) {
		finalMap.clear();
		for (int i = 0; i < vars.length; i++) {
			SimpleVariable var = vars[i];
			Set/*<Integer>*/[] incarnations = getIncarnations(var, ifTrueMap, ifFalseMap);
			int max = findMaxOfIntersection(incarnations);
			Utils.assertTrue(max >= 0, "max should be non-negative"); //$NON-NLS-1$
			finalMap.put(var, max);
		}
	}

	private void reconcile(SimpleVariable var, int max, IncarnationMap incarnationMap, IncarnationMap ifXMap, List ifXList) {
		CfgVariable lhs = new CfgVariable(var.name, var.pos, var.type, max+1, 0, 0, var.isStaticField);
		int oldInc = ifXMap.getMax(var);
		Utils.assertTrue(max+1 > oldInc, "max+1("+(max+1)+") <= oldInc("+oldInc+")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		CfgVariable rhs = new CfgVariable(var.name, var.pos, var.type, oldInc, 0, 0, var.isStaticField);
		CfgExpression expr = new CfgBinaryExpression(CfgOperator.EQUALS,lhs, rhs, TypeBinding.BOOLEAN, 0, 0);
		CfgAssume assignment = new CfgAssume(expr, 0);
		ifXList.add(assignment);
		ifXMap.add(var, max+1);
	}

	private SimpleVariable[] getVars(IncarnationMap ifTrueMap, IncarnationMap ifFalseMap) {
		List result = new ArrayList();
		result.addAll(ifTrueMap.keySet());
		result.addAll(ifFalseMap.keySet());
		return (SimpleVariable[]) result.toArray(new SimpleVariable[0]);
	}

	private Set[] getIncarnations(SimpleVariable var, IncarnationMap ifTrueMap, IncarnationMap ifFalseMap) {
		Set/*<Integer>*/[] result = new Set/*<Integer>*/[2];
		result[0] = ifTrueMap.get(var);
		result[1] = ifFalseMap.get(var);
		return result;
	}


	public CfgExpression visit(SimplePostfixExpression post, IncarnationMap incarnationMap) {
		SimpleAssignable simpleVar = post.lhs;
		CfgExpression assignableExpr = simpleVar.accept(this, incarnationMap);
		CfgAssignable assignable = (CfgAssignable) assignableExpr;
		int newIncarnation = 1 + incarnationMap.getMax(simpleVar);
		CfgAssignable lhs = assignable.withIncarnation(newIncarnation);
		incarnationMap.put(simpleVar, newIncarnation);
		CfgOperator operator = (post.operator == SimpleOperator.PLUS
							 ?  CfgOperator.PLUS
							 :  CfgOperator.MINUS);
		CfgExpression rhs = new CfgBinaryExpression(operator, assignable, CfgIntegerConstant.ONE, assignable.type, post.sourceStart, post.sourceEnd);
		CfgExpression expr = new CfgBinaryExpression(CfgOperator.EQUALS, lhs, rhs, TypeBinding.BOOLEAN, post.sourceStart, post.sourceEnd);
		this.stmtsFromExprs.add(new CfgAssume(expr, expr.sourceStart));
		return assignable;
	}

	public CfgExpression visit(SimpleBinaryExpression binExpr, IncarnationMap incarnationMap) {
		CfgExpression left = binExpr.left.accept(this, incarnationMap);
		if (this.isInQuantifiedExpression && left.type == TypeBinding.BOOLEAN)
			left = handlePossibleMethodCall(left);
		CfgExpression right = binExpr.right.accept(this, incarnationMap);
		if (this.isInQuantifiedExpression && right.type == TypeBinding.BOOLEAN)
			right = handlePossibleMethodCall(right);
		CfgOperator operator;
		TypeBinding type;
		if (binExpr.operator == SimpleOperator.AND) {
			operator = CfgOperator.AND;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.OR) {
			operator = CfgOperator.OR;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.EQUALS) {
			operator = CfgOperator.EQUALS;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.NOT_EQUALS) {
			operator = CfgOperator.NOT_EQUALS;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.GREATER) {
			operator = CfgOperator.GREATER;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.GREATER_EQUALS) {
			operator = CfgOperator.GREATER_EQUALS;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.LESS) {
			operator = CfgOperator.LESS;
	    	type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.LESS_EQUALS) {
			operator = CfgOperator.LESS_EQUALS;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.PLUS) {
			operator = CfgOperator.PLUS;
			type = left.type;
		} else if (binExpr.operator == SimpleOperator.MINUS) {
			operator = CfgOperator.MINUS;
			type = left.type;
		} else if (binExpr.operator == SimpleOperator.TIMES) {
			operator = CfgOperator.TIMES;
			type = left.type;
		} else if (binExpr.operator == SimpleOperator.DIVIDE) {
			operator = CfgOperator.DIVIDE;
			type = left.type;
		} else if (binExpr.operator == SimpleOperator.REMAINDER) {
			operator = CfgOperator.REMAINDER;
			type = left.type;
		} else if (binExpr.operator == SimpleOperator.IMPLIES) {
			operator = CfgOperator.IMPLIES;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.REV_IMPLIES) {
			operator = CfgOperator.REV_IMPLIES;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.EQUIV) {
			operator = CfgOperator.EQUIV;
			type = TypeBinding.BOOLEAN;
		} else if (binExpr.operator == SimpleOperator.NOT_EQUIV) {
			operator = CfgOperator.NOT_EQUIV;
			type = TypeBinding.BOOLEAN;
		} else {
			operator = null;
			type = null;
			Utils.assertTrue(false, "operator ("+binExpr+") not translated correctly");  //$NON-NLS-1$//$NON-NLS-2$
		}
		return new CfgBinaryExpression(operator, left, right, type, binExpr.sourceStart, binExpr.sourceEnd);
	}
	
	public CfgStatement getAssignmentsAsStatement() {
		CfgStatement result = CfgSequence.fold(this.getAndClearAssignments());
		if (useCfgSubstitutionVisitor)
			result = new CfgSubstitutionVisitor(this.map).visit(result);
		return result;
	}

	private List getAndClearAssignments() {
		List result = new ArrayList();
		result.addAll(this.stmtsFromExprs.asList());
		this.stmtsFromExprs.clear();
		return result;
	}

	public CfgExpression visit(SimpleQuantifiedExpression expr, IncarnationMap incarnationMap) {
		boolean previousIsInQuantifiedExpression = this.isInQuantifiedExpression ;
		this.isInQuantifiedExpression = true;
		CfgQuantifier quantifier = new CfgQuantifier(expr.quantifier.lexeme, expr.quantifier.type);
		int length = expr.boundVariables.length;
		CfgVarDecl[] boundVariables = new CfgVarDecl[length]; 
		for (int i = 0; i < length; i++) {
			SimpleVarDecl boundVariable = expr.boundVariables[i];
			CfgStatement result = boundVariable.accept(this, incarnationMap);
			Utils.assertTrue(result instanceof CfgVarDecl, "result is a '" + result.getClass() + "', expecting a CfgVarDecl");  //$NON-NLS-1$//$NON-NLS-2$
			boundVariables[i] = (CfgVarDecl)result;
		}
		List previousStmtsFromExprs = new ArrayList(this.stmtsFromExprs.asList());
		this.stmtsFromExprs.clear();
		final CfgExpression range = expr.range.accept(this, incarnationMap);
		final CfgExpression body = expr.body.accept(this, incarnationMap);
		final CfgExpression impRange;
		final CfgExpression impBody;
		if (body.type == TypeBinding.BOOLEAN) {
			impRange = range;
			CfgStatement[] hypotheses = this.stmtsFromExprs.toArray();
			impBody = getHypotheseFromStatements(hypotheses, body);
			this.stmtsFromExprs.clear();
			Utils.assertTrue(this.stmtsFromExprs.size() == 0, "this.stmtsFromExprs isn't empty"); //$NON-NLS-1$
		} else {
			CfgStatement[] hypotheses = this.stmtsFromExprs.toArray();
			impRange = getHypotheseFromStatements(range, hypotheses);
			this.stmtsFromExprs.clear();
			Utils.assertTrue(this.stmtsFromExprs.size() == 0, "this.stmtsFromExprs isn't empty"); //$NON-NLS-1$
			impBody = body;
		}
		this.stmtsFromExprs.addAll(previousStmtsFromExprs);
		CfgQuantifiedExpression result = new CfgQuantifiedExpression(quantifier, impRange, impBody, boundVariables, expr.type, expr.sourceStart, expr.sourceEnd);
		this.isInQuantifiedExpression = previousIsInQuantifiedExpression;
		return result;
	}

	private CfgExpression getHypotheseFromStatements(CfgExpression range, CfgStatement[] stmts) {
		stmts = CfgSequence.unfold(stmts);
		if (stmts.length == 0)
			return range;
		
		CfgStatement stmt = stmts[stmts.length - 1];
		CfgExpression result = CfgBooleanConstant.TRUE;
		if (stmt instanceof CfgAssume) {
			CfgExpression expr = ((CfgAssume)stmt).pred;
			result = expr;
		} else if (stmt instanceof CfgAssert) {
			CfgExpression expr = ((CfgAssert)stmt).pred;
			result = new CfgBinaryExpression(CfgOperator.AND, expr, result, TypeBinding.BOOLEAN, 0, 0);
		} else {
			Utils.assertTrue(stmt instanceof CfgVarDecl, "stmt is a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		for (int i = stmts.length - 2; i >= 0; i--) {
			stmt = stmts[i];
			if (stmt instanceof CfgAssume) {
				CfgExpression expr = ((CfgAssume)stmt).pred;
				result = new CfgBinaryExpression(CfgOperator.IMPLIES, expr, result, TypeBinding.BOOLEAN, 0, 0);
			} else if (stmt instanceof CfgAssert) {
				CfgExpression expr = ((CfgAssert)stmt).pred;
				result = new CfgBinaryExpression(CfgOperator.AND, expr, result, TypeBinding.BOOLEAN, 0, 0);
			} else {
				Utils.assertTrue(stmt instanceof CfgVarDecl, "stmt is a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
		result = new CfgBinaryExpression(CfgOperator.IMPLIES, range, result, TypeBinding.BOOLEAN, 0, 0);
		return result;
	}

	private CfgExpression getHypotheseFromStatements(CfgStatement stmt, CfgExpression body) {
		CfgStatement[] unfolded = (CfgStatement[]) stmt.unfold().toArray(CfgStatement.EMPTY);
		return getHypotheseFromStatements(unfolded, body);
	}
	private CfgExpression getHypotheseFromStatements(CfgStatement[] stmts, CfgExpression body) {
		stmts = CfgSequence.unfold(stmts);
		CfgExpression result = body;
		for (int i = stmts.length - 1; i >= 0; i--) {
			CfgStatement stmt = stmts[i];
			if (stmt instanceof CfgAssume) {
				CfgExpression expr = ((CfgAssume)stmt).pred;
				result = new CfgBinaryExpression(CfgOperator.IMPLIES, expr, result, TypeBinding.BOOLEAN, 0, 0);
			} else if (stmt instanceof CfgAssert) {
				CfgExpression expr = ((CfgAssert)stmt).pred;
				result = new CfgBinaryExpression(CfgOperator.AND, expr, result, TypeBinding.BOOLEAN, 0, 0);
			} else {
				Utils.assertTrue(stmt instanceof CfgVarDecl, "stmt is a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
		return result;
	}

	public CfgExpression visit(SimpleOldExpression oldExpr, IncarnationMap incarnationMap) {
		CfgExpression expr = oldExpr.expr.accept(this, incarnationMap);
		ZeroIncarnationVisitor visitor = new ZeroIncarnationVisitor();
		CfgExpression result = expr.accept(visitor);
		return result;
	}

	public CfgExpression visit(SimpleMessageSend msgSend, IncarnationMap incarnationMap) {
		SimpleStatement[][] declsAndInits = getParms(msgSend.selector, msgSend.countForLabels, msgSend.formalParams, msgSend.actualParams);
		SimpleVarDecl[] decls = (SimpleVarDecl[]) declsAndInits[0];
		SimpleExprStatement[] simpleInits = (SimpleExprStatement[]) declsAndInits[1];
		List/*<CfgStatement>*/ bindings = new ArrayList/*<CfgStatement>*/();
		List/*<CfgStatement>*/ previousStmtsFromExprs = this.stmtsFromExprs.asList();
		for (int i = 0; i < simpleInits.length; i++) {
			CfgStatement binding = simpleInits[i].accept(this, incarnationMap);
			bindings.add(binding);
			if (! useCfgSubstitutionVisitor) {
				CfgStatement decl = decls[i].accept(this, incarnationMap);
				this.paramAndResultDecls.add(decl);
				this.stmtsFromExprs.add(binding);
			}
		}
		previousStmtsFromExprs.addAll(this.stmtsFromExprs.asList());
		this.stmtsFromExprs.clear();
		this.stmtsFromExprs.addAll(previousStmtsFromExprs);
		CfgExpression result;
		if (msgSend.type == TypeBinding.VOID) {
			result = CfgBooleanConstant.TRUE;
		} else {
			result = getReturnVariable(msgSend);
			this.paramAndResultDecls.add(getReturnVarDecl(msgSend));
		}
		SimpleSubstVisitor substVisitor = new SimpleSubstVisitor(getReturnVariableName(msgSend), decls, msgSend.formalParams);
		SimpleExpression simpPre = msgSend.pre.accept(substVisitor);
		boolean previousProcessingContract = this.processingContract;
		CfgSubstitutionVisitor bindingSubstVisitor = new CfgSubstitutionVisitor(bindings);
		this.processingContract = true;
		CfgExpression preExpr = simpPre.accept(this, incarnationMap);
		if (useCfgSubstitutionVisitor)
			preExpr = preExpr.accept(bindingSubstVisitor);
		CfgStatement pre = previousProcessingContract
						 ? (CfgStatement) new CfgAssume(preExpr, preExpr.sourceStart)
						 : new CfgAssert(preExpr, KindOfAssertion.PRE, msgSend.sourceStart);
		if (previousProcessingContract) {
			Utils.assertTrue(pre.sourceStart != 0 || ((CfgAssert) pre).kind != KindOfAssertion.PRE, "pre@0"); //$NON-NLS-1$
		}
		this.stmtsFromExprs.add(pre);
		SimpleExpression simpPost = msgSend.post.accept(substVisitor);
		CfgExpression postExpr = simpPost.accept(this, incarnationMap);
		if (useCfgSubstitutionVisitor)
			postExpr = postExpr.accept(bindingSubstVisitor);
		this.processingContract  = previousProcessingContract;
		CfgStatement post = new CfgAssume(postExpr, postExpr.sourceStart);
		this.stmtsFromExprs.add(post);
		if (useCfgSubstitutionVisitor)
			this.map.putAll(bindingSubstVisitor.map);
		this.translatedAMethodCall = true;
		if (result instanceof CfgVariable && result.type == TypeBinding.BOOLEAN) {
			result = handlePossibleMethodCall(result);
			return result;
		} else
		return result;
	}

	private String getReturnVariableName(SimpleMessageSend msgSend) {
		String result = "return" + SEP + msgSend.selector+ SEP + msgSend.countForLabels; //$NON-NLS-1$
		return result;
	}

	private CfgVariable getReturnVariable(SimpleMessageSend msgSend) {
		String name = getReturnVariableName(msgSend);
		return new CfgVariable(name, 0, msgSend.type, 0, msgSend.sourceStart, msgSend.sourceEnd, false);
	}

	private CfgVarDecl getReturnVarDecl(SimpleMessageSend msgSend) {
		String name = getReturnVariableName(msgSend);
		return new CfgVarDecl(name, 0, msgSend.type, 0);
	}

	private SimpleVariable getReturnVariableAsSimpleVariable(SimpleMessageSend msgSend) {
		String name = getReturnVariableName(msgSend);
		return new SimpleVariable(name, 0, msgSend.type, 0, 0, false);
	}

	private SimpleStatement[][] getParms(String selector, int countForLabels, SimpleVarDecl[] formalParams, SimpleExpression[] actualParams) {
		SimpleStatement[] decls = new SimpleVarDecl[formalParams.length];
		SimpleStatement[] inits = new SimpleExprStatement[formalParams.length];
		for (int i = 0; i < formalParams.length; i++) {
			SimpleVarDecl formal = formalParams[i];
			SimpleExpression actual = actualParams[i];
			String name = formal.name + SEP + selector + SEP + countForLabels;
			int pos = formal.sourceStart;
			TypeBinding type = formal.type;
			SimpleVariable var = new SimpleVariable(name, pos, type, pos, pos, false);
			SimpleAssignment assignmentExpr = new SimpleAssignment(var, actual, actual.sourceStart, actual.sourceEnd);
			decls[i] = new SimpleVarDecl(name, pos, type, pos);
			inits[i] = new SimpleExprStatement(assignmentExpr);
		}
		SimpleStatement[][] result = new SimpleStatement[][]{decls, inits};
		return result;
	}

	public CfgExpression visit(SimpleFieldReference fieldRef, IncarnationMap incarnationMap) {
		CfgExpression receiver = fieldRef.receiver.accept(this, incarnationMap);
		this.passifiedReceiverCache.put(fieldRef, receiver);
		int incarnation = incarnationMap.getMax(fieldRef);
		return new CfgFieldReference(receiver, fieldRef.field, incarnation, fieldRef.type, fieldRef.sourceStart, fieldRef.sourceEnd);
	}

	public CfgExpression visit(SimpleSuperReference superRef, IncarnationMap incarnationMap) {
		return new CfgSuperReference(superRef.type, superRef.sourceStart, superRef.sourceEnd);
	}
	
	public CfgExpression visit(SimpleThisReference thisRef, IncarnationMap incarnationMap) {
		return new CfgThisReference(thisRef.type, thisRef.sourceStart, thisRef.sourceEnd);
	}

	public CfgExpression visit(SimpleArrayReference arrayRef, IncarnationMap incarnationMap) {
		CfgExpression receiver = arrayRef.receiver.accept(this, incarnationMap);
		CfgExpression position = arrayRef.position.accept(this, incarnationMap);
		int incarnation = incarnationMap.getMax(arrayRef);
		return new CfgArrayReference(receiver, position, incarnation, arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
	}

	public CfgExpression visit(SimpleArrayAllocationExpression arrayAlloc, IncarnationMap incarnationMap) {
		int length = arrayAlloc.dims.length;
		CfgExpression[] dims = new CfgExpression[length];
		for (int i = 0; i < dims.length; i++) {
			dims[i] = arrayAlloc.dims[i].accept(this, incarnationMap);
		}
		return new CfgArrayAllocationExpression(arrayAlloc.ids, dims, arrayAlloc.type, arrayAlloc.sourceStart, arrayAlloc.sourceEnd);
	}

}
