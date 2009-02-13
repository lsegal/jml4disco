package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.problem.AbortType;
import org.jmlspecs.jml4.compiler.JmlConstants;

public class JmlTypeDeclaration extends TypeDeclaration {

	private JmlInvariantForType[] invariantClauses = new JmlInvariantForType[0];	
	private JmlConstraintClause[] constraintClauses = new JmlConstraintClause[0];
	private JmlInitiallyClause[] initiallyClauses = new JmlInitiallyClause[0];
	private JmlRepresentsClause[] representsClauses = new JmlRepresentsClause[0];

	public JmlTypeDeclaration(CompilationResult compilationResult) {
		super(compilationResult);
	}

	//@ ensures  this.invariantClauses == clauses;
	public void setInvariantClauses(JmlInvariantForType[] clauses) {
		this.invariantClauses = clauses;
	}
	
	//@ ensures this.constraintClauses == clauses;
	public void setConstraintClauses(JmlConstraintClause[] clauses) {
		this.constraintClauses = clauses;
	}
	
	//@ ensures  this.initiallyClauses == clauses;
	public void setInitiallyClauses(JmlInitiallyClause[] clauses) {
		this.initiallyClauses = clauses;
	}
	
	public void setRepresentsClauses(JmlRepresentsClause[] clauses) {
		this.representsClauses  = clauses;
	}
	
	public void resolve() {
		super.resolve();
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE)
			return;

		for (int i = 0; i < invariantClauses.length; i++) {
			invariantClauses[i].resolve(this.staticInitializerScope, this.initializerScope);
		}
		for (int i = 0; i < constraintClauses.length; i++) {
			constraintClauses[i].resolve(this.staticInitializerScope, this.initializerScope);
		}		
		for (int i = 0; i < initiallyClauses.length; i++) {
			initiallyClauses[i].resolve(staticInitializerScope, initializerScope);
		}
		for (int i = 0; i < representsClauses.length; i++) {
			representsClauses[i].resolve(staticInitializerScope, initializerScope);
		}
	}
	public void analyseCode(CompilationUnitScope unitScope) {
		super.analyseCode(unitScope);
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_ANALYSIS)
			return;

		if (this.ignoreFurtherInvestigation)
			return;
		try {
			jmlAnalyseCode(new FlowContext(null, this), FlowInfo.initial(this.maxFieldCount));
		} catch (AbortType e) {
			this.ignoreFurtherInvestigation = true;
		}
	}
	public void jmlAnalyseCode(FlowContext flowContext, FlowInfo flowInfo) {
		for (int i = 0; i < invariantClauses.length; i++) {
			invariantClauses[i].analyseCode(this.staticInitializerScope, this.initializerScope, flowContext, flowInfo);
		}
		for (int i = 0; i < constraintClauses.length; i++) {
			constraintClauses[i].analyseCode(this.staticInitializerScope, this.initializerScope, flowContext, flowInfo);
		}
		for (int i = 0; i < initiallyClauses.length; i++) {
			initiallyClauses[i].analyseCode(staticInitializerScope, initializerScope, flowContext, flowInfo);
		}
		for (int i = 0; i < representsClauses.length; i++) {
			representsClauses[i].analyseCode(staticInitializerScope, initializerScope, flowContext, flowInfo);
		}
	}
	
	// this method generates checks for invariants only
	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		for (int i = 0; i < invariantClauses.length; i++) {
			invariantClauses[i].generateCheck(currentScope, methodDecl, codeStream);
		}
	}
	
	public void generateCheckForInitiallys(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		for (int i = 0; i < initiallyClauses.length; i++) {
			initiallyClauses[i].generateCheck(currentScope, methodDecl, codeStream);
		}
	}
	
	public Expression getInvariant() {
		List pres = new ArrayList(this.invariantClauses.length);
		for (int i = 0; i < this.invariantClauses.length; i++) {
			pres.add(this.invariantClauses[i].expr);
		}
		Expression result = JmlAstUtils.conjoin(pres);
		return result;
	}

}
