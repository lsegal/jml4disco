package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlCompilationUnitDeclaration extends CompilationUnitDeclaration {
	private Nullity defaultNullity;

	public JmlCompilationUnitDeclaration(ProblemReporter problemReporter,
			CompilationResult compilationResult, int sourceLength, Nullity nullity) {
		super(problemReporter, compilationResult, sourceLength);
		this.defaultNullity = nullity;
	}

	public JmlCompilationUnitDeclaration(ProblemReporter problemReporter,
			CompilationResult compilationResult, int sourceLength) {
		super(problemReporter, compilationResult, sourceLength);
		this.defaultNullity = Nullity._default;
	}

	public void setDefaultNullity(Nullity nullity) {
		this.defaultNullity = nullity;
	}
	
	public Nullity getDefaultNullity() {
		return this.defaultNullity;
	}
	protected void nullOutScope(TypeDeclaration type) {
		// Don't do this for JML declarations ... unless
		// jmlEnabled is false, in which case act as if 
		// this were a regular compilation unit.
		if(!this.problemReporter.options.jmlEnabled) 
			super.nullOutScope(type);
	}

	public StringBuffer print(int indent, StringBuffer output){
		if (JmlAstUtils.useSupersToStringMethod)
			return super.print(indent, output);
		return super.print(indent, output.append(this.defaultNullity.toString()+" ")); //$NON-NLS-1$
	}

	public void traverse(ASTVisitor visitor, CompilationUnitScope unitScope) {
		if (ignoreFurtherInvestigation)
			return;
		if(visitor.visit(this, this.scope)) {
			super.traverse(visitor, this.scope);
		}
		visitor.endVisit(this, this.scope);
	}

	
}
