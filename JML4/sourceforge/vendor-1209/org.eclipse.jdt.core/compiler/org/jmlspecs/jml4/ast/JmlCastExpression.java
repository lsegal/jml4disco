package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.CastExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.BranchLabel;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.Scope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlCastExpression extends CastExpression {

	public final boolean isExplicitNonNull;
	public JmlCastExpression(Expression expression, Expression type, boolean isExplicitNonNull) {
		super(expression, type);
		this.isExplicitNonNull = isExplicitNonNull;
	}

	public int nullStatus(FlowInfo flowInfo) {
		if (this.isExplicitNonNull)
			return FlowInfo.NON_NULL;
		return super.nullStatus(flowInfo);
	}
	public boolean isDeclaredNonNull() {
		return this.isExplicitNonNull || super.isDeclaredNonNull();
	}

	protected void generateNullityTest(CodeStream codeStream,
									   BlockScope currentScope) {
		if (this.isExplicitNonNull && currentScope.compilerOptions().jmlRacEnabled) {
			generateNullityTest(codeStream, "java/lang/ClassCastException", "RAC: attempt to cast null to non-null failed"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}
	
	static void generateTestForNullity(BlockScope currentScope, CodeStream codeStream, String ref) {
		if (!currentScope.compilerOptions().jmlRacEnabled)
		   return;
		JmlCastExpression.generateNullityTest(codeStream, "java/lang/ClassCastException", "RAC: "+ref+" declared to be non-null"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public static void generateNullityTest(CodeStream codeStream, String exceptionType, String msg) {
		BranchLabel nonnullLabel = new BranchLabel(codeStream);
		codeStream.dup();
        codeStream.ifnonnull(nonnullLabel);
        codeStream.newClassFromName(exceptionType.toCharArray(), msg);
        codeStream.athrow();
        nonnullLabel.place();
	}

	/**
	 * @see org.eclipse.jdt.internal.compiler.ast.Expression#tagAsUnnecessaryCast(Scope, TypeBinding)
	 */
	public void tagAsUnnecessaryCast(Scope scope, TypeBinding castType) {
		if (this.isExplicitNonNull && !this.expression.isDeclaredNonNull()) {
			this.tagAsNeedCheckCast();
		} else {
		    super.tagAsUnnecessaryCast(scope, castType);
		}
	}
}