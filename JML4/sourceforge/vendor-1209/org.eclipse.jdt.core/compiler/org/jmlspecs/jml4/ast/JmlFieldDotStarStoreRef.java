package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.lookup.JmlSpecialTypeBinding;

public class JmlFieldDotStarStoreRef extends JmlMultiReferenceExpression {

	private Expression receiver;

	public JmlFieldDotStarStoreRef(Expression receiver) {
		this.receiver = receiver;
		this.sourceStart = receiver.sourceStart;
	}

	public TypeBinding resolveType(BlockScope scope) {
		TypeBinding type = this.receiver.resolveType(scope);
		if (type == null)
			return null;
		// FIXME: check that the receiver actually has fields ...
		// and that they are accessible.
		// Here is a partial attempt ...
		if (type instanceof ReferenceBinding) {
			ReferenceBinding rb = (ReferenceBinding)type;
			FieldBinding[] fields = rb.fields();
			if (fields.length == 0) {
				String msg = "Receiver has no fields"; //$NON-NLS-1$
				scope.problemReporter().jmlEsc2Error(msg, sourceStart, sourceEnd);
				return null;
			}
		}
		return JmlSpecialTypeBinding.MULTI_REFERENCE_MAYBE_WITH_INFORMAL_COMMENTS;
	}
	
	public StringBuffer printExpression(int indent, StringBuffer output) {
		this.receiver.printExpression(indent, output);
		return output.append(".*"); //$NON-NLS-1$
	}

}
