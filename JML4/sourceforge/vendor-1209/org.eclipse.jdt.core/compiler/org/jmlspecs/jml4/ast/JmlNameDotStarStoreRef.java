package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.lookup.JmlSpecialTypeBinding;

/**
 * Represents a JML store ref expression of the form
 * name.*, where name is a NameReference.
 * */
public class JmlNameDotStarStoreRef extends JmlMultiReferenceExpression {
	/* delegate can be a name reference or an arbitrary expression ... */
	private NameReference nameRef;

	public JmlNameDotStarStoreRef(NameReference nameRef) {
		this.sourceStart = nameRef.sourceStart;
		this.nameRef = nameRef;
	}

	public TypeBinding resolveType(BlockScope scope) {
		TypeBinding type = this.nameRef.resolveType(scope);
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
		return this.nameRef.printExpression(indent, output).append(".*"); //$NON-NLS-1$
	}
}
