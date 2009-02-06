package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlSignalsOnlyClause extends JmlClause {

	public static final TypeReference[] EMPTY_TYPEREFS = new TypeReference[0];
	private static final TypeBinding[] EMPTY_TYPEBINDINGS = new TypeBinding[0];
	
	//@ public invariant typeRefs.length > 0 ^ expr == JmlKeywordExpression.NOTHING;
	public final TypeReference[] typeRefs;
	private TypeBinding[/*#@nullable*/] typeBindings;
	
	public JmlSignalsOnlyClause(JmlIdentifier clauseKeyword, JmlKeywordExpression keyword) {
		super(clauseKeyword, keyword);
		this.typeRefs = EMPTY_TYPEREFS;
		this.typeBindings = EMPTY_TYPEBINDINGS;
	}

	public JmlSignalsOnlyClause(JmlIdentifier clauseKeyword, TypeReference[] typeRefs) {
		super(clauseKeyword);
		this.typeRefs = typeRefs;
		this.typeBindings = new TypeBinding[typeRefs.length];
	}

	public void resolve(BlockScope scope) {
		TypeBinding throwable = scope.getJavaLangThrowable();
		for (int i = 0; i < this.typeRefs.length; i++) {
			this.typeBindings[i] = this.typeRefs[i].resolveTypeExpecting(scope, throwable);
		}
	}

	protected StringBuffer printClauseContent(StringBuffer output) {
		super.printClauseContent(output);
		for (int i = 0; i < this.typeRefs.length; i++) {
			if (i > 0)
				output.append(COMMA).append(SPACE);
			output.append(this.typeRefs[i]);
		}
		return output;
	}
}
