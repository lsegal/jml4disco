package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlSignalsOnlyClause extends JmlClause {
	
	public final TypeReference[] typeRefs; //if length is 0, then \nothing

	//@ requires typeRefs.length >= 1;
	//@ ensures  this.clauseKeyword == clauseKeyword;
	//@ ensures  this.typeRefs == typeRefs;
	public JmlSignalsOnlyClause(String clauseKeyword, boolean isRedundant, TypeReference[] typeRefs) {
		super(clauseKeyword, isRedundant);
		this.typeRefs = typeRefs;
	}

	//@ ensures  this.clauseKeyword == clauseKeyword;
	//@ ensures  this.typeRefs.length == 0;
	public JmlSignalsOnlyClause(String clauseKeyword, boolean isRedundant) {
		super(clauseKeyword, isRedundant);
		this.typeRefs = new TypeReference[0];
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		// Nothing to do
	}

	public void resolve(BlockScope scope) {
		TypeBinding throwable = scope.getJavaLangThrowable();
		for (int i = 0; i < this.typeRefs.length; i++) {
			this.typeRefs[i].resolveTypeExpecting(scope, throwable);
		}
	}
	
	public StringBuffer print(int indent, StringBuffer output) {
		output.append(clauseKeyword+SPACE);
		if (this.typeRefs.length > 0) {
			for (int i = 0; i < this.typeRefs.length; i++) {
				if (i>0)
					output.append(COMMA+SPACE);
				output.append(this.typeRefs[i]);
			}
		} else {
			output.append("\\nothing"); //$NON-NLS-1$
		}
		return output.append(SEMICOLON);
	}

}
