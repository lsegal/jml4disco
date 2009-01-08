package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class JmlInGroupClause extends ASTNode implements JmlDataGroupClause {

	public final boolean isRedundant;
	public final JmlGroupName[] groupNames;

	public JmlInGroupClause(boolean isRedundant, JmlGroupName[] groupNames) {
		this.isRedundant = isRedundant;
		this.groupNames = groupNames;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		return null;
	}

}
