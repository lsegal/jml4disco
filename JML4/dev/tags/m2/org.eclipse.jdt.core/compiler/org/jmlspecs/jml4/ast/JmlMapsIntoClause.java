package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class JmlMapsIntoClause extends ASTNode implements JmlDataGroupClause {
	
	public final boolean isRedundant;
	public final JmlMemberFieldRef fieldRef;
	public final JmlGroupName[] groupNames;
	
	public JmlMapsIntoClause(boolean isRedundant,
			JmlMemberFieldRef fieldRef, JmlGroupName[] groupNames) {
		this.isRedundant = isRedundant;
		this.fieldRef = fieldRef;
		this.groupNames = groupNames;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		output.append("maps"); //$NON-NLS-1$
		if (this.isRedundant)
			output.append("_redundantly"); //$NON-NLS-1$
		output.append(" "); //$NON-NLS-1$
		this.fieldRef.print(indent, output);
		output.append(" \\into "); //$NON-NLS-1$
		for (int i=0; i<this.groupNames.length; i++) {
			if (i>0)
				output.append(", "); //$NON-NLS-1$
			this.groupNames[i].print(indent, output);
		}
		return output.append(";"); //$NON-NLS-1$
	}

}
