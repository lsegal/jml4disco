package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class BoogieProcedure extends BoogieNode {
	private ArrayList variables = new ArrayList();
	
	public BoogieProcedure(BoogieNode parent, ASTNode node) {
		super(parent, node, null);
	}
	
	public String toString() {
		String string = "procedure ... {"; //$NON-NLS-1$
		for (int i = 0; i < variables.size(); i++) {
			string += variables.toString();
		}
		for (int i = 0; i < children.size(); i++) {
			string += children.get(i).toString();
		}
		string += "}"; //$NON-NLS-1$
		
		return string;
	}
	
	public void addVariableDeclaration(BoogieNode node) {
		variables.add(node);
	}
}
