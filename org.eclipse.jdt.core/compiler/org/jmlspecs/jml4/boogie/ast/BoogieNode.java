package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

/**
 * 
 */
public class BoogieNode {
	private String data;
	private BoogieNode parent;
	private ASTNode astNode;
	protected ArrayList/*<BoogieNode>*/ children = new ArrayList();
	
	public BoogieNode(BoogieNode parent, ASTNode node, String data) {
		this.parent = parent;
		this.data = data;
		this.astNode = node;
	}
	
	public void addChild(BoogieNode node) {
		children.add(node);
	}
	
	public String toString() {
		return data;
	}
	
	public ASTNode getASTNode() {
		return astNode;
	}
	
	public BoogieNode getParent() {
		return parent;
	}
	
	public BoogieNode[] getChildren() {
		return (BoogieNode[])children.toArray();
	}
	
	public BoogieNode findByType(Class type) {
		if (getClass() == type) return this;
		if (parent == null) return null;
		if (parent.getClass() == type) return parent;
		return parent.findByType(type);
	}
}
