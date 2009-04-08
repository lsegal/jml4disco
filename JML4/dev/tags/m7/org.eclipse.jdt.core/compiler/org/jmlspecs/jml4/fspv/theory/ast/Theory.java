package org.jmlspecs.jml4.fspv.theory.ast;

import java.util.Vector;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;

public class Theory extends TheoryNode {

	public TheoryFieldDeclaration[] fields;
	public TheoryMethodDeclaration[] methods;

	public Theory(ASTNode base) {
		super(base, null);
//		this.fields = fields;
//		this.methods = methods;
	}

	public String getName() {
		TypeDeclaration typeDeclaration = (TypeDeclaration) this.base;
		return new String(typeDeclaration.name);
	}

	public TheoryFieldDeclaration[] getInstancefields() {
		Vector tmp = new Vector();
		for(int i=0;i<this.fields.length;i++)
			if(!this.fields[i].isStatic())
				tmp.add(this.fields[i]);
		TheoryFieldDeclaration[] result = new TheoryFieldDeclaration[tmp.size()];
		for(int i=0;i<result.length;i++)
			result[i]=(TheoryFieldDeclaration) tmp.elementAt(i);
		return result;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.fields != null) {
				for(int i=0;i<this.fields.length;i++)
					this.fields[i].traverse(visitor);
			}
			if(this.methods != null) {
				for(int i=0;i<this.methods.length;i++)
					this.methods[i].traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

	
}
