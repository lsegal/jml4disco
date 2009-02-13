package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryMessageSend extends TheoryExpression {

	public final TheoryExpression receiver;
	public final TheoryExpression[] arguments;

	public TheoryMessageSend(ASTNode base, Theory theory, TheoryExpression receiver, TheoryExpression[] arguments) {
		super(base, theory);
		this.receiver = receiver;
		this.arguments = arguments;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.receiver != null) {
				this.receiver.traverse(visitor);
			}
			if(this.arguments != null) {
				for(int i=0;i<this.arguments.length;i++)
					this.arguments[i].traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
