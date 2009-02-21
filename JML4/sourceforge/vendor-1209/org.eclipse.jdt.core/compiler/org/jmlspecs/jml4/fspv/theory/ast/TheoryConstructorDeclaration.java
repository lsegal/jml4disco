package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;

public class TheoryConstructorDeclaration extends TheoryMethodDeclaration {

	public TheoryConstructorDeclaration(ASTNode base, Theory theory, TheoryExpression pre, 
			TheoryExpression post, TheoryArgument[] arguments, TheoryLocalDeclaration[] locals, TheoryStatement[] statements) {
		super(base, theory, pre, post, arguments, locals, statements);
		// TODO Auto-generated constructor stub
	}

	public String getEnclosingType() {
		ConstructorDeclaration constructorDeclaration = (ConstructorDeclaration) this.base;
		String result = new String(constructorDeclaration.binding.declaringClass.sourceName);
		return result;
	}
	
	public String getName() {
		ConstructorDeclaration constructorDeclaration = (ConstructorDeclaration) this.base;
		String argTypes = ""; //$NON-NLS-1$
		for(int i=0;i<this.arguments.length;i++) {
			if(i+1 == this.arguments.length)
				argTypes += this.arguments[i].getType();
			else
				argTypes += this.arguments[i].getType() + "_"; //$NON-NLS-1$
		}
		String result = this.getEnclosingType() + "_" + new String(constructorDeclaration.selector) + "_" + argTypes; //$NON-NLS-1$ //$NON-NLS-2$
		return result;
	}
	
	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.precondition != null) {
				this.precondition.traverse(visitor);
			}
			if(this.postcondition != null) {
				this.postcondition.traverse(visitor);
			}
			if(this.arguments != null) {
				for(int i=0;i<this.arguments.length;i++)
					this.arguments[i].traverse(visitor);
			}
			if(this.locals != null) {
				for(int i=0;i<this.locals.length;i++)
					this.locals[i].traverse(visitor);
			}
			if(this.statements != null) {
				for(int i=0;i<this.statements.length;i++)
					this.statements[i].traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
