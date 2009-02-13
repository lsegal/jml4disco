package org.jmlspecs.jml4.boogie;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.ast.JmlLocalDeclaration;

public class BoogieLocalDeclaration extends JmlLocalDeclaration {

	public BoogieLocalDeclaration(LocalDeclaration arg) {
		super(arg.name, arg.sourceStart, arg.sourceEnd);
		type = arg.type;
		declarationSourceStart = arg.declarationSourceStart;
		declarationSourceEnd = arg.declarationSourceEnd;
		this.initialization = arg.initialization;
	}
	
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		visitor.visit(this, scope);
		visitor.endVisit(this, scope);
	}	

}
