package org.jmlspecs.jml4.boogie;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;

public class BoogieVariableDeclFinderVisitor extends ASTVisitor {

	ArrayList locals = new ArrayList();
	
	public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		if (methodDeclaration.statements != null) {
			for(int i=0; i< methodDeclaration.statements.length; i ++) {
				methodDeclaration.statements[i].traverse(this, methodDeclaration.scope);
			}
		}
		return true;
	}
	public boolean visit(LocalDeclaration localDecl, BlockScope scope) {
		locals.add(localDecl);  
		return true;
	}
	public ArrayList getDecls() {
		return locals;
	}
}
