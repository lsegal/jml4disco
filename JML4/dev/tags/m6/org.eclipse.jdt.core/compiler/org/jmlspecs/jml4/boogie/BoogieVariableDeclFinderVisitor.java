package org.jmlspecs.jml4.boogie;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;

public class BoogieVariableDeclFinderVisitor extends ASTVisitor {

	ArrayList locals = new ArrayList();
	BoogieSymbolTable symbolTable;
	
	public BoogieVariableDeclFinderVisitor(BoogieSymbolTable symbolTable) {
		this.symbolTable = symbolTable;
	}
	
	public boolean visit(Block block, BlockScope scope) {
		symbolTable.enterScope(block);
		return true;
	}

	public void endVisit(Block block, BlockScope scope) {
		symbolTable.exitScope();
	}

	public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		if (methodDeclaration.statements != null) {
			for(int i=0; i< methodDeclaration.statements.length; i ++) {
				methodDeclaration.statements[i].traverse(this, methodDeclaration.scope);
			}
		}
		return true;
	}
	
	public boolean visit(LocalDeclaration localDecl, BlockScope scope) {
		String value = symbolTable.addSymbol(new String(localDecl.name));
		if (value != null) {
			locals.add(new Object[]{localDecl,symbolTable.getCurrentBlock()});
		}
		return true;
	}
	
	public ArrayList getDecls() {
		return locals;
	}
}