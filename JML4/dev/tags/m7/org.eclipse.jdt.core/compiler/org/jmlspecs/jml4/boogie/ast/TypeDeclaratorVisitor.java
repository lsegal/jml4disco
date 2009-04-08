package org.jmlspecs.jml4.boogie.ast;

/**
 * Makes sure all reference types have been declared
 */
public class TypeDeclaratorVisitor extends Visitor {
	public boolean visit(MapTypeReference term) {
		if (term.getScope().lookupType(term.getTypeName()) == null) {
			declareType(term);
		}
		return true;
	}

	public boolean visit(TypeReference term) {
		if (term.getScope().lookupType(term.getTypeName()) == null) {
			declareType(term);
		}
		return true;
	}
	
	private void declareType(TypeReference type) {
		type.getScope().addType(new TypeDeclaration(type, null, type.getScope()));
	}
}
