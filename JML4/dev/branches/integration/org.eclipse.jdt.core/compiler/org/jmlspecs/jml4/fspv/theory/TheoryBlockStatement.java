package org.jmlspecs.jml4.fspv.theory;

import org.jmlspecs.jml4.fspv.Fspv;

public class TheoryBlockStatement extends TheoryStatement {
	public static final TheoryBlockStatement EMPTY_BLOCK = new TheoryBlockStatement(TheoryStatement.EMPTY);
	public TheoryStatement [] statements;

	public TheoryBlockStatement(TheoryStatement [] statements) {
		this.statements = statements;
	}
	
	public String toString() {
		return Fspv.pretyPrintArray(this.statements);
	}

	public int size() {
		return this.statements.length;
	}

	public TheoryStatement statementAt(int i) {
		return this.statements[i];
	}

	public static TheoryBlockStatement Merge(
			TheoryBlockStatement prestateAssignments, TheoryBlockStatement block) {
		int newBodySize = prestateAssignments.size() + block.size();
		TheoryStatement [] body = new TheoryStatement[newBodySize];
		for(int i=0; i<prestateAssignments.size();i++)
			body[i] = prestateAssignments.statementAt(i);
		for(int i=0; i<block.size(); i++)
			body[prestateAssignments.size()+i] = block.statementAt(i);
		return new TheoryBlockStatement(body);
	}

	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
