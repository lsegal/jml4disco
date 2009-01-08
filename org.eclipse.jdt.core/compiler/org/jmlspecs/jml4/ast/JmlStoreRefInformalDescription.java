package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlStoreRefInformalDescription extends JmlStoreRef {

	private final JmlInformalExpression desc;

	//@ ensures this.desc == desc;
	public JmlStoreRefInformalDescription(JmlInformalExpression desc) {
		super();
		this.desc = desc;
	}

	public void resolve(BlockScope scope) {
		/* empty, since there's nothing to do for an informal description */
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		return this.desc.print(indent, output);
	}

	public FlowInfo analyseAssignment(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo, Assignment assignment,
			boolean isCompound) {
		// TODO Auto-generated method stub
		return null;
	}

	public void generateAssignment(BlockScope currentScope,
			CodeStream codeStream, Assignment assignment, boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}

	public void generateCompoundAssignment(BlockScope currentScope,
			CodeStream codeStream, Expression expression, int operator,
			int assignmentImplicitConversion, boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}

	public void generatePostIncrement(BlockScope currentScope,
			CodeStream codeStream, CompoundAssignment postIncrement,
			boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}

}
