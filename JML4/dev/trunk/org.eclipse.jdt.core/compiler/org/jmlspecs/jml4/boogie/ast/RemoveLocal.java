package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

/* FIXME this entire class is not a good idea. Using RemoveLocal
 * during node traversal will cause destructive changes to the AST
 * that cannot be undone. Ideally there should be an extra block number
 * value in each VariableReference that obsoletes the need for this hack. 
 */
public class RemoveLocal extends Statement {
	private VariableReference reference;

	public RemoveLocal(VariableReference ref, Procedure proc) {
		super(null, proc);
		this.reference = ref;
	}
	
	public VariableReference getReference() {
		return reference;
	}
	
	public void removeLocal() {
		VariableDeclaration decl = getScope().lookupVariable(getReference().getName());
		if (decl != null) {
			getScope().getProcedureScope().getLocals().remove(decl);
		}
	}

	public void toBuffer(BoogieSource out) {
		// nothing
	}

	public void traverse(Visitor visitor) {
		// nothing
	}

}
