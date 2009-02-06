package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredVarDecl extends SugaredStatement {

	public final String name;
	public final int    pos;
	public final TypeBinding type;

	public SugaredVarDecl(String name, int pos, TypeBinding type, int sourceStart) {
		super(sourceStart);
		Utils.assertNotNull(name, "name is null"); //$NON-NLS-1$
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		this.name = name;
		this.pos =  pos;
		this.type = type;
	}

	public SimpleStatement accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredStatement accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredStatement accept(DesugarLoopVisitor visitor, SugaredStatement rest) {
		return visitor.visit(this, rest);
	}

	public String toString() {
		return "[SugaredVarDecl: "+this.name+" :: "+this.type.debugName()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
