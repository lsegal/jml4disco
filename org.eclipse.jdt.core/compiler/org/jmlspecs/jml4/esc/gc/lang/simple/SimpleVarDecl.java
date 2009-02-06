package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleVarDecl extends SimpleStatement {

	public static final SimpleVarDecl[] EMPTY = new SimpleVarDecl[0];
	public final String name;
	public final int    pos;
	public final TypeBinding type;

	public SimpleVarDecl(String name, int pos, TypeBinding type, int sourceStart) {
		super(sourceStart);
		Utils.assertNotNull(name, "name is null"); //$NON-NLS-1$
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		this.name = name;
		this.pos  = pos;
		this.type = type;
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public String toString() {
		return "[SugaredVarDecl: "+this.name+" :: "+this.type.debugName()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
