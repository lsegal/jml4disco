package org.jmlspecs.jml4.esc.gc.lang;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcVarDecl;

public class CfgVarDecl extends CfgStatement {

	public static final CfgVarDecl[] EMPTY = new CfgVarDecl[0];
	public final String name;
	public final int    pos;
	public final TypeBinding type;

	public CfgVarDecl(String name, int pos, TypeBinding type, int sourceStart) {
		super(sourceStart);
		Utils.assertNotNull(name, "name is null"); //$NON-NLS-1$
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		this.name = name;
		this.pos  = pos;
		this.type = type;
	}

	public VC accept(WlpVisitor visitor, VC N) {
		VC decl = visitor.visit(this);
		Utils.assertTrue(decl instanceof VcVarDecl, "vc not a VcVarDecl but a '"+decl.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		N.addDecl((VcVarDecl)decl);
		return N;
	}

	public String toString() {
		return "[CfgVarDecl: "+this.name+" :: "+this.type.debugName()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
