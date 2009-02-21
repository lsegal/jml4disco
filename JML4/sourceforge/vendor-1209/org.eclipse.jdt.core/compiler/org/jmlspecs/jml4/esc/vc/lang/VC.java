package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;

public abstract class VC implements Comparable {

	public static final VC[] EMPTY = new VC[0];
	private /*@nullable*/ String name;
	
	public final TypeBinding type;
	public final int sourceStart;
	public final int sourceEnd;

	private /*@nullable*/ KindOfAssertion kindOfAssertion;
	protected int kindOfLabel;
	private boolean isImplication = false;
	//@ invariant label == kindOfAssertion <==> kindOfLabel == -1;
	private int labelStart = 0;

	public static final int NO_LBL = -1;
	public static final int NEGLBL =  1;
	
	public VC(TypeBinding type, /*@nullable*/ KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR_PRE && labelStart == 0), "LoopInv@0.b"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.PRE && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
//		Utils.assertTrue(sourceStart == 0 || sourceEnd == 0 || sourceStart <= sourceEnd, "source positions incorrect ("+sourceStart+">"+sourceEnd+")");   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		this.type = type;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.kindOfAssertion = kindOfAssertion;
		this.kindOfLabel = kindOfLabel;
		this.labelStart = labelStart;
	}

	public VC(TypeBinding type, int sourceStart, int sourceEnd) {
		this(type, null, NO_LBL, sourceStart, sourceEnd, 0);
	}

	public void setLabel(KindOfAssertion kindOfAssertion, int kindOfLabel, int labelStart) {
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR && labelStart == 0), "LoopInv@0.c"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR_PRE && labelStart == 0), "LoopInv@0.d"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.PRE && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
		this.kindOfAssertion = kindOfAssertion;
		this.kindOfLabel = kindOfLabel;
		this.labelStart  = labelStart;
	}

	public KindOfAssertion kindOfAssertion() {
		return this.kindOfAssertion;
	}

	public int kindOfLabel() {
		return this.kindOfLabel;
	}
	
	public int labelStart() {
		return this.labelStart;
	}

	public abstract String toString();
	public String toStringWithName() {
		String toString = this.toString();
		return (this.name == null)
		     ? toString
			 : this.name + ": " + toString; //$NON-NLS-1$
			
	}
	public abstract String accept(ProverVisitor visitor);

	public String acceptAsTerm(ProverVisitor visitor) {
		return accept(visitor);
	}
	private final List/*VcVarDecl*/ decls = new ArrayList();
	public List/*VcVarDecl*/ decls() {
		return this.decls;
	}
	public void addDecl(VcVarDecl decl) {
		if (! this.decls.contains(decl))
			this.decls.add(decl);
	}
	public void addDecls(List/*<VcVarDecl>*/ newDecls) {
		if (newDecls == decls())
			return;
		for (Iterator iterator = newDecls.iterator(); iterator.hasNext();) {
			VcVarDecl varDecl = (VcVarDecl) iterator.next();
			this.addDecl(varDecl);
		}
	}
	public String visitVarDecls(ProverVisitor visitor) {
		VcVarDecl[] varDecls = (VcVarDecl[])this.decls().toArray(new VcVarDecl[0]);
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < varDecls.length; i++) {
			result.append(varDecls[i].accept(visitor));
		}
		return result.toString();
	}
	public String declString() {
		return //(this.name == null ? "" : this.name + ": ") +
//			   (this.kindOfAssertion == null ? "" : "{"+this.kindOfAssertion.toString()+"}\n") + //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			   (this.decls.size() == 0 ? "" : this.decls.toString() + "\n"); //$NON-NLS-1$ //$NON-NLS-2$
	}
	public String getName() {
		return this.name;
	}
	public boolean hasName() {
		return this.name != null;
	}
	private static List/*<String>*/ names = new ArrayList/*<String>*/();
	public void setName(String name) {
		Utils.assertTrue(this.name==null, "trying to rename VC "+this.name); //$NON-NLS-1$
		Utils.assertTrue(! names.contains(name), "name '"+name+"' already exists"); //$NON-NLS-1$ //$NON-NLS-2$
		this.name = name;
	}
	/*package*/ static void clearNameList() {
		names.clear();
	}

	/*package*/ List/*<VC>*/ vc2vcs() {
		return Arrays.asList(new VC[]{this});
	}

	/*package*/ VC inlineAndAddDecls(Map map) {
		VC inlined = this.inline(map);
		inlined.addDecls(this.decls());
		return inlined;
	}
	/*package*/ abstract VC inline(Map map);
	public abstract int hashCode();
	public boolean endsInImpliesTrue() {
		return false;
	}

	private /*nullable*/ String asString;
	/*package*/ int originalIndex;
	private synchronized String asString() {
		if (this.asString == null) {
			this.asString = this.toString();
		}
		return this.asString;
	}
	public int compareTo(Object o) {
		if (o instanceof VC) {
			VC other = (VC)o;
			return this.asString().compareTo(other.asString());
		} else {
			return -1;
		}
	}
	// equality basically compares the toString()s
	public boolean equals(Object obj) {
		return this.compareTo(obj) == 0;
	}

	public VC negateLastImplication() {
		return new VcNot(this, this.sourceStart, this.sourceEnd);
	}

	public void markAsImplication() {
		this.isImplication = true;
	}

	public boolean isImplication() {
		return isImplication;
	}

}
