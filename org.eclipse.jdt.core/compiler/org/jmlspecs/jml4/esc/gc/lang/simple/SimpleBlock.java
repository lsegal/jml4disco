package org.jmlspecs.jml4.esc.gc.lang.simple;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgBlock;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleBlock {
	public static final SimpleBlock[] EMPTY = new SimpleBlock[0];
	public final String blockId;
	public final SimpleStatement stmt;
	public final String[] gotos;
	private /*@nullable*/ SimpleBlock[] parents;

	public SimpleBlock(String blockId, SimpleStatement stmt, String[] gotos) {
		super();
		this.blockId = blockId;
		this.stmt = addGotos(stmt, gotos);
		this.gotos = gotos;
		Utils.assertNotNull(blockId, "blockId is null"); //$NON-NLS-1$
		Utils.assertNotNull(gotos, "gotos is null"); //$NON-NLS-1$
		SimpleStatement theStmt=this.stmt;
		while (theStmt instanceof SimpleSequence)
			theStmt = ((SimpleSequence)theStmt).stmt2();
		Utils.assertTrue(theStmt instanceof SimpleGoto, "last statement isn't a goto"); //$NON-NLS-1$
		String[] theGotos = ((SimpleGoto)theStmt).gotos;
		Utils.assertTrue(theGotos.length == gotos.length, "gotos not right size: \nstmt:"+Arrays.asList(theGotos)+"\ngotos:"+Arrays.asList(gotos)); //$NON-NLS-1$ //$NON-NLS-2$
		Set set = new HashSet();
		set.addAll(Arrays.asList(theGotos));
		set.retainAll(Arrays.asList(gotos));
		Utils.assertTrue(set.size() == gotos.length, "gotos not the same: \nstmt:"+Arrays.asList(theGotos)+"\ngotos:"+Arrays.asList(gotos)); //$NON-NLS-1$ //$NON-NLS-2$
	}

	private static SimpleStatement addGotos(SimpleStatement stmt, String[] gotos) {
		SimpleGoto gotoStmt = new SimpleGoto(gotos);
		if (stmt instanceof SimpleSequence) {
			SimpleSequence ptr = (SimpleSequence) stmt;
			while (ptr.stmt2() instanceof SimpleSequence) {
				ptr = (SimpleSequence)ptr.stmt2();
			}
			//TODO: both branches below have the same code. why?
			if (ptr.stmt2() instanceof SimpleGoto) {
			   ptr.setStmt2(gotoStmt);
			} else {
			   ptr.setStmt2(gotoStmt);
			}
			return stmt;
		} else if (stmt instanceof SimpleGoto) {
			return gotoStmt;
		} else {
			return new SimpleSequence(stmt, gotoStmt);
		}
	}

	public String toString() {
		return "[SimpleBlock: " + this.blockId + "\n\t" + //$NON-NLS-1$ //$NON-NLS-2$
			   this.stmt + "]\n"; //$NON-NLS-1$
	}

	public CfgBlock accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}
	
	public SimpleBlock[] getParents() {
		if (this.parents == null) {
			this.parents = SimpleBlock.EMPTY;
		}
		Utils.assertNotNull(this.parents, "this.parents has not been set for "+this.blockId); //$NON-NLS-1$
		return this.parents;
	}
	/*package*/ void setParents(SimpleBlock[] parents) {
		Utils.assertNotNull(parents, this.blockId+": parents can't be set to null"); //$NON-NLS-1$
		this.parents = parents;
	}

	public boolean isParentOf(SimpleBlock possibleChild) {
		for (int i=0; i<this.gotos.length; i++)
			if (this.gotos[i].equals(possibleChild.blockId))
				return true;
		return false;
	}

}
