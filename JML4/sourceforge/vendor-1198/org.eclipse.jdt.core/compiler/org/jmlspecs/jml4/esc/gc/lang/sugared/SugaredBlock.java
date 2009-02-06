package org.jmlspecs.jml4.esc.gc.lang.sugared;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleBlock;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredBlock {

	private static final String[] NO_GOTOS = new String[0];
	public static final SugaredBlock[] EMPTY = new SugaredBlock[0];
	public final String blockId;
	public final SugaredStatement stmt;
	public final String[] gotos;

	public SugaredBlock(String blockId, SugaredStatement stmt) {
		Utils.assertNotNull(blockId, "blockId is null"); //$NON-NLS-1$
		this.blockId = blockId;
		this.stmt = stmt;
		this.gotos = getGotos(stmt);
		Utils.assertNotNull(gotos, "gotos is null"); //$NON-NLS-1$
	}

	public SugaredBlock(String blockId, SugaredStatement stmt, String[] gotos) {
		Utils.assertNotNull(blockId, "blockId is null"); //$NON-NLS-1$
		Utils.assertNotNull(gotos, "gotos is null"); //$NON-NLS-1$
		this.blockId = blockId;
		this.stmt = addGotos(stmt, gotos);
		this.gotos = gotos;
		String[] theGotos = getGotos(this.stmt);
		Utils.assertTrue(theGotos.length == gotos.length,
				"gotos not right size: \nstmt:"+Arrays.asList(theGotos)+"\ngotos:"+Arrays.asList(gotos)); //$NON-NLS-1$ //$NON-NLS-2$
		Set set = new HashSet();
		set.addAll(Arrays.asList(theGotos));
		set.retainAll(Arrays.asList(gotos));
		Utils.assertTrue(set.size() == gotos.length,
				"gotos not the same: \nstmt:"+Arrays.asList(theGotos)+"\ngotos:"+Arrays.asList(gotos)); //$NON-NLS-1$ //$NON-NLS-2$
	}

	private static String[] getGotos(SugaredStatement stmt) {
		while (stmt instanceof SugaredSequence) {
			stmt = ((SugaredSequence)stmt).stmt2();
		}
		if (stmt instanceof SugaredGoto) {
			return ((SugaredGoto)stmt).gotos;
		} else {
			return NO_GOTOS;
		}
	}

	private static SugaredStatement addGotos(SugaredStatement stmt, String[] gotos) {
		SugaredGoto gotoStmt = new SugaredGoto(gotos);
		if (stmt instanceof SugaredSequence) {
			SugaredSequence ptr = (SugaredSequence) stmt;
			while (ptr.stmt2() instanceof SugaredSequence) {
				ptr = (SugaredSequence)ptr.stmt2();
			}
			//TODO: both branches below have the same code. why?
			if (ptr.stmt2() instanceof SugaredGoto) {
			   ptr.setStmt2(gotoStmt);
			} else {
			   ptr.setStmt2(gotoStmt);
			}
			return stmt;
		} else if (stmt instanceof SugaredGoto) {
			return gotoStmt;
		} else {
			return new SugaredSequence(stmt, gotoStmt);
		}
	}
	public String toString() {
		return "[SugaredBlock: " + this.blockId + "\n\t" + //$NON-NLS-1$ //$NON-NLS-2$
			   this.stmt + "]"; //$NON-NLS-1$
	}

	public SimpleBlock accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredBlock[] accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredBlock[] accept(DesugarLoopVisitor visitor) {
		return visitor.visit(this);
	}
}