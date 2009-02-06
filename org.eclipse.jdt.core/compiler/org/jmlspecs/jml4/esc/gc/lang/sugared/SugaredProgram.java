package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleProgram;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredProgram {
	public final SugaredBlock[] blocks;
	public final String         startName;
	public final String         methodIndicator;

	public SugaredProgram(SugaredBlock[] blocks, String startName, String methodIdicator) {
		assertDistinceBlockIds(blocks);
		this.blocks = blocks;
		this.startName = startName;
		this.methodIndicator = methodIdicator;
	}

	private static void assertDistinceBlockIds(SugaredBlock[] blocks) {
		for (int i = 0; i < blocks.length; i++) {
			for (int j = i+1; j < blocks.length; j++) {
				Utils.assertTrue(! blocks[i].blockId.equals(blocks[j].blockId),
						"blockIds not distinct ("+i+", "+j+"): "+blocks[i].blockId); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			}
		}
	}

	public SugaredProgram accept(DesugarLoopVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredProgram accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}
	public SimpleProgram accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}
	public String toString() {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.blocks.length; i++) {
			if (i!=0)
				result.append("\n"); //$NON-NLS-1$
			result.append(this.blocks[i].toString());
		}
		return result.toString();
	}
}
