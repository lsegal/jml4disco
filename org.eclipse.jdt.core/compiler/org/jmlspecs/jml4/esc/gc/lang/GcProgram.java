package org.jmlspecs.jml4.esc.gc.lang;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class GcProgram {
	public final CfgBlock[] blocks;
	public final String startName;
	public IncarnationMap incarnations;
	public final String methodIndicator;

	public GcProgram(CfgBlock[] blocks, String startName, IncarnationMap incMap, String methodIndicator) {
		for (int i = 0; i < blocks.length; i++) {
			for (int j = i+1; j < blocks.length; j++) {
				Utils.assertTrue(!blocks[i].blockId.equals(blocks[j].blockId), "VCs' ids not unique '"+blocks[i].blockId+"' & '"+blocks[j].blockId+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			}
		}
		this.blocks = blocks;
		this.startName = startName;
		this.incarnations = incMap;
		this.methodIndicator = methodIndicator;
	}
	
 	public String toString() {
 		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.blocks.length; i++) {
			if(i!=0) result.append("\n"); //$NON-NLS-1$
			result.append(this.blocks[i]);
		}
		return result.toString();
	}

	public VcProgram accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}
}
