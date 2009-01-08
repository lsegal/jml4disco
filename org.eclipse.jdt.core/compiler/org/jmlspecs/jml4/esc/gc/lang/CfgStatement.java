package org.jmlspecs.jml4.esc.gc.lang;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public abstract class CfgStatement {
	
	public static final Object[] EMPTY = new CfgStatement[0];
	public final int sourceStart;

	public CfgStatement(int sourceStart) {
		this.sourceStart = sourceStart;
	}

	public abstract String toString();
	public abstract VC accept(WlpVisitor visitor, VC N);

	public List/*<CfgStatement>*/ unfold() {
		List/*<CfgStatement>*/ result = new ArrayList/*<CfgStatement>*/();
		result.add(this);
		return result;
	}
	public static List/*<CfgStatement>*/ unfold(List/*<CfgStatement>*/ list) {
		List/*<CfgStatement>*/ result = new ArrayList/*<CfgStatement>*/();
		for (Iterator iterator = list.iterator(); iterator.hasNext();) {
			CfgStatement stmt = (CfgStatement) iterator.next();
			result.addAll(stmt.unfold());
		}
		return result;
	}

}
