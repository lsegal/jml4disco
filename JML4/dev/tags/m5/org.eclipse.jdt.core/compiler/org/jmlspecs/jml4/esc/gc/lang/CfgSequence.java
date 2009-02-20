package org.jmlspecs.jml4.esc.gc.lang;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgSequence extends CfgStatement {

	public final CfgStatement stmt1;
	public final CfgStatement stmt2;

	public CfgSequence(CfgStatement stmt1, CfgStatement stmt2) {
		super(stmt1.sourceStart);
		this.stmt1 = stmt1;
		this.stmt2 = stmt2;
	}

	public String toString() {
		return "[CfgSequence: " + this.stmt1 + " ;\n\t\t" + this.stmt2 + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public VC accept(WlpVisitor visitor, VC N) {
		return visitor.visit(this, N);
	}

	public static CfgStatement[] unfold(CfgStatement[] stmts) {
		List/*<CfgStatement>*/ result = unfold(Arrays.asList(stmts));
		return (CfgStatement[])result.toArray(CfgStatement.EMPTY);
	}
	
	public static List/*<CfgStatement>*/ unfold(List/*<CfgStatement>*/ stmts) {
		List/*<CfgStatement>*/ result = new ArrayList/*<CfgStatement>*/();
		for (Iterator iterator = stmts.iterator(); iterator.hasNext();) {
			CfgStatement stmt = (CfgStatement) iterator.next();
			if (stmt instanceof CfgSequence) {
				CfgSequence seq = (CfgSequence) stmt;
				result.addAll(unfold(Arrays.asList(new CfgStatement[]{seq.stmt1})));
				result.addAll(unfold(Arrays.asList(new CfgStatement[]{seq.stmt2})));
			} else {
				result.add(stmt);
			}
		}
		return result;
	}

	public static CfgStatement fold(List cfgStmts) {
		int size = cfgStmts.size();
		if (size == 0) return CfgAssert.SKIP;
		if (size == 1) return (CfgStatement) cfgStmts.get(0);
		CfgStatement result = (CfgStatement) cfgStmts.get(size - 1);
		for (int i = size - 2; i >= 0; i--) {
			result = new CfgSequence((CfgStatement) cfgStmts.get(i), result);
		}
		return result;
	}

	public List/*<CfgStatement>*/ unfold() {
		List/*<CfgStatement>*/ result = new ArrayList/*<CfgStatement>*/();
		List/*<CfgStatement>*/ firsts  = this.stmt1.unfold();
		List/*<CfgStatement>*/ seconds = this.stmt2.unfold();
		result.addAll(firsts);
		result.addAll(seconds);
		return result;
	}

}
