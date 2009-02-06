package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.util.Utils;

public class VcProgram implements Serializable{
	public final VC[] vcs;
	public final String startId;
	public final Map/*<String var, Integer>*/ incarnations;
	public final String methodIndicator;

	public VcProgram(VC[] vcs, String startId, Map/*<String var, Integer>*/ incarnations, String methodIndicator) {
		boolean foundStartId = false;
		for (int i = 0; i < vcs.length; i++) {
			if (vcs[i].getName().equals(startId)) {
				foundStartId = true;
			}
		}
		Utils.assertTrue(foundStartId, "startId is not the name of any vc"); //$NON-NLS-1$
		for (int i = 0; i < vcs.length; i++) {
			for (int j = i+1; j < vcs.length; j++) {
				Utils.assertTrue(!vcs[i].getName().equals(vcs[j].getName()), "VCs' ids "+i+" & "+j+" not unique '"+vcs[i].getName()+"' & '"+vcs[j].getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$ //$NON-NLS-5$
			}
		}
		this.vcs = vcs;
		this.startId = startId;
		this.incarnations = incarnations;
		this.methodIndicator = methodIndicator;
		VC.clearNameList();
	}

	public String toString() {
		StringBuffer vcsAsString = new StringBuffer();
		for (int i = 0; i < vcs.length; i++) {
			if (i > 0)
				vcsAsString.append(",\n\n"); //$NON-NLS-1$
			vcsAsString.append(vcs[i].toStringWithName());
		}
		return this.startId + ":\n["+vcsAsString.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	//@ requires this.vcs.length > 0;
	//@ ensures \result.length  == 1;
	public VC[] getAsSingleVC() {
		VC[] beqs = new VC[this.vcs.length];
		String okSuffix = "$ok"; //$NON-NLS-1$
		for (int i = 0; i < beqs.length; i++) {
			VC vc = this.vcs[i];
			String beqName = vc.getName() + okSuffix;
			VcVarDecl varDecl = new VcVarDecl(beqName, 0, TypeBinding.BOOLEAN, 0, 0);
			VcVariable var = new VcVariable(beqName, 0, TypeBinding.BOOLEAN, 0, 0, 0);
			beqs[i] = new VcLogicalExpression(VcOperator.EQUALS, var, vc, 0, 0);
			beqs[i].addDecl(varDecl);
		}
		VC assumptions = new VcAndNary(beqs, 0, 0);
		VcVariable var = new VcVariable(this.startId+okSuffix, 0, TypeBinding.BOOLEAN, 0, 0, 0);
		VC result = new VcLogicalExpression(VcOperator.IMPLIES, assumptions, var, 0, 0);
		return new VC[]{result};
	}

	public VC[] getAsSingleVC_old() {
		VC[] beqs = new VC[this.vcs.length];
		String okSuffix = "$ok"; //$NON-NLS-1$
		for (int i = 0; i < beqs.length; i++) {
			VC vc = this.vcs[i];
			String beqName = vc.getName() + okSuffix;
			VcVarDecl varDecl = new VcVarDecl(beqName, 0, TypeBinding.BOOLEAN, 0, 0);
			VcVariable var = new VcVariable(beqName, 0, TypeBinding.BOOLEAN, 0, 0, 0);
			beqs[i] = new VcLogicalExpression(VcOperator.EQUALS, var, vc, 0, 0);
			beqs[i].addDecl(varDecl);
		}
		VC result = beqs[beqs.length-1];
		for (int i = beqs.length-2; i >= 0; i--) {
			result = new VcAnd(beqs[i], result, 0, 0);
		}
		VcVariable var = new VcVariable(this.startId+okSuffix, 0, TypeBinding.BOOLEAN, 0, 0, 0);
		result = new VcLogicalExpression(VcOperator.IMPLIES, result, var, 0, 0);
		return new VC[]{result};
	}
	
	public VC[] getAsImplications() {
		VC inlined = inline();
		VC[] unfiltered = (VC[])inlined.vc2vcs().toArray(VC.EMPTY);
		VC[] result = removeUnneeded(unfiltered);
		Set/*<VcVarDecls>*/ varDecls = new HashSet/*<VcVarDecls>*/(inlined.decls());
		for (int i = 0; i < result.length; i++) {
			VC vc = result[i];
			vc = convertImplicationsToConjunctions(vc);
			result[i] = vc;
			List/*<VcVarDecls>*/ vcsDecls = vc.decls();
			for (Iterator iterator = varDecls.iterator(); iterator.hasNext();) {
				VcVarDecl varDecl = (VcVarDecl) iterator.next();
				if (! vcsDecls.contains(varDecl))
					vc.addDecl(varDecl);
			}
		}
		return result;
	}

	private VC convertImplicationsToConjunctions(VC vc) {
		List/*<VC>*/ conjuncts = new ArrayList/*<VC>*/();
		while (vc instanceof VcLogicalExpression && ((VcLogicalExpression)vc).operator == VcOperator.IMPLIES) {
			VC lhs = ((VcLogicalExpression)vc).left;
			conjuncts.add(lhs);
			vc = ((VcLogicalExpression)vc).right;
		}
		if (conjuncts.size() == 0)
			return vc;
		VC[] aConjuncts = (VC[]) conjuncts.toArray(VC.EMPTY);
		VcAndNary assumptions = new VcAndNary(aConjuncts, 0, 0);
		VcLogicalExpression result = new VcLogicalExpression(VcOperator.IMPLIES, assumptions, vc, 0, 0);
		return result;
	}

	public VC[] getAsImplications_old() {
		VC inlined = inline();
		VC[] unfiltered = (VC[])inlined.vc2vcs().toArray(VC.EMPTY);
		VC[] result = removeUnneeded(unfiltered);
		Set/*<VcVarDecls>*/ varDecls = new HashSet/*<VcVarDecls>*/(inlined.decls());
		for (int i = 0; i < result.length; i++) {
			VC vc = result[i];
			List/*<VcVarDecls>*/ vcsDecls = vc.decls();
			for (Iterator iterator = varDecls.iterator(); iterator.hasNext();) {
				VcVarDecl varDecl = (VcVarDecl) iterator.next();
				if (! vcsDecls.contains(varDecl))
					vc.addDecl(varDecl);
			}
		}
		return result;
	}
	
	// removes duplicates and those that end in "implies true"
	private VC[] removeUnneeded(VC[] unfiltered) {
		VC[] copy = new VC[unfiltered.length];
		System.arraycopy(unfiltered, 0, copy, 0, unfiltered.length);
		for (int i = 0; i < copy.length; i++) {
			copy[i].originalIndex = i;
		}
		Arrays.sort(copy);
		VC first = copy[0];
		for (int i = 1; i < copy.length; i++) {
			if (copy[i].equals(first))
				copy[i] = null;
			else
				first = copy[i];
		}
		List/*<VC>*/ filtered = new ArrayList/*<VC>*/();
		for (int i = 0; i < copy.length; i++) {
			VC vc = copy[i];
			if (vc != null && ! vc.endsInImpliesTrue())
				filtered.add(vc);
		}
		VC[] result = (VC[])filtered.toArray(VC.EMPTY);
		return result;
	}

	private VC inline() {
		Map/*<String, VC>*/ map = new HashMap/*<String, VC>*/();
//		List/*<VcVarDecl>*/ varDecls = new ArrayList/*<VcVarDecls>*/();
		for (int i = 0; i < this.vcs.length; i++) {
			String key = vcs[i].getName()+"$ok"; //$NON-NLS-1$
			VC value = vcs[i];
			map.put(key, value);
//			varDecls.addAll(vcs[i].getVarDecls());
		}
		VC start = (VC)map.get(this.startId+"$ok"); //$NON-NLS-1$
		VC result = start.inlineAndAddDecls(map);
//		for (Iterator iterator = varDecls.iterator(); iterator.hasNext();) {
//			VcVarDecl decl = (VcVarDecl) iterator.next();
//			result.addDecl(decl);
//		}
		return result;
	}
}
