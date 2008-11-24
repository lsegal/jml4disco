package org.jmlspecs.jml4.esc.provercoordinator.prover.simplify;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverAdapter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.util.Logger;

public class SimplifyAdapter extends ProverAdapter {

	private static final boolean DEBUG = false;
	// private static final String  SIMPLIFY = "C:\\bin\\ssh.exe -p 4022 chalin@localhost simplify"; //$NON-NLS-1$
	private static final String  SIMPLIFY = "simplify"; //$NON-NLS-1$

	public SimplifyAdapter(CompilerOptions options, ProblemReporter problemReporter) {
		super(options, problemReporter);
	}

	public Result[] prove(VC vc, Map incarnations) {
		SimplifyVisitor visitor = new SimplifyVisitor();
		String simplifyString = vc.accept(visitor);
		String response = proveWithSimplify(simplifyString);
		Result[] result = formatResponse(response, vc, simplifyString);
		return result;
	}
	
	private String proveWithSimplify(String simplifyString) {
		Process process = getProverProcess();
		if (process == null) {
			// FIXME: NO more problem reported :(
			// DISCO distributed strategy reporter = null
			if (this.problemReporter != null)
				this.problemReporter.jmlEsc2Error(failedToLaunch(), 0, 0);
			return ""; //$NON-NLS-1$
		}
		
		StringBuffer result = new StringBuffer();
		try {
			OutputStream out = process.getOutputStream();
			String ubp = SimplifyBackgroundPredicate.get();
			out.write(ubp.getBytes());
			out.write(simplifyString.getBytes());
			out.close();
			InputStream in = process.getInputStream();
			BufferedReader bIn = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bIn.readLine()))
				result.append(line + "\n"); //$NON-NLS-1$
			bIn.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return result.toString();
	}
	
	public static /*@nullable*/Process getProverProcess() {
		try {
			return Runtime.getRuntime().exec(SIMPLIFY);
		} catch (IOException e) {
			if (DEBUG) {
				Logger.print(failedToLaunch());
				Logger.print(e.toString());
			}
		} catch (SecurityException e) {
			if (DEBUG) {
				Logger.print(failedToLaunch());
				Logger.print(e.toString());
			}
		}
		return null;
	}

	private static final String INVALID_REPONSE = "1: Invalid."; //$NON-NLS-1$
	private static final String LABELS_MARKER = "labels: ("; //$NON-NLS-1$
	private static final String VALID_RESPONSE = "1: Valid."; //$NON-NLS-1$
	public Result[] formatResponse(String fromProver, VC vc, String simplifyString) {
		List/*<Result>*/ result = new ArrayList/*<Result>*/();
		if (fromProver.indexOf(VALID_RESPONSE) > 0) {
			result.add(Result.VALID[0]);
		} else if (fromProver.indexOf(INVALID_REPONSE) > 0) {
			if (fromProver.indexOf(LABELS_MARKER) > 0) {
				int labelsStart = fromProver.indexOf(LABELS_MARKER) + LABELS_MARKER.length();
				int labelsEnd = fromProver.indexOf(")", labelsStart); //$NON-NLS-1$
				String line = fromProver.substring(labelsStart, labelsEnd);
				String[] labels = line.split(" "); //$NON-NLS-1$
				List/*<Integer>*/ whatList = new ArrayList/*<Integer>*/();
				int what = -1;
				while ((what = getWhat(labels, what+1)) < labels.length) {
					whatList.add(new Integer(what));
				}
				int[] whats = new int[whatList.size()];
				int i = 0;
				for (Iterator iterator = whatList.iterator(); iterator.hasNext();) {
					what = ((Integer) iterator.next()).intValue();
					whats[i++] = what;
				}
				sortWhats(labels, whats, simplifyString);
				getProblems(simplifyString, labels, whats, result);
				if (result.size() == 0) {
					getProblems(simplifyString, labels, result);
				}
			} else {
					Result unknownError = getResultForUnknownError(vc);
					result.add(unknownError);
			}
		} else {
			Logger.print(fromProver);
			Result unknownError = getResultForUnknownError(vc);
			result.add(unknownError);
		}
		return (Result[])result.toArray(Result.EMPTY);
	}

	private Result getResultForUnknownError(VC vc) {
		int start = vc.sourceStart;
		int end = vc.sourceEnd;
		Result unknownError = new Result(KindOfAssertion.UNKNOWN, start, start, end);
		return unknownError;
	}

	private void sortWhats(String[] labels, int[] whats, String simplifyString) {
		// do a simple bubble sort for now
		int n = whats.length;
		boolean swapped;
		do {
		   swapped = false;
		   for (int i=0; i<n-1; i++) {
			   int i0_pos = simplifyString.indexOf(labels[whats[i]]); 
			   int i1_pos = simplifyString.indexOf(labels[whats[i+1]]); 
			   if (i0_pos > i1_pos) {
				   int temp = whats[i];
				   whats[i] = whats[i+1];
				   whats[i+1] = temp;
				   swapped = true;
			   }
		   }
		} while (swapped);
	}

	private void getProblems(String simplifyString, String[] labels, int[] whats, List results) {
		String string = simplifyString;
		for (int i = whats.length-1; i >= 0; i--) {
			String label = labels[whats[i]];
			int posLabel = string.indexOf(label);
			Utils.assertTrue(posLabel >= 0, "problem not found"); //$NON-NLS-1$
			int regionStart = string.lastIndexOf('(', posLabel);
			Utils.assertTrue(regionStart >= 0, "region start not found"); //$NON-NLS-1$
			int regionEnd = findRegionEnd(string, posLabel);
			Utils.assertTrue(regionEnd >= 0, "region end not found"); //$NON-NLS-1$
			String region = string.substring(regionStart, regionEnd+1);
			Utils.assertTrue(string.length() == region.length() 
					+ string.substring(0, regionStart).length() 
					+ string.substring(regionEnd+1).length(), 
					"lengths not correct"); //$NON-NLS-1$
			string = string.substring(0, regionStart) + string.substring(regionEnd+1);
			Result result = findResult(labels, whats[i], region);
			if (result != null)
			   results.add(result);
		}
	}

	// we didn't find a "what", so we hope there's something in the lables that matches...
	private void getProblems(String simplifyString, String[] labels, List results) {
		for (int i = 0; i < labels.length; i++) {
			Result result = labelToResult(simplifyString, labels[i]);
			if (result != null)
				results.add(result);
		}
	}

	// for now, just say it's an assert at the label
	private Result labelToResult(String simplifyString, String label) {
		if (label.startsWith("|Assert") || label.startsWith("|Postcondition")) //$NON-NLS-1$ //$NON-NLS-2$
			return null;
		int[] where = getWhere(label.substring(label.indexOf('@')+1, label.length()-1));
		Result result = new Result(KindOfAssertion.ASSERT, -1, where[0], where[1]);
		return result;
	}

	private int findRegionEnd(String string, int startPos) {
		int result = startPos;
		int openParens = 1;
		while (openParens > 0) {
			result++;
			char c = string.charAt(result);
			if (c == ')')
				openParens--;
			else if (c == '(')
				openParens++;
		}
		return result;
	}

	private /*@nullable*/ Result findResult(String[] labels, int what, String region) {
		KindOfAssertion kind = KindOfAssertion.fromString(getLabelName(labels[what]));
		int   aWhere = getLabelPosition(labels[what]);
		int[] eWhere = getWhere(labels, region);
		if (eWhere == null)
			return null;
		return new Result(kind, aWhere, eWhere[0], eWhere[1]);
	}

	private String getLabelName(String label) {
		String result = label.split("@")[0].substring(1); //$NON-NLS-1$
		return result;
	}

	private int getLabelPosition(String label) {
		String sWhere = label.split("@")[1]; //$NON-NLS-1$
		sWhere = sWhere.substring(0, sWhere.length()-1);
		int result = Utils.parseInt(sWhere, 0);
		return result;
	}

	private static final Set/*<String>*/ WHATS = new HashSet/*<String>*/();
	static {
		KindOfAssertion[] all = KindOfAssertion.all();
		for (int i = 0; i < all.length; i++) {
			WHATS.add(all[i].description);
		}
	}
	
	// returns the index in the array of labels for the type of problem
	private int getWhat(String[] labels, int startingPoint) {
		for (int i = startingPoint; i < labels.length; i++) {
			String what = getLabelName(labels[i]);
			if (WHATS.contains(what) && !labels[i].endsWith("@0|")) { //$NON-NLS-1$
				return i;
			}
		}
		return labels.length + 1;
	}
	
	private static final Set IGNORED_LABEL_NAMES = new HashSet();
	static {
		IGNORED_LABEL_NAMES.addAll(WHATS);
		IGNORED_LABEL_NAMES.add("Assume"); //$NON-NLS-1$
//		IGNORED_LABEL_NAMES.add("eq"); //$NON-NLS-1$
//		IGNORED_LABEL_NAMES.add("var"); //$NON-NLS-1$
		IGNORED_LABEL_NAMES.add("and"); //$NON-NLS-1$
		IGNORED_LABEL_NAMES.add("implies"); //$NON-NLS-1$
	}
	
	private int[] getWhere(String s) {
		String[] pos = s.split("_"); //$NON-NLS-1$
		Utils.assertTrue(pos.length==2, "malformed label: '"+s+"'");  //$NON-NLS-1$//$NON-NLS-2$
		int labelStart = Utils.parseInt(pos[0], 0);
		int labelEnd   = Utils.parseInt(pos[1], labelStart);
		return new int[]{labelStart, labelEnd};
/*
		Utils.assertTrue(pos.length==1 || pos.length==2, "malformed label: '"+s+"'");  //$NON-NLS-1$//$NON-NLS-2$
		int labelStart;
		int labelEnd;
		if (pos.length == 2) {
			labelStart = Utils.parseInt(pos[0], 0);
			labelEnd   = Utils.parseInt(pos[1], labelStart);
		} else {
			labelStart = Utils.parseInt(pos[0], 0);
			labelEnd   = labelStart;
		}
*/
	}

	// returns the position of the error as an underscore-separated pair of integers
	private /*@nullable*/ int[] getWhere(String[] labels, String region) {
		
		int sourceStart = Integer.MAX_VALUE;
		int sourceEnd = 0;
		for (int i = 0; i < labels.length; i++) {
			if (region.indexOf(labels[i])<0)
			   continue;
			String[] label = labels[i].substring(1, labels[i].length()-1).split("@"); //$NON-NLS-1$
			String name  = label[0];
			if (IGNORED_LABEL_NAMES.contains(name))
				continue;
			String second = label[1];
			String[] pos = second.split("_"); //$NON-NLS-1$
			Utils.assertTrue(pos.length==2, "malformed label: '"+labels[i]+"'");  //$NON-NLS-1$//$NON-NLS-2$
			int labelStart = Utils.parseInt(pos[0], 0);
			int labelEnd   = Utils.parseInt(pos[1], labelStart);
			if (labelStart == 0 && labelEnd == 0)
				continue;
			Utils.assertTrue(labelStart != 0 && labelEnd != 0, "only 1 is 0: '"+region+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			if (labelStart < sourceStart) sourceStart = labelStart;
			if (sourceEnd  < labelEnd)   sourceEnd   = labelEnd;
		}
		if (sourceStart == Integer.MAX_VALUE && sourceEnd == 0) {
			// nothing set
			return null;
		}
		return new int[] {sourceStart, sourceEnd};
	}
	
	private static String failedToLaunch() {
		return "failed to launch " + SIMPLIFY; //$NON-NLS-1$
	}

}
