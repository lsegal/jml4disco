package org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverAdapter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.util.Logger;

public class IsabelleAdapter extends ProverAdapter {

	private static final String THEORY_EXTENSION = ".thy"; //$NON-NLS-1$
	private static final boolean DEBUG = false;
	private static final String ISABELLE_VALID_1 = "\nlemma\n  main:"; //$NON-NLS-1$
	private static final String ISABELLE_VALID_2 = "\nlemma main: "; //$NON-NLS-1$
	private static final String OOPS = "  oops"; //$NON-NLS-1$
	private static final String VALID_EOF_1 = "  main:"; //$NON-NLS-1$
	private static final String VALID_EOF_2 = "lemma main:"; //$NON-NLS-1$
	private static final String ERROR = "*** Failed to finish proof (after successful terminal method)"; //$NON-NLS-1$

	public IsabelleAdapter(CompilerOptions options,
			ProblemReporter problemReporter) {
		super(options, problemReporter);
		processPool = IsabelleProcessPool.getInstance();
	}

	public Result[] prove(VC vc, Map incarnations) {
		// First bogus entry is used up by user supplied theory file (if it
		// exists).
		String[] proofMethods = new String[] {
				"OUA-ESC", "by ((simp add: nat_number | auto | algebra)+)" }; //$NON-NLS-1$//$NON-NLS-2$
		String theoryFilePathWithoutExt = vc.getName();
		IsabelleVisitor visitor = new IsabelleVisitor(theoryFilePathWithoutExt);
		String theoryFilePath = theoryFilePathWithoutExt + THEORY_EXTENSION;

		Result[] results = Result.EMPTY;
		for (int i = 0; i < proofMethods.length; i++) {
			visitor.setProofMethodTo(proofMethods[i]);
			String isabelleTheoryAsString = visitor.getTheory(vc, incarnations);
			if (i == 0) {
				isabelleTheoryAsString = matchingTheoryFileExists(
						theoryFilePath, isabelleTheoryAsString);
				if (isabelleTheoryAsString == null)
					continue;
				if (isabelleTheoryAsString.indexOf(OOPS) != -1)
					return Result.EMPTY;
				// we've trying proving this before and failed.
				// else fall through an try OUA theory ...
			} else {
				//Utils.writeToFile(theoryFilePath, isabelleTheoryAsString);
			}
			results = prove(isabelleTheoryAsString, i == 0);
			
			// Return either if the VC was proven, or
			// a user supplied proof was given (even if the user
			// supplied proof did not succeed.

			if (Result.isValid(results) || i == 0)
				return results;
		}
		// If we make it here it is because Isabelle is unable
		// to prove the VC. Write VC to a theory file so that
		// the user can try to prove it him/herself.
		visitor.setProofMethodTo(OOPS);
		String isabelleTheoryAsString = visitor.getTheory(vc, incarnations);
		Utils.writeToFile(theoryFilePath, isabelleTheoryAsString);

		return results;
	}

	private Result[] prove(String theoryString, boolean isOuaEsc) {
		Process process = processPool.getFreeProcess();
		if (process == null) {
			// FIXME: recover use of problemReporter
			// DISCO distributed strategy reporter = null
			if (this.problemReporter != null)
				this.problemReporter.jmlEsc2Error(processPool.failedToLaunch(), 0, 0);
			return new Result[0];
		}

		StringBuffer buffer = new StringBuffer();
		try {
			// Isabelle argument to uss_thy command needs to be in Unix format.
			OutputStream out = process.getOutputStream();
			out.write(theoryString.getBytes());
			out.flush();
			InputStream in = process.getInputStream();
			BufferedReader bIn = new BufferedReader(new InputStreamReader(in));
			String line = bIn.readLine();
			while (!(line.contains(VALID_EOF_1) || line.startsWith(VALID_EOF_2) || line
					.startsWith(ERROR))) {
				buffer.append(line + "\n"); //$NON-NLS-1$
				line = bIn.readLine();
			}
			buffer.append(line + "\n");
			
			// read all data unread in the inputstream buffer
			byte[] response = new byte[in.available()];
			in.read(response);

			if (DEBUG)
				Logger.print(buffer.toString());
			Result[] result = formatResult(buffer.toString());
			
			//if the isabelle cannot prove it, we have to restore the state of the
			//process in order to reuse it.  To do so, we fetch the undo; command.
			if(result == Result.EMPTY) {
				String undo = "undo;"; //$NON-NLS-1$
				out.write(undo.getBytes());
				out.flush();
				response = new byte[in.available()];
				in.read(response);
			} 
			
			processPool.releaseProcess(process);
				
			return result;

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return new Result[0];
	}

	private Result[] formatResult(String string) {

		boolean valid1 = string.indexOf(ISABELLE_VALID_1) > 0;
		boolean valid2 = string.indexOf(ISABELLE_VALID_2) > 0;
		return (valid1 || valid2) ? Result.VALID : Result.EMPTY;
	}

	/**
	 * @return The content of the theory file iff there exists a file with the
	 *         given name and it contains a lemma identical to that in
	 *         isabelleTheoryAsString.
	 */
	private/* @nullable */String matchingTheoryFileExists(
			String theoryFilePath, String isabelleTheoryAsString) {
		File file = new File(theoryFilePath);
		if (!file.exists() || !file.canRead()) {
			return null;
		}
		String contents = Utils.readFromFile(theoryFilePath);
		String fileLemma = getLemma(contents);
		String newLemma = getLemma(isabelleTheoryAsString);
		return fileLemma.equals(newLemma) ? contents : null;
	}

	private String getLemma(String theory) {
		String NOT_FOUND = ""; //$NON-NLS-1$
		String mainMarker = "main:"; //$NON-NLS-1$
		int start = theory.indexOf(mainMarker);
		if (start < 0)
			return NOT_FOUND;
		start = theory.indexOf('"', start);
		if (start < 0)
			return NOT_FOUND;
		int end = theory.indexOf('"', start + 1);
		if (end < 0)
			return NOT_FOUND;
		String lemma = theory.substring(start, end);
		return lemma;
	}
}
