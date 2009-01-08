package org.jmlspecs.jml4.boogie;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.util.Logger;

public class BoogieAdapter {
	// from proverAdapter
	public static final String VALID = "Valid."; //$NON-NLS-1$
	protected transient final CompilerOptions options;
	protected transient final ProblemReporter problemReporter;

	//private static final boolean DEBUG = false;
	private static final String FILE = "out.bpl"; //$NON-NLS-1$
	private static final String BOOGIE = "boogie"; //$NON-NLS-1$
	
	private transient BoogieVisitor visitor;

	public BoogieAdapter(Compiler compiler) {
		this.options = compiler.options;
		this.problemReporter = compiler.problemReporter;
	}

	public Result[] prove(CompilationUnitDeclaration unit) {
		// fill boogie visitor
		this.visitor = new BoogieVisitor();
		unit.traverse(visitor, unit.scope);

		String[] response = proveWithBoogie();
		if (response != null) { 
			parseResult(response);
		}
		return new Result[0];
	}

	private void parseResult(String[] response) {
		for (int i = 0; i < response.length; i++) {
			Pattern p = Pattern.compile(".+\\((\\d+),(\\d+)\\):.*This assertion might not hold.*"); //$NON-NLS-1$
			Matcher m = p.matcher(response[i]);
			if (m.matches()) {
				int row = Integer.parseInt(m.group(1));
				int col = Integer.parseInt(m.group(2));
				BoogieVisitor.LinePoint lp = visitor.new LinePoint(row, col);
				BoogieVisitor.SourcePoint sp = visitor.getPoint(lp);
				this.problemReporter.jmlEsc2Error("This assertion might not hold.", sp.sourceStart, sp.sourceEnd); //$NON-NLS-1$
			}
		}
		
	}

	private String[] proveWithBoogie() {
		try {
			try {
				// Create file
				FileWriter fstream = new FileWriter(FILE);
				BufferedWriter file = new BufferedWriter(fstream);
				file.write(visitor.getResults());
				// Close the output stream
				file.close();
			} catch (Exception e) {
				// Catch exception if any
			}
			
			Process process = getProverProcess();
			if (process == null) {
				if (this.problemReporter != null)
					this.problemReporter.jmlEsc2Error("Failed to launch", 0, 0); //$NON-NLS-1$
					return null;
			}

			ArrayList/*<String>*/ results = new ArrayList();
			InputStream in = process.getInputStream();
			BufferedReader bIn = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bIn.readLine())) {
				results.add(line);
			}
			bIn.close();
			
			String[] strResults = new String[results.size()];
			for (int i = 0; i < results.size(); i++) {
				strResults[i] = results.get(i).toString();
			}
			return strResults;
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	public static/* @nullable */Process getProverProcess() {
		try {
			return Runtime.getRuntime().exec(BOOGIE + " " + FILE); //$NON-NLS-1$
		} catch (Exception e) {
			// Logger.print(failedToLaunch());
			e.printStackTrace();
			Logger.print(e.toString());
		}
		return null;
	}

}
