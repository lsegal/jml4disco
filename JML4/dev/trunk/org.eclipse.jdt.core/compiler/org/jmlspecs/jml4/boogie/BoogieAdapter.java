package org.jmlspecs.jml4.boogie;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.util.Logger;

/**
 * Wraps the Boogie runtime into a Java class that can be called
 * from Eclipse's compilation stack.
 */
public class BoogieAdapter {
	public static boolean DEBUG = false; 
	
	// from proverAdapter
	public static final String VALID = "Valid."; //$NON-NLS-1$
	protected transient final CompilerOptions options;
	protected transient final ProblemReporter problemReporter;

	//private static final boolean DEBUG = false;
	private static final String FILE = "out.bpl"; //$NON-NLS-1$
	private static final String BOOGIE = "boogie"; //$NON-NLS-1$
	
	private static Hashtable/*<String,String>*/ resultCodes = new Hashtable/*<String,String>*/();
	
	private transient BoogieSource output;

	/**
	 * Creates a new Boogie adapter attached to an instance of an Eclipse compiler
	 * object.
	 * 
	 * @param compiler the Eclipse compiler object
	 */
	public BoogieAdapter(Compiler compiler) {
		this.output = new BoogieSource();
		this.options = compiler.options;
		this.problemReporter = compiler.problemReporter;
		
		InitializeResultCodes();
	}
	
	/**
	 * Sets up the map from a Boogie error result code to a textual error message for JML.
	 * 
	 * TODO Move into BoogieResultParser
	 */
	private void InitializeResultCodes() {
		resultCodes.put("BP5001", "This assertion might not hold."); //$NON-NLS-1$//$NON-NLS-2$
		resultCodes.put("BP5002", "This precondition might not hold."); //$NON-NLS-1$//$NON-NLS-2$
		resultCodes.put("BP5003", "This postcondition might not hold."); //$NON-NLS-1$//$NON-NLS-2$
	}

	/**
	 * Translates a Java AST into Boogie code and passes it to a Boogie process
	 * to be proven formally. The results are sent to Eclipse using the ProblemReporter.
	 * 
	 * @param unit the root node of the Java AST
	 */
	public void prove(CompilationUnitDeclaration unit) {
		// fill boogie visitor
		BoogieVisitor.visit(unit, output);
		if (DEBUG) {
			System.out.println(output.getResults());
		}

		String[] response = proveWithBoogie();
		if (response != null) { 
			parseResult(response);
		}
	}

	/**
	 * Parses the Boogie output results and translates it into 
	 * something Eclipse can understand (using the ProblemReporter).
	 * 
	 * TODO Move into BoogieResultParser.
	 * 
	 * @param response the individual lines of the Boogie output
	 */
	private void parseResult(String[] response) {
		for (int i = 0; i < response.length; i++) {
			Pattern p = Pattern.compile(".+\\((\\d+),(\\d+)\\): (syntax error|Error|Error (\\S+?)): (.*)"); //$NON-NLS-1$
			Matcher m = p.matcher(response[i]);
			if (m.matches()) {
				if (m.group(3).equals("Error")) { //$NON-NLS-1$
					// Get Java code point
					int row = Integer.parseInt(m.group(1));
					int col = Integer.parseInt(m.group(2));
					BoogieSourcePoint sp = new BoogieSourcePoint(row, col);
					ASTNode term = output.getTermAtPoint(sp);
					String errorText = m.group(5);
					
					if (errorText.startsWith("command assigns to a global variable")) { //$NON-NLS-1$
						errorText = "Missing JML modifies clause for this attribute assignment."; //$NON-NLS-1$
					}
					
					if (term != null) {
						problemReporter.jmlEsc2Error(errorText, term.sourceStart, term.sourceEnd); 
					}
					else {
						problemReporter.jmlEsc2Error(errorText, 0, 0);
					}
				}
				else if (m.group(3).equals("syntax error")) { //$NON-NLS-1$
					problemReporter.jmlEsc2Fatal("Error parsing Java source code (unsuppored syntax?): " + response[i], 0, 0); //$NON-NLS-1$
				}
				else {
					// Get error message
					String errorText = (String)resultCodes.get(m.group(4));
					if (errorText == null) errorText = m.group(5); // Use Boogie's if none avail.
	
					// Get Java code point
					int row = Integer.parseInt(m.group(1));
					int col = Integer.parseInt(m.group(2));
					BoogieSourcePoint sp = new BoogieSourcePoint(row, col);
					ASTNode term = output.getTermAtPoint(sp);
					
					if (term != null) {
						problemReporter.jmlEsc2Error(errorText, term.sourceStart, term.sourceEnd); 
					}
					else {
						problemReporter.jmlEsc2Error(errorText, 0, 0);
					}
					
					// Catch related location
					p = Pattern.compile(".+\\((\\d+),(\\d+)\\): Related location: (.*)"); //$NON-NLS-1$
					m = p.matcher(response[i+1]);
					if (response[i+1] != null && m.matches()) {
						// Get Java code point
						row = Integer.parseInt(m.group(1));
						col = Integer.parseInt(m.group(2));
						sp = new BoogieSourcePoint(row, col);
						term = output.getTermAtPoint(sp);
	
						if (term != null) {
							problemReporter.jmlEsc2Error(errorText, term.sourceStart, term.sourceEnd); 
						}
					}
				}
			}
		}
		
	}

	/**
	 * Attempts to prove a block of Boogie code in a Boogie prover runtime.
	 * 
	 * @return the proving results from the Boogie process
	 */
	private String[] proveWithBoogie() {
		try {
			try {
				// Create file
				OutputStreamWriter out = new OutputStreamWriter(new FileOutputStream(FILE), "UTF8"); //$NON-NLS-1$
				BufferedWriter file = new BufferedWriter(out);
				
				file.write(output.getResults());
				// Close the output stream
				file.close();
			} catch (Exception e) {
				// Catch exception if any
			}
			
			Process process = getProverProcess();
			if (process == null) {
				if (this.problemReporter != null)
					this.problemReporter.jmlEsc2Error("Failed to launch Boogie.exe", 0, 0); //$NON-NLS-1$
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

	/**
	 * Initiates a Boogie runtime process
	 * 
	 * @return the Boogie runtime process or null if it could not be started.
	 */
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
