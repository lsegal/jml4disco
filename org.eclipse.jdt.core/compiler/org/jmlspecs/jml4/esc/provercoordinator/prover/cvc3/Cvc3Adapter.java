package org.jmlspecs.jml4.esc.provercoordinator.prover.cvc3;

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
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.util.Logger;

public class Cvc3Adapter extends ProverAdapter {

	private static final String  CVC_CMD = "cvc3"; //$NON-NLS-1$
	private static final String CMD_ARGS = " -timeout 2"; //$NON-NLS-1$
	private static final boolean DEBUG = false;

	public Cvc3Adapter(CompilerOptions options, ProblemReporter problemReporter) {
		super(options, problemReporter);
	}
	public Result[] prove(VC vc, Map incarnations) {
		Cvc3Visitor visitor = new Cvc3Visitor();
		String cvc3String = visitor.getTheory(vc, incarnations);
		return proveWithCvc3(cvc3String);
	}
	
	public Result[] proveWithCvc3(String cvc3String) {
		Process process = getProverProcess();
		if (process == null) {
			// FIXME: find a better solution. I.e. don't
			// report a problem every time a failed attempt
			// to invoke cvc3 is made.
			// this.problemReporter.jmlEsc2Error(failedToLaunch(), 0, 0);
			return new Result[0];
		}
		
		StringBuffer buffer = new StringBuffer();
		try {
			OutputStream out = process.getOutputStream();
			out.write(cvc3String.getBytes());
			out.close();
			InputStream in = process.getInputStream();
			BufferedReader bIn = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bIn.readLine())) {
				buffer.append(line);
  		    }
			bIn.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (buffer.length()==0) {
			try {
				InputStream in = process.getErrorStream();
				BufferedReader bIn = new BufferedReader(new InputStreamReader(in));
				buffer = new StringBuffer();
				String line;
				while (null != (line = bIn.readLine())) {
					buffer.append(line);
	  		    }
				bIn.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		if (DEBUG)
			Logger.print(buffer.toString());
		String result = buffer.toString();
		if (result.indexOf("Error") >= 0) { //$NON-NLS-1$
//			this.problemReporter.jmlEsc2Error("invalid CVC3 response '"+result+"'", 0, 0);  //$NON-NLS-1$//$NON-NLS-2$
		}
		if (result.equals(ProverAdapter.VALID))
			return Result.VALID;
		return Result.EMPTY;
	}
	
	public static /*@nullable*/Process getProverProcess() {
		try {
			return Runtime.getRuntime().exec(command() + CMD_ARGS);
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
	
	private static String failedToLaunch() {
		return "failed to launch " + command(); //$NON-NLS-1$
	}
	
	public ProverVisitor getVisitor() {
		return new Cvc3Visitor();
	}

	private static String command() {
		// FIXME: check for the actual OS type ...
		return File.separatorChar == '/' 
			? CVC_CMD
			: "/usr/local/bin/" + CVC_CMD; //$NON-NLS-1$
	}
}
