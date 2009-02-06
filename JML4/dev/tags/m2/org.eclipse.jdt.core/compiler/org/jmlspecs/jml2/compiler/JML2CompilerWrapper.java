package org.jmlspecs.jml2.compiler;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml2.util.Util;
import org.jmlspecs.jml4.compiler.DefaultCompilerExtension;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.util.Logger;

public class JML2CompilerWrapper extends DefaultCompilerExtension {

	public static final boolean DEBUG = false;
	private static final String JML2_COMPILER = "jmlc"; //FIXME: add a text field and obtain the value from there //$NON-NLS-1$
	private static final String QUIET = "-Q"; //$NON-NLS-1$
	private static final String DESTINATION = "-d"; //$NON-NLS-1$
	private static final String JML2BIN = "Jml2Bin"; //$NON-NLS-1$
	private static final String LINE = ", line "; //$NON-NLS-1$
	private static final String CHAR = ", character "; //$NON-NLS-1$
	private static final String ERROR= "error: "; //$NON-NLS-1$

	public String name() { return "JML2CompilerWrapper"; } //$NON-NLS-1$

	public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
		if (!compiler.options.jmlEnabled && compiler.options.jml2CompilerEnabled) {
			this.comp(compiler, unit);
		}
	}

	private void comp(Compiler compiler, CompilationUnitDeclaration unit) {
		String fileName = String.valueOf(unit.getFileName());
		String filePath = Util.translatePath(fileName);
		filePath = Utils.win2unixFileName(filePath);
		String[] a = getExecArgs(filePath);
		if(DEBUG) Logger.println(this + " - fullFlNm : " + filePath); //$NON-NLS-1$
		String output = Util.exec(a);
		if(DEBUG) Logger.println(this + " - output : \n" + output); //$NON-NLS-1$
		if(output != null && ! output.equals("")) //$NON-NLS-1$
			this.parse(compiler, unit, output);
	}

	private String[] getExecArgs(String filePath) {
		List args = new ArrayList();
		args.add(JML2_COMPILER);
		args.add(QUIET);
		String projectPath = Util.projectRawPathOf(filePath);
		if (projectPath != null) {
			// We probably don't have a workspace to get the project 
			// path from. Hence, have jmlc write the class file to the
			// same dir as the source; i.e. do not specify a destination path.
			String destinationDir = projectPath + System.getProperty("file.separator") + JML2BIN; //$NON-NLS-1$
			args.add(DESTINATION);
			args.add(destinationDir);
		}
		args.add("\"" + filePath + "\""); //$NON-NLS-1$ //$NON-NLS-2$
		String [] result = (String[]) args.toArray(new String[0]);
		if (!underUnix()) {
			String[] adaptedResult = new String[result.length+1];
			adaptedResult[0] = "bash"; //$NON-NLS-1$
			System.arraycopy(result, 0, adaptedResult, 1, result.length);
			result = adaptedResult;
		}
		return result;
	}

	private static final String LINESEP = System.getProperty("line.separator"); //$NON-NLS-1$
	private void parse(Compiler compiler, CompilationUnitDeclaration unit, String output) {
		String [] lines = output.split(LINESEP);
		for(int i=0; i<lines.length; i++)
			parseLineAndReport(compiler, unit, lines[i]);
	}
	
	private void parseLineAndReport(Compiler compiler, CompilationUnitDeclaration unit, String line) {		
//		File "dev/workspaces/runtime-EclipseApplication/Tester/src/Cube.java", line 4, character 27 error: Syntax error: unexpected token: ensure
		// Get the line
		int lineIdx=line.indexOf(LINE);
		if( lineIdx == -1) {
			Logger.println(this + " - Not able to find substring \"" + LINE + "\" in line : \n" + line); //$NON-NLS-1$ //$NON-NLS-2$
			if(line.startsWith("warning")) { //$NON-NLS-1$
				compiler.problemReporter.jmlEsc2Warning(line, 0, 0);
			} else if (line.startsWith("Error")) { //$NON-NLS-1$
				compiler.problemReporter.jmlEsc2Error(line, 0, 0);				
			}
			return;
		}
		int lineNoEnd = line.substring(lineIdx+7).indexOf(',');
		int lineNo = Integer.parseInt(line.substring(lineIdx + 7, lineIdx + 7 + lineNoEnd));
		// Get the character
		int charIdx=line.indexOf(CHAR);
		if( charIdx == -1) {
			Logger.println(this + " - Not able to find substring \"" + CHAR + "\" in line : \n" + line);  //$NON-NLS-1$//$NON-NLS-2$
			return;
		}
		// int charNoEnd = line.substring(charIdx + 12).indexOf(' ');
		// int charNo = Integer.parseInt(line.substring(charIdx + 12, charIdx + 12 + charNoEnd));
		// Get the error
		int errIdx=line.indexOf(ERROR);
		if( lineIdx == -1) {
			Logger.println(this + " - Not able to find substring \"" + ERROR + "\" in line : \n" + line); //$NON-NLS-1$ //$NON-NLS-2$
			return;
		}
		String errMsg = "JML Checker: " + line.substring(errIdx + 7); //$NON-NLS-1$
		
		ProblemReporter pr = compiler.problemReporter;
		//FIXME: Here we obtain the character position of the start of line of where the problem occurred
		//       We do this because we cannot depend on the bogus character position reported by the JML2 tools.
		int ss = Util.getSourceStartOfLine(unit.compilationResult.getLineSeparatorPositions(), lineNo);
		//FIXME: Here we obtain the character position of the end of line of where the problem occurred
		int se = Util.getSourceEndOfLine(unit.compilationResult.getLineSeparatorPositions(), lineNo);
		pr.jmlEsc2Error(errMsg, ss, se);
	}
	
	public void getOptionsMap(CompilerOptions options, Map optionsMap) {
		optionsMap.put(JmlCompilerOptions.OPTION_EnableJml2Compiler, options.jml2CompilerEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	}
	
	public void setOptionsMap(CompilerOptions options, Map optionsMap) {
		Object optionValue;
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJml2Compiler)) != null) {
				options.jml2CompilerEnabled = CompilerOptions.ENABLED.equals(optionValue);
		}
	}
	
	public int configureArgs(String currentArg, String[] args, int index, Map options) {
		if (currentArg.equals("-jml2c")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml2Compiler,
					CompilerOptions.ENABLED);
			return index;
		}
		return super.configureArgs(currentArg, args, index, options);
	}

	private static boolean underUnix() {
		return File.separatorChar == '/';
	}
	
	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
		buf.append("\n\t\t- JML2 compiler: ").append(options.jml2CompilerEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
}
}
