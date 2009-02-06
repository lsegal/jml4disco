package org.jmlspecs.eclipse.jdt.core.tests.util;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;

import org.eclipse.jdt.core.tests.util.Util;
import org.eclipse.jdt.core.compiler.batch.BatchCompiler;
import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;

public abstract class JmlTestCase extends AbstractRegressionTest {
	
	public JmlTestCase(String name) {
		super(name);
	}
	protected String compileAndDeploy(String _batchCompilerOptions, String paths, String srcPath, String destDir){
		return compileAndDeploy(_batchCompilerOptions, paths, srcPath, destDir, "");	
	}
	protected String compileAndDeploy(String _batchCompilerOptions, String paths, String srcPath, String destDir, String classPath) {
		//this.createOutputTestDirectory(destDir);
		this.createTestDirectory(destDir);
		String batchCompilerOptions = _batchCompilerOptions + " \"" + paths + "\"";
		
		if(srcPath.length() > 0) {
			batchCompilerOptions += " -sourcepath \"" + srcPath + "\"";
		}
		if(destDir.length() > 0) {
			batchCompilerOptions += " -d \"" + destDir + "\"";
		}
		batchCompilerOptions += " -classpath \"" + classPath + Util.getJavaClassLibsAsString() + destDir + "\"";
		// System.out.println(batchCompilerOptions);
		StringWriter stringWriter = new StringWriter();
		PrintWriter printWriter = new PrintWriter(stringWriter);
		boolean result = BatchCompiler.compile(batchCompilerOptions, /*out*/printWriter, /*err*/printWriter, null/*progress*/);
		String output = Util.convertToIndependantLineDelimiter(stringWriter.getBuffer().toString());
		// System.out.print("Compiler output:\n" + output);
		//return (result ? "[Ok]" : "[Problem]") + output;
		return output;
	}
	protected void createTestDirectory(String path) {
		this.outputTestDirectory =  new File(path);
		if (!this.outputTestDirectory.exists()) {
			this.outputTestDirectory.mkdirs();
		}
	}

}
