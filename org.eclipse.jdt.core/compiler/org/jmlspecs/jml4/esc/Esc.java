package org.jmlspecs.jml4.esc;

import java.io.IOException;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.ast.JmlAbstractMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import org.jmlspecs.jml4.compiler.DefaultCompilerExtension;
import org.jmlspecs.jml4.esc.gc.lang.GcProgram;
import org.jmlspecs.jml4.esc.provercoordinator.prover.CachedVcs;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Counter;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;
import org.jmlspecs.jml4.util.Logger;

public class Esc extends DefaultCompilerExtension {

	private static boolean DEBUG = false;

	public static final int NUMBER_OF_THREADS = 32;
    private final Executor executor = Executors.newFixedThreadPool(NUMBER_OF_THREADS);
    
	public String name() { return "JMLESC4";} //$NON-NLS-1$

	public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
		if (DEBUG) {
			Logger.println(this + " - compiler.options.jmlEnabled:     "+compiler.options.jmlEnabled); //$NON-NLS-1$
			Logger.println(this + " - compiler.options.jmlEscEnabled:  "+compiler.options.jmlEscEnabled); //$NON-NLS-1$
			Logger.println(this + " - compiler.options.jmlEsc2Enabled: "+compiler.options.jmlEsc2Enabled); //$NON-NLS-1$
		}
		if (compiler.options.jmlEnabled && compiler.options.jmlDbcEnabled && compiler.options.jmlEscEnabled) {
			process(compiler, unit);
		}
	}

	// processing a compilation unit means processing each of its types
	// processing a types means processing its methods (including constructors)
	// the JDT AST stores static initialization blocks as a subsclass of fields,
	// so these will need to be handled slightly differently.
	private void process(final Compiler compiler, final CompilationUnitDeclaration unit) {
		if (unit.compilationResult.hasSyntaxError
				|| unit.compilationResult.hasErrors()
				|| unit.hasErrors()) 
			return;

		final int[] done = new int[1];
		   
		String debugName = (new String(unit.compilationResult.fileName)).substring(0, unit.compilationResult.fileName.length-(".java".length()));  //$NON-NLS-1$
		if (DEBUG)
			Logger.println(this + " - CompilationUnit: "+new String(unit.getFileName())); //$NON-NLS-1$
		// DISCO threading 
		final CachedVcs cachedVcs = new CachedVcs(unit);
		final Counter postProcessorCounter = new Counter();
		int numberLaunched = 0;
		for (int i = 0; i < unit.types.length ; i++) {
			TypeDeclaration typeDeclaration = unit.types[i];
			Utils.assertTrue(typeDeclaration instanceof JmlTypeDeclaration, "'"+new String(typeDeclaration.name)+"' expected to be a JmlTypeDeclaration, but instead it is a '"+typeDeclaration.getClass().getName()+"'"); //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
			final JmlTypeDeclaration type = (JmlTypeDeclaration)typeDeclaration;
			for (int j = 0; j < type.methods.length; j++) {
				final AbstractMethodDeclaration method = type.methods[j];
				/*@ assert (method instanceof JmlMethodDeclaration)
				  @     || (method instanceof JmlConstructorDeclaration);
				  @*/
				if (method instanceof JmlMethodDeclaration
				 || method instanceof JmlConstructorDeclaration) {
					Runnable work = new Runnable() {
					   public void run() {
						   process((JmlAbstractMethodDeclaration) method, cachedVcs, postProcessorCounter, type, unit.scope, compiler.options, compiler.problemReporter);
						   synchronized (done) {
							   done[0]++;
							   done.notify();
						   }
					   }
					};
					executor.execute(work);			
					numberLaunched++;
				} else {
					if (DEBUG)
						Logger.println("Esc4 doesn't yet support '"+method.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				}
			}
		}
		waitForItToFinish(done, numberLaunched);
		try {
			cachedVcs.writeToDisk();
		} catch (IOException e) {
	    	if (compiler != null && compiler.problemReporter.referenceContext == null) {
	    		compiler.problemReporter.referenceContext = unit;
	    	}
	    	String message = "internal problem: could not write VC cache to file '" //$NON-NLS-1$
	    		+ cachedVcs.filename + "'."; //$NON-NLS-1$
			int sourceStart = 0;
			int sourceEnd = 0;
			compiler.problemReporter.jmlEsc2Error(message, sourceStart, sourceEnd);
		}
	}
	// DISCO waiting for threads to come back
	public static void waitForItToFinish(int[] done, int howMany) {
		System.out.println("waiting to finish"); //$NON-NLS-1$
		while (done[0] != howMany) {
		    synchronized(done) {
		        try{
		           done.wait();
		        } catch(InterruptedException e) {
		        	e.printStackTrace();
		        }
	        }
		}
		System.out.println("done waiting to finish!");		 //$NON-NLS-1$
	}
	// DISCO some vars became final to allow serialization
	/*package*/ void process(JmlAbstractMethodDeclaration method, CachedVcs cachedVcs, Counter postProcessorCounter, JmlTypeDeclaration typeDecl, CompilationUnitScope scope, CompilerOptions options, ProblemReporter problemReporter) {
		String debugName = getDebugNameForMethod((AbstractMethodDeclaration)method); 
		final GcTranslator gcTranslator = new GcTranslator(options, problemReporter);
		final VcGenerator vcGenerator = new VcGenerator (options, problemReporter);
		final ProverCoordinator prover = new ProverCoordinator(options, problemReporter, cachedVcs);
		final PostProcessor pp = new PostProcessor(options, problemReporter, postProcessorCounter);

		GcProgram gc = gcTranslator.translate(method, typeDecl, scope);
		VcProgram vc = vcGenerator.process(gc);
		Result[] results = prover.prove(vc);
		pp.postProcess(results, ((AbstractMethodDeclaration)method).sourceStart());
		
		// store the results in the method declaration so later stages can take advantage of the information
		method.setEscResults(results);
		// DISCO timing printout
	}

	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
		buf.append("\n\t\t- ESC: ").append(options.jmlEscEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$	
	}
	// DISCO timing 

	// DISCO timing printout
	private static String getDebugNameForMethod(AbstractMethodDeclaration asJdtMethod) {
		String filename = new String(asJdtMethod.compilationResult().getCompilationUnit().getFileName());
		filename = filename.substring(0, filename.length()-(".java".length())); //$NON-NLS-1$
		String methodIdicator =  filename+"\t"+new String(asJdtMethod.selector); //$NON-NLS-1$
		return methodIdicator;
	}
}
