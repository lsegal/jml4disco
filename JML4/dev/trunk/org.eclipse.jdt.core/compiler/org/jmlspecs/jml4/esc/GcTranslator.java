package org.jmlspecs.jml4.esc;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml2.util.Util;
import org.jmlspecs.jml4.ast.JmlAbstractMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import org.jmlspecs.jml4.esc.gc.Ast2SugaredVisitor;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.GcProgram;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBlock;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMethodSpecification;
import org.jmlspecs.jml4.esc.util.Counter;
import org.jmlspecs.jml4.esc.util.Utils;

public class GcTranslator {

	private static final String RETURN = "return"; //$NON-NLS-1$
	public static final String POST_VAR_NAME = "$post$var$"; //$NON-NLS-1$
	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	private static final String START_BLOCK = "start"; //$NON-NLS-1$
	private static final String DOT_JAVA = ".java"; //$NON-NLS-1$
	public GcTranslator(CompilerOptions options,
			ProblemReporter problemReporter) {
		this.options = options;
		this.problemReporter = problemReporter;
	}

	// Stage 1: GC Translator
	// Stage 1.1: AST to Fully Sugared CFG
	// Stage 1.2: Fully Sugared CFG, but with no method calls
	// Stage 1.3: Fully Sugared CFG to Sugared CFG, but no loop/if sugar
	// Stage 1.4: Sugared CFG to Sugared Acyclic CFG
	// Stage 1.5: Sugared Acyclic CFG to Desugared CFG  
	// Stage 1.6: Desugared CFG to Passified CFG
	public GcProgram translate(JmlAbstractMethodDeclaration method, JmlTypeDeclaration typeDecl, CompilationUnitScope scope) {

		SugaredProgram sugared = ast2sugaredCfg(method, typeDecl, scope);
		SugaredProgram acyclic = desugarLoops(sugared);
		//@ assert (* no sugar for loops, if, or switch in acyclic *)
		SimpleProgram simple =  desugar(acyclic);
		GcProgram passified = passify(simple);
		
		return passified;
	}

	protected SugaredProgram ast2sugaredCfg(JmlAbstractMethodDeclaration method, JmlTypeDeclaration typeDecl, CompilationUnitScope scope) {
		Utils.assertTrue(method instanceof JmlMethodDeclaration 
				      || method instanceof JmlConstructorDeclaration, 
				         "method '"+new String(((AbstractMethodDeclaration)method).selector)+"' is not a JmlMethodDecl or a JmlConstructorDecl but a '"+method.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		AbstractMethodDeclaration asJdtMethod = (AbstractMethodDeclaration) method;
		SugaredStatement[] params = paramDecls2sugaredVarDecls(asJdtMethod.arguments);
		Ast2SugaredVisitor ast2SugaredVisitor = new Ast2SugaredVisitor(asJdtMethod);
		SugaredStatement[] body = astBody2sugaredBody(asJdtMethod, scope, typeDecl, ast2SugaredVisitor);
		SugaredVarDecl returnVarDecl = getReturnVarDecl(method);

		SugaredMethodSpecification spec = ast2SugaredVisitor.getSpec(method);
		SugaredExpression invariant = ast2SugaredVisitor.getInvariant(typeDecl.getInvariant());
		SugaredPrecondition  pre  = (method instanceof JmlMethodDeclaration
			? new SugaredPrecondition (spec.pre,  invariant, spec.pre.sourceStart)
			: new SugaredPrecondition (spec.pre,  SugaredBooleanConstant.TRUE, spec.pre.sourceStart));
		SugaredPostcondition post = new SugaredPostcondition(spec.post, invariant, spec.post.sourceStart, asJdtMethod.sourceStart);
		SugaredStatement foldedBody = SugaredSequence.fold(params);
		if (returnVarDecl != null) {
			foldedBody = new SugaredSequence(foldedBody, returnVarDecl);
		}
		foldedBody = new SugaredSequence(foldedBody, pre);
		foldedBody = new SugaredSequence(foldedBody, SugaredSequence.fold(body));
		
		String returnLabel = SugaredReturnStatement.RETURN_BLOCK;
		SugaredBlock startBlock = new SugaredBlock(START_BLOCK, foldedBody, new String[]{returnLabel});
		SugaredBlock returnBlock = new SugaredBlock(returnLabel, post, new String[0]);
		SugaredBlock[] blocks = new SugaredBlock[]{startBlock, returnBlock};
		String filename = new String(asJdtMethod.compilationResult().getCompilationUnit().getFileName());
		filename = filename.substring(0, filename.length()-(DOT_JAVA.length()));
		filename = Util.translatePath(filename);
		filename = Utils.win2unixFileName(filename);
		String methodIdicator =  filename+"_"+new String(asJdtMethod.selector); //$NON-NLS-1$
		SugaredProgram result = new SugaredProgram(blocks, START_BLOCK, methodIdicator);
		return result;
	}

	private /*@nullable*/ SugaredVarDecl getReturnVarDecl(JmlAbstractMethodDeclaration method) {
		if (method instanceof JmlMethodDeclaration) {
			JmlMethodDeclaration jmlMethod = (JmlMethodDeclaration) method;
			TypeBinding returnType = jmlMethod.binding.returnType;
			return (returnType == TypeBinding.VOID)
			     ? null
				 : new SugaredVarDecl(RETURN, 0, returnType, 0);
		} else {
			return null;
		}
	}

	private void concatArrays(Object[] src1, Object[] src2, Object[] dst) {
		//@ assert dst.length == src1.length + scr2.length;
		System.arraycopy(src1, 0, dst, 0, src1.length);
		System.arraycopy(src2, 0, dst, src1.length, src2.length);
	}

	private SugaredStatement[] paramDecls2sugaredVarDecls(Argument[] arguments) {
		int numArgs = (arguments == null ? 0 : arguments.length);
		SugaredVarDecl[] result = new SugaredVarDecl[numArgs];
		for (int i = 0; i < numArgs; i++) {
			//@ assert arguments != null;
			Argument argument = arguments[i];
			String name = new String(argument.name);
			result[i] = new SugaredVarDecl(name, argument.sourceStart, argument.binding.type, argument.sourceStart);
		}
		return result;
	}

	protected SugaredStatement[] astBody2sugaredBody(AbstractMethodDeclaration method, 
			CompilationUnitScope cuScope, TypeDeclaration typeDecl, Ast2SugaredVisitor visitor) {
		Statement[] statements = method.statements;
		if (statements == null) 
			return new SugaredStatement[0];
		SugaredStatement[] result = new SugaredStatement[statements.length];

		for (int i = 0; i < statements.length; i++) {
			Statement stmt = statements[i];
			BlockScope scope = new BlockScope(new MethodScope(new ClassScope(cuScope, typeDecl), cuScope.referenceContext(), method.isStatic()));
			stmt.traverse(visitor, scope);
			result[i] = visitor.getResult();
		}
		return result;
	}

	protected SugaredProgram desugarLoops(SugaredProgram sugared) {
		DesugarLoopVisitor visitor = new DesugarLoopVisitor();
		return sugared.accept(visitor);
	}
	protected SimpleProgram desugar(SugaredProgram acyclic) {
		DesugaringVisitor visitor = new DesugaringVisitor();
		return acyclic.accept(visitor);
	}
	protected GcProgram passify(SimpleProgram simple) {
		PassifyVisitor visitor = new PassifyVisitor();
		return simple.accept(visitor);
	}
}
