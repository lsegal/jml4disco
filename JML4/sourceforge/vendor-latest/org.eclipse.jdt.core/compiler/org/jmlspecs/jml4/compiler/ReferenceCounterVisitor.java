package org.jmlspecs.jml4.compiler;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.ast.JmlFieldDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;
import org.jmlspecs.jml4.util.Logger;

public class ReferenceCounterVisitor extends ASTVisitor {
	private int field_non_null;
	private int field_nullable;
	private int method_non_null;
	private int method_nullable;
	private int param_non_null;
	private int param_nullable;

	private int cu_field_non_null;
	private int cu_field_nullable;
	private int cu_method_non_null;
	private int cu_method_nullable;
	private int cu_param_non_null;
	private int cu_param_nullable;

	private int typeCount;
	private final /*@non_null*/ ProblemReporter problemReporter;
	private boolean firstTime = true;
	private String filename = null;


	public ReferenceCounterVisitor(/*@non_null*/ ProblemReporter problemReporter) {
		this.problemReporter = problemReporter;
	}

	private void log(String msg) {
		if (firstTime) {
			firstTime = false;
			log("count"//$NON-NLS-1$
					+ "\t" + "filename"//$NON-NLS-1$ //$NON-NLS-2$ 
					+ "\t" + "+" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "typeCount" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "field_non_null" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "field_nullable" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "method_non_null" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "method_nullable" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "param_non_null" //$NON-NLS-1$ //$NON-NLS-2$
					+ "\t" + "param_nullable"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		Logger.println(msg);
		System.out.println(msg);
	}

	public boolean visit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		/*
		 * if (fieldDeclaration instanceof JmlFieldDeclaration) {
		 * JmlFieldDeclaration jmlDecl = (JmlFieldDeclaration) fieldDeclaration;
		 * if (jmlDecl.type == null) Logger.println("\t visit field 1 "+new
		 * String(fieldDeclaration.name)+" "+fieldDeclaration.type.toString());
		 * else Logger.println("\t visit field 2 "+new
		 * String(fieldDeclaration.name)+" "+jmlDecl.type.toString()); } else {
		 * Logger.println("\t visit field 3 "+new
		 * String(fieldDeclaration.name)+" "+fieldDeclaration.type.toString()); }
		 */
		if (fieldDeclaration instanceof JmlFieldDeclaration) {
			JmlFieldDeclaration jmlDecl = (JmlFieldDeclaration) fieldDeclaration;
			if (jmlDecl.type != null
					&& jmlDecl.binding != null && ! Nullity.isPrimitiveType(jmlDecl.binding.type)) {
				
				testForExplicitNullity(jmlDecl.type, new String(jmlDecl.name));
				if (jmlDecl.type.isDeclaredNonNull()) {
					field_non_null++;
					cu_field_non_null++;
				} else {
					field_nullable++;
					cu_field_nullable++;
				}
			} else if (jmlDecl.type != null && jmlDecl.binding == null) {
				Logger.println("----------ref counter----------"); //$NON-NLS-1$
				Logger.println("this is         '"+this+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				Logger.println("jmlDecl.type is '"+jmlDecl.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				Logger.println("its resolvedType'"+jmlDecl.type.resolvedType+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				Logger.println("-------------------------------"); //$NON-NLS-1$
			}
		}
		return true;
	}

	public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		this.problemReporter.referenceContext = methodDeclaration;
		// Logger.println("\t visit method "+new
		// String(methodDeclaration.selector));
		// Logger.println("\t ------------
		// "+methodDeclaration.returnType.toString());

		if (methodDeclaration.returnType != null
				&& !Nullity
						.isPrimitiveType(methodDeclaration.returnType.resolvedType)) {
			testForExplicitNullity(methodDeclaration.returnType, "return"); //$NON-NLS-1$
			if (methodDeclaration.returnType.isDeclaredNonNull()) {
				method_non_null++;
				cu_method_non_null++;
			} else {
				method_nullable++;
				cu_method_nullable++;
			}
		}

		dumpParams(methodDeclaration.arguments);
		return true;
	}

	private void testForExplicitNullity(TypeReference typeRef, String identifier) {
		if (typeRef instanceof JmlTypeReference) {
			JmlTypeReference jmlTypeRef = (JmlTypeReference) typeRef;
			Nullity nullity = jmlTypeRef.getNullity();
			if (!nullity.hasExplicitNullity()) {
				if (shouldReport())
					this.problemReporter
							.typeReferenceNotExplicitlyMarkedWithNullity(
									typeRef, identifier);
					// System.out.println("\ntypeRef ("+typeRef.toString()+"
					// "+identifier+") has implicit nullity");
					// //$NON-NLS-1$//$NON-NLS-2$
			} else {
				// System.out.println("\ntypeRef ("+typeRef.toString()+") has
				// explicit nullity");
			}
		} else {
			System.out.println("\ntypeRef (" + typeRef + " " + identifier + ") isn't a JmlTypeRef. it's a '" + typeRef.getClass() + "'"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		}
	}

	private boolean shouldReport() {
		if(true) return true;
		String[] files_35_jml = new String[] {"JML2/org/jmlspecs/checker/JmlPredicate.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlGenericSpecCase.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlSpecStatementClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlInterfaceDeclaration.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlTypeExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlDeclaration.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlAssignableClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JMLDefaultWarningFilter.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlExpressionFactory.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlSpaceExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlMemberDeclaration.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlSpecExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlMultExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlStoreRef.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlDebugStatement.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlCallableClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JInterfaceDeclarationWrapper.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlExpressionContext.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlSpecStatement.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlEnsuresClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlName.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlAxiom.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlStdType.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlCompilationUnit.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlOnlyAssignedExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlSpecBodyClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlMethodSpecification.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlBreaksClause.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JFieldDeclarationWrapper.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlLoopInvariant.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlConstraint.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/AndNotPatternFilenameFilter.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlReachExpression.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlNormalSpecBody.java", //$NON-NLS-1$
                                              "JML2/org/jmlspecs/checker/JmlClassOrGFImport.java" //$NON-NLS-1$
                                              };
		if (this.filename != null && (this.filename.indexOf("MJ") > 0 || this.filename.indexOf("JML2") > 0)) { //$NON-NLS-1$ //$NON-NLS-2$
			for (int i = 0; i < files_35_jml.length; i++) {
				if (this.filename.endsWith(files_35_jml[i])) {
					return true;
				}
			}
			return false;
		}
		return true;
	}

	public boolean visit(ConstructorDeclaration constructorDeclaration,
			ClassScope scope) {
		// Logger.println("\t visit constructor "+new
		// String(constructorDeclaration.selector));
		// Logger.println("\t ----- <constructor>");
		dumpParams(constructorDeclaration.arguments);
		return true;
	}

	private void dumpParams(Argument[] arguments) {
		/*
		 * if (arguments == null) System.out.println("args is null!"); for(int
		 * i=0; arguments != null && i < arguments.length; i++) { Argument
		 * argument = arguments[i]; if (argument.type instanceof
		 * JmlTypeReference) { Nullity nullity =
		 * ((JmlTypeReference)argument.type).getNullity(); if
		 * (nullity.isNon_null()) { Logger.println("\t\t visit arg - 1
		 * "+new String(argument.name)+" 1 "+argument.type.toString()); } else {
		 * Logger.println("\t\t visit arg - 2 "+new String(argument.name)+"
		 * 2 "+argument.type.toString()); } } else { Logger.println("\t\t
		 * visit arg - 3 "+new String(argument.name)+" 3
		 * "+argument.type.toString()); } }
		 */
		for (int i = 0; arguments != null && i < arguments.length; i++) {
			Argument argument = arguments[i];
			if (argument.type instanceof JmlTypeReference
					&& !Nullity.isPrimitiveType(argument.type.resolvedType)) {
				Nullity nullity = ((JmlTypeReference) argument.type)
						.getNullity();
				if (nullity != null) {
					testForExplicitNullity(argument.type, new String(
							argument.name));
					if (nullity.isNon_null()) {
						param_non_null++;
						cu_param_non_null++;
					} else {
						param_nullable++;
						cu_param_nullable++;
					}
				}
			}
		}

	}

	public boolean visit(CompilationUnitDeclaration compilationUnitDeclaration,
			CompilationUnitScope scope) {
		// Logger.println("about to visit "+new
		// String(compilationUnitDeclaration.getFileName()));

		// if (this.problemReporter.referenceContext == null) {
		this.problemReporter.referenceContext = compilationUnitDeclaration;
		// }
		this.filename = new String(compilationUnitDeclaration.getFileName()).replace('\\', '/');
		cu_field_non_null = 0;
		cu_field_nullable = 0;
		cu_method_non_null = 0;
		cu_method_nullable = 0;
		cu_param_non_null = 0;
		cu_param_nullable = 0;

		typeCount = 0;

		return true;
	}

	public void endVisit(CompilationUnitDeclaration compilationUnitDeclaration,
			CompilationUnitScope scope) {
		// Logger.println("end of visit to "+new
		// String(compilationUnitDeclaration.getFileName())); //$NON-NLS-1$
		// Logger.println(""); //$NON-NLS-1$

		log("count" //$NON-NLS-1$ 
				+ "\t" + new String(compilationUnitDeclaration.getFileName()) //$NON-NLS-1$ 
				+ "\t" + "+" //$NON-NLS-1$ //$NON-NLS-2$
				+ "\t" + typeCount //$NON-NLS-1$ 
				+ "\t" + cu_field_non_null//$NON-NLS-1$ 
				+ "\t" + cu_field_nullable//$NON-NLS-1$ 
				+ "\t" + cu_method_non_null//$NON-NLS-1$ 
				+ "\t" + cu_method_nullable//$NON-NLS-1$ 
				+ "\t" + cu_param_non_null//$NON-NLS-1$ 
				+ "\t" + cu_param_nullable);//$NON-NLS-1$ 
	}

	public boolean visit(TypeDeclaration typeDeclaration,
			CompilationUnitScope scope) {

		this.problemReporter.referenceContext = typeDeclaration;

		// Logger.println("about to visit "+new
		// String(typeDeclaration.name)+" in "+new
		// String(scope.referenceContext.getFileName()));
		field_non_null = 0;
		field_nullable = 0;
		method_non_null = 0;
		method_nullable = 0;
		param_non_null = 0;
		param_nullable = 0;

		typeCount++;

		return true;
	}

	public void endVisit(TypeDeclaration typeDeclaration,
			CompilationUnitScope scope) {
		// Logger.println("end of visit to "+new
		// String(typeDeclaration.name)+" in "+new
		// String(scope.referenceContext.getFileName()));
		// Logger.println("");

		/*
		 * don't report stats on a per-type basis Logger.println(
		 * "count"//$NON-NLS-1$ +"\t"+new
		 * String(typeDeclaration.name)//$NON-NLS-1$ +"\t"+new
		 * String(scope.referenceContext.getFileName())//$NON-NLS-1$
		 * +"\t"+"-"//$NON-NLS-1$ //$NON-NLS-2$
		 * +"\t"+field_non_null//$NON-NLS-1$ +"\t"+field_nullable//$NON-NLS-1$
		 * +"\t"+method_non_null//$NON-NLS-1$ +"\t"+method_nullable//$NON-NLS-1$
		 * +"\t"+param_non_null//$NON-NLS-1$ +"\t"+param_nullable);//$NON-NLS-1$
		 */
		for (int i = 0; typeDeclaration.memberTypes != null
				&& i < typeDeclaration.memberTypes.length; i++) {
			visit(typeDeclaration.memberTypes[i], scope);
			endVisit(typeDeclaration.memberTypes[i], scope);
		}
	}

}
