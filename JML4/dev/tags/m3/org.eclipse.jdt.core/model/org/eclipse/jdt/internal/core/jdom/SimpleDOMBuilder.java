/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.core.jdom;

import java.util.Map;

import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.compiler.CategorizedProblem;
import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.jdom.*;
import org.eclipse.jdt.internal.compiler.ISourceElementRequestor;
import org.eclipse.jdt.internal.compiler.SourceElementParser;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.ImportReference;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.env.ICompilationUnit;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblemFactory;
/**
 * A DOM builder that uses the SourceElementParser
 * @deprecated The JDOM was made obsolete by the addition in 2.0 of the more
 * powerful, fine-grained DOM/AST API found in the 
 * org.eclipse.jdt.core.dom package.
 */
public class SimpleDOMBuilder extends AbstractDOMBuilder implements ISourceElementRequestor {

/**
 * Does nothing.
 */
public void acceptProblem(CategorizedProblem problem) {
	// nothing to do
}

public void acceptImport(int declarationStart, int declarationEnd, char[][] tokens, boolean onDemand, int modifiers) {
	int[] sourceRange = {declarationStart, declarationEnd};
	String importName = new String(CharOperation.concatWith(tokens, '.'));
	/** name is set to contain the '*' */
	if (onDemand) {
		importName+=".*"; //$NON-NLS-1$
	}
	fNode= new DOMImport(fDocument, sourceRange, importName, onDemand, modifiers);
	addChild(fNode);	
}
public void acceptPackage(ImportReference importReference) {
	int[] sourceRange= new int[] {importReference.declarationSourceStart, importReference.declarationSourceEnd};
	char[] name = CharOperation.concatWith(importReference.getImportName(), '.');
	fNode= new DOMPackage(fDocument, sourceRange, new String(name));
	addChild(fNode);	
}
/**
 * @see IDOMFactory#createCompilationUnit(String, String)
 */
public IDOMCompilationUnit createCompilationUnit(String sourceCode, String name) {
	return createCompilationUnit(sourceCode.toCharArray(), name.toCharArray());
}
/**
 * @see IDOMFactory#createCompilationUnit(String, String)
 */
public IDOMCompilationUnit createCompilationUnit(ICompilationUnit compilationUnit) {
	initializeBuild(compilationUnit.getContents(), true, true);
	getParser(JavaCore.getOptions()).parseCompilationUnit(compilationUnit, false/*diet parse*/, null/*no progress*/);
	return super.createCompilationUnit(compilationUnit);
}
/**
 * Creates a new DOMMethod and inizializes.
 */
protected void enterAbstractMethod(MethodInfo methodInfo) {
		
	int[] sourceRange = {methodInfo.declarationStart, -1}; // will be fixed up on exit
	int[] nameRange = {methodInfo.nameSourceStart, methodInfo.nameSourceEnd};
	fNode = new DOMMethod(fDocument, sourceRange, CharOperation.charToString(methodInfo.name), nameRange, methodInfo.modifiers, 
		methodInfo.isConstructor, CharOperation.charToString(methodInfo.returnType),
		CharOperation.charArrayToStringArray(methodInfo.parameterTypes),
		CharOperation.charArrayToStringArray(methodInfo.parameterNames), 
		CharOperation.charArrayToStringArray(methodInfo.exceptionTypes));
	addChild(fNode);
	fStack.push(fNode);
	
	// type parameters not supported by JDOM
}
/**
 */
public void enterConstructor(MethodInfo methodInfo) {
	/* see 1FVIIQZ */
	String nameString = new String(fDocument, methodInfo.nameSourceStart, methodInfo.nameSourceEnd - methodInfo.nameSourceStart);
	int openParenPosition = nameString.indexOf('(');
	if (openParenPosition > -1)
		methodInfo.nameSourceEnd = methodInfo.nameSourceStart + openParenPosition - 1;

	enterAbstractMethod(methodInfo);
}
/**
 */
public void enterField(FieldInfo fieldInfo) {

	int[] sourceRange = {fieldInfo.declarationStart, -1};
	int[] nameRange = {fieldInfo.nameSourceStart, fieldInfo.nameSourceEnd};
	boolean isSecondary= false;
	if (fNode instanceof DOMField) {
		isSecondary = fieldInfo.declarationStart == fNode.fSourceRange[0];
	}
	fNode = new DOMField(fDocument, sourceRange, CharOperation.charToString(fieldInfo.name), nameRange, 
		fieldInfo.modifiers, CharOperation.charToString(fieldInfo.type), isSecondary);
	addChild(fNode);
	fStack.push(fNode);
}
/**

 */
public void enterInitializer(int declarationSourceStart, int modifiers) {
	int[] sourceRange = {declarationSourceStart, -1};
	fNode = new DOMInitializer(fDocument, sourceRange, modifiers);
	addChild(fNode);
	fStack.push(fNode);
}
/**
 */
public void enterMethod(MethodInfo methodInfo) {
	enterAbstractMethod(methodInfo);
}
/**
 */
public void enterType(TypeInfo typeInfo) {
	if (fBuildingType) {
		int[] sourceRange = {typeInfo.declarationStart, -1}; // will be fixed in the exit
		int[] nameRange = new int[] {typeInfo.nameSourceStart, typeInfo.nameSourceEnd};
		fNode = new DOMType(fDocument, sourceRange, new String(typeInfo.name), nameRange,
			typeInfo.modifiers, CharOperation.charArrayToStringArray(typeInfo.superinterfaces), TypeDeclaration.kind(typeInfo.modifiers) == TypeDeclaration.CLASS_DECL); // TODO (jerome) should pass in kind
		addChild(fNode);
		fStack.push(fNode);
		
		// type parameters not supported by JDOM
	}
}
/**
 * Finishes the configuration of the method DOM object which
 * was created by a previous enterConstructor call.
 *
 * @see ISourceElementRequestor#exitConstructor(int)
 */
public void exitConstructor(int declarationEnd) {
	exitMember(declarationEnd);
}
/**
 */
public void exitField(int initializationStart, int declarationEnd, int declarationSourceEnd) {
	exitMember(declarationEnd);
}
/**
 */
public void exitInitializer(int declarationEnd) {
	exitMember(declarationEnd);
}
/**
 * Finishes the configuration of the member.
 *
 * @param declarationEnd - a source position corresponding to the end of the method
 *		declaration.  This can include whitespace and comments following the closing bracket.
 */
protected void exitMember(int declarationEnd) {
	DOMMember m= (DOMMember) fStack.pop();
	m.setSourceRangeEnd(declarationEnd);
	fNode = m;
}
/**
 */
public void exitMethod(int declarationEnd, Expression defaultValue) {
	exitMember(declarationEnd);
}
/**
 * @see AbstractDOMBuilder#exitType
 *
 * @param declarationEnd - a source position corresponding to the end of the class
 *		declaration.  This can include whitespace and comments following the closing bracket.
 */
public void exitType(int declarationEnd) {
	exitType(declarationEnd, declarationEnd);
}
/**
 * Creates a new parser.
 */
protected SourceElementParser getParser(Map settings) {
	return new SourceElementParser(this, new DefaultProblemFactory(), new CompilerOptions(settings), false/*don't report local declarations*/, true/*optimize string literals*/);
}
}