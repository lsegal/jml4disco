/*******************************************************************************
 * Copyright (c) 2000, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.core.tests.rewrite.describing;

import java.util.List;

import junit.framework.Test;
import junit.framework.TestSuite;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IPackageFragment;

import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;

public class ASTRewritingTypeDeclTest extends ASTRewritingTest {
	
	private static final Class THIS= ASTRewritingTypeDeclTest.class;
	
	public ASTRewritingTypeDeclTest(String name) {
		super(name);
	}

	public static Test allTests() {
		return new Suite(THIS);
	}
	
	public static Test setUpTest(Test someTest) {
		TestSuite suite= new Suite("one test");
		suite.addTest(someTest);
		return suite;
	}
	
	public static Test suite() {
		if (true) {
			return allTests();
		}
		return setUpTest(new ASTRewritingTypeDeclTest("testEnumDeclaration"));
	}
		
	/** @deprecated using deprecated code */
	public void testTypeDeclChanges() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E extends Exception implements Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("class F implements Runnable {\n");
		buf.append("    public void foo() {\n");
		buf.append("    }\n");		
		buf.append("}\n");
		buf.append("interface G {\n");
		buf.append("}\n");		
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{  // rename type, rename supertype, rename first interface, replace inner class with field
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			SimpleName name= type.getName();
			SimpleName newName= ast.newSimpleName("X");
			
			rewrite.replace(name, newName, null);
			
			Name superClass= type.getSuperclass();
			assertTrue("Has super type", superClass != null);
			
			SimpleName newSuperclass= ast.newSimpleName("Object");
			rewrite.replace(superClass, newSuperclass, null);

			List superInterfaces= type.superInterfaces();
			assertTrue("Has super interfaces", !superInterfaces.isEmpty());
			
			SimpleName newSuperinterface= ast.newSimpleName("Cloneable");
			rewrite.replace((ASTNode) superInterfaces.get(0), newSuperinterface, null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			FieldDeclaration newFieldDecl= createNewField(ast, "fCount");
			
			rewrite.replace((ASTNode) members.get(0), newFieldDecl, null);
		}
		{ // replace method in F, change to interface
			TypeDeclaration type= findTypeDeclaration(astRoot, "F");
			
			// change flags
			int newModifiers= 0;
			rewrite.set(type, TypeDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);

			// change to interface
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.TRUE, null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", members.size() == 1);

			MethodDeclaration methodDecl= createNewMethod(ast, "newFoo", true);

			rewrite.replace((ASTNode) members.get(0), methodDecl, null);
		}
		
		{ // change to class, add supertype
			TypeDeclaration type= findTypeDeclaration(astRoot, "G");
			
			// change flags
			int newModifiers= 0;
			rewrite.set(type, TypeDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);

			// change to class
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.FALSE, null);
			
			
			SimpleName newSuperclass= ast.newSimpleName("Object");
			rewrite.set(type, TypeDeclaration.SUPERCLASS_PROPERTY, newSuperclass, null);
		}			
					

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class X extends Object implements Cloneable, Serializable {\n");
		buf.append("    private double fCount;\n");
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("interface F extends Runnable {\n");
		buf.append("    private abstract void newFoo(String str);\n");
		buf.append("}\n");				
		buf.append("class G extends Object {\n");
		buf.append("}\n");			
		assertEqualString(preview, buf.toString());

	}
	
	public void testTypeDeclChanges2() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E extends Exception implements Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("final class F implements Runnable {\n");
		buf.append("    public void foo() {\n");
		buf.append("    }\n");		
		buf.append("}\n");
		buf.append("interface G {\n");
		buf.append("}\n");		
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{  // rename type, rename supertype, rename first interface, replace inner class with field
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			SimpleName name= type.getName();
			SimpleName newName= ast.newSimpleName("X");
			
			rewrite.replace(name, newName, null);
			
			Type superClass= type.getSuperclassType();
			assertTrue("Has super type", superClass != null);
			
			Type newSuperclass= ast.newSimpleType(ast.newSimpleName("Object"));
			rewrite.replace(superClass, newSuperclass, null);

			List superInterfaces= type.superInterfaceTypes();
			assertTrue("Has super interfaces", !superInterfaces.isEmpty());
			
			Type newSuperinterface= ast.newSimpleType(ast.newSimpleName("Cloneable"));
			rewrite.replace((ASTNode) superInterfaces.get(0), newSuperinterface, null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			FieldDeclaration newFieldDecl= createNewField(ast, "fCount");
			
			rewrite.replace((ASTNode) members.get(0), newFieldDecl, null);
		}
		{ // replace method in F, change to interface
			TypeDeclaration type= findTypeDeclaration(astRoot, "F");
			
			rewrite.remove((ASTNode) type.modifiers().get(0), null);
			
			// change to interface
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.TRUE, null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", members.size() == 1);

			MethodDeclaration methodDecl= createNewMethod(ast, "newFoo", true);

			rewrite.replace((ASTNode) members.get(0), methodDecl, null);
		}
		
		{ // add modifier, change to class, add supertype
			TypeDeclaration type= findTypeDeclaration(astRoot, "G");
			
			rewrite.getListRewrite(type, TypeDeclaration.MODIFIERS2_PROPERTY).insertFirst(ast.newModifier(Modifier.ModifierKeyword.FINAL_KEYWORD), null);
						
			// change to class
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.FALSE, null);
			
			
			Type newSuperclass= ast.newSimpleType(ast.newSimpleName("Object"));
			rewrite.set(type, TypeDeclaration.SUPERCLASS_TYPE_PROPERTY, newSuperclass, null);
		}			
					

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class X extends Object implements Cloneable, Serializable {\n");
		buf.append("    private double fCount;\n");
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("interface F extends Runnable {\n");
		buf.append("    private abstract void newFoo(String str);\n");
		buf.append("}\n");				
		buf.append("final class G extends Object {\n");
		buf.append("}\n");			
		assertEqualString(preview, buf.toString());

	}

	/** @deprecated using deprecated code */
	public void testTypeDeclRemoves() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E extends Exception implements Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("class F implements Runnable {\n");
		buf.append("    public void foo() {\n");
		buf.append("    }\n");		
		buf.append("}\n");
		buf.append("interface G {\n");
		buf.append("}\n");		
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		{ // change to interface, remove supertype, remove first interface, remove field
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			
			// change flags
			int newModifiers= 0;
			rewrite.set(type, TypeDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);

			// change to interface
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.TRUE, null);
		
			Name superClass= type.getSuperclass();
			assertTrue("Has super type", superClass != null);
			
			rewrite.remove(superClass, null);

			List superInterfaces= type.superInterfaces();
			assertTrue("Has super interfaces", !superInterfaces.isEmpty());
			
			rewrite.remove((ASTNode) superInterfaces.get(0), null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
					
			rewrite.remove((ASTNode) members.get(1), null);
			
			MethodDeclaration meth= findMethodDeclaration(type, "hee");
			rewrite.remove(meth, null);
		}
		{ // remove superinterface & method, change to interface & final
			TypeDeclaration type= findTypeDeclaration(astRoot, "F");
					
			// change flags
			int newModifiers= Modifier.FINAL;
			rewrite.set(type, TypeDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);

			// change to interface
			rewrite.set(type, TypeDeclaration.INTERFACE_PROPERTY, Boolean.TRUE, null);
			
			List superInterfaces= type.superInterfaces();
			assertTrue("Has super interfaces", !superInterfaces.isEmpty());
			rewrite.remove((ASTNode) superInterfaces.get(0), null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", members.size() == 1);

			rewrite.remove((ASTNode) members.get(0), null);			
		}			
		{ // remove class G
			TypeDeclaration type= findTypeDeclaration(astRoot, "G");
			rewrite.remove(type, null);		
		}				

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("interface E extends Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("final interface F {\n");
		buf.append("}\n");				
		assertEqualString(preview, buf.toString());

	}

	public void testTypeDeclInserts() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E extends Exception implements Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("class F implements Runnable {\n");
		buf.append("    public void foo() {\n");
		buf.append("    }\n");		
		buf.append("}\n");
		buf.append("interface G {\n");
		buf.append("}\n");		
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		assertTrue("Errors in AST", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		AST ast= astRoot.getAST();
		{ // add interface & set to final
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
					
			// change flags
			int newModifiers= Modifier.PUBLIC | Modifier.FINAL;
			rewrite.set(type, TypeDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);
				
			SimpleName newSuperinterface= ast.newSimpleName("Cloneable");
			
			rewrite.getListRewrite(type, TypeDeclaration.SUPER_INTERFACES_PROPERTY).insertFirst(newSuperinterface, null);
			
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			assertTrue("Cannot find inner class", members.get(0) instanceof TypeDeclaration);
			TypeDeclaration innerType= (TypeDeclaration) members.get(0);

/*		bug 22161
			SimpleName newSuperclass= ast.newSimpleName("Exception");
			innerType.setSuperclass(newSuperclass);
			rewrite.markAsInserted(newSuperclass);
*/

			FieldDeclaration newField= createNewField(ast, "fCount");
			
			rewrite.getListRewrite(innerType, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertFirst(newField, null);
			
			MethodDeclaration newMethodDecl= createNewMethod(ast, "newMethod", false);
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertAt(newMethodDecl, 4, null);
		}
		{ // add exception, add method
			TypeDeclaration type= findTypeDeclaration(astRoot, "F");
			
			SimpleName newSuperclass= ast.newSimpleName("Exception");
			rewrite.set(type, TypeDeclaration.SUPERCLASS_PROPERTY, newSuperclass, null);
					
			MethodDeclaration newMethodDecl= createNewMethod(ast, "newMethod", false);
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertLast(newMethodDecl, null);
		}			
		{ // insert interface
			TypeDeclaration type= findTypeDeclaration(astRoot, "G");
						
			SimpleName newInterface= ast.newSimpleName("Runnable");
			rewrite.getListRewrite(type, TypeDeclaration.SUPER_INTERFACES_PROPERTY).insertLast(newInterface, null);
			
			MethodDeclaration newMethodDecl= createNewMethod(ast, "newMethod", true);
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertLast(newMethodDecl,  null);
		}			

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public final class E extends Exception implements Cloneable, Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        private double fCount;\n");
		buf.append("\n");				
		buf.append("        public void xee() {\n");
		buf.append("        }\n");
		buf.append("    }\n");		
		buf.append("    private int i;\n");	
		buf.append("    private int k;\n");	
		buf.append("    public E() {\n");
		buf.append("    }\n");
		buf.append("    private void newMethod(String str) {\n");
		buf.append("    }\n");		
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		buf.append("class F extends Exception implements Runnable {\n");
		buf.append("    public void foo() {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("    private void newMethod(String str) {\n");
		buf.append("    }\n");		
		buf.append("}\n");				
		buf.append("interface G extends Runnable {\n");
		buf.append("\n");		
		buf.append("    private abstract void newMethod(String str);\n");		
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testTypeDeclInsertFields1() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("}\n");
		buf.append("class F {\n");
		buf.append("}\n");		
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		assertTrue("Errors in AST", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		AST ast= astRoot.getAST();
		{ 	
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			
			VariableDeclarationFragment frag= ast.newVariableDeclarationFragment();
			frag.setName(ast.newSimpleName("x"));
			
			FieldDeclaration decl= ast.newFieldDeclaration(frag);
			decl.setType(ast.newPrimitiveType(PrimitiveType.INT));

			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertFirst(decl, null);
			
		}
		{ 	
			TypeDeclaration type= findTypeDeclaration(astRoot, "F");
			
			VariableDeclarationFragment frag1= ast.newVariableDeclarationFragment();
			frag1.setName(ast.newSimpleName("x"));
			
			FieldDeclaration decl1= ast.newFieldDeclaration(frag1);
			decl1.setType(ast.newPrimitiveType(PrimitiveType.INT));
			
			VariableDeclarationFragment frag2= ast.newVariableDeclarationFragment();
			frag2.setName(ast.newSimpleName("y"));
			
			FieldDeclaration decl2= ast.newFieldDeclaration(frag2);
			decl2.setType(ast.newPrimitiveType(PrimitiveType.INT));			
						
			ListRewrite listRewrite= rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
			listRewrite.insertFirst(decl1, null);
			listRewrite.insertAfter(decl2, decl1, null);
		}				

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("\n");
		buf.append("    int x;\n");
		buf.append("}\n");
		buf.append("class F {\n");
		buf.append("\n");
		buf.append("    int x;\n");
		buf.append("    int y;\n");	
		buf.append("}\n");		
		assertEqualString(preview, buf.toString());

	}	
	
	
	public void testTypeParameters() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("class E extends A {}\n");
		buf.append("class F {}\n");
		buf.append("class G <T> extends A {}\n");
		buf.append("class H <T> {}\n");
		buf.append("class I<T> extends A {}\n");
		buf.append("class J<T>extends A {}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);	
		
		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		List types= astRoot.types();

		for (int i= 0; i < 2; i++) {
			// add type parameter
			TypeDeclaration typeDecl= (TypeDeclaration) types.get(i);
			ListRewrite listRewrite= rewrite.getListRewrite(typeDecl, TypeDeclaration.TYPE_PARAMETERS_PROPERTY);
			TypeParameter typeParameter= ast.newTypeParameter();
			typeParameter.setName(ast.newSimpleName("X"));
			listRewrite.insertFirst(typeParameter, null);
		}
		for (int i= 2; i < 6; i++) {
			// remove type parameter
			TypeDeclaration typeDecl= (TypeDeclaration) types.get(i);
			rewrite.remove((ASTNode) typeDecl.typeParameters().get(0), null);
		}	
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("class E<X> extends A {}\n");
		buf.append("class F<X> {}\n");
		buf.append("class G extends A {}\n");
		buf.append("class H {}\n");	
		buf.append("class I extends A {}\n");
		buf.append("class J extends A {}\n");
		assertEqualString(preview, buf.toString());
	}
	
	
	public void testBug22161() throws Exception {
	//	System.out.println(getClass().getName()+"::" + getName() +" disabled (bug 22161)");
	
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class T extends Exception implements Runnable, Serializable {\n");
		buf.append("    public static class EInner {\n");
		buf.append("        public void xee() {\n");
		buf.append("        }\n");		
		buf.append("    }\n");		
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("T.java", buf.toString(), false, null);				

		CompilationUnit astRoot= createAST(cu);
		assertTrue("Errors in AST", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		
		TypeDeclaration type= findTypeDeclaration(astRoot, "T");
		assertTrue("Outer type not found", type != null);
		
		List members= type.bodyDeclarations();
		assertTrue("Cannot find inner class", members.size() == 1 &&  members.get(0) instanceof TypeDeclaration);

		TypeDeclaration innerType= (TypeDeclaration) members.get(0);
		
		SimpleName name= innerType.getName();
		assertTrue("Name positions not correct", name.getStartPosition() != -1 && name.getLength() > 0);
		
	}
	
	public void testAnonymousClassDeclaration() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E2 {\n");
		buf.append("    public void foo() {\n");
		buf.append("        new Runnable() {\n");
		buf.append("        };\n");
		buf.append("        new Runnable() {\n");
		buf.append("            int i= 8;\n");
		buf.append("        };\n");
		buf.append("        new Runnable() {\n");
		buf.append("            int i= 8;\n");
		buf.append("        };\n");		
		buf.append("    }\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("E2.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		TypeDeclaration type= findTypeDeclaration(astRoot, "E2");
		MethodDeclaration methodDecl= findMethodDeclaration(type, "foo");
		Block block= methodDecl.getBody();
		List statements= block.statements();
		assertTrue("Number of statements not 3", statements.size() == 3);
		{	// insert body decl in AnonymousClassDeclaration
			ExpressionStatement stmt= (ExpressionStatement) statements.get(0);
			ClassInstanceCreation creation= (ClassInstanceCreation) stmt.getExpression();
			AnonymousClassDeclaration anonym= creation.getAnonymousClassDeclaration();
			assertTrue("no anonym class decl", anonym != null);
			
			List decls= anonym.bodyDeclarations();
			assertTrue("Number of bodyDeclarations not 0", decls.size() == 0);
			
			MethodDeclaration newMethod= createNewMethod(ast, "newMethod", false);
			rewrite.getListRewrite(anonym, AnonymousClassDeclaration.BODY_DECLARATIONS_PROPERTY).insertFirst(newMethod, null);
		}
		{	// remove body decl in AnonymousClassDeclaration
			ExpressionStatement stmt= (ExpressionStatement) statements.get(1);
			ClassInstanceCreation creation= (ClassInstanceCreation) stmt.getExpression();
			AnonymousClassDeclaration anonym= creation.getAnonymousClassDeclaration();
			assertTrue("no anonym class decl", anonym != null);
			
			List decls= anonym.bodyDeclarations();
			assertTrue("Number of bodyDeclarations not 1", decls.size() == 1);

			rewrite.remove((ASTNode) decls.get(0), null);
		}		
		{	// replace body decl in AnonymousClassDeclaration
			ExpressionStatement stmt= (ExpressionStatement) statements.get(2);
			ClassInstanceCreation creation= (ClassInstanceCreation) stmt.getExpression();
			AnonymousClassDeclaration anonym= creation.getAnonymousClassDeclaration();
			assertTrue("no anonym class decl", anonym != null);
			
			List decls= anonym.bodyDeclarations();
			assertTrue("Number of bodyDeclarations not 1", decls.size() == 1);
			
			MethodDeclaration newMethod= createNewMethod(ast, "newMethod", false);

			rewrite.replace((ASTNode) decls.get(0), newMethod, null);
		}	
					
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E2 {\n");
		buf.append("    public void foo() {\n");
		buf.append("        new Runnable() {\n");
		buf.append("\n");
		buf.append("            private void newMethod(String str) {\n");
		buf.append("            }\n");	
		buf.append("        };\n");
		buf.append("        new Runnable() {\n");
		buf.append("        };\n");
		buf.append("        new Runnable() {\n");
		buf.append("            private void newMethod(String str) {\n");
		buf.append("            }\n");	
		buf.append("        };\n");		
		buf.append("    }\n");
		buf.append("}\n");	
			
		assertEqualString(preview, buf.toString());

	}
			
	public void testImportDeclaration() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("import java.util.Vector;\n");
		buf.append("import java.util.Vector;\n");
		buf.append("import java.net.*;\n");
		buf.append("import java.text.*;\n");
		buf.append("import static java.lang.Math.*;\n");
		buf.append("import java.lang.Math.*;\n");		
		buf.append("public class Z {\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("Z.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		
		List imports= astRoot.imports();
		assertTrue("Number of imports not 6", imports.size() == 6);
		
		{ // rename import
			ImportDeclaration imp= (ImportDeclaration) imports.get(0);
			
			Name name= ast.newName(new String[] { "org", "eclipse", "X" });
			rewrite.replace(imp.getName(), name, null);
		}
		{ // change to import on demand
			ImportDeclaration imp= (ImportDeclaration) imports.get(1);
			
			Name name= ast.newName(new String[] { "java", "util" });
			rewrite.replace(imp.getName(), name, null);
			
			rewrite.set(imp, ImportDeclaration.ON_DEMAND_PROPERTY, Boolean.TRUE, null);
		}
		{ // change to single import
			ImportDeclaration imp= (ImportDeclaration) imports.get(2);
			
			rewrite.set(imp, ImportDeclaration.ON_DEMAND_PROPERTY, Boolean.FALSE, null);
		}
		{ // rename import
			ImportDeclaration imp= (ImportDeclaration) imports.get(3);
			
			Name name= ast.newName(new String[] { "org", "eclipse" });
			rewrite.replace(imp.getName(), name, null);
		}
		{ // remove static 
			ImportDeclaration imp= (ImportDeclaration) imports.get(4);
			
			rewrite.set(imp, ImportDeclaration.STATIC_PROPERTY, Boolean.FALSE, null);
		}
		{ // add static
			ImportDeclaration imp= (ImportDeclaration) imports.get(5);
			
			rewrite.set(imp, ImportDeclaration.STATIC_PROPERTY, Boolean.TRUE, null);
		}
				
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("import org.eclipse.X;\n");
		buf.append("import java.util.*;\n");
		buf.append("import java.net;\n");
		buf.append("import org.eclipse.*;\n");
		buf.append("import java.lang.Math.*;\n");
		buf.append("import static java.lang.Math.*;\n");
		buf.append("public class Z {\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testPackageDeclaration() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class Z {\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("Z.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		
		{ // rename package
			PackageDeclaration packageDeclaration= astRoot.getPackage();
			
			Name name= ast.newName(new String[] { "org", "eclipse" });
			
			rewrite.replace(packageDeclaration.getName(), name, null);
		}
				
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package org.eclipse;\n");
		buf.append("public class Z {\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testCompilationUnit() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class Z {\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("Z.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		
		{
			PackageDeclaration packageDeclaration= astRoot.getPackage();
			rewrite.remove(packageDeclaration, null);
		}
				
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("\n");	
		buf.append("public class Z {\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testCompilationUnit2() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("public class Z {\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("Z.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		
		{
			PackageDeclaration packageDeclaration= ast.newPackageDeclaration();
			Name name= ast.newName(new String[] { "org", "eclipse" });
			packageDeclaration.setName(name);
			
			rewrite.set(astRoot, CompilationUnit.PACKAGE_PROPERTY, packageDeclaration, null);
		}
				
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package org.eclipse;\n");
		buf.append("public class Z {\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}	
	
	public void testSingleVariableDeclaration() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void foo(int i, final int[] k, int[] x[]) {\n");
		buf.append("    }\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		TypeDeclaration type= findTypeDeclaration(astRoot, "E");

		MethodDeclaration methodDecl= findMethodDeclaration(type, "foo");
		List arguments= methodDecl.parameters();
		{ // add modifier, change type, change name, add extra dimension
			SingleVariableDeclaration decl= (SingleVariableDeclaration) arguments.get(0);
					
			int newModifiers= Modifier.FINAL;
			rewrite.set(decl, SingleVariableDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);

			rewrite.set(decl, SingleVariableDeclaration.EXTRA_DIMENSIONS_PROPERTY, new Integer(1), null);
			
			ArrayType newVarType= ast.newArrayType(ast.newPrimitiveType(PrimitiveType.FLOAT), 2);
			rewrite.replace(decl.getType(), newVarType, null);
			
			Name newName= ast.newSimpleName("count");
			rewrite.replace(decl.getName(), newName, null);
		}
		{ // remove modifier, change type
			SingleVariableDeclaration decl= (SingleVariableDeclaration) arguments.get(1);
						
			int newModifiers= 0;
			rewrite.set(decl, SingleVariableDeclaration.MODIFIERS_PROPERTY, new Integer(newModifiers), null);
			
			Type newVarType= ast.newPrimitiveType(PrimitiveType.FLOAT);
			rewrite.replace(decl.getType(), newVarType, null);
		}
		{ // remove extra dim
			SingleVariableDeclaration decl= (SingleVariableDeclaration) arguments.get(2);
			
			rewrite.set(decl, SingleVariableDeclaration.EXTRA_DIMENSIONS_PROPERTY, new Integer(0), null);
		}			
			
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void foo(final float[][] count[], float k, int[] x) {\n");
		buf.append("    }\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}	
	
	public void testVariableDeclarationFragment() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void foo() {\n");
		buf.append("        int i, j, k= 0, x[][], y[]= {0, 1};\n");		
		buf.append("    }\n");
		buf.append("}\n");	
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);
		
		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		AST ast= astRoot.getAST();
		
		assertTrue("Parse errors", (astRoot.getFlags() & ASTNode.MALFORMED) == 0);
		TypeDeclaration type= findTypeDeclaration(astRoot, "E");

		MethodDeclaration methodDecl= findMethodDeclaration(type, "foo");
		Block block= methodDecl.getBody();
		List statements= block.statements();
		assertTrue("Number of statements not 1", statements.size() == 1);
		
		VariableDeclarationStatement variableDeclStatement= (VariableDeclarationStatement) statements.get(0);
		List fragments= variableDeclStatement.fragments();
		assertTrue("Number of fragments not 5", fragments.size() == 5);
		
		{ // rename var, add dimension
			VariableDeclarationFragment fragment= (VariableDeclarationFragment) fragments.get(0);
			
			ASTNode name= ast.newSimpleName("a");
			rewrite.replace(fragment.getName(), name, null);
			
			rewrite.set(fragment, VariableDeclarationFragment.EXTRA_DIMENSIONS_PROPERTY, new Integer(2), null);
		}
		
		{ // add initializer
			VariableDeclarationFragment fragment= (VariableDeclarationFragment) fragments.get(1);
			
			assertTrue("Has initializer", fragment.getInitializer() == null);
			
			Expression initializer= ast.newNumberLiteral("1");
			rewrite.set(fragment, VariableDeclarationFragment.INITIALIZER_PROPERTY, initializer, null);
		}
		
		{ // remove initializer
			VariableDeclarationFragment fragment= (VariableDeclarationFragment) fragments.get(2);
			
			assertTrue("Has no initializer", fragment.getInitializer() != null);
			rewrite.remove(fragment.getInitializer(), null);
		}
		{ // add dimension, add initializer
			VariableDeclarationFragment fragment= (VariableDeclarationFragment) fragments.get(3);			
			
			rewrite.set(fragment, VariableDeclarationFragment.EXTRA_DIMENSIONS_PROPERTY, new Integer(4), null);

			assertTrue("Has initializer", fragment.getInitializer() == null);
			
			Expression initializer= ast.newNullLiteral();
			rewrite.set(fragment, VariableDeclarationFragment.INITIALIZER_PROPERTY, initializer, null);
		}
		{ // remove dimension
			VariableDeclarationFragment fragment= (VariableDeclarationFragment) fragments.get(4);			
			
			rewrite.set(fragment, VariableDeclarationFragment.EXTRA_DIMENSIONS_PROPERTY, new Integer(0), null);
		}					
			
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void foo() {\n");
		buf.append("        int a[][], j = 1, k, x[][][][] = null, y= {0, 1};\n");		
		buf.append("    }\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testTypeDeclSpacingMethods1() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");		
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{  // insert method
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			MethodDeclaration newMethodDecl= createNewMethod(ast, "foo", false);
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertLast(newMethodDecl, null);
			
		}
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");		
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("\n");		
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");		
		buf.append("}\n");		
		assertEqualString(preview, buf.toString());

	}

	public void testTypeDeclSpacingMethods2() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("\n");			
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{  // insert method at first position
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			MethodDeclaration newMethodDecl= createNewMethod(ast, "foo", false);
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertFirst(newMethodDecl, null);
		}
		
		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("\n");			
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("\n");
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");		
		assertEqualString(preview, buf.toString());

	}
	
	public void testTypeDeclSpacingFields() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    private int x;\n");
		buf.append("    private int y;\n");
		buf.append("\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("\n");			
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{  // insert method at first position
			TypeDeclaration type= findTypeDeclaration(astRoot, "E");
			List members= type.bodyDeclarations();
			assertTrue("Has declarations", !members.isEmpty());
			
			FieldDeclaration newField= createNewField(ast, "fCount");
			rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY).insertFirst(newField, null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    private double fCount;\n");
		buf.append("    private int x;\n");
		buf.append("    private int y;\n");
		buf.append("\n");
		buf.append("    public void gee() {\n");
		buf.append("    }\n");
		buf.append("\n");
		buf.append("\n");			
		buf.append("    public void hee() {\n");
		buf.append("    }\n");
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}

	public void testEnumDeclaration() throws Exception {
		// test the creation of an enum declaration
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		TypeDeclaration type= findTypeDeclaration(astRoot, "E");
		List members= type.bodyDeclarations();
		assertTrue("Has declarations", members.isEmpty());
		
        ListRewrite declarations= rewrite.getListRewrite(type, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
		{  // insert an enum inner class
	        EnumDeclaration enumD= ast.newEnumDeclaration();
		      
	        // where fEnumName is a String
	        SimpleName enumName= ast.newSimpleName("MyEnum");
	        enumD.setName(enumName);
	        List enumStatements= enumD.enumConstants();

	        String[] names= { "a", "b", "c" };
	        
	        // where fFieldsToExtract is an array of SimpleNames
	        for (int i= 0; i < names.length; i++) {
	            String curr= names[i];
	            EnumConstantDeclaration constDecl= ast.newEnumConstantDeclaration();
	            constDecl.setName(ast.newSimpleName(curr));
	            enumStatements.add(constDecl);
	        }

	        declarations.insertFirst(enumD, null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("\n");
		buf.append("    enum MyEnum {\n");
		buf.append("        a, b, c\n");
		buf.append("    }\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	
	public void testEnumDeclaration1() throws Exception {
		// test the creation of an enum declaration
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");

		List members= declaration.bodyDeclarations();
		assertTrue("Has declarations", members.isEmpty());
		
        ListRewrite declarations= rewrite.getListRewrite(declaration, EnumDeclaration.ENUM_CONSTANTS_PROPERTY);
        EnumConstantDeclaration constDecl= ast.newEnumConstantDeclaration();
        constDecl.setName(ast.newSimpleName("A"));
        
        declarations.insertFirst(constDecl, null);
    

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}

	
	public void testEnumDeclaration2() throws Exception {
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B, C\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");
		
		{ 	
			// remove first, insert after 2nd
			rewrite.remove((ASTNode) declaration.enumConstants().get(0), null);
			
			ASTNode newNode= ast.newSimpleName("X");
			
			ListRewrite listRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.ENUM_CONSTANTS_PROPERTY);
			listRewrite.insertAfter(newNode, (ASTNode) declaration.enumConstants().get(1), null);
			
			// add body declaration
			
			ListRewrite bodyListRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.BODY_DECLARATIONS_PROPERTY);
			bodyListRewrite.insertFirst(createNewMethod(ast, "foo", false), null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    B, X, C;\n");
		buf.append("\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	public void testEnumDeclaration3() throws Exception {
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B, C;\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");
		
		{ 	
			// remove first, insert after 2nd
			rewrite.remove((ASTNode) declaration.enumConstants().get(0), null);
			
			ASTNode newNode= ast.newSimpleName("X");
			
			ListRewrite listRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.ENUM_CONSTANTS_PROPERTY);
			listRewrite.insertAfter(newNode, (ASTNode) declaration.enumConstants().get(1), null);
			
			// add body declaration
			
			ListRewrite bodyListRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.BODY_DECLARATIONS_PROPERTY);
			bodyListRewrite.insertFirst(createNewMethod(ast, "foo", false), null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    B, X, C;\n");
		buf.append("\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	public void testEnumDeclaration4() throws Exception {
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B, C;\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");
		{ 	
			rewrite.remove((ASTNode) declaration.enumConstants().get(2), null);
			rewrite.remove((ASTNode) declaration.bodyDeclarations().get(0), null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	public void testEnumDeclaration5() throws Exception {
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B, C;\n");
		buf.append("\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("    private void foo2(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");
		{ 	
			
			ASTNode newNode= astRoot.getAST().newSimpleName("X");
			
			ListRewrite listRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.ENUM_CONSTANTS_PROPERTY);
			listRewrite.insertAfter(newNode, (ASTNode) declaration.enumConstants().get(2), null);

			rewrite.remove((ASTNode) declaration.bodyDeclarations().get(0), null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A, B, C, X;\n");
		buf.append("\n");
		buf.append("    private void foo2(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}

	public void testEnumDeclaration6() throws Exception {
		// test the creation of an enum declaration
		
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    A\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");

		List members= declaration.bodyDeclarations();
		assertTrue("Has declarations", members.isEmpty());
		
		rewrite.remove((ASTNode) declaration.enumConstants().get(0), null);
    

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	public void testEnumDeclaration7() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		EnumDeclaration declaration= (EnumDeclaration) findAbstractTypeDeclaration(astRoot, "E");
		
		ListRewrite bodyListRewrite= rewrite.getListRewrite(declaration, EnumDeclaration.BODY_DECLARATIONS_PROPERTY);
		
		AST ast= astRoot.getAST();
		bodyListRewrite.insertFirst(createNewMethod(ast, "foo", false), null);

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public enum E {\n");
		buf.append("    ;\n");
		buf.append("\n");
		buf.append("    private void foo(String str) {\n");
		buf.append("    }\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());		
	}
	
	
	public void testAnnotationTypeDeclaration1() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("/**\n");
		buf.append(" * test\n");
		buf.append(" */\n");
		buf.append("public @interface E {\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		{
			AnnotationTypeDeclaration type= (AnnotationTypeDeclaration) findAbstractTypeDeclaration(astRoot, "E");
			
			ListRewrite listRewrite= rewrite.getListRewrite(type, AnnotationTypeDeclaration.MODIFIERS2_PROPERTY);
			listRewrite.insertFirst(ast.newModifier(Modifier.ModifierKeyword.FINAL_KEYWORD), null);
			
			SimpleName name= type.getName();
			SimpleName newName= ast.newSimpleName("X");
			
			rewrite.replace(name, newName, null);
			
			AnnotationTypeMemberDeclaration declaration= ast.newAnnotationTypeMemberDeclaration();
			declaration.setName(ast.newSimpleName("value"));
			declaration.setType(ast.newSimpleType(ast.newSimpleName("String")));
			
			ListRewrite bodyList= rewrite.getListRewrite(type, AnnotationTypeDeclaration.BODY_DECLARATIONS_PROPERTY);
			bodyList.insertFirst(declaration, null);
		}

		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("/**\n");
		buf.append(" * test\n");
		buf.append(" */\n");
		buf.append("final public @interface X {\n");
		buf.append("\n");	
		buf.append("    String value();\n");	
		buf.append("}\n");	
		assertEqualString(preview, buf.toString());

	}
	
	public void testWildcardType() throws Exception {
		IPackageFragment pack1= this.sourceFolder.createPackageFragment("test1", false, null);
		StringBuffer buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    X<?, ?, ? extends A, ? super B, ? extends A, ? super B> x;\n");
		buf.append("}\n");
		ICompilationUnit cu= pack1.createCompilationUnit("E.java", buf.toString(), false, null);			

		CompilationUnit astRoot= createAST3(cu);
		ASTRewrite rewrite= ASTRewrite.create(astRoot.getAST());
		AST ast= astRoot.getAST();
		
		TypeDeclaration type= findTypeDeclaration(astRoot, "E");
		FieldDeclaration field= type.getFields()[0];
		ParameterizedType fieldType= (ParameterizedType) field.getType();
		List args= fieldType.typeArguments();
		{
			WildcardType wildcardType= (WildcardType) args.get(0);
			rewrite.set(wildcardType, WildcardType.UPPER_BOUND_PROPERTY, Boolean.TRUE, null);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, ast.newSimpleType(ast.newSimpleName("A")), null);
		}
		{
			WildcardType wildcardType= (WildcardType) args.get(1);
			rewrite.set(wildcardType, WildcardType.UPPER_BOUND_PROPERTY, Boolean.FALSE, null);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, ast.newSimpleType(ast.newSimpleName("B")), null);
		}
		{
			WildcardType wildcardType= (WildcardType) args.get(2);
			rewrite.set(wildcardType, WildcardType.UPPER_BOUND_PROPERTY, Boolean.FALSE, null);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, ast.newSimpleType(ast.newSimpleName("B")), null);
		}
		{
			WildcardType wildcardType= (WildcardType) args.get(3);
			rewrite.set(wildcardType, WildcardType.UPPER_BOUND_PROPERTY, Boolean.TRUE, null);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, ast.newSimpleType(ast.newSimpleName("A")), null);
		}
		{
			WildcardType wildcardType= (WildcardType) args.get(4);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, null, null);
		}
		{
			WildcardType wildcardType= (WildcardType) args.get(5);
			rewrite.set(wildcardType, WildcardType.BOUND_PROPERTY, null, null);
		}


		String preview= evaluateRewrite(cu, rewrite);
		
		buf= new StringBuffer();
		buf.append("package test1;\n");
		buf.append("public class E {\n");
		buf.append("    X<? extends A, ? super B, ? super B, ? extends A, ?, ?> x;\n");
		buf.append("}\n");
		assertEqualString(preview, buf.toString());

	}


	
}
