/**
 * 
 */
package org.jmlspecs.eclipse.jdt.internal.esc2;

import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.CompilationUnit;
import javafe.ast.ConstructorDecl;
import javafe.ast.ConstructorInvocation;
import javafe.ast.ExprVec;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.ast.ImportDeclVec;
import javafe.ast.LexicalPragmaVec;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Name;
import javafe.ast.StmtVec;
import javafe.ast.TypeDeclElemVec;
import javafe.ast.TypeDeclVec;
import javafe.ast.TypeModifierPragmaVec;
import javafe.ast.TypeName;
import javafe.ast.TypeNameVec;
import javafe.util.Location;
import javafe.util.StackVector;

import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ExplicitConstructorCall;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;

/**
 * @author karabot
 * @deprecated because it is very unlikely that we will try to map between JML4 and ESC/Java2 ASTs.
 */
public class JdtAst2EscjAstVisitor extends PrintVisitor {

	public CompilationUnit   cu;
	
	protected final Name pkgName;
	protected final StackVector seqTypeName;
	protected final StackVector seqFormalParaDecl;
	protected final StackVector seqImportDecl;
	protected final StackVector seqTypeDecl;
	protected final StackVector seqExpr;
	protected final StackVector seqVarInit;
	protected final StackVector seqTypeDeclElem;
	protected final StackVector seqStmt;
	protected final StackVector seqCatchClause;
	protected ModifierPragmaVec modifierPragmas;
	protected LexicalPragmaVec  lexicalPragmas;

	
	public JdtAst2EscjAstVisitor() {
		pkgName=null;
		seqTypeName=new StackVector();
		seqFormalParaDecl=new StackVector();
		seqImportDecl=new StackVector();
		seqTypeDecl=new StackVector();
		seqExpr=new StackVector();
		seqVarInit=new StackVector();
		seqTypeDeclElem=new StackVector();
		seqStmt=new StackVector();
		seqCatchClause=new StackVector();
		modifierPragmas=null;
		cu=null;
		lexicalPragmas = LexicalPragmaVec.make();
	}

	public boolean visit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		System.out.println("->1"); //$NON-NLS-1$
		super.visit(compilationUnitDeclaration, scope);
		return true; // do nothing by default, keep traversing
	}
	public void endVisit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		System.out.println("1<-"); //$NON-NLS-1$
	}

	public boolean visit(CompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		System.out.println("->1.1"); //$NON-NLS-1$
		super.visit(compilationUnitDeclaration, scope);
		/* Import Declarations */
		seqImportDecl.push();
		/* Type Declarations */
		seqTypeDeclElem.push();
		seqTypeDecl.push();
		return(true);
	}
	public void endVisit(CompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		ImportDeclVec imports = ImportDeclVec.popFromStackVector(seqImportDecl);
		TypeDeclVec elems = TypeDeclVec.popFromStackVector(seqTypeDecl);
	    TypeDeclElemVec extras = TypeDeclElemVec.popFromStackVector(seqTypeDeclElem);
	    cu = CompilationUnit.make(pkgName,lexicalPragmas,imports,elems,compilationUnitDeclaration.sourceStart(),extras);
		System.out.println("1.1<-");//$NON-NLS-1$
	}
	
	
	public boolean visit(TypeDeclaration localTypeDeclaration, BlockScope scope) {
		System.out.println("->2"); //$NON-NLS-1$
		super.visit(localTypeDeclaration, scope);
		return true; // do nothing by default, keep traversing
	}
	public void endVisit(TypeDeclaration localTypeDeclaration, BlockScope scope) {
		System.out.println("2<-");//$NON-NLS-1$
	}
	
	public boolean visit(TypeDeclaration memberTypeDeclaration,	ClassScope scope) {
		System.out.println("->3");//$NON-NLS-1$
		super.visit(memberTypeDeclaration, scope);
		return true; // do nothing by default, keep traversing
	}	
	public void endVisit(TypeDeclaration memberTypeDeclaration, ClassScope scope) {
		System.out.println("3<-");//$NON-NLS-1$
	}

	public boolean visit(TypeDeclaration typeDeclaration, CompilationUnitScope scope) {
		System.out.println("->4");//$NON-NLS-1$
		super.visit(typeDeclaration, scope);
		/* Type Declarations */
		seqTypeDeclElem.push();
		return true; // do nothing by default, keep traversing
	}
	public void endVisit(TypeDeclaration typeDeclaration, CompilationUnitScope scope) {
		TypeDeclElemVec elems = TypeDeclElemVec.popFromStackVector( seqTypeDeclElem );
		int modifiers = typeDeclaration.modifiers;
		Identifier id = Identifier.intern(new String(typeDeclaration.name));
		TypeNameVec superInterfaces = TypeNameVec.make();
		TypeModifierPragmaVec tmodifiers = null;
		int loc = typeDeclaration.sourceStart;
		int locId = typeDeclaration.sourceStart;
		int locOpenBrace = typeDeclaration.bodyStart;
		int locCloseBrace = typeDeclaration.bodyEnd;
		TypeName superClass = null;
		ClassDecl result = ClassDecl.make(modifiers, modifierPragmas, id, 
				superInterfaces, tmodifiers, elems,
				loc, locId, locOpenBrace, locCloseBrace,
				superClass);
		result.specOnly=false; //FIXME: we need to pass this info from somewhere and not hard-coded.
		seqTypeDecl.addElement(result);
		System.out.println("4<-");//$NON-NLS-1$
	}

	
	
	public boolean visit(JmlConstructorDeclaration constructorDeclaration, ClassScope scope) {
		System.out.println("->5");//$NON-NLS-1$
		super.visit(constructorDeclaration, scope);
		return true; // do nothing by default, keep traversing
	}
	public void endVisit(JmlConstructorDeclaration constructorDeclaration, ClassScope scope) {
		System.out.println("5<-");//$NON-NLS-1$
	}
	
	public boolean visit(ConstructorDeclaration constructorDeclaration,	ClassScope scope) {
		//Debugging
		System.out.println("->5.1"); //$NON-NLS-1$
		System.out.println("PrintVisitor: " + constructorDeclaration.getClass() + " ==> " + constructorDeclaration + " <==");  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$

		// push a new vector that will hold the constructor's body.
		seqStmt.push();

		return true; // do nothing by default, keep traversing
	}	
	public void endVisit(ConstructorDeclaration constructorDeclaration,	ClassScope scope) {
		// pop from the stack the sequence of statements for the constructor 
		StmtVec stmts = StmtVec.popFromStackVector(seqStmt);
		// Generate a block statement which is what is required for the representation of the body.
		BlockStmt body = BlockStmt.make(stmts, constructorDeclaration.bodyStart, constructorDeclaration.bodyEnd);
		TypeModifierPragmaVec tmodifiers = null; //TODO: Figure out what these are for?
		FormalParaDeclVec args = FormalParaDeclVec.make(); // TODO: consider cases with parameters.
		TypeNameVec raises = TypeNameVec.make(); // TODO: consider cases with throws
		int locOpenBrace = constructorDeclaration.bodyStart;
		int loc = constructorDeclaration.declarationSourceStart;
		int locId = constructorDeclaration.declarationSourceStart; // FIXME: We need the ID sourceStart here.
		int locThrowsKeyword = Location.NULL;
		ConstructorDecl cd = ConstructorDecl.make(
				constructorDeclaration.modifiers,//modifiers, - WOW the codes between eclipse and ESCJ match one to one!
				modifierPragmas, // TODO: What are these modifier pragmas for?
				tmodifiers,
				args, 
				raises, body,
				locOpenBrace,
				loc, locId, 
				locThrowsKeyword );
		cd.specOnly=false;
		//Add the constructor to the sequence of TD elements.
		seqTypeDeclElem.addElement(cd);
		//Debugging
		System.out.println("5.1<-");//$NON-NLS-1$
	}

	
	public boolean visit(ExplicitConstructorCall explicitConstructor, BlockScope scope) {
		System.out.println("->6");//$NON-NLS-1$
		super.visit(explicitConstructor, scope);
		// Store the arguments
		seqExpr.push(); // stores the individual arguments.
		return true; // do nothing by default, keep traversing
	}
	public void endVisit(ExplicitConstructorCall explicitConstructor, BlockScope scope) {
		boolean superCall = explicitConstructor.isImplicitSuper();
		int loc = explicitConstructor.sourceStart(); // Assumming loc is the start character of the super() invocation.
		int locOpenParen = explicitConstructor.sourceEnd();
		//pop the arguments.
		ExprVec args = ExprVec.popFromStackVector( seqExpr );
		ConstructorInvocation ci = ConstructorInvocation.make( superCall, 
															   null, 
															   Location.NULL,
															   loc, 
															   locOpenParen,
															   args );
		seqStmt.addElement(ci);
		System.out.println("6<-");//$NON-NLS-1$

	}
}
