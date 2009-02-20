package org.eclipse.jdt.internal.compiler.parser;

import java.util.Arrays;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MarkerAnnotation;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.ast.SuperReference;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.jmlspecs.jml4.ast.JmlAllRangeExpression;
import org.jmlspecs.jml4.ast.JmlArrayIndexRangeExpression;
import org.jmlspecs.jml4.ast.JmlArrayRangeStoreRef;
import org.jmlspecs.jml4.ast.JmlArrayReference;
import org.jmlspecs.jml4.ast.JmlAssertStatement;
import org.jmlspecs.jml4.ast.JmlAssignableClause;
import org.jmlspecs.jml4.ast.JmlAssumeStatement;
import org.jmlspecs.jml4.ast.JmlCastExpressionWithoutType;
import org.jmlspecs.jml4.ast.JmlClause;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlConstraintClause;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlDataGroupClause;
import org.jmlspecs.jml4.ast.JmlDivergesClause;
import org.jmlspecs.jml4.ast.JmlDoStatement;
import org.jmlspecs.jml4.ast.JmlElemtypeExpression;
import org.jmlspecs.jml4.ast.JmlEnsuresClause;
import org.jmlspecs.jml4.ast.JmlFieldDeclaration;
import org.jmlspecs.jml4.ast.JmlFieldDotStarStoreRef;
import org.jmlspecs.jml4.ast.JmlForStatement;
import org.jmlspecs.jml4.ast.JmlFreshExpression;
import org.jmlspecs.jml4.ast.JmlInDataGroupClause;
import org.jmlspecs.jml4.ast.JmlInitiallyClause;
import org.jmlspecs.jml4.ast.JmlInvariantForType;
import org.jmlspecs.jml4.ast.JmlKeywordExpression;
import org.jmlspecs.jml4.ast.JmlLocalDeclaration;
import org.jmlspecs.jml4.ast.JmlLoopAnnotations;
import org.jmlspecs.jml4.ast.JmlLoopInvariant;
import org.jmlspecs.jml4.ast.JmlLoopVariant;
import org.jmlspecs.jml4.ast.JmlMapsIntoClause;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlMethodSpecification;
import org.jmlspecs.jml4.ast.JmlModifier;
import org.jmlspecs.jml4.ast.JmlNameDotStarStoreRef;
import org.jmlspecs.jml4.ast.JmlOldExpression;
import org.jmlspecs.jml4.ast.JmlQuantifiedExpression;
import org.jmlspecs.jml4.ast.JmlRepresentsClause;
import org.jmlspecs.jml4.ast.JmlRequiresClause;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlSetComprehension;
import org.jmlspecs.jml4.ast.JmlSetStatement;
import org.jmlspecs.jml4.ast.JmlSignalsClause;
import org.jmlspecs.jml4.ast.JmlSignalsOnlyClause;
import org.jmlspecs.jml4.ast.JmlSpecCase;
import org.jmlspecs.jml4.ast.JmlSpecCaseBlock;
import org.jmlspecs.jml4.ast.JmlSpecCaseBody;
import org.jmlspecs.jml4.ast.JmlSpecCaseHeader;
import org.jmlspecs.jml4.ast.JmlSpecCaseRest;
import org.jmlspecs.jml4.ast.JmlSpecCaseRestAsClauseSeq;
import org.jmlspecs.jml4.ast.JmlStoreRefListExpression;
import org.jmlspecs.jml4.ast.JmlSubtypeExpression;
import org.jmlspecs.jml4.ast.JmlTypeBodyDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeExpression;
import org.jmlspecs.jml4.ast.JmlTypeofExpression;
import org.jmlspecs.jml4.ast.JmlUnaryExpression;
import org.jmlspecs.jml4.ast.JmlWhileStatement;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;
import org.jmlspecs.jml4.nonnull.Nullity;
import org.jmlspecs.jml4.util.Logger;

public class JmlParserHelper implements TerminalTokens, OperatorIds {

	private Parser _this;

	public JmlParserHelper(Parser _this) {
		super();
		this._this = _this;
	}

	//===========================================================================
	//===========================================================================
	// JML4 code below this point. Tags and indentation help delimit cohesive 
	// method groups.

	// for detection of inner class default nullity error
	protected int classDeclarationCount = 0;
	// only meaningful before the end of consumeClassHeader()
	protected boolean reportDefaultNullityAnnotationOnInnerClassError = false;
	protected boolean defaultNullityAnnotationPushed = false;

	// <jml-start id="level-0.jmlTypeDeclarations" />
	private static final boolean DEBUG = Parser.DEBUG4JML;
	// <jml-end id="level-0.jmlTypeDeclarations" />
	// <jml-start id="ownershipModifiers" />
	/**/public/**/ long ownershipModifiers;
	// <jml-end id="ownershipModifiers" />

	// <jml-start id="nullity" />
	private boolean jmlInRecoveryMode = false;
	/**/public/**/ void setJmlInRecoveryMode() {
		this.jmlInRecoveryMode = true;
	}
	private boolean shouldIgnoreNullityStacks() {
		CompilationResult compilationResult = _this.compilationUnit.compilationResult;
		return this.jmlInRecoveryMode   || compilationResult.hasSyntaxError
		|| !_this.options.jmlEnabled || compilationResult.hasErrors();
	}
	/**/public/**/ Nullity defaultNullity; // of ComilationUnit (for now)
	private final int NullityStackIncrement = 10;
	private int nullityLengthPtr = -1;
	private int[] nullityLengthStack = new int[NullityStackIncrement];
	private int nullityPtr = -1;
	private Nullity[] nullityStack = new Nullity[NullityStackIncrement];

	/**/public/**/ Nullity getAndResetNullity() {
		Nullity result;
		if (this.nullityStackIsEmpty() || this.nullityTopIsDims()) {
			if (_this.options.useNonNullTypeSystem() && this.defaultNullity.isNon_null())
				result = Nullity.non_null_by_default;
			else
				result = Nullity.nullable_by_default;
		} else {
			result = this.popNullityStack();
		}
		Assert_isTrue(result != null);
		return result;
	}
	// TODO: if not using non-null type system, there should be no default nullity (revisit)
	void resetDefaultNullity() {
		this.defaultNullity = _this.options.useNonNullTypeSystem() && _this.options.jmlDefaultIsNonNull 
		? Nullity.non_null_by_default : Nullity.nullable_by_default;
	}
	// <jml-end id="nullity" />
	// <jml-start id="ownershipModifiers" />
	/**/public/**/ long getAndResetOwnershipModifiers() {
		long result = this.ownershipModifiers;
		this.ownershipModifiers = 0;
		return result;
	}
	// <jml-end id="ownershipModifiers" />
	// <jml-start id="level.0-1-a" />
	/**/public/**/ boolean processingSpecVarDecls;
	/**/public/**/ boolean jmlKeywordHasRedundantSuffix;
	/**/public/**/ int jmlKeywordTokenId; // holds the TokenNamexxx value of the last JML keyword read.
	// <jml-end id="level.0-1-a" />

	//<jml-start id="jmlComments" />
	/* package */void jmlDisabled(int sourceStart, int sourceEnd) {
		_this.problemReporter().jmlDisabled(sourceStart, sourceEnd);
	}
	//<jml-start id="jmlComments" />

	//=======================================================================
	// Parser semantic action methods (consume* methods):

	// <jml-start id="nnts" />
	/**/public/**/ void consumeDefaultNullity() {
		// TODO: remove DEBUGs & println
		if (DEBUG) Logger.println("***\nParser.consumeTypeDeclaration(): '"+new String(_this.compilationUnit.getFileName())+"'\nParser.consumeTypeDeclaration: this.options.defaultIsNonNull is "+_this.options.jmlDefaultIsNonNull); //$NON-NLS-1$ //$NON-NLS-2$
		if (_this.compilationUnit instanceof JmlCompilationUnitDeclaration) {
			if (!this.defaultNullity.hasExplicitNullity()) {
				// prj: can we ever reach here?
				resetDefaultNullity();
				if (DEBUG) Logger.println("setting parser.defaultNullity = "+this.defaultNullity+"\n***"); //$NON-NLS-1$//$NON-NLS-2$
			}
			// FIXME: this should be setting the default nullity for the type ...
			((JmlCompilationUnitDeclaration)_this.compilationUnit).setDefaultNullity(this.defaultNullity);
			if (DEBUG) Logger.println("setting compilationUnit.defaultNullity = "+this.defaultNullity+"\n***"); //$NON-NLS-1$//$NON-NLS-2$
		} else {
			System.out.println("this.compilationUnit not an instance of JmlCompilationUnitDeclaration"); //$NON-NLS-1$
		}
		// is this needed here or elsewhere when we're done with this compilation unit?:  resetDefaultNullity();

		if (this.classDeclarationCount > 0) {
			this.reportDefaultNullityAnnotationOnInnerClassError = true;
		}
	}
	// <jml-end id="nnts" />
	// <jml-start id="nntsElements" />
	/**/public/**/ void consumeOneDimLoopWithNullity() {
		_this.consumeOneDimLoop();
		/*Nullity extra =*/ this.popNullityStack();
		//Assert_isTrue(extra.hasDefaultNullity());
	}
	/**/public/**/ void consumeDimLoop() {
		this.concatNullityLists();
	}
	// <jml-end id="nntsElements" />
	// <jml-start id="jmlSetStatement" />
	/**/public/**/ void consumeJmlSetStatement() {
		// JmlSetStatement ::= 'set' AssignmentExpression ExitJmlClause ';'
		/*
		 * _this.identifierStack : 'set'
		 * _this.identifierPositionStack: start/end
		 * _this.astStack : 
		 * _this.expressionStack : JmlAssignment 
		 * ==>
		 * _this.identifierStack : 
		 * _this.identifierPositionStack: 
		 * _this.astStack : JmlSetStatement 
		 * _this.expressionStack :
		 */
		JmlIdentifier setKeyword = this.popIdentifierStack();

		int sourceStart = setKeyword.sourceStart();
		int sourceEnd = _this.endStatementPosition;
		Assignment assgnExp = (Assignment) this.popExpressionStack();
		_this.pushOnAstStack(new JmlSetStatement(assgnExp, sourceStart, sourceEnd));
	}
	// <jml-end id-"jmlSetStatement" />
	//<jml-start id="jml.loop-annotations" />
	/**/public/**/ void consumeEmptyJmlLabel() {
		_this.pushIdentifier(0);
	}
	/**/public/**/ void consumeJmlLoopVariantSeq() {
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeJmlLoopInvariantSeq() {
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeLoopAnnotations(boolean hasInvariantSeq, boolean hasVariantSeq) {
		//JmlLoopAnnotations ::= JmlLoopInvariantSeq JmlLoopVariantSeq 
		/*	
			_this.astStack : JmlLoopInvariants and/or JmlLoopVariants
			_this.astLengthStack : n and/or m           n, m >0
			 ==>
			_this.astStack : JmlLoopAnnotations
			_this.astLengthStack : 1
		 */
		JmlLoopVariant[] variants = hasVariantSeq
		? (JmlLoopVariant[]) this.popAstStack(JmlLoopVariant.class)
				: JmlLoopAnnotations.EMPTY_VARIANTS;
		JmlLoopInvariant[] invariants = hasInvariantSeq
		? (JmlLoopInvariant[]) this.popAstStack(JmlLoopInvariant.class)
				: JmlLoopAnnotations.EMPTY_INVARIANTS;
		JmlLoopAnnotations annotations = new JmlLoopAnnotations(invariants, variants);
		_this.pushOnAstStack(annotations);
	}
	//<jml-end id="jml.loop-annotations" />
	//<jml-start id="signals" />
	/**/public/**/ void consumeSignalsClause(boolean hasIdentifier) {
		//SignalsClause ::= SignalsOrSignalsRedundantly '(' ClassType ')' PredicateOrNotSpecifiedopt ExitJmlClause ';'
		//SignalsClause ::= SignalsOrSignalsRedundantly '(' ClassType 'Identifier' ')' PredicateOrNotSpecifiedopt ExitJmlClause ';'

		Expression expr = this.popExpressionStackMayBeNull();
		char [] idName = JmlConstants.JML_ANON;
		long pos = 0;
		if (hasIdentifier) {
			JmlIdentifier identifier = this.popIdentifierStack();
			idName = identifier.token();
			pos = identifier.getPos();
		}
		TypeReference thrownType = _this.getTypeReference(0);
		if (pos == 0)
			pos = (((long) thrownType.sourceStart) << 32) + thrownType.sourceEnd; 
		Argument arg = new Argument(idName, pos, thrownType, 0);
		arg.type = thrownType;
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		JmlSignalsClause clause = new JmlSignalsClause(clauseKeyword, arg, expr);
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	//<jml-end id="signals" />
	//<jml-start id="signalsOnly" />
	/**/public/**/ void consumeSignalsOnlyClause() {
		//SignalsOnlyClause ::= SignalsOnlyOrSignalsOnlyRedundantly ClassTypeList ExitJmlClause ';'
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		TypeReference[] typeRefs = (TypeReference[])this.popAstStack(TypeReference.class);
		JmlSignalsOnlyClause clause = 
			new JmlSignalsOnlyClause(clauseKeyword, typeRefs);
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	/**/public/**/ void consumeSignalsOnlyClauseNothing() {
		//SignalsOnlyClause ::= SignalsOnlyOrSignalsOnlyRedundantly 'slash_nothing' ExitJmlClause ';'
		JmlKeywordExpression nothing = (JmlKeywordExpression) this.popExpressionStack();
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		JmlSignalsOnlyClause clause = new JmlSignalsOnlyClause(clauseKeyword, nothing);
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	//<jml-end id="signalsOnly" />
	//<jml-start id="dataGroups" />
	/**/public/**/ void consumeFieldDeclarationWithDataGroupClause() {
		// FieldDeclaration ::= Modifiersopt Type VariableDeclarators ';' JmlDataGroupClauseSeq
		int numGroups = _this.astLengthStack[_this.astLengthPtr--];
		_this.astPtr -= numGroups;
		JmlDataGroupClause[] dataGroups = new JmlDataGroupClause[numGroups];
		System.arraycopy(_this.astStack, _this.astPtr+1, dataGroups, 0, numGroups);

		_this.consumeFieldDeclaration();
		Assert_isTrue(_this.astStack[_this.astPtr] instanceof JmlFieldDeclaration);
		JmlFieldDeclaration fieldDecl = (JmlFieldDeclaration)(_this.astStack[_this.astPtr]);
		fieldDecl.dataGroups = dataGroups;
	}
	/**/public/**/ void consumeDataGroupClauseSeq() {
		// JmlDataGroupClauseSeq ::= JmlDataGroupClauseSeq JmlDataGroupClause
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeInDataGroupClause() {
		// InDataGroupClause ::= InKeyword DataGroupNameList ';'
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		Expression[] groupNames = this.popExpressionStack(Expression.class);
		JmlInDataGroupClause clause = new JmlInDataGroupClause(clauseKeyword, groupNames);
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	/**/public/**/ void consumeMapsIntoClause() {
		// MapsIntoClause ::= MapsKeyword MemberFieldRef 'slash_into' DataGroupNameList ';'
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		Expression[] groupNames = this.popExpressionStack(Expression.class);
		Expression mapstoExprRef = this.popExpressionStack();
		JmlMapsIntoClause clause = new JmlMapsIntoClause(clauseKeyword, mapstoExprRef, groupNames);
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	/**/public/**/ void consumeExitJmlClause() {
		_this.scanner.resetInExpressionPartOfJmlClause();
		Assert_isTrue(!DEBUG || nullityStackIsEmpty(), "nullities left on stack after jml clause"); //$NON-NLS-1$
	}
	// <jml-end id="identifierKeywords" />
	//<jml-start id="ownershipModifiers" />
	/**/public/**/ void consumeOwnershipModifiers(int numModifiers) {
		//@ assert numModifiers == 1 || numModifiers == 2;
		for (int i=0; i< numModifiers; i++) {
			processOwnershipModifier();
		}
		if (numModifiers == 2) {
			_this.concatExpressionLists();
		}
	}
	private void processOwnershipModifier() {
		char[] identifier = _this.identifierStack[_this.identifierPtr];
		if (identifier[0]=='\\') {
			//strip off the slash
			int idLength = identifier.length - 1;
			char[] newId = new char[idLength];
			System.arraycopy(identifier, 1, newId, 0, idLength);
			_this.identifierStack[_this.identifierPtr] = newId;
		}
		consumeJmlModifierAsModifier();
	}
	/**/public/**/ void consumeTypeWithOwnershipModifiers() {
		int numModifiers = _this.expressionLengthStack[_this.expressionLengthPtr--];
		_this.expressionPtr -= numModifiers;
		Annotation[] annotations = new Annotation[numModifiers];
		System.arraycopy(_this.expressionStack, _this.expressionPtr+1, annotations, 0, numModifiers);
		this.ownershipModifiers = JmlModifier.getFromAnnotations(annotations);
	}
	/**/public/**/ void consumeReferenceTypeWithoutOwnershipModifiers() {
		//<jml-start id="ownershipModifiers" />
		this.ownershipModifiers = 0;
		//<jml-end id="ownershipModifiers" />
	}
	//<jml-end id="ownershipModifiers" />
	//<jml-start id="JmlModifiers" />
	/**/public/**/ void consumeJmlModifierAsModifier() {
		// take identifier off stack and make a marker annotation
		// push the marker annotation on the expression stack

		// the following based on code taken from consumeMarkerAnnotation()
		MarkerAnnotation markerAnnotation = null;

		// int numIds = _this.identifierLengthStack[_this.identifierLengthPtr--];
		_this.identifierLengthPtr--;
		//@ assert numIds == 1;
		char[] identifier = _this.identifierStack[_this.identifierPtr];
		long pos = _this.identifierPositionStack[_this.identifierPtr--];
		// BEWARE: do NOT mutate the contents of identifier since
		// identifier char arrays seems to be reused.
		TypeReference typeReference = JmlModifier.identToTypeRef(identifier, pos);

		markerAnnotation = new MarkerAnnotation(typeReference, typeReference.sourceStart);
		markerAnnotation.declarationSourceEnd = markerAnnotation.sourceEnd;
		_this.pushOnExpressionStack(markerAnnotation);

		// the following based on code taken from consumeMarkerAnnotation()
		int sourceStart = markerAnnotation.sourceStart;
		if (_this.modifiersSourceStart < 0) {
			_this.modifiersSourceStart = sourceStart;
		}
	}
	//<jml-end id="JmlModifiers" />
	//<jml-start id="level.0-1-a" />
	/**/public/**/ void consumeJmlTypeBodyDeclaration() {
		// JmlTypeBodyDeclaration ::= Modifiersopt JmlInvariantDeclaration
		//                         |  Modifiersopt JmlRepresentsClause
		//                         |  Modifiersopt JmlInitiallyClause
		/*	
			_this.astStack : JmlTypeBodyDeclaration
			_this.astLengthStack : 1
			_this.intStack : modifiers modifiersSourceStart
			 ==>
			_this.astStack : JmlTypeBodyDeclaration (but with modifiers)
			_this.astLengthStack : 1
			_this.intStack : 
		 */
		int declModifiersSourceStart = _this.intStack[_this.intPtr--];
		int declModifiers = _this.intStack[_this.intPtr--];

		JmlTypeBodyDeclaration decl = (JmlTypeBodyDeclaration) _this.astStack[_this.astPtr];
		decl.setModifers(declModifiers, declModifiersSourceStart);

		// consume annotations.	
		Annotation[] annotations = (Annotation[])this.popExpressionStack(Annotation.class);
		decl.setJmlAnnotations(annotations);
	}
	/**/public/**/ void consumeConstraintDeclaration() {
		// JmlInvariantDeclaration -> 'constraint' Predicate ';'
		/*	
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.identifierStack : InvariantKeyword
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: 1
			 ==>
			_this.astStack : JmlInvariantDeclaration
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
			_this.identifierStack :
			_this.identifierPositionStack:
			_this.identifierLengthStack: 
		 */

		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		Expression expr = this.popExpressionStack();
		JmlConstraintClause cons = new JmlConstraintClause(clauseKeyword, expr);
		cons.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(cons);
	}
	/**/public/**/ void consumeJmlPrimaryResult() {
		// FIXME: push directly on expression stack.
		// JmlPrimary ::= 'slash_result'
		JmlIdentifier identifierInfo = popIdentifierStack();	
		_this.pushOnExpressionStack(new JmlResultReference(identifierInfo.sourceStart(), identifierInfo.sourceEnd()));
	}
	/**/public/**/ void consumeJmlFreshExpression() {
		// JmlFreshExpression ::= \fresh '(' ArgumentList ')'
		/*	
			_this.expressionStack : Expression ...
			_this.expressionLengthStack: numArg
			_this.intStack: starting-position-of-keyword
			 ==>
			this.expStack : JmlFreshExpression
			_this.expressionLengthStack:
			_this.intStack: 
		 */
		int numArg = _this.expressionLengthStack[_this.expressionLengthPtr--];
		Expression[] args = new Expression[numArg];
		System.arraycopy(
				_this.expressionStack, 
				(_this.expressionPtr -= numArg) + 1, 
				args, 
				0, 
				numArg);
		JmlFreshExpression expr = new JmlFreshExpression(args);
		expr.sourceStart = _this.intStack[_this.intPtr--];
		expr.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(expr);
	}
	/**/public/**/ void consumeJmlTypeExpression(int op) {
		// JmlTypeExpression ::= \type '(' Type ')'
		/*	
			_this.identifierStack : type
			_this.intStack : starting-position-of-keyword dim dim
			 ==>
			_this.identifierStack :
			_this.expressionStack : JmlTypeExpression
			_this.expressionLengthStack: 1
			_this.intStack:
		 */
		final int extendedDimensions = 0; // FIXME: _this.intStack[_this.intPtr--];
		final int firstDimensions = _this.intStack[_this.intPtr--];
		final int typeDimensions = firstDimensions + extendedDimensions;
		TypeReference type = _this.getTypeReference(typeDimensions);
		JmlTypeExpression expr = new JmlTypeExpression(type, op);
		expr.sourceStart = _this.intStack[_this.intPtr--];
		expr.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(expr);
	}
	/**/public/**/ void consumeJmlUnaryExpression(int op) {
		// JmlUnaryExpression ::= jml-unary-operator '(' SpecExpression ')'
		/*	
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.intStack: sourceStart // of operator
			 ==>
			_this.astStack : JmlUnaryExpression
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
		 */
		Expression expr = this.popExpressionStack();
		JmlUnaryExpression oldExp = JmlUnaryExpression.factory(expr, op);
		oldExp.sourceStart = this.popIntStack();
		oldExp.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(oldExp);
	}
	/**/public/**/ void consumeJmlTypeofExpression(int op) {
		// JmlTypeofExpression ::= slash_typeof '(' SpecExpression ')'
		/*	
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.intStack: sourceStart // of operator
			 ==>
			_this.astStack : JmlTypeofExpression
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
		 */

		Expression exp = popExpressionStack();
		JmlUnaryExpression typeofExp = new JmlTypeofExpression(exp, op);
		typeofExp.sourceStart = popIntStack();
		typeofExp.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(typeofExp);
	}
	/**/public/**/ void consumeJmlElemtypeExpression(int op) {
		// JmlElemtypeExpression ::= slash_elemtype '(' SpecExpression ')'
		/*	
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.intStack: sourceStart // of operator
			 ==>
			_this.astStack : JmlElemtypeExpression
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
		 */

		Expression exp = _this.expressionStack[_this.expressionPtr--];
		_this.expressionLengthPtr--;
		JmlUnaryExpression elemtypeExp = new JmlElemtypeExpression(exp, op);
		elemtypeExp.sourceStart = _this.intStack[_this.intPtr--];
		elemtypeExp.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(elemtypeExp);
	}
	/**/public/**/ void consumeJmlPrimaryOldExpression(int op) {
		// OldExpression ::= slash_old '(' SpecExpression ')'
		/*	
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.intStack: sourceStart // of operator
			 ==>
			_this.astStack : JmlOldExpression
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
		 */

		Expression exp = _this.expressionStack[_this.expressionPtr--];
		_this.expressionLengthPtr--;
		JmlOldExpression oldExp = new JmlOldExpression(exp, op);
		oldExp.sourceStart = _this.intStack[_this.intPtr--];
		oldExp.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(oldExp);
	}
	/**/public/**/ void consumeJmlPrimaryLabeledOldExpression(int op) {
		// OldExpression ::= slash_old '(' SpecExpression ',' Identifier ')'
		/*	
			_this.expressionStack : Expression
			_this.expressionLengthStack: 1
			_this.intStack: sourceStart // of operator
			_this.identifierStack : label
			 ==>
			_this.astStack : JmlOldExpression
			_this.astLengthStack : 1
			this.expStack :
			_this.expressionLengthStack:
			_this.identifierStack :
		 */

		Expression exp = _this.expressionStack[_this.expressionPtr--];
		_this.expressionLengthPtr--;
		JmlIdentifier label = this.popIdentifierStack();
		JmlOldExpression oldExp = new JmlOldExpression(exp, op, label.token());
		oldExp.sourceStart = _this.intStack[_this.intPtr--];
		oldExp.sourceEnd = _this.rParenPos;
		_this.pushOnExpressionStack(oldExp);
	}
	/**/public/**/ void consumeSpecCaseBodySeq() {
		// SpecCaseBodySeq ::= SpecCaseBodySeq 'also' SpecCaseBody
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeSpecCaseRestClauseSeq() {
		// SpecCaseRestClauseSeq ::= SpecCaseRestClauseSeq SpecCaseClause
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeSpecCaseSeq() {
		// SpecCaseRestClauseSeq ::= SpecCaseRestClauseSeq 'also' SpecCaseClause
		// ignore the 'also', don't even push its loc on the intStack
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeLightweightSpecCase() {
		// LightweightSpecCase ::= SpecCaseBody
		/*
			_this.astStack : SpecCaseBody
			_this.astLengthStack : 1
			 ==>
			_this.astStack : SpecCase
			_this.astLengthStack : 1
		 */	
		JmlSpecCaseBody body = (JmlSpecCaseBody) _this.astStack[_this.astPtr--];
		_this.astLengthPtr--;

		JmlSpecCase specCase = new JmlSpecCase(body);
		specCase.sourceStart = body.sourceStart;
		specCase.sourceEnd = body.sourceEnd;
		_this.pushOnAstStack(specCase);
	}
	/**/public/**/ void consumeHeavyweightSpecCase() {
		// HeavyweightSpecCase ::= Modifiersopt HeavyweightBehaviorKeyword SpecCaseBody
		/*
			_this.astStack : SpecCaseBody
			_this.astLengthStack : 1
			_this.intStack : modifiers modifiersSourceStart
			_this.identifierStack : HeavyweightBehaviorKeyword
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: 1
			 ==>
			_this.astStack : SpecCase
			_this.astLengthStack : 1
			_this.identifierStack :
			_this.identifierPositionStack:
			_this.identifierLengthStack: 
			_this.intStack : 
		 */	
		JmlSpecCaseBody body = (JmlSpecCaseBody) _this.astStack[_this.astPtr--];
		_this.astLengthPtr--;
		String behaviorTokenLexeme = new String(_this.identifierStack[_this.identifierPtr]);	
		long startAndEndPosition = _this.identifierPositionStack[_this.identifierPtr--]; 
		_this.identifierLengthPtr--;
		int specCaseModifiersSourceStart = _this.intStack[_this.intPtr--];
		int specCaseModifiers = _this.intStack[_this.intPtr--];

		JmlSpecCase specCase = new JmlSpecCase(behaviorTokenLexeme,body, specCaseModifiers);
		specCase.sourceStart = (specCaseModifiers != 0 ? specCaseModifiersSourceStart : (int)(startAndEndPosition >>> 32));
		specCase.sourceEnd = body.sourceEnd;
		_this.pushOnAstStack(specCase);
	}
	/**/public/**/ void consumeSpecCaseRestAsClauseSeq() {
		//	spec-case-rest ::= spec-case-rest-clause-seq
		//  SpecCaseRest ::= SpecCaseRestClauseSeq

		/*
			_this.astStack : clause_1 ... clause_n
			_this.astLengthStack : n  (n >= 1)
			 ==>
			_this.astStack : JmlSpecCaseRestClauseSeq // which is a subclass of SpecCaseRest.
			_this.astLengthStack : 1
		 */	
		int numClauses = _this.astLengthStack[_this.astLengthPtr--];
		_this.astPtr -= numClauses;
		JmlClause clauses[] = new JmlClause[numClauses];
		System.arraycopy(_this.astStack, _this.astPtr+1, clauses, 0, numClauses);
		JmlSpecCaseRestAsClauseSeq restAsClauseSeq = new JmlSpecCaseRestAsClauseSeq(clauses);
		restAsClauseSeq.sourceStart = clauses[0].sourceStart;
		restAsClauseSeq.sourceEnd = clauses[numClauses-1].sourceEnd;
		_this.pushOnAstStack(restAsClauseSeq);
	}
	/**/public/**/ void consumeRequiresClauseSeq() {
		// RequiresClauseSeq ::= RequiresClauseSeq RequiresClause
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeSpecCaseHeader() {
		// SpecCaseHeader ::= RequiresClauseSeq
		/*
			_this.astStack : requiresClause_1 ... requiresClause_n
			_this.astLengthStack : n  (n >= 1)
			 ==>
			_this.astStack : SpecCaseHeader
			_this.astLengthStack : 1
		 */	
		JmlRequiresClause[] requires = (JmlRequiresClause[])this.popAstStack(JmlRequiresClause.class);
		JmlSpecCaseHeader header = new JmlSpecCaseHeader(requires);
		header.sourceStart = requires[0].sourceStart;
		header.sourceEnd = requires[requires.length-1].sourceEnd;
		_this.pushOnAstStack(header);
	}
	/**/public/**/ void consumeSpecCaseBody(boolean hasHeader, boolean hasRest) {
		//	spec-case-body ::= spec-var-decls ( spec-case-header [ spec-case-rest ] | spec-case-rest )
		/*
			_this.astStack : SpecVarDecl1 .. SpecVarDeclm SpecVarDecl1 .. SpecVarDecln SpecCaseHeader SpecCaseRest
			_this.astLengthStack : m n 1 1 or m n 1 (depending of the values of the arguments to this method)
			 ==>
			_this.astStack : SpecCaseBody
			_this.astLengthStack : 1
		 */
		this.processingSpecVarDecls = false; // we are done processing spec vars.
		JmlSpecCaseRest rest = hasRest ? (JmlSpecCaseRest) this.popAstStack() : null;
		JmlSpecCaseHeader header = hasHeader ? (JmlSpecCaseHeader) this.popAstStack() : null;
		JmlLocalDeclaration[] oldVars = (JmlLocalDeclaration[]) this.popAstStack(JmlLocalDeclaration.class);
		JmlLocalDeclaration[] forallVars = (JmlLocalDeclaration[]) this.popAstStack(JmlLocalDeclaration.class);
		JmlSpecCaseBody body = new JmlSpecCaseBody(forallVars, oldVars, header, rest);
		_this.pushOnAstStack(body);
	}
	/**/public/**/ void consumeStartSpecVarDecls() {
		// StartSpecVarDecls ::= $empty
		this.processingSpecVarDecls = true;
	}
	/**/public/**/ void consumeEmptyJmlSpecVarDecls() {
		_this.pushOnAstLengthStack(0);
	}
	/**/public/**/ void consumeJmlVarDecls() {
		_this.concatNodeLists();
	}
	/**/public/**/ void consumeSpecCaseBlock() {
		//	spec-case-block ::= '{|' spec-case-body [ 'also' spec-case-body ] ... '|}'
		//  SpecCaseBlock ::= LBRACE_OR SpecCaseBodySeq OR_RBRACE
		/*
			_this.astStack : specCaseBody_1 ... specCaseBody_n
			_this.astLengthStack : n (n >= 1)
			_this.intStack : startPosOfLbrace_or endPosOfOr_rbrace
			 ==>
			_this.astStack : SpecCaseBlock
			_this.astLengthStack : 1
			_this.intStack : 
		 */	
		int endPosOfOr_rbrace = _this.intStack[_this.intPtr--];
		int startPosOfLbrace_or = _this.intStack[_this.intPtr--];

		int numSpecCaseBodies = _this.astLengthStack[_this.astLengthPtr--];
		_this.astPtr -= numSpecCaseBodies;
		JmlSpecCaseBody bodies[] = new JmlSpecCaseBody[numSpecCaseBodies];
		System.arraycopy(_this.astStack, _this.astPtr+1, bodies, 0, numSpecCaseBodies);

		JmlSpecCaseBlock block = new JmlSpecCaseBlock(bodies);
		block.sourceStart = startPosOfLbrace_or;
		block.sourceEnd = endPosOfOr_rbrace;
		_this.pushOnAstStack(block);
	}
	/**/public/**/ void consumeJmlClause() {
		// This consume method handles clauses like this:
		// Clause ::= ClauseKeyword ClauseExpressionsOrKeyword';'
		// ClauseExpressionsOrKeyword ::= JmlKeywordExpression | Expression ...
		/*	
			_this.astStack : 
			this.expStack : expr ...
			_this.identifierStack : clause-keyword
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: n >= 1
			 ==>
			_this.astStack : JmlClause
			this.expStack :
			_this.identifierStack : 
			_this.identifierPositionStack: 
			_this.identifierLengthStack: 
		 */
		// Expressions are popped by the factory.
		JmlIdentifier clauseKeyword = this.popIdentifierStack();
		JmlClause clause = this.jmlClauseFactory(clauseKeyword);
		clause.sourceStart = clauseKeyword.sourceStart();
		clause.sourceEnd = _this.endStatementPosition;
		_this.pushOnAstStack(clause);
	}
	private JmlClause jmlClauseFactory(JmlIdentifier keyword) {
		switch (keyword.id()) {
		case TokenNamediverges:
		case TokenNamediverges_redundantly:
			return new JmlDivergesClause(keyword, popExpressionStack());
		case TokenNameEnsuresOrSynonym:
		case TokenNameEnsuresRedundantlyOrSynonym:
			return new JmlEnsuresClause(keyword, popExpressionStack());
		case TokenNameRequiresOrSynonym:
		case TokenNameRequiresRedundantlyOrSynonym:
			return new JmlRequiresClause(keyword, popExpressionStack());
		case TokenNameloop_invariant:
		case TokenNameloop_invariant_redundantly:
			return new JmlLoopInvariant(keyword, popExpressionStack());
		case TokenNamedecreases:
		case TokenNamedecreases_redundantly:
			return new JmlLoopVariant(keyword, popExpressionStack());
		case TokenNameAssignableOrSynonym:
		case TokenNameAssignableRedundantlyOrSynonym:
			return new JmlAssignableClause(keyword, popExpressionStack());
		case TokenNameinitially:
			return new JmlInitiallyClause(keyword, popExpressionStack());
		case TokenNameinvariant:
		case TokenNameinvariant_redundantly:
			return new JmlInvariantForType(keyword, popExpressionStack());
		case TokenNamerepresents:
		case TokenNamerepresents_redundantly:
			Expression specExpr = popExpressionStack();
			Expression storeRefExpr = popExpressionStack();
			return new JmlRepresentsClause(keyword, storeRefExpr, specExpr);
		default:
			throw new IllegalArgumentException();
		}
	}
	/**/public/**/ void consumeJmlStoreRefSeqAsStoreRefListExpression() {
		/*
			_this.expressionStack : expr1 ... exprn
			_this.expressionLengthStack : n  (n > 0)
			 ==>
			_this.expressionStack : JmlStoreRefListExpression
			_this.expressionLengthStack : 1
		 */	
		Expression storeRefs[] = this.popExpressionStack(Expression.class);
		_this.pushOnExpressionStack(new JmlStoreRefListExpression(storeRefs));
	}
	//@ requires hasSpecCaseSeq || hasRedundantPart;
	/**/public/**/ void consumeMethodSpecification(
			boolean isExtending, // i.e. has 'also'
			boolean hasSpecCaseSeq,
			boolean hasRedundantPart) {
		// method-specification ::= ['also'] [spec-case-seq] [method-spec-redundant-part]
		/*
			_this.astStack : specCase_1 ... specCase_n specCase_1 ... specCase_m
			_this.astLengthStack : will have one or both of n and m (n >= 1 && m >= 1)
			 ==>
			_this.astStack : methodSpecification
			_this.astLengthStack : 1
		 */	
		JmlSpecCase specCases[] = hasSpecCaseSeq
		? (JmlSpecCase[]) this.popAstStack(JmlSpecCase.class)
				: JmlSpecCase.EMPTY_SPEC_CASE_ARRAY;
		JmlSpecCase redundantSpecCases[] = hasRedundantPart
		? (JmlSpecCase[]) this.popAstStack(JmlSpecCase.class)
				: JmlSpecCase.EMPTY_SPEC_CASE_ARRAY;
		JmlMethodSpecification spec = new JmlMethodSpecification(specCases, redundantSpecCases, isExtending);
		spec.sourceStart = hasSpecCaseSeq
		? specCases[0].sourceStart
				: redundantSpecCases[0].sourceStart;
		JmlSpecCase lastSpecCase = hasRedundantPart
		? redundantSpecCases[redundantSpecCases.length-1]
		                     : specCases[specCases.length-1];
		spec.sourceEnd = lastSpecCase.sourceEnd;
		_this.pushOnAstStack(spec);
	}

	/**/public/**/ void consumeSpecedMethodDeclaration(boolean isNotAbstract) {
		//System.out.println("consumeSpecedMethodDeclaration");
		// MethodDeclaration ::= MethodSpecification MethodHeader MethodBody
		// AbstractMethodDeclaration ::= MethodSpecification MethodHeader ';'
		/*
			_this.astStack : spec modifiers arguments throws statements
			_this.astStack : JmlMethodSpecification MethodDeclaration statements // jml-note: PC: this is what I think is on the stack.
			_this.identifierStack : type name
			_this.intStack : dim dim dim
			 ==>
			_this.astStack : MethodDeclaration
			_this.identifierStack :
			_this.intStack : 
		 */
		_this.consumeMethodDeclaration(isNotAbstract);
		// _this.astStack : JmlMethodSpecification JmlMethodDeclaration
		JmlMethodDeclaration md = (JmlMethodDeclaration) _this.astStack[_this.astPtr--];
		Assert_isTrue(_this.astLengthStack[_this.astLengthPtr] == 1, "JmlMethodDeclaration astLength == 1"); //$NON-NLS-1$
		_this.astLengthPtr--;
		// _this.astStack : JmlMethodSpecification 
		md.specification = (JmlMethodSpecification) _this.astStack[_this.astPtr--];
		_this.astLengthPtr--;
		_this.pushOnAstStack(md);
	}
	/**/public/**/ void consumeInvalidSpecedMethodDeclaration() {
		_this.consumeInvalidMethodDeclaration();
		_this.astPtr--;
	}
	/**/public/**/ void consumeSpecedConstructorDeclaration() {
		//System.out.println("consumeSpecedConstructorDeclaration");
		// ConstructorDeclaration ::= MethodSpecification ConstructorHeader ConstructorBody
		/*
			_this.astStack : MethodSpecification MethodDeclaration statements
			_this.identifierStack : name
			 ==>
			_this.astStack : MethodDeclaration
			_this.identifierStack :
		 */
		_this.consumeConstructorDeclaration();
		// now we know that we have a JML method declaration   at the top of the ast stack
		JmlConstructorDeclaration md = (JmlConstructorDeclaration) _this.astStack[_this.astPtr--];
		// now we know that we have a JML method specification at the top of the ast stack
		md.specification = (JmlMethodSpecification) _this.astStack[_this.astPtr--];
		_this.astStack[++_this.astPtr] = md;
		_this.astLengthPtr -= 1;
	}
	/**/public/**/ void consumeInvalidSpecedConstructorDeclaration(boolean isAbstract) {
		// ConstructorDeclaration ::= MethodSpecification ConstructorHeader ';'
		/*
			_this.astStack : MethodSpecification ConstructorDeclaration
			_this.identifierStack : name
			 ==>
			_this.astStack : ConstructorDeclaration
			_this.identifierStack :
		 */
		_this.consumeInvalidConstructorDeclaration(isAbstract);
		// now we know that we have a JML construcot declaration at the top of the ast stack
		JmlConstructorDeclaration md = (JmlConstructorDeclaration) _this.astStack[_this.astPtr--];
		// now we know that we have a JML method specification at the top of the ast stack
		md.specification = (JmlMethodSpecification) _this.astStack[_this.astPtr--];
		_this.astStack[++_this.astPtr] = md;
		_this.astLengthPtr -= 1;
	}
	//<jml-end id="level.0-1-a" />
	// <jml-start id="castNullityWithoutType" />
	/**/public/**/ void consumeCastExpressionWithoutType() {
		//_this.intStack : posOfLeftParen posOfRightParen

		/*Nullity nullity =*/ this.getAndResetNullity(); // to "consume" the non_null
		//@ assert nullity == Nullity.non_null;

		Expression exp, cast;
		_this.intPtr--;
		// <jml-start id="5" />
		_this.expressionStack[_this.expressionPtr] = cast = 
			new JmlCastExpressionWithoutType(exp = _this.expressionStack[_this.expressionPtr], true);
		cast.sourceStart = _this.intStack[_this.intPtr--] + 1;
		cast.sourceEnd = exp.sourceEnd;
	}
	// <jml-end id="castNullityWithoutType" />
	// <jml-start id="level.0-1-a" />
	/**/public/**/ void consumeJmlSimpleAssertStatement() {
		// JmlAssertStatement ::= 'jml_assert' Predicate ';'
		_this.expressionLengthPtr--;
		long pos = _this.identifierPositionStack[_this.identifierPtr];
		int start = (int) (pos >>> 32);
		char[] lexeme = _this.identifierStack[_this.identifierPtr--];
		_this.identifierLengthPtr--;
		_this.pushOnAstStack(new JmlAssertStatement(new String(lexeme), _this.expressionStack[_this.expressionPtr--], start));	
	}
	/**/public/**/ void consumeJmlAssertStatement() {
		// JmlAssertStatement ::= 'jml_assert' Predicate ':' Expression ';'
		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : Predicate Expression
			_this.expressionLengthStack : 1 1
			_this.identifierStack : assert-lexeme
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: 1
			 ==>
			_this.astStack : JmlAssertStatement
			_this.astLengthStack : 1
			_this.expressionStack :  
			_this.expressionLengthStack : 
			_this.identifierStack : 
			_this.identifierPositionStack: 
			_this.identifierLengthStack: 
		 */	
		_this.expressionLengthPtr--;
		Expression expr = _this.expressionStack[_this.expressionPtr--];
		_this.expressionLengthPtr--;
		Expression pred = _this.expressionStack[_this.expressionPtr--];
		long pos = _this.identifierPositionStack[_this.identifierPtr];
		int start = (int) (pos >>> 32);
		char[] lexeme = _this.identifierStack[_this.identifierPtr--];
		_this.identifierLengthPtr--;
		_this.pushOnAstStack(new JmlAssertStatement(new String(lexeme), expr, pred, start));	
	}
	/**/public/**/ void consumeJmlAssumeStatement() {
		// JmlAssumeStatement ::= 'assume' Predicate ':' Expression ';'
		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : Predicate Expression
			_this.expressionLengthStack : 1 1
			_this.identifierStack : assert-lexeme
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: 1
			 ==>
			_this.astStack : JmlAssumeStatement
			_this.astLengthStack : 1
			_this.expressionStack :  
			_this.expressionLengthStack : 
			_this.identifierStack : 
			_this.identifierPositionStack: 
			_this.identifierLengthStack: 
		 */	
		_this.expressionLengthPtr--;
		Expression expr = _this.expressionStack[_this.expressionPtr--];
		_this.expressionLengthPtr--;
		Expression pred = _this.expressionStack[_this.expressionPtr--];
		long pos = _this.identifierPositionStack[_this.identifierPtr];
		int start = (int) (pos >>> 32);
		char[] lexeme = _this.identifierStack[_this.identifierPtr--];
		_this.identifierLengthPtr--;
		_this.pushOnAstStack(new JmlAssumeStatement(new String(lexeme), expr, pred, start));	
	}
	/**/public/**/ void consumeJmlSimpleAssumeStatement() {
		// JmlAssumeStatement ::= 'assume' Predicate ';'
		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : Predicate 
			_this.expressionLengthStack : 1
			_this.identifierStack : assume-lexeme
			_this.identifierPositionStack: start/end
			_this.identifierLengthStack: 1
			 ==>
			_this.astStack : JmlAssumeStatement
			_this.astLengthStack : 1
			_this.expressionStack :  
			_this.expressionLengthStack : 
			_this.identifierStack : 
			_this.identifierPositionStack: 
			_this.identifierLengthStack: 
		 */	
		_this.expressionLengthPtr--;
		Expression pred = _this.expressionStack[_this.expressionPtr--];
		long pos = _this.identifierPositionStack[_this.identifierPtr];
		int start = (int) (pos >>> 32);
		char[] lexeme = _this.identifierStack[_this.identifierPtr--];
		_this.identifierLengthPtr--;
		_this.pushOnAstStack(new JmlAssumeStatement(new String(lexeme), pred, start));	
	}
	// <jml-end id="level.0-1-a" />
	//<jml-start id="jml.loop-annotations" />
	/**/public/**/ void consumeStatementDoWithAnnotations() {
		// DoStatement ::= JmlLoopAnnotations 'do' Statement 'while' '(' Expression ')' ';'

		//the 'while' pushes a value on _this.intStack that we need to remove
		_this.intPtr--;

		_this.astLengthPtr--;
		Statement statement = (Statement) _this.astStack[_this.astPtr--];
		JmlLoopAnnotations annotations = (JmlLoopAnnotations) _this.astStack[_this.astPtr];
		_this.expressionLengthPtr--;
		_this.astStack[_this.astPtr] = 
			new JmlDoStatement(
					annotations,
					_this.expressionStack[_this.expressionPtr--], 
					statement, 
					_this.intStack[_this.intPtr--], 
					_this.endStatementPosition); 

		int numIdentifiers = _this.identifierLengthStack[_this.identifierLengthPtr];
		if (numIdentifiers == 0) {
			_this.identifierLengthPtr--;
		} else {
			_this.consumeStatementLabel();
		}
	}
	//<jml-end id="jml.loop-annotations" />
	//<jml-start id="jml.loop-annotations" />
	/**/public/**/ void consumeStatementForWithAnnotations() {
		// ForStatement ::= 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' Statement
		// ForStatementNoShortIf ::= 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' StatementNoShortIf

		int length;
		Expression cond = null;
		Statement[] inits, updates;
		boolean scope = true;

		//statements
		_this.astLengthPtr--;
		Statement statement = (Statement) _this.astStack[_this.astPtr--];

		//updates are on the expresion stack
		if ((length = _this.expressionLengthStack[_this.expressionLengthPtr--]) == 0) {
			updates = null;
		} else {
			_this.expressionPtr -= length;
			System.arraycopy(
					_this.expressionStack, 
					_this.expressionPtr + 1, 
					updates = new Statement[length], 
					0, 
					length); 
		}

		if (_this.expressionLengthStack[_this.expressionLengthPtr--] != 0)
			cond = _this.expressionStack[_this.expressionPtr--];

		//inits may be on two different stacks
		if ((length = _this.astLengthStack[_this.astLengthPtr--]) == 0) {
			inits = null;
			scope = false;
		} else {
			if (length == -1) { //on _this.expressionStack
				scope = false;
				length = _this.expressionLengthStack[_this.expressionLengthPtr--];
				_this.expressionPtr -= length;
				System.arraycopy(
						_this.expressionStack, 
						_this.expressionPtr + 1, 
						inits = new Statement[length], 
						0, 
						length); 
			} else { //on _this.astStack
				_this.astPtr -= length;
				System.arraycopy(
						_this.astStack, 
						_this.astPtr + 1, 
						inits = new Statement[length], 
						0, 
						length); 
			}
		}
		_this.astLengthPtr--;
		Assert_isTrue(_this.astStack[_this.astPtr] instanceof JmlLoopAnnotations, "expecting astStack top to be a 'JmlLoopAnnotations' but found a '"+(_this.astStack[_this.astPtr].getClass().getName())+"'");  //$NON-NLS-1$//$NON-NLS-2$
		JmlLoopAnnotations annotations = (JmlLoopAnnotations) _this.astStack[_this.astPtr--];
		_this.pushOnAstStack(
				new JmlForStatement(
						annotations,
						inits, 
						cond, 
						updates, 
						statement, 
						scope, 
						_this.intStack[_this.intPtr--], 
						_this.endStatementPosition)); 
		int numIdentifiers = _this.identifierLengthStack[_this.identifierLengthPtr];
		if (numIdentifiers == 0) {
			_this.identifierLengthPtr--;
		} else {
			_this.consumeStatementLabel();
		}
	}
	//<jml-end id="jml.loop-annotations" />
	//<jml-start id="jml.loop-annotations" />
	/**/public/**/ void consumeStatementWhileWithAnnotations() {
		// WhileStatement ::= LoopAnnotations 'while' '(' Expression ')' Statement
		// WhileStatementNoShortIf ::= LoopAnnotations'while' '(' Expression ')' StatementNoShortIf

		_this.expressionLengthPtr--;
		_this.astLengthPtr--;
		Statement statement = (Statement) _this.astStack[_this.astPtr--];
		JmlLoopAnnotations annotations = (JmlLoopAnnotations) _this.astStack[_this.astPtr];
		_this.astStack[_this.astPtr] = 
			new JmlWhileStatement(
					annotations,
					_this.expressionStack[_this.expressionPtr--], 
					statement, 
					_this.intStack[_this.intPtr--], 
					_this.endStatementPosition);
		int numIdentifiers = _this.identifierLengthStack[_this.identifierLengthPtr];
		if (numIdentifiers == 0) {
			_this.identifierLengthPtr--;
		} else {
			_this.consumeStatementLabel();
		}
	}
	//<jml-end id="jml.loop-annotations" />

	/**/public/**/ void consumeMethodSpecRedundantPart() {
		// method-spec-redundant-part ::= 'implies_that' spec-case-seq
		/*
			_this.astStack : specCase_1 ... specCase_n
			_this.astLengthStack : n (n >= 1)
			_this.intStack : start-pos-of-implies_that
			 ==>
			_this.astStack : specCase_1 ... specCase_n
			_this.astLengthStack : n (n >= 1)
			_this.intStack : 
		 */
		// No information is retained for the implies_that keyword
		// on any of the stacks.  Hence, do nothing in this method.
		// I.e. simply return so that the next rule to reduce
		// will consume the specCases on the top of the AST stack.
	}

	// <jml-start id="quantifiers" />
	/**/public/**/ void consumeJmlQuantifiedExpression(boolean rangeSpecified) {
		// JmlQuantifiedExpression ::= '(' JmlQuantifier JmlTypeSpec JmlQuantifiedVarDeclarators ';' SpecExpression ')'
		// JmlQuantifiedExpression ::= '(' JmlQuantifier JmlTypeSpec JmlQuantifiedVarDeclarators ';' Predicate ';' SpecExpression ')'

		/*
			_this.astStack : Type LocalDeclaration ... LocalDeclaration
			_this.astLengthStack : 1 (number of bound variables in the quantifier)
			_this.expressionStack : Predicate SpecExpression (if rangeSpecified) or SpecExpression (if not)
			_this.expressionLengthStack : 1 1 or 1
			_this.identifierStack : JmlQuantifier
			 ==>
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : JmlQuantifiedExpression  
			_this.expressionLengthStack : 1
			_this.identifierStack : 
		 */	

		final JmlIdentifier quant = popIdentifierStack();
		final Expression body = popExpressionStack();

		/*@nullable*/ Expression range = null;
		try {
			range = 
				rangeSpecified ? popExpressionStack() : null;
		} catch(java.lang.ArrayIndexOutOfBoundsException e) {
			throw e;
		}

		final LocalDeclaration[] boundVariables = (LocalDeclaration[]) popAstStack(LocalDeclaration.class);
		// discard the type of the bound variables, which is now at the top of the AST stack
		popAstStack();
		_this.pushOnExpressionStack(new JmlQuantifiedExpression(quant.toString(), range, body, boundVariables, quant.sourceStart()));
	}
	/**/public/**/ void consumeJmlQuantifiedVarDeclarators(boolean isFirst) {
		// JmlQuantifiedVarDeclarators -> JmlQuantifiedVarDeclarator
		// JmlQuantifiedVarDeclarators ::= JmlQuantifiedVarDeclarators ',' JmlQuantifiedVarDeclarator

		/*
			_this.astStack : (K LocalDeclarations, for some 0 <= K)
			_this.astLengthStack : K (empty if K = 0)
			_this.expressionStack : 
			_this.expressionLengthStack :
			_this.identifierStack : Identifier
			 ==>
			_this.astStack : (K + 1 LocalDeclarations)
			_this.astLengthStack : K + 1
			_this.expressionStack :   
			_this.expressionLengthStack : 
			_this.identifierStack : 
		 */	

		final JmlIdentifier identifier = popIdentifierStack();
		final int extraDims = popIntStack();
		TypeReference type; 

		LocalDeclaration declaration = createLocalDeclaration(identifier);
		declaration.declarationSourceEnd = declaration.declarationEnd;

		if (isFirst) { 
			// this is the first bound variable, so we need to find its type
			Nullity[] extraNullities = null;
			if (!nullityStackIsEmpty() && nullityTopIsDims() && nullityTopIsDims(1)) {
				// handle split array dimensions (copied from consumeEnterVariable())
				extraNullities = popNullityStack(-nullityTopLength());
			}
			type = _this.getTypeReference(popIntStack());
			_this.pushOnAstStack(type);
			if (extraNullities != null) {
				pushOnNullityStack(extraNullities);
			}
		} else { 
			// we use the existing type, which is before the first LocalDeclaration on the AST stack
			type = (TypeReference) _this.astStack[_this.astPtr - _this.astLengthStack[_this.astLengthPtr]];
		}

		if (extraDims == 0) {
			declaration.type = type;
		} else {
			declaration.type = _this.copyDims(type, type.dimensions() + extraDims);
		}

		_this.pushOnAstStack(declaration);

		if (!isFirst) {
			// concatenate the AST node list if this is not the first bound variable, to keep
			// them all in one list (note that the bound variable type is in its own list)
			_this.optimizedConcatNodeLists();
		}
	}
	// <jml-end id="quantifiers" />
	// <jml-start id="set-comprehensions" />
	/**/public/**/ void consumeClassInstanceCreationExpressionWithSetComprehension() {
		// ClassInstanceCreationExpression ::= 'new' ClassType JmlSetComprehension
		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : JmlSetComprehension
			_this.expressionLengthStack : 1
			_this.identifierStack : ClassType-Information
			 ==>
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : JmlSetComprehension
			_this.expressionLengthStack : 1
			_this.identifierStack : 
		 */	

		final TypeReference classTypeRef = _this.getTypeReference(0);
		final JmlSetComprehension comprehension = (JmlSetComprehension) _this.expressionStack[_this.expressionPtr];
		comprehension.setTypeReference(classTypeRef);
		comprehension.sourceStart = popIntStack(); 
	}
	/**/public/**/ void consumeJmlSetComprehension() {
		// JmlSetComprehension ::= '{' JmlTypeSpec Identifier Dimsopt '|' JmlSetComprehensionPredicate '}'
		// JmlSetComprehensionPredicate -> JmlSetComprehensionMethodInvocation '&&' Predicate
		// JmlSetComprehensionMethodInvocation ::= Primary '.' Identifier '(' ArgumentListopt ')'

		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : MessageSend Predicate
			_this.expressionLengthStack : 1 1
			_this.identifierStack : TypeReference-Information Identifier
			 ==>
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : JmlSetComprehension
			_this.expressionLengthStack : 1
			_this.identifierStack : 
		 */

		final Expression pred = popExpressionStack();
		final Expression supersetPred = popExpressionStack();
		final JmlIdentifier identifier = popIdentifierStack();
		final int extraDims = popIntStack();
		LocalDeclaration declaration = createLocalDeclaration(identifier);		
		Nullity[] extraNullities = null;

		if (!nullityStackIsEmpty() && nullityTopIsDims() && nullityTopIsDims(1)) {
			// handle split array dimensions (copied from consumeEnterVariable())
			extraNullities = popNullityStack(-nullityTopLength());
		}

		TypeReference type = _this.getTypeReference(popIntStack());

		// deal with the split array dimensions from earlier 

		if (extraNullities != null) {
			pushOnNullityStack(extraNullities);
		}

		if (extraDims != 0) {
			type = _this.copyDims(type, type.dimensions() + extraDims);
		}

		declaration.declarationSourceEnd = declaration.declarationEnd;
		declaration.type = type;
		_this.pushOnExpressionStack(new JmlSetComprehension(declaration, supersetPred, pred));
	}
	// <jml-end id="set-comprehensions" />
	// <jml-start id="subtype-expression" />
	/**/public/**/ void consumeJmlSubtypeExpression() {
		// RelationalExpression ::= ShiftExpression '<:' ShiftExpression

		/*
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : LeftExpression RightExpression
			_this.expressionLengthStack : 1 1
			_this.identifierStack : 
			 ==>
			_this.astStack : 
			_this.astLengthStack : 
			_this.expressionStack : JmlSubtypeExpression
			_this.expressionLengthStack : 1
			_this.identifierStack : 
		 */

		final Expression right = popExpressionStack();
		final Expression left  = popExpressionStack();
		_this.pushOnExpressionStack(new JmlSubtypeExpression(left, right));
	}
	// <jml-end id="subtype-expression" />
	// <jml-start id="multifield" />
	/**/public/**/ void consumeJmlMultiReferenceExpressionAsNameDotStar() {
		// Based on consumePostfixExpression().
		// JmlMultiReferenceExpression ::= Name '.' '*'
		NameReference nameRef = _this.getUnspecifiedReferenceOptimized();
		Expression expr = new JmlNameDotStarStoreRef(nameRef);
		expr.sourceEnd = _this.scanner.currentPosition - 2;
		_this.pushOnExpressionStack(expr);
	}
	/**/public/**/ void consumeJmlMultiFieldAccess(boolean isSuperAccess) {
		// This method is based on consumeFieldAccess().
		// JmlMultiFieldAccess ::= Primary '.' '*'
		// JmlMultiFieldAccess ::= 'super' '.' '*'

		Expression receiver = isSuperAccess
		? new SuperReference(this.popIntStack(), _this.endPosition) 
		: this.popExpressionStack();
		JmlFieldDotStarStoreRef storeRef = new JmlFieldDotStarStoreRef(receiver);
		storeRef.sourceEnd = _this.endPosition;
		_this.pushOnExpressionStack(storeRef);
	}
	/**/public/**/ void consumeJmlArrayRangeAccess(boolean unspecifiedReference) {
		// This method is based on consumeArrayAccess.
		// ArrayAccess ::= Name '[' Expression ']' ==> true
		// ArrayAccess ::= PrimaryNoNewArray '[' Expression ']' ==> false
		Expression exp;
		if (unspecifiedReference) {
			exp = 
				_this.expressionStack[_this.expressionPtr] = 
					// <jml-start id="nnts" />
					new JmlArrayReference(
							// <jml-end id="nnts" />
							_this.getUnspecifiedReferenceOptimized(),
							_this.expressionStack[_this.expressionPtr]);
		} else {
			_this.expressionPtr--;
			_this.expressionLengthPtr--;
			exp = 
				_this.expressionStack[_this.expressionPtr] = 
					// <jml-start id="nnts" />
					new JmlArrayReference(
							// <jml-end id="nnts" />
							_this.expressionStack[_this.expressionPtr],
							_this.expressionStack[_this.expressionPtr + 1]);
		}
		exp.sourceEnd = _this.endStatementPosition;
		JmlArrayReference ar = (JmlArrayReference) this.popExpressionStack();
		Expression wrappedExpr = new JmlArrayRangeStoreRef(ar);
		wrappedExpr.sourceEnd = _this.endPosition;
		_this.pushOnExpressionStack(wrappedExpr);
	}
	/**/public/**/ void consumeJmlArrayIndexRange(int i) {
		// i == 0  means '*'
		// i == -1 means lower ..
		// i == 1  means .. upper
		// i == 2  means lower .. upper
		Expression upperBoundExpr = (i == 1 || i == 2)
			? this.popExpressionStack() : null;
		Expression lowerBoundExpr = (i == -1 || i == 2)
			? this.popExpressionStack() : null;
		Expression indexRangeExpr;
		if (i == 0)
			indexRangeExpr = new JmlAllRangeExpression();
		else
			indexRangeExpr = new JmlArrayIndexRangeExpression(lowerBoundExpr, upperBoundExpr);
		_this.pushOnExpressionStack(indexRangeExpr);
	}
	// <jml-end id="multifield" />

	//=======================================================================
	// General helper methods:

	protected LocalDeclaration createLocalDeclaration(JmlIdentifier id) {
		return new JmlLocalDeclaration(id.token(), id.sourceStart(), id.sourceEnd());
	}

	/**/public/**/ void Assert_isTrue(boolean b) {
		try {
			Assert.isTrue(b);
		} catch (NoClassDefFoundError ignored) {/**/}
	}
	/**/public/**/ void Assert_isTrue(boolean b, String msg) {
		try {
			Assert.isTrue(b, msg);
		} catch (NoClassDefFoundError ignored) {/**/}
	}

	//=======================================================================
	// Stack helper methods:

	// <jml-start id="nnts" />
	/**/public/**/ void pushOnNullityStack(Nullity nullity) {
		int stackLength = this.nullityStack.length;
		if (++this.nullityPtr >= stackLength) {
			System.arraycopy(this.nullityStack, 0, this.nullityStack = new Nullity[stackLength + NullityStackIncrement], 0, stackLength);
		}
		this.nullityStack[this.nullityPtr] = nullity;

		stackLength = this.nullityLengthStack.length;
		if (++this.nullityLengthPtr >= stackLength) {
			System.arraycopy(this.nullityLengthStack, 0, this.nullityLengthStack = new int[stackLength + NullityStackIncrement], 0, stackLength);
		}
		this.nullityLengthStack[this.nullityLengthPtr] = 1;
	}
	/**/public/**/ void pushOnNullityStack(Nullity[] nullities) {
		if (nullities.length == 0) { 
			Assert_isTrue(shouldIgnoreNullityStacks());
			return;
		}
		Assert_isTrue(nullities.length > 0);
		pushOnNullityStack(nullities[0]);
		for (int i=1; i<nullities.length; i++) {
			pushOnNullityStack(nullities[i]);
			concatNullityLists();
		}
		markNullityStackAsDims();
	}
	//private void pushOnNullityStackLengthStack(int pos) {
	//	int stackLength = this.nullityLengthStack.length;
	//	if (++this.nullityLengthPtr >= stackLength) {
	//		System.arraycopy(this.nullityLengthStack, 0,
	//				this.nullityLengthStack = new int[stackLength + StackIncrement], 0, stackLength);
	//	}
	//	this.nullityLengthStack[_this.expressionLengthPtr] = pos;
	//}
	private void concatNullityLists() {
		Assert_isTrue(this.nullityLengthStack[this.nullityLengthPtr] == 1);
		this.nullityLengthStack[--this.nullityLengthPtr]++;
	}
	/**/public/**/ boolean nullityStackIsEmpty() {
		boolean result = (this.nullityLengthPtr == -1);
		if (result) {
			Assert_isTrue(_this.hasError || this.nullityPtr == -1);
		}
		return result;
	}
	/**/public/**/ Nullity popNullityStack() {
		if (shouldIgnoreNullityStacks() && (nullityStackIsEmpty() || nullityTopIsDims())) {
			return defaultNullity;
		}
		Assert_isTrue(!nullityStackIsEmpty());
		int length = this.nullityLengthStack[this.nullityLengthPtr--];
		Assert_isTrue(length == 1);
		Nullity result = this.nullityStack[this.nullityPtr--];
		Assert_isTrue(result != null);
		return result;
	}
	/**/public/**/ Nullity[] popNullityStack(int n) {
		if (shouldIgnoreNullityStacks() && (!(n > 0 && ! nullityStackIsEmpty() && nullityTopIsDims()))) {
			return new Nullity[0];
		}
		Assert_isTrue(n > 0);
		Assert_isTrue(!nullityStackIsEmpty());
		Assert_isTrue(nullityTopIsDims());
		Nullity[] result = new Nullity[n];
		int length = - this.nullityLengthStack[this.nullityLengthPtr--];
		Assert_isTrue(_this.hasError || length <= n);
		if (n > length) {
			Assert_isTrue(!nullityStackIsEmpty());
			Assert_isTrue(nullityTopIsDims());
			length += -this.nullityLengthStack[this.nullityLengthPtr--];
		}
		Assert_isTrue(_this.hasError || length == n);
		if (length == n) {
			this.nullityPtr -= length;
			System.arraycopy(this.nullityStack, this.nullityPtr + 1, result, 0, n);
		}
		Assert_isTrue(_this.hasError || result.length != 0);
		return result;
	}
	/**/public/**/ void markNullityStackAsDims() {
		Assert_isTrue(!nullityStackIsEmpty());
		Assert_isTrue(!nullityTopIsDims());
		int length = this.nullityLengthStack[this.nullityLengthPtr];
		Assert_isTrue(length > 0);
		this.nullityLengthStack[this.nullityLengthPtr] = - length;
	}
	/**/public/**/ boolean nullityTopIsDims() {
		Assert_isTrue(!nullityStackIsEmpty());
		return nullityTopIsDims(0);
	}
	/**/public/**/ boolean nullityTopIsDims(int pos) {
		if (this.nullityLengthPtr-pos < 0)
			return false;
		int length = this.nullityLengthStack[this.nullityLengthPtr-pos];
		Assert_isTrue(length != 0);
		return length < 0;
	}
	/**/public/**/ boolean nullityTopIsLength(int n) {
		Assert_isTrue(!nullityStackIsEmpty());
		int length = this.nullityLengthStack[this.nullityLengthPtr];
		Assert_isTrue(length != 0);
		return (length == n) || (-length == n);
	}
	/**/public/**/ int nullityTopLength() {
		Assert_isTrue(!nullityStackIsEmpty());
		int length = this.nullityLengthStack[this.nullityLengthPtr];
		Assert_isTrue(length != 0);
		return length;
	}
	/**/public/**/ void emptyNullityStacks() {
		this.nullityLengthPtr = -1;
		this.nullityPtr = -1;
	}
	// <jml-end id="nnts" />
	//<jml-start id="stack.utility.methods" />
	///*@pure*/ private int topAstLengthStack() {
	//	return _this.astLengthStack[_this.astLengthPtr];
	//}

	//@ requires topAstLengthStack() == 1;
	private ASTNode popAstStack() {
		try {
			_this.astLengthPtr--;
			return _this.astStack[_this.astPtr--];
		} finally {
			// zero array elements helps in debugging (easier to see true stack content).
			// If you really feel this consumed too many cpu cycles, just comment
			// out this finally block.
			_this.astLengthStack[_this.astLengthPtr+1] = 0;
			_this.astStack[_this.astPtr+1] = null;
		}
	}

	/*@ public normal_behavior
		  @   old length = topAstLengthStack();	
		  @   requires elementType <: \type(ASTNode);
		  @   requires length >= 0;
		  @   modifies (* TBC *);
		  @   ensures \elemtype(\result) == elementType;
		  @   ensures \result.length == length;
		  @   ensures _this.astPtr == \old(_this.astPtr) - length;
		  @   // ensures ...
		  @*/
	private ASTNode[] popAstStack(Class elementType) {
		int length = _this.astLengthStack[_this.astLengthPtr--];
		ASTNode[] result = (ASTNode[]) java.lang.reflect.Array.newInstance(elementType, length);
		_this.astPtr -= length;
		System.arraycopy(_this.astStack, _this.astPtr + 1, result, 0, length);
		// zero array elements helps in debugging (easier to see true stack content).
		// If you really feel this consumed too many cpu cycles, just comment
		// out these two lines:
		_this.astLengthStack[_this.astLengthPtr+1] = 0;
		Arrays.fill(_this.astStack, _this.astPtr+1, _this.astPtr+1+length, null);
		return result;
	}

	/*@ pure
		private int topExpressionLengthStack() {
			return _this.expressionLengthStack[_this.expressionLengthPtr];
		}
		pure
		private Expression topExpressionStack() {
			return _this.expressionStack[_this.expressionPtr];
		}
	 */

	private /*@nullable*/Expression popExpressionStackMayBeNull() {
		int len = _this.expressionLengthStack[_this.expressionLengthPtr--];
		if (len == 0)
			return null;
		return _this.expressionStack[_this.expressionPtr--];
	}

	//@ requires topExpressionLengthStack() == 1;
	private Expression popExpressionStack() {
		_this.expressionLengthPtr--;
		return _this.expressionStack[_this.expressionPtr--];
	}

	/*@ public normal_behavior
		  @   old length = topExpressionLengthStack();	
		  @   requires elementType <: \type(Expression);
		  @   requires length >= 0;
		  @   modifies (* TBC *);
		  @   ensures \elemtype(\result) == elementType;
		  @   ensures \result.length == length;
		  @   ensures _this.astPtr == \old(_this.astPtr) - length;
		  @   // ensures ...
		  @*/
	private Expression[] popExpressionStack(Class elementType) {
		int length = (_this.expressionLengthStack[_this.expressionLengthPtr--]);
		Expression[] result = (Expression[]) java.lang.reflect.Array.newInstance(elementType, length);
		_this.expressionPtr -= length;
		System.arraycopy(_this.expressionStack, _this.expressionPtr + 1, result, 0, length);
		return result;
	}

	private int popIntStack() {
		return _this.intStack[_this.intPtr--];
	}

	///*@pure*/ private int topIdentifierLengthStack() {
	//	return _this.identifierLengthStack[_this.identifierLengthPtr];
	//}

	//!@ requires topIdentifierLengthStack() == 1;
	private JmlIdentifier popIdentifierStack() {
		int idLength = _this.identifierLengthStack[_this.identifierLengthPtr--];
		if (idLength != 1) {
			// Note that we could return null if the length is 0.
			throw new IllegalStateException("unexpected id length: " + idLength); //$NON-NLS-1$
		}

		char[] token = _this.identifierStack[_this.identifierPtr];
		long pos = _this.identifierPositionStack[_this.identifierPtr--];
		int id = this.jmlKeywordTokenId;
		// FIXME: don't really want to allocate a new JmlIdentifier every time. Reuse, then have the caller clone if necessary.
		return new JmlIdentifier(token, this.jmlKeywordHasRedundantSuffix, id, pos);
	}
	//<jml-end id="stack.utility.methods" />

	// <jml-start id="nnts" />
	/**/public/**/ void signalEndOfClassAndResetDefaultNullity(){
		this.classDeclarationCount--;
		if (this.classDeclarationCount == 0) {
			this.resetDefaultNullity();
		}
	}
	/**/public/**/ void signalNewClassAndCheckInnerClassDefaultNullity(TypeDeclaration typedecl, String type){
		this.classDeclarationCount ++;
		// detection of inner class default nullity
		if (this.defaultNullityAnnotationPushed) {
			JmlIdentifier defaultNullityAnnotation = this.popIdentifierStack();
			this.defaultNullityAnnotationPushed = false;
			if (this.reportDefaultNullityAnnotationOnInnerClassError) {			
				int sourceStart = defaultNullityAnnotation.sourceStart();
				int sourceEnd = defaultNullityAnnotation.sourceEnd();

				_this.problemReporter.invalidModifier(type, new String(typedecl.name), "outer class default nullity annotations", sourceStart, sourceEnd, typedecl); //$NON-NLS-1$
				this.reportDefaultNullityAnnotationOnInnerClassError = false;
			}		
		}
	}
	public void resetStacksExtra() {
		this.emptyNullityStacks();
		this.classDeclarationCount = 0;
		this.reportDefaultNullityAnnotationOnInnerClassError = false;
		this.defaultNullityAnnotationPushed = false;
	}

	private static boolean warning_marker_for_consume = true;
	
	// No user servicable parts below this line.
protected void consumeRule(int act) {
  switch ( act ) {
    case 30 : if (DEBUG) { System.out.println("Type ::= PrimitiveType"); }  //$NON-NLS-1$
		    _this.consumePrimitiveType();  
			break;
 
    case 31 : if (DEBUG) { System.out.println("Type ::= NullityModifier PrimitiveType"); }  //$NON-NLS-1$
		    _this.consumePrimitiveType();  
			break;
 
    case 32 : if (DEBUG) { System.out.println("Type ::= OwnershipModifiers PrimitiveType"); }  //$NON-NLS-1$
		    /*jml*/consumeTypeWithOwnershipModifiers();  
			break;
 
    case 33 : if (DEBUG) { System.out.println("Type ::= ReferenceType"); }  //$NON-NLS-1$
		    /*jml*/consumeReferenceTypeWithoutOwnershipModifiers();  
			break;
 
    case 34 : if (DEBUG) { System.out.println("Type ::= OwnershipModifiers ReferenceType"); }  //$NON-NLS-1$
		    /*jml*/consumeTypeWithOwnershipModifiers();  
			break;
 
    case 47 : if (DEBUG) { System.out.println("ReferenceType ::= ClassOrInterfaceType"); }  //$NON-NLS-1$
		    _this.consumeReferenceType();   
			break;
 
    case 48 : if (DEBUG) { System.out.println("ReferenceType ::= NullityModifier ClassOrInterfaceType"); }  //$NON-NLS-1$
		    _this.consumeReferenceType();   
			break;
 
    case 52 : if (DEBUG) { System.out.println("ClassOrInterface ::= Name"); }  //$NON-NLS-1$
		    _this.consumeClassOrInterfaceName();   
			break;
 
    case 53 : if (DEBUG) { System.out.println("ClassOrInterface ::= GenericType DOT Name"); }  //$NON-NLS-1$
		    _this.consumeClassOrInterface();   
			break;
 
    case 54 : if (DEBUG) { System.out.println("GenericType ::= ClassOrInterface TypeArguments"); }  //$NON-NLS-1$
		    _this.consumeGenericType();   
			break;
 
    case 55 : if (DEBUG) { System.out.println("ArrayTypeWithTypeArgumentsName ::= GenericType DOT Name"); }  //$NON-NLS-1$
		    _this.consumeArrayTypeWithTypeArgumentsName();   
			break;
 
    case 56 : if (DEBUG) { System.out.println("ArrayType ::= NullityModifier PrimitiveType Dims"); }  //$NON-NLS-1$
		    _this.consumePrimitiveArrayType();   
			break;
 
    case 57 : if (DEBUG) { System.out.println("ArrayType ::= PrimitiveType Dims"); }  //$NON-NLS-1$
		    _this.consumePrimitiveArrayType();   
			break;
 
    case 58 : if (DEBUG) { System.out.println("ArrayType ::= NullityModifier Name Dims"); }  //$NON-NLS-1$
		    _this.consumeNameArrayType();   
			break;
 
    case 59 : if (DEBUG) { System.out.println("ArrayType ::= Name Dims"); }  //$NON-NLS-1$
		    _this.consumeNameArrayType();   
			break;
 
    case 60 : if (DEBUG) { System.out.println("ArrayType ::= ArrayTypeWithTypeArgumentsName Dims"); }  //$NON-NLS-1$
		    _this.consumeGenericTypeNameArrayType();   
			break;
 
    case 61 : if (DEBUG) { System.out.println("ArrayType ::= GenericType Dims"); }  //$NON-NLS-1$
		    _this.consumeGenericTypeArrayType();   
			break;
 
    case 66 : if (DEBUG) { System.out.println("QualifiedName ::= Name DOT SimpleName"); }  //$NON-NLS-1$
		    _this.consumeQualifiedName();  
			break;
 
    case 67 : if (DEBUG) { System.out.println("CompilationUnit ::= EnterCompilationUnit..."); }  //$NON-NLS-1$
		    _this.consumeCompilationUnit();  
			break;
 
    case 68 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= PackageDeclaration"); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnit();  
			break;
 
    case 69 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= PackageDeclaration..."); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnit();  
			break;
 
    case 70 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= PackageDeclaration..."); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnitWithTypes();  
			break;
 
    case 71 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= PackageDeclaration..."); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnitWithTypes();  
			break;
 
    case 72 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= ImportDeclarations..."); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnit();  
			break;
 
    case 73 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= TypeDeclarations"); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnitWithTypes();  
			break;
 
    case 74 : if (DEBUG) { System.out.println("InternalCompilationUnit ::= ImportDeclarations..."); }  //$NON-NLS-1$
		    _this.consumeInternalCompilationUnitWithTypes();  
			break;
 
    case 75 : if (DEBUG) { System.out.println("InternalCompilationUnit ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyInternalCompilationUnit();  
			break;
 
    case 76 : if (DEBUG) { System.out.println("ReduceImports ::="); }  //$NON-NLS-1$
		    _this.consumeReduceImports();  
			break;
 
    case 77 : if (DEBUG) { System.out.println("EnterCompilationUnit ::="); }  //$NON-NLS-1$
		    _this.consumeEnterCompilationUnit();  
			break;
 
    case 93 : if (DEBUG) { System.out.println("CatchHeader ::= catch LPAREN FormalParameter RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeCatchHeader();  
			break;
 
    case 95 : if (DEBUG) { System.out.println("ImportDeclarations ::= ImportDeclarations..."); }  //$NON-NLS-1$
		    _this.consumeImportDeclarations();  
			break;
 
    case 97 : if (DEBUG) { System.out.println("TypeDeclarations ::= TypeDeclarations TypeDeclaration"); }  //$NON-NLS-1$
		    _this.consumeTypeDeclarations();  
			break;
 
    case 98 : if (DEBUG) { System.out.println("PackageDeclaration ::= PackageDeclarationName SEMICOLON"); }  //$NON-NLS-1$
		     _this.consumePackageDeclaration();  
			break;
 
    case 99 : if (DEBUG) { System.out.println("PackageDeclarationName ::= Modifiers package..."); }  //$NON-NLS-1$
		     _this.consumePackageDeclarationNameWithModifiers();  
			break;
 
    case 100 : if (DEBUG) { System.out.println("PackageDeclarationName ::= PackageComment package Name"); }  //$NON-NLS-1$
		     _this.consumePackageDeclarationName();  
			break;
 
    case 101 : if (DEBUG) { System.out.println("PackageComment ::="); }  //$NON-NLS-1$
		     _this.consumePackageComment();  
			break;
 
    case 106 : if (DEBUG) { System.out.println("SingleTypeImportDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeImportDeclaration();  
			break;
 
    case 107 : if (DEBUG) { System.out.println("SingleTypeImportDeclarationName ::= import Name"); }  //$NON-NLS-1$
		    _this.consumeSingleTypeImportDeclarationName();  
			break;
 
    case 108 : if (DEBUG) { System.out.println("TypeImportOnDemandDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeImportDeclaration();  
			break;
 
    case 109 : if (DEBUG) { System.out.println("TypeImportOnDemandDeclarationName ::= import Name DOT..."); }  //$NON-NLS-1$
		    _this.consumeTypeImportOnDemandDeclarationName();  
			break;
 
     case 112 : if (DEBUG) { System.out.println("TypeDeclaration ::= SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeEmptyTypeDeclaration();  
			break;
 
    case 116 : if (DEBUG) { System.out.println("Modifiers ::= Modifiers Modifier"); }  //$NON-NLS-1$
		    _this.consumeModifiers2();  
			break;
 
    case 128 : if (DEBUG) { System.out.println("Modifier ::= JmlModifier"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlModifierAsModifier();  
			break;
 
    case 129 : if (DEBUG) { System.out.println("Modifier ::= Annotation"); }  //$NON-NLS-1$
		    _this.consumeAnnotationAsModifier();  
			break;
 
    case 147 : if (DEBUG) { System.out.println("NullityByDefaultModifier ::= non_null_by_default"); }  //$NON-NLS-1$
		    /*jml*/consumeDefaultNullity();  
			break;
 
    case 148 : if (DEBUG) { System.out.println("NullityByDefaultModifier ::= nullable_by_default"); }  //$NON-NLS-1$
		    /*jml*/consumeDefaultNullity();  
			break;
 
    case 149 : if (DEBUG) { System.out.println("OwnershipModifiers ::= OwnershipModifier"); }  //$NON-NLS-1$
		    /*jml*/consumeOwnershipModifiers(1);  
			break;
 
    case 150 : if (DEBUG) { System.out.println("OwnershipModifiers ::= OwnershipModifier..."); }  //$NON-NLS-1$
		    /*jml*/consumeOwnershipModifiers(2);  
			break;
 
    case 158 : if (DEBUG) { System.out.println("ClassDeclaration ::= ClassHeader ClassBody"); }  //$NON-NLS-1$
		    _this.consumeClassDeclaration();  
			break;
 
    case 159 : if (DEBUG) { System.out.println("ClassDeclaration ::= NullityByDefaultModifier..."); }  //$NON-NLS-1$
		    _this.consumeClassDeclaration();  
			break;
 
    case 160 : if (DEBUG) { System.out.println("ClassHeader ::= ClassHeaderName ClassHeaderExtendsopt..."); }  //$NON-NLS-1$
		    _this.consumeClassHeader();  
			break;
 
    case 161 : if (DEBUG) { System.out.println("ClassHeaderName ::= ClassHeaderName1 TypeParameters"); }  //$NON-NLS-1$
		    _this.consumeTypeHeaderNameWithTypeParameters();  
			break;
 
    case 163 : if (DEBUG) { System.out.println("ClassHeaderName1 ::= Modifiersopt class Identifier"); }  //$NON-NLS-1$
		    _this.consumeClassHeaderName1();  
			break;
 
    case 164 : if (DEBUG) { System.out.println("ClassHeaderExtends ::= extends ClassType"); }  //$NON-NLS-1$
		    _this.consumeClassHeaderExtends();  
			break;
 
    case 165 : if (DEBUG) { System.out.println("ClassHeaderImplements ::= implements InterfaceTypeList"); }  //$NON-NLS-1$
		    _this.consumeClassHeaderImplements();  
			break;
 
    case 167 : if (DEBUG) { System.out.println("InterfaceTypeList ::= InterfaceTypeList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceTypeList();  
			break;
 
    case 168 : if (DEBUG) { System.out.println("InterfaceType ::= ClassOrInterfaceType"); }  //$NON-NLS-1$
		    _this.consumeInterfaceType();  
			break;
 
    case 171 : if (DEBUG) { System.out.println("ClassBodyDeclarations ::= ClassBodyDeclarations..."); }  //$NON-NLS-1$
		    _this.consumeClassBodyDeclarations();  
			break;
 
    case 176 : if (DEBUG) { System.out.println("ClassBodyDeclaration ::= Diet NestedMethod..."); }  //$NON-NLS-1$
		    _this.consumeClassBodyDeclaration();  
			break;
 
    case 177 : if (DEBUG) { System.out.println("Diet ::="); }  //$NON-NLS-1$
		    _this.consumeDiet();  
			break;

    case 178 : if (DEBUG) { System.out.println("Initializer ::= Diet NestedMethod CreateInitializer..."); }  //$NON-NLS-1$
		    _this.consumeClassBodyDeclaration();  
			break;
 
    case 179 : if (DEBUG) { System.out.println("CreateInitializer ::="); }  //$NON-NLS-1$
		    _this.consumeCreateInitializer();  
			break;

    case 186 : if (DEBUG) { System.out.println("ClassMemberDeclaration ::= SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeEmptyTypeDeclaration();  
			break;

    case 189 : if (DEBUG) { System.out.println("FieldDeclaration ::= Modifiersopt Type..."); }  //$NON-NLS-1$
		    _this.consumeFieldDeclaration();  
			break;
 
    case 190 : if (DEBUG) { System.out.println("FieldDeclaration ::= Modifiersopt Type..."); }  //$NON-NLS-1$
		    /*jml*/consumeFieldDeclarationWithDataGroupClause();  
			break;
 
    case 192 : if (DEBUG) { System.out.println("VariableDeclarators ::= VariableDeclarators COMMA..."); }  //$NON-NLS-1$
		    _this.consumeVariableDeclarators();  
			break;
 
    case 195 : if (DEBUG) { System.out.println("EnterVariable ::="); }  //$NON-NLS-1$
		    _this.consumeEnterVariable();  
			break;
 
    case 196 : if (DEBUG) { System.out.println("ExitVariableWithInitialization ::="); }  //$NON-NLS-1$
		    _this.consumeExitVariableWithInitialization();  
			break;
 
    case 197 : if (DEBUG) { System.out.println("ExitVariableWithoutInitialization ::="); }  //$NON-NLS-1$
		    _this.consumeExitVariableWithoutInitialization();  
			break;
 
    case 198 : if (DEBUG) { System.out.println("ForceNoDiet ::="); }  //$NON-NLS-1$
		    _this.consumeForceNoDiet();  
			break;
 
    case 199 : if (DEBUG) { System.out.println("RestoreDiet ::="); }  //$NON-NLS-1$
		    _this.consumeRestoreDiet();  
			break;
 
    case 204 : if (DEBUG) { System.out.println("MethodDeclaration ::= MethodHeader MethodBody"); }  //$NON-NLS-1$
		    // set to true to consume a method with a body
  _this.consumeMethodDeclaration(true);   
			break;
 
    case 205 : if (DEBUG) { System.out.println("MethodDeclaration ::= MethodSpecification MethodHeader"); }  //$NON-NLS-1$
		    // set to true to consume a method with a body
  /*jml*/consumeSpecedMethodDeclaration(true);   
			break;
 
    case 206 : if (DEBUG) { System.out.println("AbstractMethodDeclaration ::= MethodHeader SEMICOLON"); }  //$NON-NLS-1$
		    // set to false to consume a method without body
  _this.consumeMethodDeclaration(false);  
			break;
 
    case 207 : if (DEBUG) { System.out.println("AbstractMethodDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    // set to false to consume a method without body
   /*jml*/consumeSpecedMethodDeclaration(false);  
			break;
 
    case 208 : if (DEBUG) { System.out.println("MethodHeader ::= MethodHeaderName FormalParameterListopt"); }  //$NON-NLS-1$
		    _this.consumeMethodHeader();  
			break;
 
    case 209 : if (DEBUG) { System.out.println("MethodHeaderName ::= Modifiersopt TypeParameters Type..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderNameWithTypeParameters(false);  
			break;
 
    case 210 : if (DEBUG) { System.out.println("MethodHeaderName ::= Modifiersopt Type Identifier LPAREN"); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderName(false);  
			break;
 
    case 211 : if (DEBUG) { System.out.println("MethodHeaderRightParen ::= RPAREN"); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderRightParen();  
			break;
 
    case 212 : if (DEBUG) { System.out.println("MethodHeaderExtendedDims ::= Dimsopt"); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderExtendedDims();  
			break;
 
    case 213 : if (DEBUG) { System.out.println("MethodHeaderThrowsClause ::= throws ClassTypeList"); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderThrowsClause();  
			break;
 
    case 214 : if (DEBUG) { System.out.println("ConstructorHeader ::= ConstructorHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeConstructorHeader();  
			break;
 
    case 215 : if (DEBUG) { System.out.println("ConstructorHeaderName ::= Modifiersopt TypeParameters..."); }  //$NON-NLS-1$
		    _this.consumeConstructorHeaderNameWithTypeParameters();  
			break;
 
    case 216 : if (DEBUG) { System.out.println("ConstructorHeaderName ::= Modifiersopt Identifier LPAREN"); }  //$NON-NLS-1$
		    _this.consumeConstructorHeaderName();  
			break;
 
    case 218 : if (DEBUG) { System.out.println("FormalParameterList ::= FormalParameterList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeFormalParameterList();  
			break;
 
    case 219 : if (DEBUG) { System.out.println("FormalParameter ::= Modifiersopt Type..."); }  //$NON-NLS-1$
		    _this.consumeFormalParameter(false);  
			break;
 
    case 220 : if (DEBUG) { System.out.println("FormalParameter ::= Modifiersopt Type ELLIPSIS..."); }  //$NON-NLS-1$
		    _this.consumeFormalParameter(true);  
			break;
 
    case 222 : if (DEBUG) { System.out.println("ClassTypeList ::= ClassTypeList COMMA ClassTypeElt"); }  //$NON-NLS-1$
		    _this.consumeClassTypeList();  
			break;
 
    case 223 : if (DEBUG) { System.out.println("ClassTypeElt ::= ClassType"); }  //$NON-NLS-1$
		    _this.consumeClassTypeElt();  
			break;
 
    case 224 : if (DEBUG) { System.out.println("MethodBody ::= NestedMethod LBRACE BlockStatementsopt..."); }  //$NON-NLS-1$
		    _this.consumeMethodBody();  
			break;
 
    case 225 : if (DEBUG) { System.out.println("NestedMethod ::="); }  //$NON-NLS-1$
		    _this.consumeNestedMethod();  
			break;
 
    case 226 : if (DEBUG) { System.out.println("StaticInitializer ::= StaticOnly Block"); }  //$NON-NLS-1$
		    _this.consumeStaticInitializer();  
			break;

    case 227 : if (DEBUG) { System.out.println("StaticOnly ::= static"); }  //$NON-NLS-1$
		    _this.consumeStaticOnly();  
			break;
 
    case 228 : if (DEBUG) { System.out.println("ConstructorDeclaration ::= ConstructorHeader MethodBody"); }  //$NON-NLS-1$
		    _this.consumeConstructorDeclaration() ;  
			break;
 
    case 229 : if (DEBUG) { System.out.println("ConstructorDeclaration ::= ConstructorHeader SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeInvalidConstructorDeclaration() ;  
			break;
 
    case 230 : if (DEBUG) { System.out.println("ConstructorDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    /*jml*/consumeSpecedConstructorDeclaration() ;  
			break;
 
    case 231 : if (DEBUG) { System.out.println("ConstructorDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    /*jml*/consumeInvalidSpecedConstructorDeclaration(false) ;  
			break;
 
    case 232 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= this LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(0, Parser.THIS_CALL);  
			break;
 
    case 233 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= OnlyTypeArguments this"); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(0,Parser.THIS_CALL);  
			break;
 
    case 234 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= super LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(0,Parser.SUPER_CALL);  
			break;
 
    case 235 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= OnlyTypeArguments..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(0,Parser.SUPER_CALL);  
			break;
 
    case 236 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Primary DOT super..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(1, Parser.SUPER_CALL);  
			break;
 
    case 237 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Primary DOT..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(1, Parser.SUPER_CALL);  
			break;
 
    case 238 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Name DOT super LPAREN"); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(2, Parser.SUPER_CALL);  
			break;
 
    case 239 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Name DOT..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(2, Parser.SUPER_CALL);  
			break;
 
    case 240 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Primary DOT this..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(1, Parser.THIS_CALL);  
			break;
 
    case 241 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Primary DOT..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(1, Parser.THIS_CALL);  
			break;
 
    case 242 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Name DOT this LPAREN"); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocation(2, Parser.THIS_CALL);  
			break;
 
    case 243 : if (DEBUG) { System.out.println("ExplicitConstructorInvocation ::= Name DOT..."); }  //$NON-NLS-1$
		    _this.consumeExplicitConstructorInvocationWithTypeArguments(2, Parser.THIS_CALL);  
			break;
 
    case 244 : if (DEBUG) { System.out.println("InterfaceDeclaration ::= InterfaceHeader InterfaceBody"); }  //$NON-NLS-1$
		    _this.consumeInterfaceDeclaration();  
			break;
 
    case 245 : if (DEBUG) { System.out.println("InterfaceDeclaration ::= NullityByDefaultModifier..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceDeclaration();  
			break;
 
    case 246 : if (DEBUG) { System.out.println("InterfaceHeader ::= InterfaceHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceHeader();  
			break;
 
    case 247 : if (DEBUG) { System.out.println("InterfaceHeaderName ::= InterfaceHeaderName1..."); }  //$NON-NLS-1$
		    _this.consumeTypeHeaderNameWithTypeParameters();  
			break;
 
    case 249 : if (DEBUG) { System.out.println("InterfaceHeaderName1 ::= Modifiersopt interface..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceHeaderName1();  
			break;
 
    case 250 : if (DEBUG) { System.out.println("InterfaceHeaderExtends ::= extends InterfaceTypeList"); }  //$NON-NLS-1$
		    _this.consumeInterfaceHeaderExtends();  
			break;
 
    case 253 : if (DEBUG) { System.out.println("InterfaceMemberDeclarations ::=..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceMemberDeclarations();  
			break;
 
    case 254 : if (DEBUG) { System.out.println("InterfaceMemberDeclaration ::= SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeEmptyTypeDeclaration();  
			break;
 
    case 256 : if (DEBUG) { System.out.println("InterfaceMemberDeclaration ::= MethodHeader MethodBody"); }  //$NON-NLS-1$
		    _this.consumeInvalidMethodDeclaration();  
			break;
 
    case 258 : if (DEBUG) { System.out.println("InterfaceMemberDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    /*jml*/consumeInvalidSpecedMethodDeclaration();  
			break;
 
    case 259 : if (DEBUG) { System.out.println("InvalidConstructorDeclaration ::= ConstructorHeader..."); }  //$NON-NLS-1$
		    _this.consumeInvalidConstructorDeclaration(true);   
			break;
 
    case 260 : if (DEBUG) { System.out.println("InvalidConstructorDeclaration ::= ConstructorHeader..."); }  //$NON-NLS-1$
		    _this.consumeInvalidConstructorDeclaration(false);   
			break;
 
    case 261 : if (DEBUG) { System.out.println("InvalidConstructorDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    /*jml*/consumeInvalidSpecedConstructorDeclaration(true);   
			break;
 
    case 262 : if (DEBUG) { System.out.println("InvalidConstructorDeclaration ::= MethodSpecification..."); }  //$NON-NLS-1$
		    /*jml*/consumeInvalidSpecedConstructorDeclaration(false);   
			break;
 
    case 270 : if (DEBUG) { System.out.println("PushLeftBrace ::="); }  //$NON-NLS-1$
		    _this.consumePushLeftBrace();  
			break;
 
    case 271 : if (DEBUG) { System.out.println("ArrayInitializer ::= LBRACE PushLeftBrace ,opt RBRACE"); }  //$NON-NLS-1$
		    _this.consumeEmptyArrayInitializer();  
			break;
 
    case 272 : if (DEBUG) { System.out.println("ArrayInitializer ::= LBRACE PushLeftBrace..."); }  //$NON-NLS-1$
		    _this.consumeArrayInitializer();  
			break;
 
    case 273 : if (DEBUG) { System.out.println("ArrayInitializer ::= LBRACE PushLeftBrace..."); }  //$NON-NLS-1$
		    _this.consumeArrayInitializer();  
			break;
 
    case 275 : if (DEBUG) { System.out.println("VariableInitializers ::= VariableInitializers COMMA..."); }  //$NON-NLS-1$
		    _this.consumeVariableInitializers();  
			break;
 
    case 276 : if (DEBUG) { System.out.println("Block ::= OpenBlock LBRACE BlockStatementsopt RBRACE"); }  //$NON-NLS-1$
		    _this.consumeBlock();  
			break;
 
    case 277 : if (DEBUG) { System.out.println("OpenBlock ::="); }  //$NON-NLS-1$
		    _this.consumeOpenBlock() ;  
			break;
 
    case 279 : if (DEBUG) { System.out.println("BlockStatements ::= BlockStatements BlockStatement"); }  //$NON-NLS-1$
		    _this.consumeBlockStatements() ;  
			break;
 
    case 283 : if (DEBUG) { System.out.println("BlockStatement ::= InterfaceDeclaration"); }  //$NON-NLS-1$
		    _this.consumeInvalidInterfaceDeclaration();  
			break;
 
    case 284 : if (DEBUG) { System.out.println("BlockStatement ::= AnnotationTypeDeclaration"); }  //$NON-NLS-1$
		    _this.consumeInvalidAnnotationTypeDeclaration();  
			break;
 
    case 285 : if (DEBUG) { System.out.println("BlockStatement ::= EnumDeclaration"); }  //$NON-NLS-1$
		    _this.consumeInvalidEnumDeclaration();  
			break;
 
    case 286 : if (DEBUG) { System.out.println("LocalVariableDeclarationStatement ::=..."); }  //$NON-NLS-1$
		    _this.consumeLocalVariableDeclarationStatement();  
			break;
 
    case 287 : if (DEBUG) { System.out.println("LocalVariableDeclaration ::= Type PushModifiers..."); }  //$NON-NLS-1$
		    _this.consumeLocalVariableDeclaration();  
			break;
 
    case 288 : if (DEBUG) { System.out.println("LocalVariableDeclaration ::= Modifiers Type..."); }  //$NON-NLS-1$
		    _this.consumeLocalVariableDeclaration();  
			break;
 
    case 289 : if (DEBUG) { System.out.println("PushModifiers ::="); }  //$NON-NLS-1$
		    _this.consumePushModifiers();  
			break;
 
    case 290 : if (DEBUG) { System.out.println("PushModifiersForHeader ::="); }  //$NON-NLS-1$
		    _this.consumePushModifiersForHeader();  
			break;
 
    case 291 : if (DEBUG) { System.out.println("PushRealModifiers ::="); }  //$NON-NLS-1$
		    _this.consumePushRealModifiers();  
			break;
 
    case 321 : if (DEBUG) { System.out.println("JmlSetStatement ::= set Assignment ExitJmlClause..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSetStatement() ;  
			break;
 
    case 322 : if (DEBUG) { System.out.println("EmptyStatement ::= SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeEmptyStatement();  
			break;
 
    case 323 : if (DEBUG) { System.out.println("LabeledStatement ::= Label COLON Statement"); }  //$NON-NLS-1$
		    _this.consumeStatementLabel() ;  
			break;
 
    case 324 : if (DEBUG) { System.out.println("LabeledStatementNoShortIf ::= Label COLON..."); }  //$NON-NLS-1$
		    _this.consumeStatementLabel() ;  
			break;
 
    case 325 : if (DEBUG) { System.out.println("Label ::= Identifier"); }  //$NON-NLS-1$
		    _this.consumeLabel() ;  
			break;
 
     case 326 : if (DEBUG) { System.out.println("ExpressionStatement ::= StatementExpression SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeExpressionStatement();  
			break;
 
    case 335 : if (DEBUG) { System.out.println("IfThenStatement ::= if LPAREN Expression RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementIfNoElse();  
			break;
 
    case 336 : if (DEBUG) { System.out.println("IfThenElseStatement ::= if LPAREN Expression RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementIfWithElse();  
			break;
 
    case 337 : if (DEBUG) { System.out.println("IfThenElseStatementNoShortIf ::= if LPAREN Expression..."); }  //$NON-NLS-1$
		    _this.consumeStatementIfWithElse();  
			break;
 
    case 338 : if (DEBUG) { System.out.println("SwitchStatement ::= switch LPAREN Expression RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementSwitch() ;  
			break;
 
    case 339 : if (DEBUG) { System.out.println("SwitchBlock ::= LBRACE RBRACE"); }  //$NON-NLS-1$
		    _this.consumeEmptySwitchBlock() ;  
			break;
 
    case 342 : if (DEBUG) { System.out.println("SwitchBlock ::= LBRACE SwitchBlockStatements..."); }  //$NON-NLS-1$
		    _this.consumeSwitchBlock() ;  
			break;
 
    case 344 : if (DEBUG) { System.out.println("SwitchBlockStatements ::= SwitchBlockStatements..."); }  //$NON-NLS-1$
		    _this.consumeSwitchBlockStatements() ;  
			break;
 
    case 345 : if (DEBUG) { System.out.println("SwitchBlockStatement ::= SwitchLabels BlockStatements"); }  //$NON-NLS-1$
		    _this.consumeSwitchBlockStatement() ;  
			break;
 
    case 347 : if (DEBUG) { System.out.println("SwitchLabels ::= SwitchLabels SwitchLabel"); }  //$NON-NLS-1$
		    _this.consumeSwitchLabels() ;  
			break;
 
     case 348 : if (DEBUG) { System.out.println("SwitchLabel ::= case ConstantExpression COLON"); }  //$NON-NLS-1$
		    _this.consumeCaseLabel();  
			break;
 
     case 349 : if (DEBUG) { System.out.println("SwitchLabel ::= default COLON"); }  //$NON-NLS-1$
		    _this.consumeDefaultLabel();  
			break;
 
    case 350 : if (DEBUG) { System.out.println("WhileStatement ::= while LPAREN Expression RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementWhile() ;  
			break;
 
    case 351 : if (DEBUG) { System.out.println("WhileStatement ::= JmlLoopAnnotations while LPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeStatementWhileWithAnnotations() ;  
			break;
 
    case 352 : if (DEBUG) { System.out.println("WhileStatementNoShortIf ::= while LPAREN Expression..."); }  //$NON-NLS-1$
		    _this.consumeStatementWhile() ;  
			break;
 
    case 353 : if (DEBUG) { System.out.println("WhileStatementNoShortIf ::= JmlLoopAnnotations while..."); }  //$NON-NLS-1$
		    /*jml*/consumeStatementWhileWithAnnotations() ;  
			break;
 
    case 354 : if (DEBUG) { System.out.println("JmlLoopAnnotations ::= JmlLoopInvariantSeq JmlLabelopt"); }  //$NON-NLS-1$
		    /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/true, /*hasVariantSeq*/false);  
			break;
 
    case 355 : if (DEBUG) { System.out.println("JmlLoopAnnotations ::= JmlLoopVariantSeq JmlLabelopt"); }  //$NON-NLS-1$
		    /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/false, /*hasVariantSeq*/true);  
			break;
 
    case 356 : if (DEBUG) { System.out.println("JmlLoopAnnotations ::= JmlLoopInvariantSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/true, /*hasVariantSeq*/true);  
			break;
 
    case 357 : if (DEBUG) { System.out.println("JmlLabelopt ::="); }  //$NON-NLS-1$
		    /*jml*/consumeEmptyJmlLabel() ;  
			break;
 
    case 360 : if (DEBUG) { System.out.println("JmlLoopInvariantSeq ::= JmlLoopInvariantSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlLoopInvariantSeq();  
			break;
 
    case 362 : if (DEBUG) { System.out.println("JmlLoopVariantSeq ::= JmlLoopVariantSeq JmlLoopVariant"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlLoopVariantSeq();  
			break;
 
    case 363 : if (DEBUG) { System.out.println("JmlLoopInvariant ::= MaintainingKeyword Predicate..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause() ;  
			break;
 
    case 366 : if (DEBUG) { System.out.println("JmlLoopVariant ::= DecreasingKeyword Predicate..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause() ;  
			break;
 
    case 369 : if (DEBUG) { System.out.println("DoStatement ::= do Statement while LPAREN Expression..."); }  //$NON-NLS-1$
		    _this.consumeStatementDo() ;  
			break;
 
    case 370 : if (DEBUG) { System.out.println("DoStatement ::= JmlLoopAnnotations do Statement while..."); }  //$NON-NLS-1$
		    /*jml*/consumeStatementDoWithAnnotations() ;  
			break;
 
    case 371 : if (DEBUG) { System.out.println("ForStatement ::= for LPAREN ForInitopt SEMICOLON..."); }  //$NON-NLS-1$
		    _this.consumeStatementFor() ;  
			break;
 
    case 372 : if (DEBUG) { System.out.println("ForStatement ::= JmlLoopAnnotations for LPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeStatementForWithAnnotations() ;  
			break;
 
    case 373 : if (DEBUG) { System.out.println("ForStatementNoShortIf ::= for LPAREN ForInitopt..."); }  //$NON-NLS-1$
		    _this.consumeStatementFor() ;  
			break;
 
    case 374 : if (DEBUG) { System.out.println("ForStatementNoShortIf ::= JmlLoopAnnotations for LPAREN"); }  //$NON-NLS-1$
		    /*jml*/consumeStatementForWithAnnotations() ;  
			break;
 
    case 375 : if (DEBUG) { System.out.println("ForInit ::= StatementExpressionList"); }  //$NON-NLS-1$
		    _this.consumeForInit() ;  
			break;
 
    case 379 : if (DEBUG) { System.out.println("StatementExpressionList ::= StatementExpressionList..."); }  //$NON-NLS-1$
		    _this.consumeStatementExpressionList() ;  
			break;
 
    case 380 : if (DEBUG) { System.out.println("AssertStatement ::= assert Expression SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeSimpleAssertStatement() ;  
			break;
 
    case 381 : if (DEBUG) { System.out.println("AssertStatement ::= assert Expression COLON Expression"); }  //$NON-NLS-1$
		    _this.consumeAssertStatement() ;  
			break;
 
    case 382 : if (DEBUG) { System.out.println("JmlAssertStatement ::= jml_assert Predicate..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSimpleAssertStatement() ;  
			break;
 
    case 383 : if (DEBUG) { System.out.println("JmlAssertStatement ::= jml_assert Predicate COLON..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlAssertStatement() ;  
			break;
 
    case 384 : if (DEBUG) { System.out.println("JmlAssumeStatement ::= assume Predicate ExitJmlClause..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSimpleAssumeStatement() ;  
			break;
 
    case 385 : if (DEBUG) { System.out.println("JmlAssumeStatement ::= assume Predicate COLON Expression"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlAssumeStatement() ;  
			break;
 
    case 386 : if (DEBUG) { System.out.println("BreakStatement ::= break SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementBreak() ;  
			break;
 
    case 387 : if (DEBUG) { System.out.println("BreakStatement ::= break Identifier SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementBreakWithLabel() ;  
			break;
 
    case 388 : if (DEBUG) { System.out.println("ContinueStatement ::= continue SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementContinue() ;  
			break;
 
    case 389 : if (DEBUG) { System.out.println("ContinueStatement ::= continue Identifier SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementContinueWithLabel() ;  
			break;
 
    case 390 : if (DEBUG) { System.out.println("ReturnStatement ::= return Expressionopt SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementReturn() ;  
			break;
 
    case 391 : if (DEBUG) { System.out.println("ThrowStatement ::= throw Expression SEMICOLON"); }  //$NON-NLS-1$
		    _this.consumeStatementThrow();  
			break;
 
    case 392 : if (DEBUG) { System.out.println("SynchronizedStatement ::= OnlySynchronized LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementSynchronized();  
			break;
 
    case 393 : if (DEBUG) { System.out.println("OnlySynchronized ::= synchronized"); }  //$NON-NLS-1$
		    _this.consumeOnlySynchronized();  
			break;
 
    case 394 : if (DEBUG) { System.out.println("TryStatement ::= try TryBlock Catches"); }  //$NON-NLS-1$
		    _this.consumeStatementTry(false);  
			break;
 
    case 395 : if (DEBUG) { System.out.println("TryStatement ::= try TryBlock Catchesopt Finally"); }  //$NON-NLS-1$
		    _this.consumeStatementTry(true);  
			break;
 
    case 397 : if (DEBUG) { System.out.println("ExitTryBlock ::="); }  //$NON-NLS-1$
		    _this.consumeExitTryBlock();  
			break;
 
    case 399 : if (DEBUG) { System.out.println("Catches ::= Catches CatchClause"); }  //$NON-NLS-1$
		    _this.consumeCatches();  
			break;
 
    case 400 : if (DEBUG) { System.out.println("CatchClause ::= catch LPAREN FormalParameter RPAREN..."); }  //$NON-NLS-1$
		    _this.consumeStatementCatch() ;  
			break;
 
    case 402 : if (DEBUG) { System.out.println("PushLPAREN ::= LPAREN"); }  //$NON-NLS-1$
		    _this.consumeLeftParen();  
			break;
 
    case 403 : if (DEBUG) { System.out.println("PushRPAREN ::= RPAREN"); }  //$NON-NLS-1$
		    _this.consumeRightParen();  
			break;
 
    case 408 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= this"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayThis();  
			break;
 
    case 409 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= PushLPAREN Expression_NotName..."); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArray();  
			break;
 
    case 410 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= PushLPAREN Name PushRPAREN"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayWithName();  
			break;
 
    case 413 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= Name DOT this"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayNameThis();  
			break;
 
    case 414 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= Name DOT super"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayNameSuper();  
			break;
 
    case 415 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= Name DOT class"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayName();  
			break;
 
    case 416 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= Name Dims DOT class"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayArrayType();  
			break;
 
    case 417 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= PrimitiveType Dims DOT class"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayPrimitiveArrayType();  
			break;
 
    case 418 : if (DEBUG) { System.out.println("PrimaryNoNewArray ::= PrimitiveType DOT class"); }  //$NON-NLS-1$
		    _this.consumePrimaryNoNewArrayPrimitiveType();  
			break;
 
    case 422 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::= new ClassType..."); }  //$NON-NLS-1$
		    /*jml*/consumeClassInstanceCreationExpressionWithSetComprehension();  
			break;
 
    case 423 : if (DEBUG) { System.out.println("AllocationHeader ::= new ClassType LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeAllocationHeader();  
			break;
 
    case 424 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::= new..."); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionWithTypeArguments();  
			break;
 
    case 425 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::= new ClassType LPAREN"); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpression();  
			break;
 
    case 426 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::= Primary DOT new..."); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionQualifiedWithTypeArguments() ;  
			break;
 
    case 427 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::= Primary DOT new..."); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionQualified() ;  
			break;
 
    case 428 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::=..."); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionQualified() ;  
			break;
 
    case 429 : if (DEBUG) { System.out.println("ClassInstanceCreationExpression ::=..."); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionQualifiedWithTypeArguments() ;  
			break;
 
    case 430 : if (DEBUG) { System.out.println("ClassInstanceCreationExpressionName ::= Name DOT"); }  //$NON-NLS-1$
		    _this.consumeClassInstanceCreationExpressionName() ;  
			break;
 
    case 431 : if (DEBUG) { System.out.println("ClassBodyopt ::="); }  //$NON-NLS-1$
		    _this.consumeClassBodyopt();  
			break;
 
    case 433 : if (DEBUG) { System.out.println("EnterAnonymousClassBody ::="); }  //$NON-NLS-1$
		    _this.consumeEnterAnonymousClassBody();  
			break;
 
    case 435 : if (DEBUG) { System.out.println("ArgumentList ::= ArgumentList COMMA Expression"); }  //$NON-NLS-1$
		    _this.consumeArgumentList();  
			break;
 
    case 436 : if (DEBUG) { System.out.println("ArrayCreationHeader ::= new PrimitiveType..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationHeader();  
			break;
 
    case 437 : if (DEBUG) { System.out.println("ArrayCreationHeader ::= new ClassOrInterfaceType..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationHeader();  
			break;
 
    case 438 : if (DEBUG) { System.out.println("ArrayCreationWithoutArrayInitializer ::= new..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationExpressionWithoutInitializer();  
			break;
 
    case 439 : if (DEBUG) { System.out.println("ArrayCreationWithArrayInitializer ::= new PrimitiveType"); }  //$NON-NLS-1$
		    _this.consumeArrayCreationExpressionWithInitializer();  
			break;
 
    case 440 : if (DEBUG) { System.out.println("ArrayCreationWithoutArrayInitializer ::= new..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationExpressionWithoutInitializer();  
			break;
 
    case 441 : if (DEBUG) { System.out.println("ArrayCreationWithArrayInitializer ::= new..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationExpressionWithInitializer();  
			break;
 
    case 442 : if (DEBUG) { System.out.println("ArrayCreationWithArrayInitializer ::= new..."); }  //$NON-NLS-1$
		    _this.consumeArrayCreationExpressionWithInitializer();  
			break;
 
    case 444 : if (DEBUG) { System.out.println("DimWithOrWithOutExprs ::= DimWithOrWithOutExprs..."); }  //$NON-NLS-1$
		    _this.consumeDimWithOrWithOutExprs();  
			break;
 
     case 446 : if (DEBUG) { System.out.println("DimWithOrWithOutExpr ::= LBRACKET RBRACKET"); }  //$NON-NLS-1$
		    _this.consumeDimWithOrWithOutExpr();  
			break;
 
     case 447 : if (DEBUG) { System.out.println("Dims ::= DimsLoop"); }  //$NON-NLS-1$
		    _this.consumeDims();  
			break;
 
     case 449 : if (DEBUG) { System.out.println("DimsLoop ::= DimsLoop OneDimLoop"); }  //$NON-NLS-1$
		    /*jml*/consumeDimLoop();  
			break;
 
     case 450 : if (DEBUG) { System.out.println("OneDimLoop ::= LBRACKET RBRACKET"); }  //$NON-NLS-1$
		    _this.consumeOneDimLoop();  
			break;
 
     case 451 : if (DEBUG) { System.out.println("OneDimLoop ::= LBRACKET NullityModifier RBRACKET"); }  //$NON-NLS-1$
		    /*jml*/consumeOneDimLoopWithNullity();  
			break;
 
    case 452 : if (DEBUG) { System.out.println("FieldAccess ::= Primary DOT Identifier"); }  //$NON-NLS-1$
		    _this.consumeFieldAccess(false);  
			break;
 
    case 453 : if (DEBUG) { System.out.println("FieldAccess ::= super DOT Identifier"); }  //$NON-NLS-1$
		    _this.consumeFieldAccess(true);  
			break;
 
    case 454 : if (DEBUG) { System.out.println("MethodInvocation ::= Name LPAREN ArgumentListopt RPAREN"); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationName();  
			break;
 
    case 455 : if (DEBUG) { System.out.println("MethodInvocation ::= Name DOT OnlyTypeArguments..."); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationNameWithTypeArguments();  
			break;
 
    case 456 : if (DEBUG) { System.out.println("MethodInvocation ::= Primary DOT OnlyTypeArguments..."); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationPrimaryWithTypeArguments();  
			break;
 
    case 457 : if (DEBUG) { System.out.println("MethodInvocation ::= Primary DOT Identifier LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationPrimary();  
			break;
 
    case 458 : if (DEBUG) { System.out.println("MethodInvocation ::= super DOT OnlyTypeArguments..."); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationSuperWithTypeArguments();  
			break;
 
    case 459 : if (DEBUG) { System.out.println("MethodInvocation ::= super DOT Identifier LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeMethodInvocationSuper();  
			break;
 
    case 460 : if (DEBUG) { System.out.println("ArrayAccess ::= Name LBRACKET Expression RBRACKET"); }  //$NON-NLS-1$
		    _this.consumeArrayAccess(true);  
			break;
 
    case 461 : if (DEBUG) { System.out.println("ArrayAccess ::= PrimaryNoNewArray LBRACKET Expression..."); }  //$NON-NLS-1$
		    _this.consumeArrayAccess(false);  
			break;
 
    case 462 : if (DEBUG) { System.out.println("ArrayAccess ::= ArrayCreationWithArrayInitializer..."); }  //$NON-NLS-1$
		    _this.consumeArrayAccess(false);  
			break;
 
    case 464 : if (DEBUG) { System.out.println("PostfixExpression ::= Name"); }  //$NON-NLS-1$
		    _this.consumePostfixExpression();  
			break;
 
    case 467 : if (DEBUG) { System.out.println("PostIncrementExpression ::= PostfixExpression PLUS_PLUS"); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.PLUS,true);  
			break;
 
    case 468 : if (DEBUG) { System.out.println("PostDecrementExpression ::= PostfixExpression..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.MINUS,true);  
			break;
 
    case 469 : if (DEBUG) { System.out.println("PushPosition ::="); }  //$NON-NLS-1$
		    _this.consumePushPosition();  
			break;
 
    case 472 : if (DEBUG) { System.out.println("UnaryExpression ::= PLUS PushPosition UnaryExpression"); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.PLUS);  
			break;
 
    case 473 : if (DEBUG) { System.out.println("UnaryExpression ::= MINUS PushPosition UnaryExpression"); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.MINUS);  
			break;
 
    case 475 : if (DEBUG) { System.out.println("PreIncrementExpression ::= PLUS_PLUS PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.PLUS,false);  
			break;
 
    case 476 : if (DEBUG) { System.out.println("PreDecrementExpression ::= MINUS_MINUS PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.MINUS,false);  
			break;
 
    case 478 : if (DEBUG) { System.out.println("UnaryExpressionNotPlusMinus ::= TWIDDLE PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.TWIDDLE);  
			break;
 
    case 479 : if (DEBUG) { System.out.println("UnaryExpressionNotPlusMinus ::= NOT PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.NOT);  
			break;
 
    case 481 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN PrimitiveType Dimsopt..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithPrimitiveType();  
			break;
 
    case 482 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN Name..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithGenericsArray();  
			break;
 
    case 483 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN Name..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithQualifiedGenericsArray();  
			break;
 
    case 484 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN Name PushRPAREN..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionLL1();  
			break;
 
    case 485 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN Name Dims PushRPAREN..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithNameArray();  
			break;
 
    case 486 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null PrimitiveType..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithPrimitiveType();  
			break;
 
    case 487 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null Name..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithGenericsArray();  
			break;
 
    case 488 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null Name..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithQualifiedGenericsArray();  
			break;
 
    case 489 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null Name PushRPAREN"); }  //$NON-NLS-1$
		    _this.consumeCastExpressionLL1();  
			break;
 
    case 490 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null Name Dims..."); }  //$NON-NLS-1$
		    _this.consumeCastExpressionWithNameArray();  
			break;
 
    case 491 : if (DEBUG) { System.out.println("CastExpression ::= PushLPAREN non_null PushRPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeCastExpressionWithoutType();  
			break;
 
    case 492 : if (DEBUG) { System.out.println("OnlyTypeArgumentsForCastExpression ::= OnlyTypeArguments"); }  //$NON-NLS-1$
		    _this.consumeOnlyTypeArgumentsForCastExpression();  
			break;
 
    case 493 : if (DEBUG) { System.out.println("InsideCastExpression ::="); }  //$NON-NLS-1$
		    _this.consumeInsideCastExpression();  
			break;
 
    case 494 : if (DEBUG) { System.out.println("InsideCastExpressionLL1 ::="); }  //$NON-NLS-1$
		    _this.consumeInsideCastExpressionLL1();  
			break;
 
    case 495 : if (DEBUG) { System.out.println("InsideCastExpressionWithQualifiedGenerics ::="); }  //$NON-NLS-1$
		    _this.consumeInsideCastExpressionWithQualifiedGenerics();  
			break;
 
    case 497 : if (DEBUG) { System.out.println("MultiplicativeExpression ::= MultiplicativeExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.MULTIPLY);  
			break;
 
    case 498 : if (DEBUG) { System.out.println("MultiplicativeExpression ::= MultiplicativeExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.DIVIDE);  
			break;
 
    case 499 : if (DEBUG) { System.out.println("MultiplicativeExpression ::= MultiplicativeExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.REMAINDER);  
			break;
 
    case 501 : if (DEBUG) { System.out.println("AdditiveExpression ::= AdditiveExpression PLUS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.PLUS);  
			break;
 
    case 502 : if (DEBUG) { System.out.println("AdditiveExpression ::= AdditiveExpression MINUS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.MINUS);  
			break;
 
    case 504 : if (DEBUG) { System.out.println("ShiftExpression ::= ShiftExpression LEFT_SHIFT..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LEFT_SHIFT);  
			break;
 
    case 505 : if (DEBUG) { System.out.println("ShiftExpression ::= ShiftExpression RIGHT_SHIFT..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.RIGHT_SHIFT);  
			break;
 
    case 506 : if (DEBUG) { System.out.println("ShiftExpression ::= ShiftExpression UNSIGNED_RIGHT_SHIFT"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.UNSIGNED_RIGHT_SHIFT);  
			break;
 
    case 508 : if (DEBUG) { System.out.println("RelationalExpression ::= RelationalExpression LESS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LESS);  
			break;
 
    case 509 : if (DEBUG) { System.out.println("RelationalExpression ::= RelationalExpression GREATER..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.GREATER);  
			break;
 
    case 510 : if (DEBUG) { System.out.println("RelationalExpression ::= RelationalExpression LESS_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LESS_EQUAL);  
			break;
 
    case 511 : if (DEBUG) { System.out.println("RelationalExpression ::= RelationalExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.GREATER_EQUAL);  
			break;
 
    case 512 : if (DEBUG) { System.out.println("RelationalExpression ::= ShiftExpression SUBTYPE..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSubtypeExpression();  
			break;
 
    case 514 : if (DEBUG) { System.out.println("InstanceofExpression ::= InstanceofExpression instanceof"); }  //$NON-NLS-1$
		    _this.consumeInstanceOfExpression();  
			break;
 
    case 516 : if (DEBUG) { System.out.println("EqualityExpression ::= EqualityExpression EQUAL_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.EQUAL_EQUAL);  
			break;
 
    case 517 : if (DEBUG) { System.out.println("EqualityExpression ::= EqualityExpression NOT_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.NOT_EQUAL);  
			break;
 
    case 519 : if (DEBUG) { System.out.println("AndExpression ::= AndExpression AND EqualityExpression"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.AND);  
			break;
 
    case 521 : if (DEBUG) { System.out.println("ExclusiveOrExpression ::= ExclusiveOrExpression XOR..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.XOR);  
			break;
 
    case 523 : if (DEBUG) { System.out.println("InclusiveOrExpression ::= InclusiveOrExpression OR..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.OR);  
			break;
 
    case 525 : if (DEBUG) { System.out.println("ConditionalAndExpression ::= ConditionalAndExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.AND_AND);  
			break;
 
    case 527 : if (DEBUG) { System.out.println("ConditionalOrExpression ::= ConditionalOrExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.OR_OR);  
			break;
 
    case 529 : if (DEBUG) { System.out.println("ConditionalExpression ::= EquivalenceExpression QUESTION"); }  //$NON-NLS-1$
		    _this.consumeConditionalExpression(OperatorIds.QUESTIONCOLON) ;  
			break;
 
    case 531 : if (DEBUG) { System.out.println("EquivalenceExpression ::= EquivalenceExpression EQUIV..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.JML_EQUIV);  
			break;
 
    case 532 : if (DEBUG) { System.out.println("EquivalenceExpression ::= EquivalenceExpression..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.JML_NOT_EQUIV);  
			break;
 
    case 534 : if (DEBUG) { System.out.println("ImpliesExpression ::= ImpliesExpression REV_IMPLIES..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.JML_REV_IMPLIES) ;  
			break;
 
    case 535 : if (DEBUG) { System.out.println("ImpliesExpression ::= ConditionalOrExpression IMPLIES..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.JML_IMPLIES) ;  
			break;
 
    case 537 : if (DEBUG) { System.out.println("NotRevImpliesExpression ::= ConditionalOrExpression..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.JML_IMPLIES) ;  
			break;
 
    case 539 : if (DEBUG) { System.out.println("EquivalenceExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.JML_EQUIV);  
			break;
 
    case 540 : if (DEBUG) { System.out.println("EquivalenceExpression_NotName ::= Name EQUIV..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpressionWithName(OperatorIds.JML_EQUIV);  
			break;
 
    case 541 : if (DEBUG) { System.out.println("EquivalenceExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.JML_NOT_EQUIV);  
			break;
 
    case 542 : if (DEBUG) { System.out.println("EquivalenceExpression_NotName ::= Name NOT_EQUIV..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpressionWithName(OperatorIds.JML_NOT_EQUIV);  
			break;
 
    case 544 : if (DEBUG) { System.out.println("ImpliesExpression_NotName ::= ImpliesExpression_NotName"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.JML_REV_IMPLIES) ;  
			break;
 
    case 545 : if (DEBUG) { System.out.println("ImpliesExpression_NotName ::= Name REV_IMPLIES..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.JML_REV_IMPLIES) ;  
			break;
 
    case 546 : if (DEBUG) { System.out.println("ImpliesExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.JML_IMPLIES) ;  
			break;
 
    case 547 : if (DEBUG) { System.out.println("ImpliesExpression_NotName ::= Name IMPLIES..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.JML_IMPLIES) ;  
			break;
 
    case 550 : if (DEBUG) { System.out.println("Assignment ::= PostfixExpression AssignmentOperator..."); }  //$NON-NLS-1$
		    _this.consumeAssignment();  
			break;
 
    case 552 : if (DEBUG) { System.out.println("Assignment ::= InvalidArrayInitializerAssignement"); }  //$NON-NLS-1$
		    _this.ignoreExpressionAssignment(); 
			break;
 
    case 553 : if (DEBUG) { System.out.println("AssignmentOperator ::= EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(EQUAL);  
			break;
 
    case 554 : if (DEBUG) { System.out.println("AssignmentOperator ::= MULTIPLY_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(MULTIPLY);  
			break;
 
    case 555 : if (DEBUG) { System.out.println("AssignmentOperator ::= DIVIDE_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(DIVIDE);  
			break;
 
    case 556 : if (DEBUG) { System.out.println("AssignmentOperator ::= REMAINDER_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(REMAINDER);  
			break;
 
    case 557 : if (DEBUG) { System.out.println("AssignmentOperator ::= PLUS_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(PLUS);  
			break;
 
    case 558 : if (DEBUG) { System.out.println("AssignmentOperator ::= MINUS_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(MINUS);  
			break;
 
    case 559 : if (DEBUG) { System.out.println("AssignmentOperator ::= LEFT_SHIFT_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(LEFT_SHIFT);  
			break;
 
    case 560 : if (DEBUG) { System.out.println("AssignmentOperator ::= RIGHT_SHIFT_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(RIGHT_SHIFT);  
			break;
 
    case 561 : if (DEBUG) { System.out.println("AssignmentOperator ::= UNSIGNED_RIGHT_SHIFT_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(UNSIGNED_RIGHT_SHIFT);  
			break;
 
    case 562 : if (DEBUG) { System.out.println("AssignmentOperator ::= AND_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(AND);  
			break;
 
    case 563 : if (DEBUG) { System.out.println("AssignmentOperator ::= XOR_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(XOR);  
			break;
 
    case 564 : if (DEBUG) { System.out.println("AssignmentOperator ::= OR_EQUAL"); }  //$NON-NLS-1$
		    _this.consumeAssignmentOperator(OR);  
			break;
 
    case 568 : if (DEBUG) { System.out.println("Expressionopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyExpression();  
			break;
 
    case 573 : if (DEBUG) { System.out.println("ClassBodyDeclarationsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyClassBodyDeclarationsopt();  
			break;
 
    case 574 : if (DEBUG) { System.out.println("ClassBodyDeclarationsopt ::= NestedType..."); }  //$NON-NLS-1$
		    _this.consumeClassBodyDeclarationsopt();  
			break;
 
     case 575 : if (DEBUG) { System.out.println("Modifiersopt ::="); }  //$NON-NLS-1$
		    _this.consumeDefaultModifiers();  
			break;
 
    case 576 : if (DEBUG) { System.out.println("Modifiersopt ::= Modifiers"); }  //$NON-NLS-1$
		    _this.consumeModifiers();  
			break;
 
    case 577 : if (DEBUG) { System.out.println("BlockStatementsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyBlockStatementsopt();  
			break;
 
     case 579 : if (DEBUG) { System.out.println("Dimsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyDimsopt();  
			break;
 
     case 581 : if (DEBUG) { System.out.println("ArgumentListopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyArgumentListopt();  
			break;
 
    case 585 : if (DEBUG) { System.out.println("FormalParameterListopt ::="); }  //$NON-NLS-1$
		    _this.consumeFormalParameterListopt();  
			break;
 
     case 589 : if (DEBUG) { System.out.println("InterfaceMemberDeclarationsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyInterfaceMemberDeclarationsopt();  
			break;
 
     case 590 : if (DEBUG) { System.out.println("InterfaceMemberDeclarationsopt ::= NestedType..."); }  //$NON-NLS-1$
		    _this.consumeInterfaceMemberDeclarationsopt();  
			break;
 
    case 591 : if (DEBUG) { System.out.println("NestedType ::="); }  //$NON-NLS-1$
		    _this.consumeNestedType();  
			break;

     case 592 : if (DEBUG) { System.out.println("ForInitopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyForInitopt();  
			break;
 
     case 594 : if (DEBUG) { System.out.println("ForUpdateopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyForUpdateopt();  
			break;
 
     case 598 : if (DEBUG) { System.out.println("Catchesopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyCatchesopt();  
			break;
 
     case 600 : if (DEBUG) { System.out.println("EnumDeclaration ::= EnumHeader EnumBody"); }  //$NON-NLS-1$
		    _this.consumeEnumDeclaration();  
			break;
 
     case 601 : if (DEBUG) { System.out.println("EnumHeader ::= EnumHeaderName ClassHeaderImplementsopt"); }  //$NON-NLS-1$
		    _this.consumeEnumHeader();  
			break;
 
     case 602 : if (DEBUG) { System.out.println("EnumHeaderName ::= Modifiersopt enum Identifier"); }  //$NON-NLS-1$
		    _this.consumeEnumHeaderName();  
			break;
 
     case 603 : if (DEBUG) { System.out.println("EnumHeaderName ::= Modifiersopt enum Identifier..."); }  //$NON-NLS-1$
		    _this.consumeEnumHeaderNameWithTypeParameters();  
			break;
 
     case 604 : if (DEBUG) { System.out.println("EnumBody ::= LBRACE EnumBodyDeclarationsopt RBRACE"); }  //$NON-NLS-1$
		    _this.consumeEnumBodyNoConstants();  
			break;
 
     case 605 : if (DEBUG) { System.out.println("EnumBody ::= LBRACE COMMA EnumBodyDeclarationsopt..."); }  //$NON-NLS-1$
		    _this.consumeEnumBodyNoConstants();  
			break;
 
     case 606 : if (DEBUG) { System.out.println("EnumBody ::= LBRACE EnumConstants COMMA..."); }  //$NON-NLS-1$
		    _this.consumeEnumBodyWithConstants();  
			break;
 
     case 607 : if (DEBUG) { System.out.println("EnumBody ::= LBRACE EnumConstants..."); }  //$NON-NLS-1$
		    _this.consumeEnumBodyWithConstants();  
			break;
 
    case 609 : if (DEBUG) { System.out.println("EnumConstants ::= EnumConstants COMMA EnumConstant"); }  //$NON-NLS-1$
		    _this.consumeEnumConstants();  
			break;
 
    case 610 : if (DEBUG) { System.out.println("EnumConstantHeaderName ::= Modifiersopt Identifier"); }  //$NON-NLS-1$
		    _this.consumeEnumConstantHeaderName();  
			break;
 
    case 611 : if (DEBUG) { System.out.println("EnumConstantHeader ::= EnumConstantHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeEnumConstantHeader();  
			break;
 
    case 612 : if (DEBUG) { System.out.println("EnumConstant ::= EnumConstantHeader ForceNoDiet..."); }  //$NON-NLS-1$
		    _this.consumeEnumConstantWithClassBody();  
			break;
 
    case 613 : if (DEBUG) { System.out.println("EnumConstant ::= EnumConstantHeader"); }  //$NON-NLS-1$
		    _this.consumeEnumConstantNoClassBody();  
			break;
 
    case 614 : if (DEBUG) { System.out.println("Arguments ::= LPAREN ArgumentListopt RPAREN"); }  //$NON-NLS-1$
		    _this.consumeArguments();  
			break;
 
    case 615 : if (DEBUG) { System.out.println("Argumentsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyArguments();  
			break;
 
    case 617 : if (DEBUG) { System.out.println("EnumDeclarations ::= SEMICOLON ClassBodyDeclarationsopt"); }  //$NON-NLS-1$
		    _this.consumeEnumDeclarations();  
			break;
 
    case 618 : if (DEBUG) { System.out.println("EnumBodyDeclarationsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyEnumDeclarations();  
			break;
 
    case 620 : if (DEBUG) { System.out.println("EnhancedForStatement ::= EnhancedForStatementHeader..."); }  //$NON-NLS-1$
		    _this.consumeEnhancedForStatement();  
			break;
 
    case 621 : if (DEBUG) { System.out.println("EnhancedForStatementNoShortIf ::=..."); }  //$NON-NLS-1$
		    _this.consumeEnhancedForStatement();  
			break;
 
    case 622 : if (DEBUG) { System.out.println("EnhancedForStatementHeaderInit ::= for LPAREN Type..."); }  //$NON-NLS-1$
		    _this.consumeEnhancedForStatementHeaderInit(false);  
			break;
 
    case 623 : if (DEBUG) { System.out.println("EnhancedForStatementHeaderInit ::= for LPAREN Modifiers"); }  //$NON-NLS-1$
		    _this.consumeEnhancedForStatementHeaderInit(true);  
			break;
 
    case 624 : if (DEBUG) { System.out.println("EnhancedForStatementHeader ::=..."); }  //$NON-NLS-1$
		    _this.consumeEnhancedForStatementHeader();  
			break;
 
    case 625 : if (DEBUG) { System.out.println("SingleStaticImportDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeImportDeclaration();  
			break;
 
    case 626 : if (DEBUG) { System.out.println("SingleStaticImportDeclarationName ::= import static Name"); }  //$NON-NLS-1$
		    _this.consumeSingleStaticImportDeclarationName();  
			break;
 
    case 627 : if (DEBUG) { System.out.println("StaticImportOnDemandDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeImportDeclaration();  
			break;
 
    case 628 : if (DEBUG) { System.out.println("StaticImportOnDemandDeclarationName ::= import static..."); }  //$NON-NLS-1$
		    _this.consumeStaticImportOnDemandDeclarationName();  
			break;
 
    case 629 : if (DEBUG) { System.out.println("TypeArguments ::= LESS TypeArgumentList1"); }  //$NON-NLS-1$
		    _this.consumeTypeArguments();  
			break;
 
    case 630 : if (DEBUG) { System.out.println("OnlyTypeArguments ::= LESS TypeArgumentList1"); }  //$NON-NLS-1$
		    _this.consumeOnlyTypeArguments();  
			break;
 
    case 632 : if (DEBUG) { System.out.println("TypeArgumentList1 ::= TypeArgumentList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentList1();  
			break;
 
    case 634 : if (DEBUG) { System.out.println("TypeArgumentList ::= TypeArgumentList COMMA TypeArgument"); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentList();  
			break;
 
    case 635 : if (DEBUG) { System.out.println("TypeArgument ::= ReferenceType"); }  //$NON-NLS-1$
		    _this.consumeTypeArgument();  
			break;
 
    case 639 : if (DEBUG) { System.out.println("ReferenceType1 ::= ReferenceType GREATER"); }  //$NON-NLS-1$
		    _this.consumeReferenceType1();  
			break;
 
    case 640 : if (DEBUG) { System.out.println("ReferenceType1 ::= ClassOrInterface LESS..."); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentReferenceType1();  
			break;
 
    case 642 : if (DEBUG) { System.out.println("TypeArgumentList2 ::= TypeArgumentList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentList2();  
			break;
 
    case 645 : if (DEBUG) { System.out.println("ReferenceType2 ::= ReferenceType RIGHT_SHIFT"); }  //$NON-NLS-1$
		    _this.consumeReferenceType2();  
			break;
 
    case 646 : if (DEBUG) { System.out.println("ReferenceType2 ::= ClassOrInterface LESS..."); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentReferenceType2();  
			break;
 
    case 648 : if (DEBUG) { System.out.println("TypeArgumentList3 ::= TypeArgumentList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeTypeArgumentList3();  
			break;
 
    case 651 : if (DEBUG) { System.out.println("ReferenceType3 ::= ReferenceType UNSIGNED_RIGHT_SHIFT"); }  //$NON-NLS-1$
		    _this.consumeReferenceType3();  
			break;
 
    case 652 : if (DEBUG) { System.out.println("Wildcard ::= QUESTION"); }  //$NON-NLS-1$
		    _this.consumeWildcard();  
			break;
 
    case 653 : if (DEBUG) { System.out.println("Wildcard ::= QUESTION WildcardBounds"); }  //$NON-NLS-1$
		    _this.consumeWildcardWithBounds();  
			break;
 
    case 654 : if (DEBUG) { System.out.println("WildcardBounds ::= extends ReferenceType"); }  //$NON-NLS-1$
		    _this.consumeWildcardBoundsExtends();  
			break;
 
    case 655 : if (DEBUG) { System.out.println("WildcardBounds ::= super ReferenceType"); }  //$NON-NLS-1$
		    _this.consumeWildcardBoundsSuper();  
			break;
 
    case 656 : if (DEBUG) { System.out.println("Wildcard1 ::= QUESTION GREATER"); }  //$NON-NLS-1$
		    _this.consumeWildcard1();  
			break;
 
    case 657 : if (DEBUG) { System.out.println("Wildcard1 ::= QUESTION WildcardBounds1"); }  //$NON-NLS-1$
		    _this.consumeWildcard1WithBounds();  
			break;
 
    case 658 : if (DEBUG) { System.out.println("WildcardBounds1 ::= extends ReferenceType1"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds1Extends();  
			break;
 
    case 659 : if (DEBUG) { System.out.println("WildcardBounds1 ::= super ReferenceType1"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds1Super();  
			break;
 
    case 660 : if (DEBUG) { System.out.println("Wildcard2 ::= QUESTION RIGHT_SHIFT"); }  //$NON-NLS-1$
		    _this.consumeWildcard2();  
			break;
 
    case 661 : if (DEBUG) { System.out.println("Wildcard2 ::= QUESTION WildcardBounds2"); }  //$NON-NLS-1$
		    _this.consumeWildcard2WithBounds();  
			break;
 
    case 662 : if (DEBUG) { System.out.println("WildcardBounds2 ::= extends ReferenceType2"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds2Extends();  
			break;
 
    case 663 : if (DEBUG) { System.out.println("WildcardBounds2 ::= super ReferenceType2"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds2Super();  
			break;
 
    case 664 : if (DEBUG) { System.out.println("Wildcard3 ::= QUESTION UNSIGNED_RIGHT_SHIFT"); }  //$NON-NLS-1$
		    _this.consumeWildcard3();  
			break;
 
    case 665 : if (DEBUG) { System.out.println("Wildcard3 ::= QUESTION WildcardBounds3"); }  //$NON-NLS-1$
		    _this.consumeWildcard3WithBounds();  
			break;
 
    case 666 : if (DEBUG) { System.out.println("WildcardBounds3 ::= extends ReferenceType3"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds3Extends();  
			break;
 
    case 667 : if (DEBUG) { System.out.println("WildcardBounds3 ::= super ReferenceType3"); }  //$NON-NLS-1$
		    _this.consumeWildcardBounds3Super();  
			break;
 
    case 668 : if (DEBUG) { System.out.println("TypeParameterHeader ::= Identifier"); }  //$NON-NLS-1$
		    _this.consumeTypeParameterHeader();  
			break;
 
    case 669 : if (DEBUG) { System.out.println("TypeParameters ::= LESS TypeParameterList1"); }  //$NON-NLS-1$
		    _this.consumeTypeParameters();  
			break;
 
    case 671 : if (DEBUG) { System.out.println("TypeParameterList ::= TypeParameterList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameterList();  
			break;
 
    case 673 : if (DEBUG) { System.out.println("TypeParameter ::= TypeParameterHeader extends..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameterWithExtends();  
			break;
 
    case 674 : if (DEBUG) { System.out.println("TypeParameter ::= TypeParameterHeader extends..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameterWithExtendsAndBounds();  
			break;
 
    case 676 : if (DEBUG) { System.out.println("AdditionalBoundList ::= AdditionalBoundList..."); }  //$NON-NLS-1$
		    _this.consumeAdditionalBoundList();  
			break;
 
    case 677 : if (DEBUG) { System.out.println("AdditionalBound ::= AND ReferenceType"); }  //$NON-NLS-1$
		    _this.consumeAdditionalBound();  
			break;
 
    case 679 : if (DEBUG) { System.out.println("TypeParameterList1 ::= TypeParameterList COMMA..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameterList1();  
			break;
 
    case 680 : if (DEBUG) { System.out.println("TypeParameter1 ::= TypeParameterHeader GREATER"); }  //$NON-NLS-1$
		    _this.consumeTypeParameter1();  
			break;
 
    case 681 : if (DEBUG) { System.out.println("TypeParameter1 ::= TypeParameterHeader extends..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameter1WithExtends();  
			break;
 
    case 682 : if (DEBUG) { System.out.println("TypeParameter1 ::= TypeParameterHeader extends..."); }  //$NON-NLS-1$
		    _this.consumeTypeParameter1WithExtendsAndBounds();  
			break;
 
    case 684 : if (DEBUG) { System.out.println("AdditionalBoundList1 ::= AdditionalBoundList..."); }  //$NON-NLS-1$
		    _this.consumeAdditionalBoundList1();  
			break;
 
    case 685 : if (DEBUG) { System.out.println("AdditionalBound1 ::= AND ReferenceType1"); }  //$NON-NLS-1$
		    _this.consumeAdditionalBound1();  
			break;
 
    case 691 : if (DEBUG) { System.out.println("UnaryExpression_NotName ::= PLUS PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.PLUS);  
			break;
 
    case 692 : if (DEBUG) { System.out.println("UnaryExpression_NotName ::= MINUS PushPosition..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.MINUS);  
			break;
 
    case 695 : if (DEBUG) { System.out.println("UnaryExpressionNotPlusMinus_NotName ::= TWIDDLE..."); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.TWIDDLE);  
			break;
 
    case 696 : if (DEBUG) { System.out.println("UnaryExpressionNotPlusMinus_NotName ::= NOT PushPosition"); }  //$NON-NLS-1$
		    _this.consumeUnaryExpression(OperatorIds.NOT);  
			break;
 
    case 699 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.MULTIPLY);  
			break;
 
    case 700 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::= Name MULTIPLY..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.MULTIPLY);  
			break;
 
    case 701 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.DIVIDE);  
			break;
 
    case 702 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::= Name DIVIDE..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.DIVIDE);  
			break;
 
    case 703 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.REMAINDER);  
			break;
 
    case 704 : if (DEBUG) { System.out.println("MultiplicativeExpression_NotName ::= Name REMAINDER..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.REMAINDER);  
			break;
 
    case 706 : if (DEBUG) { System.out.println("AdditiveExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.PLUS);  
			break;
 
    case 707 : if (DEBUG) { System.out.println("AdditiveExpression_NotName ::= Name PLUS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.PLUS);  
			break;
 
    case 708 : if (DEBUG) { System.out.println("AdditiveExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.MINUS);  
			break;
 
    case 709 : if (DEBUG) { System.out.println("AdditiveExpression_NotName ::= Name MINUS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.MINUS);  
			break;
 
    case 711 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= ShiftExpression_NotName..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LEFT_SHIFT);  
			break;
 
    case 712 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= Name LEFT_SHIFT..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.LEFT_SHIFT);  
			break;
 
    case 713 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= ShiftExpression_NotName..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.RIGHT_SHIFT);  
			break;
 
    case 714 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= Name RIGHT_SHIFT..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.RIGHT_SHIFT);  
			break;
 
    case 715 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= ShiftExpression_NotName..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.UNSIGNED_RIGHT_SHIFT);  
			break;
 
    case 716 : if (DEBUG) { System.out.println("ShiftExpression_NotName ::= Name UNSIGNED_RIGHT_SHIFT..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.UNSIGNED_RIGHT_SHIFT);  
			break;
 
    case 718 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= ShiftExpression_NotName"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LESS);  
			break;
 
    case 719 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= Name LESS..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.LESS);  
			break;
 
    case 720 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= ShiftExpression_NotName"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.GREATER);  
			break;
 
    case 721 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= Name GREATER..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.GREATER);  
			break;
 
    case 722 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.LESS_EQUAL);  
			break;
 
    case 723 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= Name LESS_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.LESS_EQUAL);  
			break;
 
    case 724 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.GREATER_EQUAL);  
			break;
 
    case 725 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= Name GREATER_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.GREATER_EQUAL);  
			break;
 
    case 726 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::= Name SUBTYPE..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSubtypeExpression();  
			break;
 
    case 727 : if (DEBUG) { System.out.println("RelationalExpression_NotName ::=..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSubtypeExpression();  
			break;
 
    case 729 : if (DEBUG) { System.out.println("InstanceofExpression_NotName ::= Name instanceof..."); }  //$NON-NLS-1$
		    _this.consumeInstanceOfExpressionWithName();  
			break;
 
    case 730 : if (DEBUG) { System.out.println("InstanceofExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeInstanceOfExpression();  
			break;
 
    case 732 : if (DEBUG) { System.out.println("EqualityExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.EQUAL_EQUAL);  
			break;
 
    case 733 : if (DEBUG) { System.out.println("EqualityExpression_NotName ::= Name EQUAL_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpressionWithName(OperatorIds.EQUAL_EQUAL);  
			break;
 
    case 734 : if (DEBUG) { System.out.println("EqualityExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpression(OperatorIds.NOT_EQUAL);  
			break;
 
    case 735 : if (DEBUG) { System.out.println("EqualityExpression_NotName ::= Name NOT_EQUAL..."); }  //$NON-NLS-1$
		    _this.consumeEqualityExpressionWithName(OperatorIds.NOT_EQUAL);  
			break;
 
    case 737 : if (DEBUG) { System.out.println("AndExpression_NotName ::= AndExpression_NotName AND..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.AND);  
			break;
 
    case 738 : if (DEBUG) { System.out.println("AndExpression_NotName ::= Name AND EqualityExpression"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.AND);  
			break;
 
    case 740 : if (DEBUG) { System.out.println("ExclusiveOrExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.XOR);  
			break;
 
    case 741 : if (DEBUG) { System.out.println("ExclusiveOrExpression_NotName ::= Name XOR AndExpression"); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.XOR);  
			break;
 
    case 743 : if (DEBUG) { System.out.println("InclusiveOrExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.OR);  
			break;
 
    case 744 : if (DEBUG) { System.out.println("InclusiveOrExpression_NotName ::= Name OR..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.OR);  
			break;
 
    case 746 : if (DEBUG) { System.out.println("ConditionalAndExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.AND_AND);  
			break;
 
    case 747 : if (DEBUG) { System.out.println("ConditionalAndExpression_NotName ::= Name AND_AND..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.AND_AND);  
			break;
 
    case 749 : if (DEBUG) { System.out.println("ConditionalOrExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpression(OperatorIds.OR_OR);  
			break;
 
    case 750 : if (DEBUG) { System.out.println("ConditionalOrExpression_NotName ::= Name OR_OR..."); }  //$NON-NLS-1$
		    _this.consumeBinaryExpressionWithName(OperatorIds.OR_OR);  
			break;
 
    case 752 : if (DEBUG) { System.out.println("ConditionalExpression_NotName ::=..."); }  //$NON-NLS-1$
		    _this.consumeConditionalExpression(OperatorIds.QUESTIONCOLON) ;  
			break;
 
    case 753 : if (DEBUG) { System.out.println("ConditionalExpression_NotName ::= Name QUESTION..."); }  //$NON-NLS-1$
		    _this.consumeConditionalExpressionWithName(OperatorIds.QUESTIONCOLON) ;  
			break;
 
    case 757 : if (DEBUG) { System.out.println("AnnotationTypeDeclarationHeaderName ::= Modifiers AT..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclarationHeaderName() ;  
			break;
 
    case 758 : if (DEBUG) { System.out.println("AnnotationTypeDeclarationHeaderName ::= Modifiers AT..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclarationHeaderNameWithTypeParameters() ;  
			break;
 
    case 759 : if (DEBUG) { System.out.println("AnnotationTypeDeclarationHeaderName ::= AT..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclarationHeaderNameWithTypeParameters() ;  
			break;
 
    case 760 : if (DEBUG) { System.out.println("AnnotationTypeDeclarationHeaderName ::= AT..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclarationHeaderName() ;  
			break;
 
    case 761 : if (DEBUG) { System.out.println("AnnotationTypeDeclarationHeader ::=..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclarationHeader() ;  
			break;
 
    case 762 : if (DEBUG) { System.out.println("AnnotationTypeDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeDeclaration() ;  
			break;
 
    case 764 : if (DEBUG) { System.out.println("AnnotationTypeMemberDeclarationsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyAnnotationTypeMemberDeclarationsopt() ;  
			break;
 
    case 765 : if (DEBUG) { System.out.println("AnnotationTypeMemberDeclarationsopt ::= NestedType..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeMemberDeclarationsopt() ;  
			break;
 
    case 767 : if (DEBUG) { System.out.println("AnnotationTypeMemberDeclarations ::=..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeMemberDeclarations() ;  
			break;
 
    case 768 : if (DEBUG) { System.out.println("AnnotationMethodHeaderName ::= Modifiersopt..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderNameWithTypeParameters(true);  
			break;
 
    case 769 : if (DEBUG) { System.out.println("AnnotationMethodHeaderName ::= Modifiersopt Type..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderName(true);  
			break;
 
    case 770 : if (DEBUG) { System.out.println("AnnotationMethodHeaderDefaultValueopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyMethodHeaderDefaultValue() ;  
			break;
 
    case 771 : if (DEBUG) { System.out.println("AnnotationMethodHeaderDefaultValueopt ::= DefaultValue"); }  //$NON-NLS-1$
		    _this.consumeMethodHeaderDefaultValue();  
			break;
 
    case 772 : if (DEBUG) { System.out.println("AnnotationMethodHeader ::= AnnotationMethodHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeader();  
			break;
 
    case 773 : if (DEBUG) { System.out.println("AnnotationTypeMemberDeclaration ::=..."); }  //$NON-NLS-1$
		    _this.consumeAnnotationTypeMemberDeclaration() ;  
			break;
 
    case 781 : if (DEBUG) { System.out.println("AnnotationName ::= AT Name"); }  //$NON-NLS-1$
		    _this.consumeAnnotationName() ;  
			break;
 
    case 782 : if (DEBUG) { System.out.println("NormalAnnotation ::= AnnotationName LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeNormalAnnotation() ;  
			break;
 
    case 783 : if (DEBUG) { System.out.println("MemberValuePairsopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyMemberValuePairsopt() ;  
			break;
 
    case 786 : if (DEBUG) { System.out.println("MemberValuePairs ::= MemberValuePairs COMMA..."); }  //$NON-NLS-1$
		    _this.consumeMemberValuePairs() ;  
			break;
 
    case 787 : if (DEBUG) { System.out.println("MemberValuePair ::= SimpleName EQUAL EnterMemberValue..."); }  //$NON-NLS-1$
		    _this.consumeMemberValuePair() ;  
			break;
 
    case 788 : if (DEBUG) { System.out.println("EnterMemberValue ::="); }  //$NON-NLS-1$
		    _this.consumeEnterMemberValue() ;  
			break;
 
    case 789 : if (DEBUG) { System.out.println("ExitMemberValue ::="); }  //$NON-NLS-1$
		    _this.consumeExitMemberValue() ;  
			break;
 
    case 791 : if (DEBUG) { System.out.println("MemberValue ::= Name"); }  //$NON-NLS-1$
		    _this.consumeMemberValueAsName() ;  
			break;
 
    case 794 : if (DEBUG) { System.out.println("MemberValueArrayInitializer ::=..."); }  //$NON-NLS-1$
		    _this.consumeMemberValueArrayInitializer() ;  
			break;
 
    case 795 : if (DEBUG) { System.out.println("MemberValueArrayInitializer ::=..."); }  //$NON-NLS-1$
		    _this.consumeMemberValueArrayInitializer() ;  
			break;
 
    case 796 : if (DEBUG) { System.out.println("MemberValueArrayInitializer ::=..."); }  //$NON-NLS-1$
		    _this.consumeEmptyMemberValueArrayInitializer() ;  
			break;
 
    case 797 : if (DEBUG) { System.out.println("MemberValueArrayInitializer ::=..."); }  //$NON-NLS-1$
		    _this.consumeEmptyMemberValueArrayInitializer() ;  
			break;
 
    case 798 : if (DEBUG) { System.out.println("EnterMemberValueArrayInitializer ::="); }  //$NON-NLS-1$
		    _this.consumeEnterMemberValueArrayInitializer() ;  
			break;
 
    case 800 : if (DEBUG) { System.out.println("MemberValues ::= MemberValues COMMA MemberValue"); }  //$NON-NLS-1$
		    _this.consumeMemberValues() ;  
			break;
 
    case 801 : if (DEBUG) { System.out.println("MarkerAnnotation ::= AnnotationName"); }  //$NON-NLS-1$
		    _this.consumeMarkerAnnotation() ;  
			break;
 
    case 802 : if (DEBUG) { System.out.println("SingleMemberAnnotationMemberValue ::= MemberValue"); }  //$NON-NLS-1$
		    _this.consumeSingleMemberAnnotationMemberValue() ;  
			break;
 
    case 803 : if (DEBUG) { System.out.println("SingleMemberAnnotation ::= AnnotationName LPAREN..."); }  //$NON-NLS-1$
		    _this.consumeSingleMemberAnnotation() ;  
			break;
 
    case 806 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_elemtype LPAREN SpecExpression..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlElemtypeExpression(OperatorIds.JML_ELEMTYPE);  
			break;
 
    case 807 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_fresh LPAREN ArgumentList RPAREN"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlFreshExpression();  
			break;
 
    case 809 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_nonnullelements LPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NONNULLELEMENTS);  
			break;
 
    case 812 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_result"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlPrimaryResult();  
			break;
 
    case 813 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_type LPAREN Type RPAREN"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeExpression(OperatorIds.JML_TYPE);  
			break;
 
    case 814 : if (DEBUG) { System.out.println("JmlPrimary ::= slash_typeof LPAREN SpecExpression RPAREN"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeofExpression(OperatorIds.JML_TYPEOF);  
			break;
 
    case 817 : if (DEBUG) { System.out.println("JmlOperationOverStoreRefs ::= slash_not_assigned..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NOT_ASSIGNED);  
			break;
 
    case 818 : if (DEBUG) { System.out.println("JmlOperationOverStoreRefs ::= slash_not_modified..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NOT_MODIFIED);  
			break;
 
    case 819 : if (DEBUG) { System.out.println("JmlStoreRefListAsUnaryArgument ::= LPAREN StoreRefSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlStoreRefSeqAsStoreRefListExpression();  
			break;
 
    case 821 : if (DEBUG) { System.out.println("JmlReferenceExpression ::= Name"); }  //$NON-NLS-1$
		    _this.consumePostfixExpression();  
			break;
 
    case 823 : if (DEBUG) { System.out.println("JmlMultiReferenceExpression ::= Name DOT MULTIPLY"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlMultiReferenceExpressionAsNameDotStar();  
			break;
 
    case 826 : if (DEBUG) { System.out.println("JmlMultiFieldAccess ::= Primary DOT MULTIPLY"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlMultiFieldAccess(false);  
			break;
 
    case 827 : if (DEBUG) { System.out.println("JmlMultiFieldAccess ::= super DOT MULTIPLY"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlMultiFieldAccess(true);  
			break;
 
    case 828 : if (DEBUG) { System.out.println("JmlArrayRangeAccess ::= Name LBRACKET JmlArrayIndexRange"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayRangeAccess(true);  
			break;
 
    case 829 : if (DEBUG) { System.out.println("JmlArrayRangeAccess ::= PrimaryNoNewArray LBRACKET..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayRangeAccess(false);  
			break;
 
    case 830 : if (DEBUG) { System.out.println("JmlArrayIndexRange ::= MULTIPLY"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayIndexRange(0);  
			break;
 
    case 831 : if (DEBUG) { System.out.println("JmlArrayIndexRange ::= DOTDOT Expression"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayIndexRange(1);  
			break;
 
    case 832 : if (DEBUG) { System.out.println("JmlArrayIndexRange ::= Expression DOTDOT"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayIndexRange(-1);  
			break;
 
    case 833 : if (DEBUG) { System.out.println("JmlArrayIndexRange ::= Expression DOTDOT Expression"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlArrayIndexRange(2);  
			break;
 
    case 839 : if (DEBUG) { System.out.println("StoreRefSeqOrKeyword ::= StoreRefSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlStoreRefSeqAsStoreRefListExpression();  
			break;
 
    case 840 : if (DEBUG) { System.out.println("JmlOldExpression ::= slash_old LPAREN SpecExpression..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlPrimaryOldExpression(OperatorIds.JML_OLD);  
			break;
 
    case 841 : if (DEBUG) { System.out.println("JmlOldExpression ::= slash_old LPAREN SpecExpression..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlPrimaryLabeledOldExpression(OperatorIds.JML_OLD);  
			break;
 
    case 842 : if (DEBUG) { System.out.println("JmlOldExpression ::= slash_pre LPAREN SpecExpression..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_PRE);  
			break;
 
    case 843 : if (DEBUG) { System.out.println("JmlQuantifiedExpression ::= LPAREN JmlQuantifier..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlQuantifiedExpression(false);  
			break;
 
    case 844 : if (DEBUG) { System.out.println("JmlQuantifiedExpression ::= LPAREN JmlQuantifier..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlQuantifiedExpression(false);  
			break;
 
    case 845 : if (DEBUG) { System.out.println("JmlQuantifiedExpression ::= LPAREN JmlQuantifier..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlQuantifiedExpression(true);  
			break;
 
    case 846 : if (DEBUG) { System.out.println("JmlTypeSpec ::= PrimitiveType"); }  //$NON-NLS-1$
		    _this.consumePrimitiveType();  
			break;
 
    case 847 : if (DEBUG) { System.out.println("JmlTypeSpec ::= NullityModifier PrimitiveType"); }  //$NON-NLS-1$
		    _this.consumePrimitiveType();  
			break;
 
    case 848 : if (DEBUG) { System.out.println("JmlTypeSpec ::= ReferenceType"); }  //$NON-NLS-1$
		    /*jml*/consumeReferenceTypeWithoutOwnershipModifiers();  
			break;
 
    case 849 : if (DEBUG) { System.out.println("JmlQuantifiedVarDeclarators ::= Identifier Dimsopt"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlQuantifiedVarDeclarators(true);  
			break;
 
    case 850 : if (DEBUG) { System.out.println("JmlQuantifiedVarDeclarators ::=..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlQuantifiedVarDeclarators(false);  
			break;
 
    case 858 : if (DEBUG) { System.out.println("JmlSetComprehension ::= LBRACE JmlTypeSpec Identifier..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlSetComprehension();  
			break;
 
    case 859 : if (DEBUG) { System.out.println("JmlTypeBodyDeclaration ::= Modifiersopt..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeBodyDeclaration();  
			break;
 
    case 860 : if (DEBUG) { System.out.println("JmlTypeBodyDeclaration ::= Modifiersopt..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeBodyDeclaration();  
			break;
 
    case 861 : if (DEBUG) { System.out.println("JmlTypeBodyDeclaration ::= Modifiersopt..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeBodyDeclaration();  
			break;
 
    case 862 : if (DEBUG) { System.out.println("JmlTypeBodyDeclaration ::= Modifiersopt..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlTypeBodyDeclaration();  
			break;
 
    case 863 : if (DEBUG) { System.out.println("JmlInvariantDeclaration ::= invariant Predicate..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 864 : if (DEBUG) { System.out.println("JmlConstraintDeclaration ::= constraint Predicate..."); }  //$NON-NLS-1$
		    /*jml*/consumeConstraintDeclaration();  
			break;
 
    case 865 : if (DEBUG) { System.out.println("JmlRepresentsClause ::=..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 868 : if (DEBUG) { System.out.println("JmlInitiallyClause ::= initially Predicate ExitJmlClause"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 869 : if (DEBUG) { System.out.println("MethodSpecification ::= also SpecCaseSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ false);  
			break;
 
    case 870 : if (DEBUG) { System.out.println("MethodSpecification ::= SpecCaseSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ false);  
			break;
 
    case 871 : if (DEBUG) { System.out.println("MethodSpecification ::= also SpecCaseSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ true);  
			break;
 
    case 872 : if (DEBUG) { System.out.println("MethodSpecification ::= SpecCaseSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ true);  
			break;
 
    case 873 : if (DEBUG) { System.out.println("MethodSpecification ::= also MethodSpecRedundantPart"); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ false, /*hasRedundantPart*/ true);  
			break;
 
    case 874 : if (DEBUG) { System.out.println("MethodSpecification ::= MethodSpecRedundantPart"); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ false, /*hasRedundantPart*/ true);  
			break;
 
    case 875 : if (DEBUG) { System.out.println("MethodSpecRedundantPart ::= implies_that SpecCaseSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeMethodSpecRedundantPart();  
			break;
 
    case 877 : if (DEBUG) { System.out.println("SpecCaseSeq ::= SpecCaseSeq also SpecCase"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseSeq();  
			break;
 
    case 880 : if (DEBUG) { System.out.println("LightweightSpecCase ::= SpecCaseBody"); }  //$NON-NLS-1$
		    /*jml*/consumeLightweightSpecCase();  
			break;
 
    case 881 : if (DEBUG) { System.out.println("HeavyweightSpecCase ::= Modifiersopt BehaviorOrSynonym"); }  //$NON-NLS-1$
		    /*jml*/consumeHeavyweightSpecCase();  
			break;
 
    case 882 : if (DEBUG) { System.out.println("SpecCaseBody ::= JmlSpecVarDecls SpecCaseRest"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseBody(/*hasHeader*/false, /*hasRest*/true);  
			break;
 
    case 883 : if (DEBUG) { System.out.println("SpecCaseBody ::= JmlSpecVarDecls SpecCaseHeader"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseBody(/*hasHeader*/true, /*hasRest*/false);  
			break;
 
    case 884 : if (DEBUG) { System.out.println("SpecCaseBody ::= JmlSpecVarDecls SpecCaseHeader..."); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseBody(/*hasHeader*/true, /*hasRest*/true);  
			break;
 
    case 886 : if (DEBUG) { System.out.println("StartSpecVarDecls ::="); }  //$NON-NLS-1$
		    /*jml*/consumeStartSpecVarDecls();  
			break;
 
    case 887 : if (DEBUG) { System.out.println("JmlForallVarDecls ::="); }  //$NON-NLS-1$
		    /*jml*/consumeEmptyJmlSpecVarDecls();  
			break;
 
    case 888 : if (DEBUG) { System.out.println("JmlForallVarDecls ::= JmlForallVarDecls JmlForallVarDecl"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlVarDecls();  
			break;
 
    case 890 : if (DEBUG) { System.out.println("JmlOldVarDecls ::="); }  //$NON-NLS-1$
		    /*jml*/consumeEmptyJmlSpecVarDecls();  
			break;
 
    case 891 : if (DEBUG) { System.out.println("JmlOldVarDecls ::= JmlOldVarDecls JmlOldVarDecl"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlVarDecls();  
			break;
 
    case 893 : if (DEBUG) { System.out.println("SpecCaseHeader ::= RequiresClauseSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseHeader();  
			break;
 
    case 895 : if (DEBUG) { System.out.println("RequiresClauseSeq ::= RequiresClauseSeq RequiresClause"); }  //$NON-NLS-1$
		    /*jml*/consumeRequiresClauseSeq();  
			break;
 
    case 897 : if (DEBUG) { System.out.println("SpecCaseRest ::= SpecCaseRestClauseSeq"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseRestAsClauseSeq();  
			break;
 
    case 898 : if (DEBUG) { System.out.println("SpecCaseBlock ::= LBRACE_OR SpecCaseBodySeq OR_RBRACE"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseBlock();  
			break;
 
    case 900 : if (DEBUG) { System.out.println("SpecCaseBodySeq ::= SpecCaseBodySeq also SpecCaseBody"); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseBodySeq();  
			break;
 
    case 902 : if (DEBUG) { System.out.println("SpecCaseRestClauseSeq ::= SpecCaseRestClauseSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeSpecCaseRestClauseSeq();  
			break;
 
    case 908 : if (DEBUG) { System.out.println("AssignableClause ::= AssignableOrAssignableRedundantly"); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 911 : if (DEBUG) { System.out.println("DivergesClause ::= DivergesOrDivergesRedundantly..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 914 : if (DEBUG) { System.out.println("EnsuresClause ::= EnsuresOrEnsuresRedundantly..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 917 : if (DEBUG) { System.out.println("RequiresClause ::= RequiresOrRequiresRedundantly..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 918 : if (DEBUG) { System.out.println("RequiresClause ::= RequiresOrRequiresRedundantly..."); }  //$NON-NLS-1$
		    /*jml*/consumeJmlClause();  
			break;
 
    case 921 : if (DEBUG) { System.out.println("SignalsClause ::= SignalsOrSignalsRedundantly LPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeSignalsClause(/*hasIdentifier*/false);  
			break;
 
    case 922 : if (DEBUG) { System.out.println("SignalsClause ::= SignalsOrSignalsRedundantly LPAREN..."); }  //$NON-NLS-1$
		    /*jml*/consumeSignalsClause(/*hasIdentifier*/true);  
			break;
 
    case 923 : if (DEBUG) { System.out.println("PredicateOrNotSpecifiedopt ::="); }  //$NON-NLS-1$
		    _this.consumeEmptyExpression();  
			break;
 
    case 927 : if (DEBUG) { System.out.println("SignalsOnlyClause ::=..."); }  //$NON-NLS-1$
		    /*jml*/consumeSignalsOnlyClause();  
			break;
 
    case 928 : if (DEBUG) { System.out.println("SignalsOnlyClause ::=..."); }  //$NON-NLS-1$
		    /*jml*/consumeSignalsOnlyClauseNothing();  
			break;
 
    case 934 : if (DEBUG) { System.out.println("ExitJmlClause ::="); }  //$NON-NLS-1$
		    /*jml*/consumeExitJmlClause();  
			break;
 
    case 936 : if (DEBUG) { System.out.println("JmlDataGroupClauseSeq ::= JmlDataGroupClauseSeq..."); }  //$NON-NLS-1$
		    /*jml*/consumeDataGroupClauseSeq();  
			break;
 
    case 939 : if (DEBUG) { System.out.println("InDataGroupClause ::= InKeyword DataGroupNameList..."); }  //$NON-NLS-1$
		    /*jml*/consumeInDataGroupClause();  
			break;
 
    case 943 : if (DEBUG) { System.out.println("MapsIntoClause ::= MapsKeyword MemberFieldRef slash_into"); }  //$NON-NLS-1$
		    /*jml*/consumeMapsIntoClause();  
			break;
 
    case 947 : if (DEBUG) { System.out.println("RecoveryMethodHeaderName ::= Modifiersopt TypeParameters"); }  //$NON-NLS-1$
		    _this.consumeRecoveryMethodHeaderNameWithTypeParameters();  
			break;
 
    case 948 : if (DEBUG) { System.out.println("RecoveryMethodHeaderName ::= Modifiersopt Type..."); }  //$NON-NLS-1$
		    _this.consumeRecoveryMethodHeaderName();  
			break;
 
    case 949 : if (DEBUG) { System.out.println("RecoveryMethodHeader ::= RecoveryMethodHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeader();  
			break;
 
    case 950 : if (DEBUG) { System.out.println("RecoveryMethodHeader ::= RecoveryMethodHeaderName..."); }  //$NON-NLS-1$
		    _this.consumeMethodHeader();  
			break;
 
	}
} 

} // end of file
