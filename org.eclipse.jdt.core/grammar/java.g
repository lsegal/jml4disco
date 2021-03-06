--main options
%options ACTION, AN=JavaAction.java, GP=java, 
%options FILE-PREFIX=java, ESCAPE=$, PREFIX=TokenName, OUTPUT-SIZE=125 ,
%options NOGOTO-DEFAULT, SINGLE-PRODUCTIONS, LALR=1 , TABLE, 

--error recovering options.....
%options ERROR_MAPS 

--grammar understanding options
%options first follow
%options TRACE=FULL ,
%options VERBOSE

%options DEFERRED
%options NAMES=MAX
%options SCOPES

--Usefull macros helping reading/writing semantic actions
$Define 
$putCase 
/.    case $rule_number : if (DEBUG) { System.out.println("$rule_text"); }  //$NON-NLS-1$
		   ./

$break
/. 
			break;
./


$readableName 
/.1#$rule_number#./
$compliance
/.2#$rule_number#./
$recovery
/.2#$rule_number# recovery./
$recovery_template
/.3#$rule_number#./
$no_statements_recovery
/.4#$rule_number# 1./
-- here it starts really ------------------------------------------
$Terminals

	Identifier

	abstract assert boolean break byte case catch char class 
	continue const default do double else enum extends false final finally float
	for goto if implements import instanceof int
	interface long native new null package private
	protected public return short static strictfp super switch
	synchronized this throw throws transient true try void
	volatile while
	IntegerLiteral
	LongLiteral
	FloatingPointLiteral
	DoubleLiteral
	CharacterLiteral
	StringLiteral

	-- <jml-start id="level.0-1-a" />
	-- In this section ($Terminals) we name grammar terminal symbols. It is important
	-- to note that symbol names do not necessarily match their corresponding lexemes.
	-- E.g. jml_assert's lexeme is "assert" (which in this particular case
	-- has the prefix "jml_" so that we can distinguish between it and a
	-- java "assert".
	
	-- NOTE: if you add the definition of a terminal symbol that is a keyword
	-- then you also need to add it to:
	-- org.eclipse.jdt.internal.compiler.problem.ProblemReporter.isKeyword()

	also
	jml_assert
	assume

    -- modifiers
    code_bigint_math code_java_math code_safe_math
    forall
    ghost 
    helper 
    instance 
    model
	mono_non_null
	non_null non_null_by_default
	nowarn -- nowarn is currently processed directly in the Scanner.
	nullable nullable_by_default
	old
    pure 
    spec_public 
    spec_protected 
    spec_bigint_math spec_java_math spec_safe_math
	uninitialized
	-- ownership modifiers
	slash_rep slash_peer slash_readonly
	rep peer readonly
	-- Clause keywords. Terminal symbols names ending with
	-- OrSynonym denote a lexeme class of size greater than 1.
	-- E.g. RequiresOrSynonym is returned for 'requires', 'pre'.
    AssignableOrSynonym
    AssignableRedundantlyOrSynonym
    axiom 
    BehaviorOrSynonym -- behaviour normal_behavior normal_behaviour exceptional_behavior exceptional_behaviour
    constraint
    diverges diverges_redundantly
    EnsuresOrSynonym -- ensures post
    EnsuresRedundantlyOrSynonym
    implies_that
    initially 
    invariant invariant_redundantly
    represents represents_redundantly
    RequiresOrSynonym -- requires pre
    RequiresRedundantlyOrSynonym
    SignalsOrSynonym -- signals exsures
    SignalsRedundantlyOrSynonym
    signals_only signals_only_redundantly
    set

    loop_invariant loop_invariant_redundantly
    decreases decreases_redundantly

    slash_everything slash_nonnullelements slash_nothing
    slash_old slash_pre
    slash_result slash_same slash_not_specified
    slash_forall
    slash_fresh
	slash_exists
	slash_max
	slash_min
	slash_not_assigned
	slash_not_modified
	slash_num_of
	slash_product
	slash_sum
    slash_type
    slash_typeof
	slash_elemtype

    in in_redundantly maps maps_redundantly slash_into
	InformalDescription
	DOTDOT
	EQUIV
	IMPLIES
	LBRACE_OR
	NOT_EQUIV
	OR_RBRACE
	REV_IMPLIES
	SUBTYPE
	-- <jml-end id="level.0-1-a" />
	PLUS_PLUS
	MINUS_MINUS
	EQUAL_EQUAL
	LESS_EQUAL
	GREATER_EQUAL
	NOT_EQUAL
	LEFT_SHIFT
	RIGHT_SHIFT
	UNSIGNED_RIGHT_SHIFT
	PLUS_EQUAL
	MINUS_EQUAL
	MULTIPLY_EQUAL
	DIVIDE_EQUAL
	AND_EQUAL
	OR_EQUAL
	XOR_EQUAL
	REMAINDER_EQUAL
	LEFT_SHIFT_EQUAL
	RIGHT_SHIFT_EQUAL
	UNSIGNED_RIGHT_SHIFT_EQUAL
	OR_OR
	AND_AND
	PLUS
	MINUS
	NOT
	REMAINDER
	XOR
	AND
	MULTIPLY
	OR
	TWIDDLE
	DIVIDE
	GREATER
	LESS
	LPAREN
	RPAREN
	LBRACE
	RBRACE
	LBRACKET
	RBRACKET
	SEMICOLON
	QUESTION
	COLON
	COMMA
	DOT
	EQUAL
	AT
	ELLIPSIS

--    BodyMarker

$Alias

	'++'   ::= PLUS_PLUS
	'--'   ::= MINUS_MINUS
	'=='   ::= EQUAL_EQUAL
	'<='   ::= LESS_EQUAL
	'>='   ::= GREATER_EQUAL
	'!='   ::= NOT_EQUAL
	'<<'   ::= LEFT_SHIFT
	'>>'   ::= RIGHT_SHIFT
	'>>>'  ::= UNSIGNED_RIGHT_SHIFT
	'+='   ::= PLUS_EQUAL
	'-='   ::= MINUS_EQUAL
	'*='   ::= MULTIPLY_EQUAL
	'/='   ::= DIVIDE_EQUAL
	'&='   ::= AND_EQUAL
	'|='   ::= OR_EQUAL
	'^='   ::= XOR_EQUAL
	'%='   ::= REMAINDER_EQUAL
	'<<='  ::= LEFT_SHIFT_EQUAL
	'>>='  ::= RIGHT_SHIFT_EQUAL
	'>>>=' ::= UNSIGNED_RIGHT_SHIFT_EQUAL
	'||'   ::= OR_OR
	'&&'   ::= AND_AND
	'+'    ::= PLUS
	'-'    ::= MINUS
	'!'    ::= NOT
	'%'    ::= REMAINDER
	'^'    ::= XOR
	'&'    ::= AND
	'*'    ::= MULTIPLY
	'|'    ::= OR
	'~'    ::= TWIDDLE
	'/'    ::= DIVIDE
	'>'    ::= GREATER
	'<'    ::= LESS
	'('    ::= LPAREN
	')'    ::= RPAREN
	'{'    ::= LBRACE
	'}'    ::= RBRACE
	'['    ::= LBRACKET
	']'    ::= RBRACKET
	';'    ::= SEMICOLON
	'?'    ::= QUESTION
	':'    ::= COLON
	','    ::= COMMA
	'.'    ::= DOT
	'='    ::= EQUAL
	'@'	   ::= AT
	'...'  ::= ELLIPSIS
-- <jml-start id="syntax" />
	'..'   ::= DOTDOT
	'<==>' ::= EQUIV
	'==>'  ::= IMPLIES
	'{|'   ::= LBRACE_OR
	'<=!=>' ::= NOT_EQUIV
	'|}'   ::= OR_RBRACE
	'<=='  ::= REV_IMPLIES
	'<:'   ::= SUBTYPE
-- <jml-end id="syntax" />
$Start
	Goal

$Rules

/.// This method is part of an automatic generation : do NOT edit-modify  
protected void consumeRule(int act) {
  switch ( act ) {
./



Goal ::= '++' CompilationUnit
Goal ::= '--' MethodBody
-- Initializer
Goal ::= '>>' StaticInitializer
Goal ::= '>>' Initializer
-- error recovery
-- Modifiersopt is used to properly consume a header and exit the rule reduction at the end of the parse() method
Goal ::= '>>>' Header1 Modifiersopt
Goal ::= '!' Header2 Modifiersopt
Goal ::= '*' BlockStatements
Goal ::= '*' CatchHeader
-- JDOM
Goal ::= '&&' FieldDeclaration
Goal ::= '||' ImportDeclaration
Goal ::= '?' PackageDeclaration
Goal ::= '+' TypeDeclaration
Goal ::= '/' GenericMethodDeclaration
Goal ::= '&' ClassBodyDeclarations
-- code snippet
Goal ::= '%' Expression
Goal ::= '%' ArrayInitializer
-- completion parser
Goal ::= '~' BlockStatementsopt
-- source type converter
Goal ::= '||' MemberValue
-- syntax diagnosis
Goal ::= '?' AnnotationTypeMemberDeclaration
/:$readableName Goal:/

Literal -> IntegerLiteral
Literal -> LongLiteral
Literal -> FloatingPointLiteral
Literal -> DoubleLiteral
Literal -> CharacterLiteral
Literal -> StringLiteral
Literal -> null
Literal -> BooleanLiteral
/:$readableName Literal:/
BooleanLiteral -> true
BooleanLiteral -> false
/:$readableName BooleanLiteral:/
Type ::= PrimitiveType
/.$putCase consumePrimitiveType(); $break ./
-- <jml-start id="nnts" />
Type ::= NullityModifier PrimitiveType
/.$putCase consumePrimitiveType(); $break ./
-- <jml-end id="nnts" />
-- <jml-start id="ownershipModifiers" />
Type ::= OwnershipModifiers PrimitiveType
/.$putCase /*jml*/consumeTypeWithOwnershipModifiers(); $break ./
Type ::= ReferenceType
/.$putCase /*jml*/consumeReferenceTypeWithoutOwnershipModifiers(); $break ./
Type ::= OwnershipModifiers ReferenceType
/.$putCase /*jml*/consumeTypeWithOwnershipModifiers(); $break ./
-- <jml-end id="ownershipModifiers" />
/:$readableName Type:/

PrimitiveType -> NumericType
/:$readableName PrimitiveType:/
NumericType -> IntegralType
NumericType -> FloatingPointType
/:$readableName NumericType:/

PrimitiveType -> 'boolean'
PrimitiveType -> 'void'
IntegralType -> 'byte'
IntegralType -> 'short'
IntegralType -> 'int'
IntegralType -> 'long'
IntegralType -> 'char'
/:$readableName IntegralType:/
FloatingPointType -> 'float'
FloatingPointType -> 'double'
/:$readableName FloatingPointType:/

ReferenceType ::= ClassOrInterfaceType
/.$putCase consumeReferenceType();  $break ./
-- <jml-start id="nullity" />
-- TODO: make use of the opt
ReferenceType ::= NullityModifier ClassOrInterfaceType
/.$putCase consumeReferenceType();  $break ./
-- <jml-end id="nullity" />
ReferenceType -> ArrayType
/:$readableName ReferenceType:/

---------------------------------------------------------------
-- 1.5 feature
---------------------------------------------------------------
ClassOrInterfaceType -> ClassOrInterface
ClassOrInterfaceType -> GenericType
/:$readableName Type:/

ClassOrInterface ::= Name
/.$putCase consumeClassOrInterfaceName();  $break ./
ClassOrInterface ::= GenericType '.' Name
/.$putCase consumeClassOrInterface();  $break ./
/:$readableName Type:/

GenericType ::= ClassOrInterface TypeArguments
/.$putCase consumeGenericType();  $break ./
/:$readableName GenericType:/

--
-- These rules have been rewritten to avoid some conflicts introduced
-- by adding the 1.1 features
--
-- ArrayType ::= PrimitiveType '[' ']'
-- ArrayType ::= Name '[' ']'
-- ArrayType ::= ArrayType '[' ']'
--

ArrayTypeWithTypeArgumentsName ::= GenericType '.' Name
/.$putCase consumeArrayTypeWithTypeArgumentsName();  $break ./
/:$readableName ArrayTypeWithTypeArgumentsName:/

-- <jml-start id="4" />
ArrayType ::= NullityModifier PrimitiveType Dims
/.$putCase consumePrimitiveArrayType();  $break ./
-- <jml-end id="4" />
ArrayType ::= PrimitiveType Dims
/.$putCase consumePrimitiveArrayType();  $break ./
-- <jml-start id="4" />
ArrayType ::= NullityModifier Name Dims
/.$putCase consumeNameArrayType();  $break ./
-- <jml-end id="4" />
ArrayType ::= Name Dims
/.$putCase consumeNameArrayType();  $break ./
ArrayType ::= ArrayTypeWithTypeArgumentsName Dims
/.$putCase consumeGenericTypeNameArrayType();  $break ./
ArrayType ::= GenericType Dims
/.$putCase consumeGenericTypeArrayType();  $break ./
/:$readableName ArrayType:/

ClassType -> ClassOrInterfaceType
/:$readableName ClassType:/

--------------------------------------------------------------
--------------------------------------------------------------

Name -> SimpleName
Name -> QualifiedName
/:$readableName Name:/
/:$recovery_template Identifier:/

SimpleName -> 'Identifier'
/:$readableName SimpleName:/

QualifiedName ::= Name '.' SimpleName 
/.$putCase consumeQualifiedName(); $break ./
/:$readableName QualifiedName:/

CompilationUnit ::= EnterCompilationUnit InternalCompilationUnit
/.$putCase consumeCompilationUnit(); $break ./
/:$readableName CompilationUnit:/

InternalCompilationUnit ::= PackageDeclaration
/.$putCase consumeInternalCompilationUnit(); $break ./
InternalCompilationUnit ::= PackageDeclaration ImportDeclarations ReduceImports
/.$putCase consumeInternalCompilationUnit(); $break ./
InternalCompilationUnit ::= PackageDeclaration ImportDeclarations ReduceImports TypeDeclarations
/.$putCase consumeInternalCompilationUnitWithTypes(); $break ./
InternalCompilationUnit ::= PackageDeclaration TypeDeclarations
/.$putCase consumeInternalCompilationUnitWithTypes(); $break ./
InternalCompilationUnit ::= ImportDeclarations ReduceImports
/.$putCase consumeInternalCompilationUnit(); $break ./
InternalCompilationUnit ::= TypeDeclarations
/.$putCase consumeInternalCompilationUnitWithTypes(); $break ./
InternalCompilationUnit ::= ImportDeclarations ReduceImports TypeDeclarations
/.$putCase consumeInternalCompilationUnitWithTypes(); $break ./
InternalCompilationUnit ::= $empty
/.$putCase consumeEmptyInternalCompilationUnit(); $break ./
/:$readableName CompilationUnit:/

ReduceImports ::= $empty
/.$putCase consumeReduceImports(); $break ./
/:$readableName ReduceImports:/

EnterCompilationUnit ::= $empty
/.$putCase consumeEnterCompilationUnit(); $break ./
/:$readableName EnterCompilationUnit:/

Header -> ImportDeclaration
Header -> PackageDeclaration
Header -> ClassHeader
Header -> InterfaceHeader
Header -> EnumHeader
Header -> AnnotationTypeDeclarationHeader
Header -> StaticInitializer
Header -> RecoveryMethodHeader
Header -> FieldDeclaration
Header -> AllocationHeader
Header -> ArrayCreationHeader
/:$readableName Header:/

Header1 -> Header
Header1 -> ConstructorHeader
/:$readableName Header1:/

Header2 -> Header
Header2 -> EnumConstantHeader
/:$readableName Header2:/

CatchHeader ::= 'catch' '(' FormalParameter ')' '{'
/.$putCase consumeCatchHeader(); $break ./
/:$readableName CatchHeader:/

ImportDeclarations -> ImportDeclaration
ImportDeclarations ::= ImportDeclarations ImportDeclaration 
/.$putCase consumeImportDeclarations(); $break ./
/:$readableName ImportDeclarations:/

TypeDeclarations -> TypeDeclaration
TypeDeclarations ::= TypeDeclarations TypeDeclaration
/.$putCase consumeTypeDeclarations(); $break ./
/:$readableName TypeDeclarations:/

PackageDeclaration ::= PackageDeclarationName ';'
/.$putCase  consumePackageDeclaration(); $break ./
/:$readableName PackageDeclaration:/

PackageDeclarationName ::= Modifiers 'package' PushRealModifiers Name
/.$putCase  consumePackageDeclarationNameWithModifiers(); $break ./
/:$readableName PackageDeclarationName:/
/:$compliance 1.5:/

PackageDeclarationName ::= PackageComment 'package' Name
/.$putCase  consumePackageDeclarationName(); $break ./
/:$readableName PackageDeclarationName:/

PackageComment ::= $empty
/.$putCase  consumePackageComment(); $break ./
/:$readableName PackageComment:/

-- <jml-start id="level.1.modelImports" />
--should be -> import-definition ::= [ model ] import name-star ;
--for now is-> import-definition ::=           import name-star ;
-- simply adding the rules below introduces shift-reduce conflicts 
--ImportDeclaration -> 'model' SingleTypeImportDeclaration
--ImportDeclaration -> 'model' TypeImportOnDemandDeclaration
-- <jml-end id="level.1.modelImports" />
ImportDeclaration -> SingleTypeImportDeclaration
ImportDeclaration -> TypeImportOnDemandDeclaration
-----------------------------------------------
-- 1.5 feature
-----------------------------------------------
ImportDeclaration -> SingleStaticImportDeclaration
ImportDeclaration -> StaticImportOnDemandDeclaration
/:$readableName ImportDeclaration:/

SingleTypeImportDeclaration ::= SingleTypeImportDeclarationName ';'
/.$putCase consumeImportDeclaration(); $break ./
/:$readableName SingleTypeImportDeclaration:/
			  
SingleTypeImportDeclarationName ::= 'import' Name
/.$putCase consumeSingleTypeImportDeclarationName(); $break ./
/:$readableName SingleTypeImportDeclarationName:/
			  
TypeImportOnDemandDeclaration ::= TypeImportOnDemandDeclarationName ';'
/.$putCase consumeImportDeclaration(); $break ./
/:$readableName TypeImportOnDemandDeclaration:/

TypeImportOnDemandDeclarationName ::= 'import' Name '.' '*'
/.$putCase consumeTypeImportOnDemandDeclarationName(); $break ./
/:$readableName TypeImportOnDemandDeclarationName:/

TypeDeclaration -> ClassDeclaration
TypeDeclaration -> InterfaceDeclaration
-- this declaration in part of a list od declaration and we will
-- use and optimized list length calculation process 
-- thus we decrement the number while it will be incremend.....
TypeDeclaration ::= ';' 
/. $putCase consumeEmptyTypeDeclaration(); $break ./
-----------------------------------------------
-- 1.5 feature
-----------------------------------------------
TypeDeclaration -> EnumDeclaration
TypeDeclaration -> AnnotationTypeDeclaration
/:$readableName TypeDeclaration:/

--18.7 Only in the LALR(1) Grammar

Modifiers -> Modifier
Modifiers ::= Modifiers Modifier
/.$putCase consumeModifiers2(); $break ./
/:$readableName Modifiers:/

Modifier -> 'public' 
Modifier -> 'protected'
Modifier -> 'private'
Modifier -> 'static'
Modifier -> 'abstract'
Modifier -> 'final'
Modifier -> 'native'
Modifier -> 'synchronized'
Modifier -> 'transient'
Modifier -> 'volatile'
Modifier -> 'strictfp'
-- <jml-begin id="level.0-1-a" />
Modifier ::= JmlModifier
/.$putCase /*jml*/consumeJmlModifierAsModifier(); $break ./
-- <jml-end id="level.0-1-a" />
Modifier ::= Annotation
/.$putCase consumeAnnotationAsModifier(); $break ./
/:$readableName Modifier:/

-- <jml-start id="level.0-1-a" />
JmlModifier -> 'code_bigint_math'
JmlModifier -> 'code_java_math'
JmlModifier -> 'code_safe_math'
JmlModifier -> 'ghost'
JmlModifier -> 'helper'
JmlModifier -> 'instance'
JmlModifier -> 'model'
-- the following haven't been made JmlModifiers because the grammar
--     would no longer be LALR(1) after adding modifiers to the 
--     ReferenceType, ArrayType and ArrayCreationWithArrayInitializer
--     productions.  ("_by_default"s might not be a problem)
-- JmlModifier -> 'non_null'
-- JmlModifier -> 'non_null_by_default'
-- JmlModifier -> 'nullable'
-- JmlModifier -> 'nullable_by_default'
-- JmlModifier -> 'mono_non_null'
JmlModifier -> 'pure'
JmlModifier -> 'spec_public'
JmlModifier -> 'spec_protected'
JmlModifier -> 'spec_bigint_math'
JmlModifier -> 'spec_java_math'
JmlModifier -> 'spec_safe_math'
JmlModifier -> 'uninitialized' -- level 1

-- FIXME: integrate nullity modifiers into JmlModifier.
--        (see note above)
NullityModifier -> 'nullable'
NullityModifier -> 'non_null'
NullityModifier -> 'mono_non_null'
NullityByDefaultModifier ::= 'non_null_by_default'
/.$putCase /*jml*/consumeDefaultNullity(); $break ./
NullityByDefaultModifier ::= 'nullable_by_default'
/.$putCase /*jml*/consumeDefaultNullity(); $break ./
/:$readableName NullityByDefaultModifier:/
-- <jml-end id="level.0-1-a" />
	
-- <jml-start id="ownershipModifiers" />
--ownership-modifiers ::= ownership-modifier [ ownership-modifier ]
OwnershipModifiers ::= OwnershipModifier
/.$putCase /*jml*/consumeOwnershipModifiers(1); $break ./
OwnershipModifiers ::= OwnershipModifier OwnershipModifier
/.$putCase /*jml*/consumeOwnershipModifiers(2); $break ./
/:$readableName NullityByDefaultModifier:/

--ownership-modifier ::= \rep | \peer | \readonly | reserved-ownership-modifier // with --universesx parse or --universesx full
OwnershipModifier -> 'slash_rep'
OwnershipModifier -> 'slash_peer'
OwnershipModifier -> 'slash_readonly'
OwnershipModifier -> ReservedOwnershipModifier
/:$readableName OwnershipModifier:/

--reserved-ownership-modifier ::= rep | peer | readonly
ReservedOwnershipModifier -> 'rep'
ReservedOwnershipModifier -> 'peer'
ReservedOwnershipModifier -> 'readonly'
-- <jml-end id="ownershipModifiers" />

--18.8 Productions from 8: Class Declarations
--ClassModifier ::=
--      'abstract'
--    | 'final'
--    | 'public'
--18.8.1 Productions from 8.1: Class Declarations

ClassDeclaration ::= ClassHeader ClassBody
/.$putCase consumeClassDeclaration(); $break ./
-- <jml-start id="4" />
ClassDeclaration ::= NullityByDefaultModifier ClassHeader ClassBody
/.$putCase consumeClassDeclaration(); $break ./
-- <jml-end id="4" />
/:$readableName ClassDeclaration:/

ClassHeader ::= ClassHeaderName ClassHeaderExtendsopt ClassHeaderImplementsopt
/.$putCase consumeClassHeader(); $break ./
/:$readableName ClassHeader:/

-----------------------------------------------
-- 1.5 features : generics
-----------------------------------------------
ClassHeaderName ::= ClassHeaderName1 TypeParameters
/.$putCase consumeTypeHeaderNameWithTypeParameters(); $break ./

ClassHeaderName -> ClassHeaderName1
/:$readableName ClassHeaderName:/

ClassHeaderName1 ::= Modifiersopt 'class' 'Identifier'
/.$putCase consumeClassHeaderName1(); $break ./
/:$readableName ClassHeaderName:/

ClassHeaderExtends ::= 'extends' ClassType
/.$putCase consumeClassHeaderExtends(); $break ./
/:$readableName ClassHeaderExtends:/

ClassHeaderImplements ::= 'implements' InterfaceTypeList
/.$putCase consumeClassHeaderImplements(); $break ./
/:$readableName ClassHeaderImplements:/

InterfaceTypeList -> InterfaceType
InterfaceTypeList ::= InterfaceTypeList ',' InterfaceType
/.$putCase consumeInterfaceTypeList(); $break ./
/:$readableName InterfaceTypeList:/

InterfaceType ::= ClassOrInterfaceType
/.$putCase consumeInterfaceType(); $break ./
/:$readableName InterfaceType:/

ClassBody ::= '{' ClassBodyDeclarationsopt '}'
/:$readableName ClassBody:/
/:$no_statements_recovery:/

ClassBodyDeclarations -> ClassBodyDeclaration
ClassBodyDeclarations ::= ClassBodyDeclarations ClassBodyDeclaration
/.$putCase consumeClassBodyDeclarations(); $break ./
/:$readableName ClassBodyDeclarations:/

ClassBodyDeclaration -> ClassMemberDeclaration
ClassBodyDeclaration -> StaticInitializer
ClassBodyDeclaration -> ConstructorDeclaration
-- <jml-start id="level.0-1-a" />
ClassBodyDeclaration -> JmlTypeBodyDeclaration
-- <jml-end id="level.0-1-a" />
--1.1 feature
ClassBodyDeclaration ::= Diet NestedMethod CreateInitializer Block
/.$putCase consumeClassBodyDeclaration(); $break ./
/:$readableName ClassBodyDeclaration:/

Diet ::= $empty
/.$putCase consumeDiet(); $break./
/:$readableName Diet:/

Initializer ::= Diet NestedMethod CreateInitializer Block
/.$putCase consumeClassBodyDeclaration(); $break ./
/:$readableName Initializer:/

CreateInitializer ::= $empty
/.$putCase consumeCreateInitializer(); $break./
/:$readableName CreateInitializer:/

ClassMemberDeclaration -> FieldDeclaration
ClassMemberDeclaration -> MethodDeclaration
--1.1 feature
ClassMemberDeclaration -> ClassDeclaration
--1.1 feature
ClassMemberDeclaration -> InterfaceDeclaration
-- 1.5 feature
ClassMemberDeclaration -> EnumDeclaration
ClassMemberDeclaration -> AnnotationTypeDeclaration
/:$readableName ClassMemberDeclaration:/

-- Empty declarations are not valid Java ClassMemberDeclarations.
-- However, since the current (2/14/97) Java compiler accepts them 
-- (in fact, some of the official tests contain this erroneous
-- syntax)
ClassMemberDeclaration ::= ';'
/.$putCase consumeEmptyTypeDeclaration(); $break./

GenericMethodDeclaration -> MethodDeclaration
GenericMethodDeclaration -> ConstructorDeclaration
/:$readableName GenericMethodDeclaration:/

--18.8.2 Productions from 8.3: Field Declarations
--VariableModifier ::=
--      'public'
--    | 'protected'
--    | 'private'
--    | 'static'
--    | 'final'
--    | 'transient'
--    | 'volatile'

FieldDeclaration ::= Modifiersopt Type VariableDeclarators ';'
/.$putCase consumeFieldDeclaration(); $break ./
-- <jml-start id="level.0.data-groups" />
FieldDeclaration ::= Modifiersopt Type VariableDeclarators ';' JmlDataGroupClauseSeq
/.$putCase /*jml*/consumeFieldDeclarationWithDataGroupClause(); $break ./
-- <jml-end id="level.0.data-groups" />
/:$readableName FieldDeclaration:/

VariableDeclarators -> VariableDeclarator 
VariableDeclarators ::= VariableDeclarators ',' VariableDeclarator
/.$putCase consumeVariableDeclarators(); $break ./
/:$readableName VariableDeclarators:/

VariableDeclarator ::= VariableDeclaratorId EnterVariable ExitVariableWithoutInitialization
VariableDeclarator ::= VariableDeclaratorId EnterVariable '=' ForceNoDiet VariableInitializer RestoreDiet ExitVariableWithInitialization
/:$readableName VariableDeclarator:/
/:$recovery_template Identifier:/

EnterVariable ::= $empty
/.$putCase consumeEnterVariable(); $break ./
/:$readableName EnterVariable:/

ExitVariableWithInitialization ::= $empty
/.$putCase consumeExitVariableWithInitialization(); $break ./
/:$readableName ExitVariableWithInitialization:/

ExitVariableWithoutInitialization ::= $empty
/.$putCase consumeExitVariableWithoutInitialization(); $break ./
/:$readableName ExitVariableWithoutInitialization:/

ForceNoDiet ::= $empty
/.$putCase consumeForceNoDiet(); $break ./
/:$readableName ForceNoDiet:/
RestoreDiet ::= $empty
/.$putCase consumeRestoreDiet(); $break ./
/:$readableName RestoreDiet:/

VariableDeclaratorId ::= 'Identifier' Dimsopt
/:$readableName VariableDeclaratorId:/
/:$recovery_template Identifier:/

VariableInitializer -> Expression
VariableInitializer -> ArrayInitializer
/:$readableName VariableInitializer:/
/:$recovery_template Identifier:/

--18.8.3 Productions from 8.4: Method Declarations
--MethodModifier ::=
--      'public'
--    | 'protected'
--    | 'private'
--    | 'static'
--    | 'abstract'
--    | 'final'
--    | 'native'
--    | 'synchronized'
--

MethodDeclaration -> AbstractMethodDeclaration
MethodDeclaration ::= MethodHeader MethodBody 
/.$putCase // set to true to consume a method with a body
  consumeMethodDeclaration(true);  $break ./
/:$readableName MethodDeclaration:/
-- <jml-start id="level.0-1-a" />
MethodDeclaration ::= MethodSpecification MethodHeader MethodBody 
/.$putCase // set to true to consume a method with a body
  /*jml*/consumeSpecedMethodDeclaration(true);  $break ./
/:$readableName SpecedMethodDeclaration:/
-- <jml-end id="level.0-1-a" />

AbstractMethodDeclaration ::= MethodHeader ';'
/.$putCase // set to false to consume a method without body
  consumeMethodDeclaration(false); $break ./
/:$readableName MethodDeclaration:/
-- <jml-start id="level.0-1-a">
AbstractMethodDeclaration ::= MethodSpecification MethodHeader ';'
/.$putCase // set to false to consume a method without body
   /*jml*/consumeSpecedMethodDeclaration(false); $break ./
/:$readableName MethodDeclaration:/
-- <jml-end id="level.0-1-a">

MethodHeader ::= MethodHeaderName FormalParameterListopt MethodHeaderRightParen MethodHeaderExtendedDims MethodHeaderThrowsClauseopt
/.$putCase consumeMethodHeader(); $break ./
/:$readableName MethodDeclaration:/

MethodHeaderName ::= Modifiersopt TypeParameters Type 'Identifier' '('
/.$putCase consumeMethodHeaderNameWithTypeParameters(false); $break ./
MethodHeaderName ::= Modifiersopt Type 'Identifier' '('
/.$putCase consumeMethodHeaderName(false); $break ./
/:$readableName MethodHeaderName:/

MethodHeaderRightParen ::= ')'
/.$putCase consumeMethodHeaderRightParen(); $break ./
/:$readableName ):/
/:$recovery_template ):/

MethodHeaderExtendedDims ::= Dimsopt
/.$putCase consumeMethodHeaderExtendedDims(); $break ./
/:$readableName MethodHeaderExtendedDims:/

MethodHeaderThrowsClause ::= 'throws' ClassTypeList
/.$putCase consumeMethodHeaderThrowsClause(); $break ./
/:$readableName MethodHeaderThrowsClause:/

ConstructorHeader ::= ConstructorHeaderName FormalParameterListopt MethodHeaderRightParen MethodHeaderThrowsClauseopt
/.$putCase consumeConstructorHeader(); $break ./
/:$readableName ConstructorDeclaration:/

ConstructorHeaderName ::=  Modifiersopt TypeParameters 'Identifier' '('
/.$putCase consumeConstructorHeaderNameWithTypeParameters(); $break ./
ConstructorHeaderName ::=  Modifiersopt 'Identifier' '('
/.$putCase consumeConstructorHeaderName(); $break ./
/:$readableName ConstructorHeaderName:/

FormalParameterList -> FormalParameter
FormalParameterList ::= FormalParameterList ',' FormalParameter
/.$putCase consumeFormalParameterList(); $break ./
/:$readableName FormalParameterList:/

--1.1 feature
FormalParameter ::= Modifiersopt Type VariableDeclaratorId
/.$putCase consumeFormalParameter(false); $break ./
FormalParameter ::= Modifiersopt Type '...' VariableDeclaratorId
/.$putCase consumeFormalParameter(true); $break ./
/:$readableName FormalParameter:/
/:$compliance 1.5:/
/:$recovery_template Identifier Identifier:/

ClassTypeList -> ClassTypeElt
ClassTypeList ::= ClassTypeList ',' ClassTypeElt
/.$putCase consumeClassTypeList(); $break ./
/:$readableName ClassTypeList:/

ClassTypeElt ::= ClassType
/.$putCase consumeClassTypeElt(); $break ./
/:$readableName ClassType:/

MethodBody ::= NestedMethod '{' BlockStatementsopt '}' 
/.$putCase consumeMethodBody(); $break ./
/:$readableName MethodBody:/
/:$no_statements_recovery:/

NestedMethod ::= $empty
/.$putCase consumeNestedMethod(); $break ./
/:$readableName NestedMethod:/

--18.8.4 Productions from 8.5: Static Initializers

StaticInitializer ::=  StaticOnly Block
/.$putCase consumeStaticInitializer(); $break./
/:$readableName StaticInitializer:/

StaticOnly ::= 'static'
/.$putCase consumeStaticOnly(); $break ./
/:$readableName StaticOnly:/

--18.8.5 Productions from 8.6: Constructor Declarations
--ConstructorModifier ::=
--      'public'
--    | 'protected'
--    | 'private'
--
--
ConstructorDeclaration ::= ConstructorHeader MethodBody
/.$putCase consumeConstructorDeclaration() ; $break ./ 
-- These rules are added to be able to parse constructors with no body
ConstructorDeclaration ::= ConstructorHeader ';'
/.$putCase consumeInvalidConstructorDeclaration() ; $break ./ 
/:$readableName ConstructorDeclaration:/
-- <jml-start id="level.0-1-a"> 
ConstructorDeclaration ::= MethodSpecification ConstructorHeader MethodBody
/.$putCase /*jml*/consumeSpecedConstructorDeclaration() ; $break ./ 
-- These rules are added to be able to parse constructors with no body
ConstructorDeclaration ::= MethodSpecification ConstructorHeader ';'
/.$putCase /*jml*/consumeInvalidSpecedConstructorDeclaration(false) ; $break ./ 
/:$readableName SpecedConstructorDeclaration:/
-- <jml-end id="level.0-1-a">

-- the rules ExplicitConstructorInvocationopt has been expanded
-- in the rule below in order to make the grammar lalr(1).

ExplicitConstructorInvocation ::= 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(0, THIS_CALL); $break ./

ExplicitConstructorInvocation ::= OnlyTypeArguments 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(0,THIS_CALL); $break ./

ExplicitConstructorInvocation ::= 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(0,SUPER_CALL); $break ./

ExplicitConstructorInvocation ::= OnlyTypeArguments 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(0,SUPER_CALL); $break ./

--1.1 feature
ExplicitConstructorInvocation ::= Primary '.' 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(1, SUPER_CALL); $break ./

ExplicitConstructorInvocation ::= Primary '.' OnlyTypeArguments 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(1, SUPER_CALL); $break ./

--1.1 feature
ExplicitConstructorInvocation ::= Name '.' 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(2, SUPER_CALL); $break ./

ExplicitConstructorInvocation ::= Name '.' OnlyTypeArguments 'super' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(2, SUPER_CALL); $break ./

--1.1 feature
ExplicitConstructorInvocation ::= Primary '.' 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(1, THIS_CALL); $break ./

ExplicitConstructorInvocation ::= Primary '.' OnlyTypeArguments 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(1, THIS_CALL); $break ./

--1.1 feature
ExplicitConstructorInvocation ::= Name '.' 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocation(2, THIS_CALL); $break ./

ExplicitConstructorInvocation ::= Name '.' OnlyTypeArguments 'this' '(' ArgumentListopt ')' ';'
/.$putCase consumeExplicitConstructorInvocationWithTypeArguments(2, THIS_CALL); $break ./
/:$readableName ExplicitConstructorInvocation:/

--18.9 Productions from 9: Interface Declarations

--18.9.1 Productions from 9.1: Interface Declarations
--InterfaceModifier ::=
--      'public'
--    | 'abstract'
--
InterfaceDeclaration ::= InterfaceHeader InterfaceBody
/.$putCase consumeInterfaceDeclaration(); $break ./
-- <jml-start id="4" />
InterfaceDeclaration ::= NullityByDefaultModifier InterfaceHeader InterfaceBody
/.$putCase consumeInterfaceDeclaration(); $break ./
-- <jml-end id="4" />
/:$readableName InterfaceDeclaration:/

InterfaceHeader ::= InterfaceHeaderName InterfaceHeaderExtendsopt
/.$putCase consumeInterfaceHeader(); $break ./
/:$readableName InterfaceHeader:/

-----------------------------------------------
-- 1.5 features : generics
-----------------------------------------------
InterfaceHeaderName ::= InterfaceHeaderName1 TypeParameters
/.$putCase consumeTypeHeaderNameWithTypeParameters(); $break ./

InterfaceHeaderName -> InterfaceHeaderName1
/:$readableName InterfaceHeaderName:/

InterfaceHeaderName1 ::= Modifiersopt interface Identifier
/.$putCase consumeInterfaceHeaderName1(); $break ./
/:$readableName InterfaceHeaderName:/

InterfaceHeaderExtends ::= 'extends' InterfaceTypeList
/.$putCase consumeInterfaceHeaderExtends(); $break ./
/:$readableName InterfaceHeaderExtends:/

InterfaceBody ::= '{' InterfaceMemberDeclarationsopt '}' 
/:$readableName InterfaceBody:/

InterfaceMemberDeclarations -> InterfaceMemberDeclaration
InterfaceMemberDeclarations ::= InterfaceMemberDeclarations InterfaceMemberDeclaration
/.$putCase consumeInterfaceMemberDeclarations(); $break ./
/:$readableName InterfaceMemberDeclarations:/

--same as for class members
InterfaceMemberDeclaration ::= ';'
/.$putCase consumeEmptyTypeDeclaration(); $break ./
/:$readableName InterfaceMemberDeclaration:/

InterfaceMemberDeclaration -> ConstantDeclaration
InterfaceMemberDeclaration ::= MethodHeader MethodBody
/.$putCase consumeInvalidMethodDeclaration(); $break ./
/:$readableName InterfaceMemberDeclaration:/
-- <jml-start id="level.0-1-a" />
InterfaceMemberDeclaration -> JmlTypeBodyDeclaration
InterfaceMemberDeclaration ::= MethodSpecification MethodHeader MethodBody
/.$putCase /*jml*/consumeInvalidSpecedMethodDeclaration(); $break ./
/:$readableName InterfaceMemberDeclaration:/
-- <jml-end id="level.0-1-a" />

-- These rules are added to be able to parse constructors inside interface and then report a relevent error message
InvalidConstructorDeclaration ::= ConstructorHeader MethodBody
/.$putCase consumeInvalidConstructorDeclaration(true);  $break ./
InvalidConstructorDeclaration ::= ConstructorHeader ';'
/.$putCase consumeInvalidConstructorDeclaration(false);  $break ./
/:$readableName InvalidConstructorDeclaration:/
-- <jml-start id="level.0-1-a" />
InvalidConstructorDeclaration ::= MethodSpecification ConstructorHeader MethodBody
/.$putCase /*jml*/consumeInvalidSpecedConstructorDeclaration(true);  $break ./
InvalidConstructorDeclaration ::= MethodSpecification ConstructorHeader ';'
/.$putCase /*jml*/consumeInvalidSpecedConstructorDeclaration(false);  $break ./
/:$readableName InvalidConstructorDeclaration:/
-- <jml-end id="level.0-1-a" />

InterfaceMemberDeclaration -> AbstractMethodDeclaration
InterfaceMemberDeclaration -> InvalidConstructorDeclaration
--1.1 feature
InterfaceMemberDeclaration -> ClassDeclaration
--1.1 feature
InterfaceMemberDeclaration -> InterfaceDeclaration
InterfaceMemberDeclaration -> EnumDeclaration
InterfaceMemberDeclaration -> AnnotationTypeDeclaration
/:$readableName InterfaceMemberDeclaration:/

ConstantDeclaration -> FieldDeclaration
/:$readableName ConstantDeclaration:/

PushLeftBrace ::= $empty
/.$putCase consumePushLeftBrace(); $break ./
/:$readableName PushLeftBrace:/

ArrayInitializer ::= '{' PushLeftBrace ,opt '}'
/.$putCase consumeEmptyArrayInitializer(); $break ./
ArrayInitializer ::= '{' PushLeftBrace VariableInitializers '}'
/.$putCase consumeArrayInitializer(); $break ./
ArrayInitializer ::= '{' PushLeftBrace VariableInitializers , '}'
/.$putCase consumeArrayInitializer(); $break ./
/:$readableName ArrayInitializer:/
/:$recovery_template Identifier:/

VariableInitializers ::= VariableInitializer
VariableInitializers ::= VariableInitializers ',' VariableInitializer
/.$putCase consumeVariableInitializers(); $break ./
/:$readableName VariableInitializers:/

Block ::= OpenBlock '{' BlockStatementsopt '}'
/.$putCase consumeBlock(); $break ./
/:$readableName Block:/

OpenBlock ::= $empty
/.$putCase consumeOpenBlock() ; $break ./
/:$readableName OpenBlock:/

BlockStatements -> BlockStatement
BlockStatements ::= BlockStatements BlockStatement
/.$putCase consumeBlockStatements() ; $break ./
/:$readableName BlockStatements:/

BlockStatement -> LocalVariableDeclarationStatement
BlockStatement -> Statement
--1.1 feature
BlockStatement -> ClassDeclaration
BlockStatement ::= InterfaceDeclaration
/.$putCase consumeInvalidInterfaceDeclaration(); $break ./
/:$readableName BlockStatement:/
BlockStatement ::= AnnotationTypeDeclaration
/.$putCase consumeInvalidAnnotationTypeDeclaration(); $break ./
/:$readableName BlockStatement:/
BlockStatement ::= EnumDeclaration
/.$putCase consumeInvalidEnumDeclaration(); $break ./
/:$readableName BlockStatement:/

LocalVariableDeclarationStatement ::= LocalVariableDeclaration ';'
/.$putCase consumeLocalVariableDeclarationStatement(); $break ./
/:$readableName LocalVariableDeclarationStatement:/

LocalVariableDeclaration ::= Type PushModifiers VariableDeclarators
/.$putCase consumeLocalVariableDeclaration(); $break ./
-- 1.1 feature
-- The modifiers part of this rule makes the grammar more permissive. 
-- The only modifier here is final. We put Modifiers to allow multiple modifiers
-- This will require to check the validity of the modifier
LocalVariableDeclaration ::= Modifiers Type PushRealModifiers VariableDeclarators
/.$putCase consumeLocalVariableDeclaration(); $break ./
/:$readableName LocalVariableDeclaration:/

PushModifiers ::= $empty
/.$putCase consumePushModifiers(); $break ./
/:$readableName PushModifiers:/

PushModifiersForHeader ::= $empty
/.$putCase consumePushModifiersForHeader(); $break ./
/:$readableName PushModifiersForHeader:/

PushRealModifiers ::= $empty
/.$putCase consumePushRealModifiers(); $break ./
/:$readableName PushRealModifiers:/

Statement -> StatementWithoutTrailingSubstatement
Statement -> LabeledStatement
Statement -> IfThenStatement
Statement -> IfThenElseStatement
Statement -> WhileStatement
Statement -> ForStatement
-- <jml-start id="level.0.loopAnnotations" />
--(should be) level 0 (redundanyly is level 1)
-- Statement ::= possibly-annotated-loop
--possibly-annotated-loop ::=
--          [ loop-invariant ] ...
--          [ variant-function ] ...
--          [ ident : ] loop-stmt
--loop-stmt ::= while ( expression ) statement
--        | do statement while ( expression ) ;
--        | for ( [ for-init ] ; [ expression ] ; [ expression-list ] )
--             statement
--for-init ::= local-declaration | expression-list
--loop-invariant ::= maintaining-keyword predicate ;
--maintaining-keyword ::= maintaining | maintaining_redundantly
--        | loop_invariant | loop_invariant_redundantly
--variant-function ::= decreasing-keyword spec-expression ;
--decreasing-keyword ::= decreasing | decreasing_redundantly
--        | decreases | decreases_redundantly
-- <jml-end id="level.0.loopAnnotations" />

-----------------------------------------------
-- 1.5 feature
-----------------------------------------------
Statement -> EnhancedForStatement
/:$readableName Statement:/
/:$recovery_template ;:/

StatementNoShortIf -> StatementWithoutTrailingSubstatement
StatementNoShortIf -> LabeledStatementNoShortIf
StatementNoShortIf -> IfThenElseStatementNoShortIf
StatementNoShortIf -> WhileStatementNoShortIf
StatementNoShortIf -> ForStatementNoShortIf
-----------------------------------------------
-- 1.5 feature
-----------------------------------------------
StatementNoShortIf -> EnhancedForStatementNoShortIf
/:$readableName Statement:/

StatementWithoutTrailingSubstatement -> AssertStatement
StatementWithoutTrailingSubstatement -> Block
StatementWithoutTrailingSubstatement -> EmptyStatement
StatementWithoutTrailingSubstatement -> ExpressionStatement
StatementWithoutTrailingSubstatement -> SwitchStatement
StatementWithoutTrailingSubstatement -> DoStatement
StatementWithoutTrailingSubstatement -> BreakStatement
StatementWithoutTrailingSubstatement -> ContinueStatement
StatementWithoutTrailingSubstatement -> ReturnStatement
StatementWithoutTrailingSubstatement -> SynchronizedStatement
StatementWithoutTrailingSubstatement -> ThrowStatement
StatementWithoutTrailingSubstatement -> TryStatement
/:$readableName Statement:/
-- <jml-start id="level.0.statements" />
StatementWithoutTrailingSubstatement -> JmlStatementWithoutTrailingSubstatement
/:$readableName Statement:/

JmlStatementWithoutTrailingSubstatement -> JmlAssertStatement
JmlStatementWithoutTrailingSubstatement -> JmlAssumeStatement
JmlStatementWithoutTrailingSubstatement -> JmlSetStatement

-- according to the manual, set-statement ::= set assignment-expr ;
-- Considering semantics, (and taking advantage of LR grammar), set-statement ::= set assignment ;
-- <jml-start id="level.0.statements" />
JmlSetStatement ::= 'set' Assignment ExitJmlClause ';'
/.$putCase /*jml*/consumeJmlSetStatement() ; $break ./

--set-statement ::= set assignment-expr ;
-- <jml-start id="level.0.statements" />
/:$readableName JmlStatement:/
-- <jml-end id="level.0.statements" />

EmptyStatement ::= ';'
/.$putCase consumeEmptyStatement(); $break ./
/:$readableName EmptyStatement:/

LabeledStatement ::= Label ':' Statement
/.$putCase consumeStatementLabel() ; $break ./
/:$readableName LabeledStatement:/

LabeledStatementNoShortIf ::= Label ':' StatementNoShortIf
/.$putCase consumeStatementLabel() ; $break ./
/:$readableName LabeledStatement:/

Label ::= 'Identifier'
/.$putCase consumeLabel() ; $break ./
/:$readableName Label:/

ExpressionStatement ::= StatementExpression ';'
/. $putCase consumeExpressionStatement(); $break ./
ExpressionStatement ::= ExplicitConstructorInvocation
/:$readableName Statement:/

StatementExpression ::= Assignment
StatementExpression ::= PreIncrementExpression
StatementExpression ::= PreDecrementExpression
StatementExpression ::= PostIncrementExpression
StatementExpression ::= PostDecrementExpression
StatementExpression ::= MethodInvocation
StatementExpression ::= ClassInstanceCreationExpression
/:$readableName Expression:/

IfThenStatement ::=  'if' '(' Expression ')' Statement
/.$putCase consumeStatementIfNoElse(); $break ./
/:$readableName IfStatement:/

IfThenElseStatement ::=  'if' '(' Expression ')' StatementNoShortIf 'else' Statement
/.$putCase consumeStatementIfWithElse(); $break ./
/:$readableName IfStatement:/

IfThenElseStatementNoShortIf ::=  'if' '(' Expression ')' StatementNoShortIf 'else' StatementNoShortIf
/.$putCase consumeStatementIfWithElse(); $break ./
/:$readableName IfStatement:/

SwitchStatement ::= 'switch' '(' Expression ')' OpenBlock SwitchBlock
/.$putCase consumeStatementSwitch() ; $break ./
/:$readableName SwitchStatement:/

SwitchBlock ::= '{' '}'
/.$putCase consumeEmptySwitchBlock() ; $break ./

SwitchBlock ::= '{' SwitchBlockStatements '}'
SwitchBlock ::= '{' SwitchLabels '}'
SwitchBlock ::= '{' SwitchBlockStatements SwitchLabels '}'
/.$putCase consumeSwitchBlock() ; $break ./
/:$readableName SwitchBlock:/

SwitchBlockStatements -> SwitchBlockStatement
SwitchBlockStatements ::= SwitchBlockStatements SwitchBlockStatement
/.$putCase consumeSwitchBlockStatements() ; $break ./
/:$readableName SwitchBlockStatements:/

SwitchBlockStatement ::= SwitchLabels BlockStatements
/.$putCase consumeSwitchBlockStatement() ; $break ./
/:$readableName SwitchBlockStatement:/

SwitchLabels -> SwitchLabel
SwitchLabels ::= SwitchLabels SwitchLabel
/.$putCase consumeSwitchLabels() ; $break ./
/:$readableName SwitchLabels:/

SwitchLabel ::= 'case' ConstantExpression ':'
/. $putCase consumeCaseLabel(); $break ./

SwitchLabel ::= 'default' ':'
/. $putCase consumeDefaultLabel(); $break ./
/:$readableName SwitchLabel:/

WhileStatement ::= 'while' '(' Expression ')' Statement
/.$putCase consumeStatementWhile() ; $break ./
/:$readableName WhileStatement:/

-- <jml-start id="jml.loop-annotations" />
--annotated-loop ::= loop-annotations while ( expression ) statement
WhileStatement ::= JmlLoopAnnotations 'while' '(' Expression ')' Statement
/.$putCase /*jml*/consumeStatementWhileWithAnnotations() ; $break ./
/:$readableName WhileStatement:/
-- <jml-end id="jml.loop-annotations" />

WhileStatementNoShortIf ::= 'while' '(' Expression ')' StatementNoShortIf
/.$putCase consumeStatementWhile() ; $break ./
/:$readableName WhileStatement:/

-- <jml-start id="jml.loop-annotations" />
-- annotated-loop ::= loop-annotations while ( expression ) statement
WhileStatementNoShortIf ::= JmlLoopAnnotations 'while' '(' Expression ')' StatementNoShortIf
	/.$putCase /*jml*/consumeStatementWhileWithAnnotations() ; $break ./
	/:$readableName WhileStatement:/

-- loop-annotation ::= loop-invariant | loop-invariant loop-variant | loop-variant
JmlLoopAnnotations ::= 
	JmlLoopInvariantSeq JmlLabelopt 
		/.$putCase /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/true, /*hasVariantSeq*/false); $break ./
	| JmlLoopVariantSeq JmlLabelopt
		/.$putCase /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/false, /*hasVariantSeq*/true); $break ./
	| JmlLoopInvariantSeq JmlLoopVariantSeq JmlLabelopt 
		/.$putCase /*jml*/consumeLoopAnnotations(/*hasInvariantSeq*/true, /*hasVariantSeq*/true); $break ./
	/:$readableName JmlLoopAnnotation:/

JmlLabelopt ::= $empty /.$putCase /*jml*/consumeEmptyJmlLabel() ; $break ./
	| Label ':'
	/:$readableName JmlLabel:/

JmlLoopInvariantSeq ::= JmlLoopInvariant
	| JmlLoopInvariantSeq JmlLoopInvariant
		/.$putCase /*jml*/consumeJmlLoopInvariantSeq(); $break ./

JmlLoopVariantSeq ::= JmlLoopVariant
	| JmlLoopVariantSeq JmlLoopVariant
		/.$putCase /*jml*/consumeJmlLoopVariantSeq(); $break ./

-- loop-invariant ::= maintaining-keyword predicate ';'
JmlLoopInvariant ::= MaintainingKeyword Predicate ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause() ; $break ./

MaintainingKeyword -> 'loop_invariant' | 'loop_invariant_redundantly'
	/:$readableName LoopInvariantOrMaintainingKeyword:/

JmlLoopVariant ::= DecreasingKeyword Predicate ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause() ; $break ./

DecreasingKeyword -> 'decreases' | 'decreases_redundantly'
-- <jml-end id="jml.loop-annotations" />

DoStatement ::= 'do' Statement 'while' '(' Expression ')' ';'
/.$putCase consumeStatementDo() ; $break ./
/:$readableName DoStatement:/
-- <jml-start id="jml.loop-annotations" />
--annotated-loop ::= loop-annotations do statement while ( expression ) 
DoStatement ::= JmlLoopAnnotations 'do' Statement 'while' '(' Expression ')' ';'
/.$putCase /*jml*/consumeStatementDoWithAnnotations() ; $break ./
/:$readableName DoStatement:/
-- <jml-end id="jml.loop-annotations" />

ForStatement ::= 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' Statement
/.$putCase consumeStatementFor() ; $break ./
/:$readableName ForStatement:/

-- <jml-start id="jml.loop-annotations" />
--annotated-loop ::= loop-annotations do statement while ( expression ) 
ForStatement ::= JmlLoopAnnotations 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' Statement
/.$putCase /*jml*/consumeStatementForWithAnnotations() ; $break ./
/:$readableName ForStatement:/
-- <jml-end id="jml.loop-annotations" />

ForStatementNoShortIf ::= 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' StatementNoShortIf
/.$putCase consumeStatementFor() ; $break ./
/:$readableName ForStatement:/

-- <jml-start id="jml.loop-annotations" />
--annotated-loop ::= loop-annotations do statement while ( expression ) 
ForStatementNoShortIf ::= JmlLoopAnnotations 'for' '(' ForInitopt ';' Expressionopt ';' ForUpdateopt ')' StatementNoShortIf
/.$putCase /*jml*/consumeStatementForWithAnnotations() ; $break ./
/:$readableName ForStatement:/
-- <jml-end id="jml.loop-annotations" />

--the minus one allows to avoid a stack-to-stack transfer
ForInit ::= StatementExpressionList
/.$putCase consumeForInit() ; $break ./
ForInit -> LocalVariableDeclaration
/:$readableName ForInit:/

ForUpdate -> StatementExpressionList
/:$readableName ForUpdate:/

StatementExpressionList -> StatementExpression
StatementExpressionList ::= StatementExpressionList ',' StatementExpression
/.$putCase consumeStatementExpressionList() ; $break ./
/:$readableName StatementExpressionList:/

-- 1.4 feature
AssertStatement ::= 'assert' Expression ';'
/.$putCase consumeSimpleAssertStatement() ; $break ./
/:$compliance 1.4:/

AssertStatement ::= 'assert' Expression ':' Expression ';'
/.$putCase consumeAssertStatement() ; $break ./
/:$readableName AssertStatement:/
/:$compliance 1.4:/

-- <jml-start id="jmlstatements.level.0" />
-- FIXME: we most likely want only one of the following grammar productions; hence
-- make the change in the reference manual.
--assert-statement ::= assert expression [ : expression ] ;
--        		     | assert predicate [ : expression ] ;
--(should be)
--WARNING: we propose dropping the assert_redundantly clause.
--assert-redundantly-statement ::= assert_redundantly predicate [ : expression ] ;
JmlAssertStatement ::= 'jml_assert' Predicate ExitJmlClause ';'
/.$putCase /*jml*/consumeJmlSimpleAssertStatement() ; $break ./
JmlAssertStatement ::= 'jml_assert' Predicate ':' Expression ExitJmlClause ';'
/.$putCase /*jml*/consumeJmlAssertStatement() ; $break ./
/:$readableName JmlAssertStatement:/

--assume-statement ::= assume-keyword predicate [ : expression ] ;
--WARNING: we propose dropping the assume_redundantly clause.
--should be -> assume-keyword ::= assume | assume_redundantly
--for now is-> assume-keyword ::= assume
JmlAssumeStatement ::= 'assume' Predicate ExitJmlClause ';'
/.$putCase /*jml*/consumeJmlSimpleAssumeStatement() ; $break ./
JmlAssumeStatement ::= 'assume' Predicate ':' Expression ExitJmlClause ';'
/.$putCase /*jml*/consumeJmlAssumeStatement() ; $break ./
/:$readableName JmlAssumeStatement:/
-- <jml-end id="jmlstatements.level.0" />

BreakStatement ::= 'break' ';'
/.$putCase consumeStatementBreak() ; $break ./

BreakStatement ::= 'break' Identifier ';'
/.$putCase consumeStatementBreakWithLabel() ; $break ./
/:$readableName BreakStatement:/

ContinueStatement ::= 'continue' ';'
/.$putCase consumeStatementContinue() ; $break ./

ContinueStatement ::= 'continue' Identifier ';'
/.$putCase consumeStatementContinueWithLabel() ; $break ./
/:$readableName ContinueStatement:/

ReturnStatement ::= 'return' Expressionopt ';'
/.$putCase consumeStatementReturn() ; $break ./
/:$readableName ReturnStatement:/

ThrowStatement ::= 'throw' Expression ';'
/.$putCase consumeStatementThrow(); $break ./
/:$readableName ThrowStatement:/

SynchronizedStatement ::= OnlySynchronized '(' Expression ')'    Block
/.$putCase consumeStatementSynchronized(); $break ./
/:$readableName SynchronizedStatement:/

OnlySynchronized ::= 'synchronized'
/.$putCase consumeOnlySynchronized(); $break ./
/:$readableName OnlySynchronized:/

TryStatement ::= 'try' TryBlock Catches
/.$putCase consumeStatementTry(false); $break ./
TryStatement ::= 'try' TryBlock Catchesopt Finally
/.$putCase consumeStatementTry(true); $break ./
/:$readableName TryStatement:/

TryBlock ::= Block ExitTryBlock
/:$readableName Block:/

ExitTryBlock ::= $empty
/.$putCase consumeExitTryBlock(); $break ./
/:$readableName ExitTryBlock:/

Catches -> CatchClause
Catches ::= Catches CatchClause
/.$putCase consumeCatches(); $break ./
/:$readableName Catches:/

CatchClause ::= 'catch' '(' FormalParameter ')'    Block
/.$putCase consumeStatementCatch() ; $break ./
/:$readableName CatchClause:/

Finally ::= 'finally'    Block
/:$readableName Finally:/
/:$recovery_template finally { }:/

--18.12 Productions from 14: Expressions

--for source positioning purpose
PushLPAREN ::= '('
/.$putCase consumeLeftParen(); $break ./
/:$readableName (:/
/:$recovery_template (:/
PushRPAREN ::= ')'
/.$putCase consumeRightParen(); $break ./
/:$readableName ):/
/:$recovery_template ):/

Primary -> PrimaryNoNewArray
Primary -> ArrayCreationWithArrayInitializer
Primary -> ArrayCreationWithoutArrayInitializer
/:$readableName Expression:/

PrimaryNoNewArray -> Literal
PrimaryNoNewArray ::= 'this'
/.$putCase consumePrimaryNoNewArrayThis(); $break ./

PrimaryNoNewArray ::=  PushLPAREN Expression_NotName PushRPAREN 
/.$putCase consumePrimaryNoNewArray(); $break ./

PrimaryNoNewArray ::=  PushLPAREN Name PushRPAREN 
/.$putCase consumePrimaryNoNewArrayWithName(); $break ./

PrimaryNoNewArray -> ClassInstanceCreationExpression
PrimaryNoNewArray -> FieldAccess
--1.1 feature
PrimaryNoNewArray ::= Name '.' 'this'
/.$putCase consumePrimaryNoNewArrayNameThis(); $break ./
PrimaryNoNewArray ::= Name '.' 'super'
/.$putCase consumePrimaryNoNewArrayNameSuper(); $break ./

--1.1 feature
--PrimaryNoNewArray ::= Type '.' 'class'   
--inline Type in the previous rule in order to make the grammar LL1 instead 
-- of LL2. The result is the 3 next rules.

PrimaryNoNewArray ::= Name '.' 'class'
/.$putCase consumePrimaryNoNewArrayName(); $break ./

PrimaryNoNewArray ::= Name Dims '.' 'class'
/.$putCase consumePrimaryNoNewArrayArrayType(); $break ./

PrimaryNoNewArray ::= PrimitiveType Dims '.' 'class'
/.$putCase consumePrimaryNoNewArrayPrimitiveArrayType(); $break ./

PrimaryNoNewArray ::= PrimitiveType '.' 'class'
/.$putCase consumePrimaryNoNewArrayPrimitiveType(); $break ./

PrimaryNoNewArray -> MethodInvocation
PrimaryNoNewArray -> ArrayAccess
-- <jml-start id="level.0.expression" />
PrimaryNoNewArray -> JmlPrimary 
-- <jml-end id="level.0.expression" />
/:$readableName Expression:/
--1.1 feature
--
-- In Java 1.0 a ClassBody could not appear at all in a
-- ClassInstanceCreationExpression.
--
-- <jml-start id="level.0.set comprehensions" />
--(should be) level 0
-- need something here corresponding to set-comprehension, where
--new-expr ::= new type new-suffix
--new-suffix ::= ( [ expression-list ] ) [ class-block ]
--        | array-decl [ array-initializer ]
--        | set-comprehension
ClassInstanceCreationExpression ::= 'new' ClassType JmlSetComprehension
/.$putCase /*jml*/consumeClassInstanceCreationExpressionWithSetComprehension(); $break ./
-- <jml-end id="level.0.set comprehensions" />
AllocationHeader ::= 'new' ClassType '(' ArgumentListopt ')'
/.$putCase consumeAllocationHeader(); $break ./
/:$readableName AllocationHeader:/

ClassInstanceCreationExpression ::= 'new' OnlyTypeArguments ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpressionWithTypeArguments(); $break ./

ClassInstanceCreationExpression ::= 'new' ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpression(); $break ./
--1.1 feature

ClassInstanceCreationExpression ::= Primary '.' 'new' OnlyTypeArguments ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpressionQualifiedWithTypeArguments() ; $break ./

ClassInstanceCreationExpression ::= Primary '.' 'new' ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpressionQualified() ; $break ./

--1.1 feature
ClassInstanceCreationExpression ::= ClassInstanceCreationExpressionName 'new' ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpressionQualified() ; $break ./
/:$readableName ClassInstanceCreationExpression:/

ClassInstanceCreationExpression ::= ClassInstanceCreationExpressionName 'new' OnlyTypeArguments ClassType '(' ArgumentListopt ')' ClassBodyopt
/.$putCase consumeClassInstanceCreationExpressionQualifiedWithTypeArguments() ; $break ./
/:$readableName ClassInstanceCreationExpression:/

ClassInstanceCreationExpressionName ::= Name '.'
/.$putCase consumeClassInstanceCreationExpressionName() ; $break ./
/:$readableName ClassInstanceCreationExpressionName:/

ClassBodyopt ::= $empty --test made using null as contents
/.$putCase consumeClassBodyopt(); $break ./
ClassBodyopt ::= EnterAnonymousClassBody ClassBody
/:$readableName ClassBody:/
/:$no_statements_recovery:/

EnterAnonymousClassBody ::= $empty
/.$putCase consumeEnterAnonymousClassBody(); $break ./
/:$readableName EnterAnonymousClassBody:/

ArgumentList ::= Expression
ArgumentList ::= ArgumentList ',' Expression
/.$putCase consumeArgumentList(); $break ./
/:$readableName ArgumentList:/

ArrayCreationHeader ::= 'new' PrimitiveType DimWithOrWithOutExprs
/.$putCase consumeArrayCreationHeader(); $break ./

ArrayCreationHeader ::= 'new' ClassOrInterfaceType DimWithOrWithOutExprs
/.$putCase consumeArrayCreationHeader(); $break ./
/:$readableName ArrayCreationHeader:/

ArrayCreationWithoutArrayInitializer ::= 'new' PrimitiveType DimWithOrWithOutExprs
/.$putCase consumeArrayCreationExpressionWithoutInitializer(); $break ./
/:$readableName ArrayCreationWithoutArrayInitializer:/

ArrayCreationWithArrayInitializer ::= 'new' PrimitiveType DimWithOrWithOutExprs ArrayInitializer
/.$putCase consumeArrayCreationExpressionWithInitializer(); $break ./
/:$readableName ArrayCreationWithArrayInitializer:/

ArrayCreationWithoutArrayInitializer ::= 'new' ClassOrInterfaceType DimWithOrWithOutExprs
/.$putCase consumeArrayCreationExpressionWithoutInitializer(); $break ./

ArrayCreationWithArrayInitializer ::= 'new' ClassOrInterfaceType DimWithOrWithOutExprs ArrayInitializer
/.$putCase consumeArrayCreationExpressionWithInitializer(); $break ./

-- <jml-start id="5" />
ArrayCreationWithArrayInitializer ::= 'new' NullityModifier ClassOrInterfaceType DimWithOrWithOutExprs ArrayInitializer
/.$putCase consumeArrayCreationExpressionWithInitializer(); $break ./
-- <jml-end id="5" />

DimWithOrWithOutExprs ::= DimWithOrWithOutExpr
DimWithOrWithOutExprs ::= DimWithOrWithOutExprs DimWithOrWithOutExpr
/.$putCase consumeDimWithOrWithOutExprs(); $break ./
/:$readableName Dimensions:/

DimWithOrWithOutExpr ::= '[' Expression ']'
DimWithOrWithOutExpr ::= '[' ']'
/. $putCase consumeDimWithOrWithOutExpr(); $break ./
/:$readableName Dimension:/
-- -----------------------------------------------

Dims ::= DimsLoop
/. $putCase consumeDims(); $break ./
/:$readableName Dimensions:/
DimsLoop -> OneDimLoop
DimsLoop ::= DimsLoop OneDimLoop
-- <jml-start id="nntsElements" />
/. $putCase /*jml*/consumeDimLoop(); $break ./
-- <jml-end id="nntsElements" />
/:$readableName Dimensions:/
OneDimLoop ::= '[' ']'
/. $putCase consumeOneDimLoop(); $break ./
OneDimLoop ::= '[' NullityModifier ']'
/. $putCase /*jml*/consumeOneDimLoopWithNullity(); $break ./
/:$readableName Dimension:/

FieldAccess ::= Primary '.' 'Identifier'
/.$putCase consumeFieldAccess(false); $break ./

FieldAccess ::= 'super' '.' 'Identifier'
/.$putCase consumeFieldAccess(true); $break ./
/:$readableName FieldAccess:/

MethodInvocation ::= Name '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationName(); $break ./

MethodInvocation ::= Name '.' OnlyTypeArguments 'Identifier' '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationNameWithTypeArguments(); $break ./

MethodInvocation ::= Primary '.' OnlyTypeArguments 'Identifier' '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationPrimaryWithTypeArguments(); $break ./

MethodInvocation ::= Primary '.' 'Identifier' '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationPrimary(); $break ./

MethodInvocation ::= 'super' '.' OnlyTypeArguments 'Identifier' '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationSuperWithTypeArguments(); $break ./

MethodInvocation ::= 'super' '.' 'Identifier' '(' ArgumentListopt ')'
/.$putCase consumeMethodInvocationSuper(); $break ./
/:$readableName MethodInvocation:/

ArrayAccess ::= Name '[' Expression ']'
/.$putCase consumeArrayAccess(true); $break ./
ArrayAccess ::= PrimaryNoNewArray '[' Expression ']'
/.$putCase consumeArrayAccess(false); $break ./
ArrayAccess ::= ArrayCreationWithArrayInitializer '[' Expression ']'
/.$putCase consumeArrayAccess(false); $break ./
/:$readableName ArrayAccess:/

PostfixExpression -> Primary
PostfixExpression ::= Name
/.$putCase consumePostfixExpression(); $break ./
PostfixExpression -> PostIncrementExpression
PostfixExpression -> PostDecrementExpression
/:$readableName Expression:/

PostIncrementExpression ::= PostfixExpression '++'
/.$putCase consumeUnaryExpression(OperatorIds.PLUS,true); $break ./
/:$readableName PostIncrementExpression:/

PostDecrementExpression ::= PostfixExpression '--'
/.$putCase consumeUnaryExpression(OperatorIds.MINUS,true); $break ./
/:$readableName PostDecrementExpression:/

--for source managment purpose
PushPosition ::= $empty
 /.$putCase consumePushPosition(); $break ./
/:$readableName PushPosition:/

UnaryExpression -> PreIncrementExpression
UnaryExpression -> PreDecrementExpression
UnaryExpression ::= '+' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.PLUS); $break ./
UnaryExpression ::= '-' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.MINUS); $break ./
UnaryExpression -> UnaryExpressionNotPlusMinus
/:$readableName Expression:/

PreIncrementExpression ::= '++' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.PLUS,false); $break ./
/:$readableName PreIncrementExpression:/

PreDecrementExpression ::= '--' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.MINUS,false); $break ./
/:$readableName PreDecrementExpression:/

UnaryExpressionNotPlusMinus -> PostfixExpression
UnaryExpressionNotPlusMinus ::= '~' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.TWIDDLE); $break ./
UnaryExpressionNotPlusMinus ::= '!' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.NOT); $break ./
UnaryExpressionNotPlusMinus -> CastExpression
/:$readableName Expression:/

CastExpression ::= PushLPAREN PrimitiveType Dimsopt PushRPAREN InsideCastExpression UnaryExpression
/.$putCase consumeCastExpressionWithPrimitiveType(); $break ./
CastExpression ::= PushLPAREN Name OnlyTypeArgumentsForCastExpression Dimsopt PushRPAREN InsideCastExpression UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithGenericsArray(); $break ./
CastExpression ::= PushLPAREN Name OnlyTypeArgumentsForCastExpression '.' ClassOrInterfaceType Dimsopt PushRPAREN InsideCastExpressionWithQualifiedGenerics UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithQualifiedGenericsArray(); $break ./
CastExpression ::= PushLPAREN Name PushRPAREN InsideCastExpressionLL1 UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionLL1(); $break ./
CastExpression ::= PushLPAREN Name Dims PushRPAREN InsideCastExpression UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithNameArray(); $break ./
/:$readableName CastExpression:/

-- <jml-start id="5" />
-- note: 'non_null' refers to the terminal, not the lexeme. 
--       Do we need to rename the terminal token to something else that is not so confusing
-- beware: Dims is not optional on PrimitiveType casts
CastExpression ::= PushLPAREN 'non_null' PrimitiveType Dims PushRPAREN InsideCastExpression UnaryExpression
/.$putCase consumeCastExpressionWithPrimitiveType(); $break ./
CastExpression ::= PushLPAREN 'non_null' Name OnlyTypeArgumentsForCastExpression Dimsopt PushRPAREN InsideCastExpression UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithGenericsArray(); $break ./
CastExpression ::= PushLPAREN 'non_null' Name OnlyTypeArgumentsForCastExpression '.' ClassOrInterfaceType Dimsopt PushRPAREN InsideCastExpressionWithQualifiedGenerics UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithQualifiedGenericsArray(); $break ./
CastExpression ::= PushLPAREN 'non_null' Name PushRPAREN InsideCastExpressionLL1 UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionLL1(); $break ./
CastExpression ::= PushLPAREN 'non_null' Name Dims PushRPAREN InsideCastExpression UnaryExpressionNotPlusMinus
/.$putCase consumeCastExpressionWithNameArray(); $break ./
-- <jml-end id="5" />
-- <jml-start id="castNullityWithoutType" />
CastExpression ::= PushLPAREN 'non_null' PushRPAREN InsideCastExpression UnaryExpression
/.$putCase /*jml*/consumeCastExpressionWithoutType(); $break ./
/:$readableName CastExpressionWithoutType:/
-- <jml-end id="castNullityWithoutType" />

OnlyTypeArgumentsForCastExpression ::= OnlyTypeArguments
/.$putCase consumeOnlyTypeArgumentsForCastExpression(); $break ./
/:$readableName TypeArguments:/

InsideCastExpression ::= $empty
/.$putCase consumeInsideCastExpression(); $break ./
/:$readableName InsideCastExpression:/
InsideCastExpressionLL1 ::= $empty
/.$putCase consumeInsideCastExpressionLL1(); $break ./
/:$readableName InsideCastExpression:/
InsideCastExpressionWithQualifiedGenerics ::= $empty
/.$putCase consumeInsideCastExpressionWithQualifiedGenerics(); $break ./
/:$readableName InsideCastExpression:/

MultiplicativeExpression -> UnaryExpression
MultiplicativeExpression ::= MultiplicativeExpression '*' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.MULTIPLY); $break ./
MultiplicativeExpression ::= MultiplicativeExpression '/' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.DIVIDE); $break ./
MultiplicativeExpression ::= MultiplicativeExpression '%' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.REMAINDER); $break ./
/:$readableName Expression:/

AdditiveExpression -> MultiplicativeExpression
AdditiveExpression ::= AdditiveExpression '+' MultiplicativeExpression
/.$putCase consumeBinaryExpression(OperatorIds.PLUS); $break ./
AdditiveExpression ::= AdditiveExpression '-' MultiplicativeExpression
/.$putCase consumeBinaryExpression(OperatorIds.MINUS); $break ./
/:$readableName Expression:/

ShiftExpression -> AdditiveExpression
ShiftExpression ::= ShiftExpression '<<'  AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.LEFT_SHIFT); $break ./
ShiftExpression ::= ShiftExpression '>>'  AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.RIGHT_SHIFT); $break ./
ShiftExpression ::= ShiftExpression '>>>' AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.UNSIGNED_RIGHT_SHIFT); $break ./
/:$readableName Expression:/

RelationalExpression -> ShiftExpression
RelationalExpression ::= RelationalExpression '<'  ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.LESS); $break ./
RelationalExpression ::= RelationalExpression '>'  ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.GREATER); $break ./
RelationalExpression ::= RelationalExpression '<=' ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.LESS_EQUAL); $break ./
RelationalExpression ::= RelationalExpression '>=' ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.GREATER_EQUAL); $break ./
/:$readableName Expression:/
-- <jml-start id="subtype-expression" />
--relational-expr ::= shift-expr '<:' shift-expr
RelationalExpression ::= ShiftExpression '<:' ShiftExpression
/.$putCase /*jml*/consumeJmlSubtypeExpression(); $break ./
-- <jml-end id="subtype-expression" />

InstanceofExpression -> RelationalExpression
InstanceofExpression ::= InstanceofExpression 'instanceof' ReferenceType
/.$putCase consumeInstanceOfExpression(); $break ./
/:$readableName Expression:/

EqualityExpression -> InstanceofExpression
EqualityExpression ::= EqualityExpression '==' InstanceofExpression
/.$putCase consumeEqualityExpression(OperatorIds.EQUAL_EQUAL); $break ./
EqualityExpression ::= EqualityExpression '!=' InstanceofExpression
/.$putCase consumeEqualityExpression(OperatorIds.NOT_EQUAL); $break ./
/:$readableName Expression:/

AndExpression -> EqualityExpression
AndExpression ::= AndExpression '&' EqualityExpression
/.$putCase consumeBinaryExpression(OperatorIds.AND); $break ./
/:$readableName Expression:/

ExclusiveOrExpression -> AndExpression
ExclusiveOrExpression ::= ExclusiveOrExpression '^' AndExpression
/.$putCase consumeBinaryExpression(OperatorIds.XOR); $break ./
/:$readableName Expression:/

InclusiveOrExpression -> ExclusiveOrExpression
InclusiveOrExpression ::= InclusiveOrExpression '|' ExclusiveOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.OR); $break ./
/:$readableName Expression:/

ConditionalAndExpression -> InclusiveOrExpression
ConditionalAndExpression ::= ConditionalAndExpression '&&' InclusiveOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.AND_AND); $break ./
/:$readableName Expression:/

ConditionalOrExpression -> ConditionalAndExpression
ConditionalOrExpression ::= ConditionalOrExpression '||' ConditionalAndExpression
/.$putCase consumeBinaryExpression(OperatorIds.OR_OR); $break ./
/:$readableName Expression:/

-- <jml-start id="level.0.expressions" />
--conditional-expr ::= equivalence-expr [ '?' expr ':' conditional-expr ]
ConditionalExpression -> EquivalenceExpression
ConditionalExpression ::= EquivalenceExpression '?' Expression ':' ConditionalExpression
-- <jml-end id="level.0.expressions" />
/.$putCase consumeConditionalExpression(OperatorIds.QUESTIONCOLON) ; $break ./
/:$readableName Expression:/

-- <jml-start id="level.0.expressions" />
-- BEWARE: there are two versions of these productions:
-- foo and fo_NotName. If you make changes to one, also change
-- the other!

--equivalence-expr ::= implies-expr [ ( '<==>' | '<=!=>' ) implies-expr ] ...
EquivalenceExpression -> ImpliesExpression
EquivalenceExpression ::= EquivalenceExpression '<==>' ImpliesExpression
/.$putCase consumeEqualityExpression(OperatorIds.JML_EQUIV); $break ./
EquivalenceExpression ::= EquivalenceExpression '<=!=>' ImpliesExpression
/.$putCase consumeEqualityExpression(OperatorIds.JML_NOT_EQUIV); $break ./
/:$readableName Expression:/

--implies-expr ::= logical-or-expr '<==' logical-or-expr [ '<==' logical-or-expr ] ...
--              |  logical-or-expr [ '==>' implies-non-backward-expr ]
--implies-non-backward-expr ::= logical-or-expr [ '==>' implies-non-backward-expr ]
ImpliesExpression -> ConditionalOrExpression
ImpliesExpression ::= ImpliesExpression '<==' ConditionalOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.JML_REV_IMPLIES) ; $break ./
ImpliesExpression ::= ConditionalOrExpression '==>' NotRevImpliesExpression
/.$putCase consumeBinaryExpression(OperatorIds.JML_IMPLIES) ; $break ./
/:$readableName Expression:/
NotRevImpliesExpression -> ConditionalOrExpression
NotRevImpliesExpression ::= ConditionalOrExpression '==>' NotRevImpliesExpression
/.$putCase consumeBinaryExpression(OperatorIds.JML_IMPLIES) ; $break ./
/:$readableName Expression:/

-- _NotName version of productions:

EquivalenceExpression_NotName -> ImpliesExpression_NotName
EquivalenceExpression_NotName ::= EquivalenceExpression_NotName '<==>' ImpliesExpression
/.$putCase consumeEqualityExpression(OperatorIds.JML_EQUIV); $break ./
EquivalenceExpression_NotName ::= Name '<==>' ImpliesExpression
/.$putCase consumeEqualityExpressionWithName(OperatorIds.JML_EQUIV); $break ./
EquivalenceExpression_NotName ::= EquivalenceExpression_NotName '<=!=>' ImpliesExpression
/.$putCase consumeEqualityExpression(OperatorIds.JML_NOT_EQUIV); $break ./
EquivalenceExpression_NotName ::= Name '<=!=>' ImpliesExpression
/.$putCase consumeEqualityExpressionWithName(OperatorIds.JML_NOT_EQUIV); $break ./
/:$readableName Expression:/

ImpliesExpression_NotName -> ConditionalOrExpression_NotName
ImpliesExpression_NotName ::= ImpliesExpression_NotName '<==' ConditionalOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.JML_REV_IMPLIES) ; $break ./
ImpliesExpression_NotName ::= Name '<==' ConditionalOrExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.JML_REV_IMPLIES) ; $break ./
ImpliesExpression_NotName ::= ConditionalOrExpression_NotName '==>' NotRevImpliesExpression
/.$putCase consumeBinaryExpression(OperatorIds.JML_IMPLIES) ; $break ./
ImpliesExpression_NotName ::= Name '==>' NotRevImpliesExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.JML_IMPLIES) ; $break ./
/:$readableName Expression:/
-- <jml-end id="level.0.expressions" />

AssignmentExpression -> ConditionalExpression
AssignmentExpression -> Assignment
/:$readableName Expression:/
/:$recovery_template Identifier:/

Assignment ::= PostfixExpression AssignmentOperator AssignmentExpression
/.$putCase consumeAssignment(); $break ./
/:$readableName Assignment:/

-- this rule is added to parse an array initializer in a assigment and then report a syntax error knowing the exact senario
InvalidArrayInitializerAssignement ::= PostfixExpression AssignmentOperator ArrayInitializer
/:$readableName ArrayInitializerAssignment:/
/:$recovery:/
Assignment ::= InvalidArrayInitializerAssignement
/.$putCase ignoreExpressionAssignment();$break ./
/:$recovery:/

AssignmentOperator ::= '='
/.$putCase consumeAssignmentOperator(EQUAL); $break ./
AssignmentOperator ::= '*='
/.$putCase consumeAssignmentOperator(MULTIPLY); $break ./
AssignmentOperator ::= '/='
/.$putCase consumeAssignmentOperator(DIVIDE); $break ./
AssignmentOperator ::= '%='
/.$putCase consumeAssignmentOperator(REMAINDER); $break ./
AssignmentOperator ::= '+='
/.$putCase consumeAssignmentOperator(PLUS); $break ./
AssignmentOperator ::= '-='
/.$putCase consumeAssignmentOperator(MINUS); $break ./
AssignmentOperator ::= '<<='
/.$putCase consumeAssignmentOperator(LEFT_SHIFT); $break ./
AssignmentOperator ::= '>>='
/.$putCase consumeAssignmentOperator(RIGHT_SHIFT); $break ./
AssignmentOperator ::= '>>>='
/.$putCase consumeAssignmentOperator(UNSIGNED_RIGHT_SHIFT); $break ./
AssignmentOperator ::= '&='
/.$putCase consumeAssignmentOperator(AND); $break ./
AssignmentOperator ::= '^='
/.$putCase consumeAssignmentOperator(XOR); $break ./
AssignmentOperator ::= '|='
/.$putCase consumeAssignmentOperator(OR); $break ./
/:$readableName AssignmentOperator:/
/:$recovery_template =:/

Expression -> AssignmentExpression
/:$readableName Expression:/
/:$recovery_template Identifier:/

-- The following rules are for optional nonterminals.
--
ClassHeaderExtendsopt ::= $empty
ClassHeaderExtendsopt -> ClassHeaderExtends
/:$readableName ClassHeaderExtends:/

Expressionopt ::= $empty
/.$putCase consumeEmptyExpression(); $break ./
Expressionopt -> Expression
/:$readableName Expression:/

ConstantExpression -> Expression
/:$readableName ConstantExpression:/

---------------------------------------------------------------------------------------
--
-- The rules below are for optional terminal symbols.  An optional comma,
-- is only used in the context of an array initializer - It is a
-- "syntactic sugar" that otherwise serves no other purpose. By contrast,
-- an optional identifier is used in the definition of a break and 
-- continue statement. When the identifier does not appear, a NULL
-- is produced. When the identifier is present, the user should use the
-- corresponding TOKEN(i) method. See break statement as an example.
--
---------------------------------------------------------------------------------------

,opt -> $empty
,opt -> ,
/:$readableName ,:/

ClassBodyDeclarationsopt ::= $empty
/.$putCase consumeEmptyClassBodyDeclarationsopt(); $break ./
ClassBodyDeclarationsopt ::= NestedType ClassBodyDeclarations
/.$putCase consumeClassBodyDeclarationsopt(); $break ./
/:$readableName ClassBodyDeclarations:/

Modifiersopt ::= $empty 
/. $putCase consumeDefaultModifiers(); $break ./
Modifiersopt ::= Modifiers
/.$putCase consumeModifiers(); $break ./ 
/:$readableName Modifiers:/

BlockStatementsopt ::= $empty
/.$putCase consumeEmptyBlockStatementsopt(); $break ./
BlockStatementsopt -> BlockStatements
/:$readableName BlockStatements:/

Dimsopt ::= $empty
/. $putCase consumeEmptyDimsopt(); $break ./
Dimsopt -> Dims
/:$readableName Dimensions:/

ArgumentListopt ::= $empty
/. $putCase consumeEmptyArgumentListopt(); $break ./
ArgumentListopt -> ArgumentList
/:$readableName ArgumentList:/

MethodHeaderThrowsClauseopt ::= $empty
MethodHeaderThrowsClauseopt -> MethodHeaderThrowsClause
/:$readableName MethodHeaderThrowsClause:/

FormalParameterListopt ::= $empty
/.$putCase consumeFormalParameterListopt(); $break ./
FormalParameterListopt -> FormalParameterList
/:$readableName FormalParameterList:/

ClassHeaderImplementsopt ::= $empty
ClassHeaderImplementsopt -> ClassHeaderImplements
/:$readableName ClassHeaderImplements:/

InterfaceMemberDeclarationsopt ::= $empty
/. $putCase consumeEmptyInterfaceMemberDeclarationsopt(); $break ./
InterfaceMemberDeclarationsopt ::= NestedType InterfaceMemberDeclarations
/. $putCase consumeInterfaceMemberDeclarationsopt(); $break ./
/:$readableName InterfaceMemberDeclarations:/

NestedType ::= $empty 
/.$putCase consumeNestedType(); $break./
/:$readableName NestedType:/

ForInitopt ::= $empty
/. $putCase consumeEmptyForInitopt(); $break ./
ForInitopt -> ForInit
/:$readableName ForInit:/

ForUpdateopt ::= $empty
/. $putCase consumeEmptyForUpdateopt(); $break ./
ForUpdateopt -> ForUpdate
/:$readableName ForUpdate:/

InterfaceHeaderExtendsopt ::= $empty
InterfaceHeaderExtendsopt -> InterfaceHeaderExtends
/:$readableName InterfaceHeaderExtends:/

Catchesopt ::= $empty
/. $putCase consumeEmptyCatchesopt(); $break ./
Catchesopt -> Catches
/:$readableName Catches:/

-----------------------------------------------
-- 1.5 features : enum type
-----------------------------------------------
EnumDeclaration ::= EnumHeader EnumBody
/. $putCase consumeEnumDeclaration(); $break ./
/:$readableName EnumDeclaration:/

EnumHeader ::= EnumHeaderName ClassHeaderImplementsopt
/. $putCase consumeEnumHeader(); $break ./
/:$readableName EnumHeader:/

EnumHeaderName ::= Modifiersopt 'enum' Identifier
/. $putCase consumeEnumHeaderName(); $break ./
/:$compliance 1.5:/
EnumHeaderName ::= Modifiersopt 'enum' Identifier TypeParameters
/. $putCase consumeEnumHeaderNameWithTypeParameters(); $break ./
/:$readableName EnumHeaderName:/
/:$compliance 1.5:/

EnumBody ::= '{' EnumBodyDeclarationsopt '}'
/. $putCase consumeEnumBodyNoConstants(); $break ./
EnumBody ::= '{' ',' EnumBodyDeclarationsopt '}'
/. $putCase consumeEnumBodyNoConstants(); $break ./
EnumBody ::= '{' EnumConstants ',' EnumBodyDeclarationsopt '}'
/. $putCase consumeEnumBodyWithConstants(); $break ./
EnumBody ::= '{' EnumConstants EnumBodyDeclarationsopt '}'
/. $putCase consumeEnumBodyWithConstants(); $break ./
/:$readableName EnumBody:/

EnumConstants -> EnumConstant
EnumConstants ::= EnumConstants ',' EnumConstant
/.$putCase consumeEnumConstants(); $break ./
/:$readableName EnumConstants:/

EnumConstantHeaderName ::= Modifiersopt Identifier
/.$putCase consumeEnumConstantHeaderName(); $break ./
/:$readableName EnumConstantHeaderName:/

EnumConstantHeader ::= EnumConstantHeaderName ForceNoDiet Argumentsopt RestoreDiet
/.$putCase consumeEnumConstantHeader(); $break ./
/:$readableName EnumConstantHeader:/

EnumConstant ::= EnumConstantHeader ForceNoDiet ClassBody RestoreDiet
/.$putCase consumeEnumConstantWithClassBody(); $break ./
EnumConstant ::= EnumConstantHeader
/.$putCase consumeEnumConstantNoClassBody(); $break ./
/:$readableName EnumConstant:/

Arguments ::= '(' ArgumentListopt ')'
/.$putCase consumeArguments(); $break ./
/:$readableName Arguments:/

Argumentsopt ::= $empty
/.$putCase consumeEmptyArguments(); $break ./
Argumentsopt -> Arguments
/:$readableName Argumentsopt:/

EnumDeclarations ::= ';' ClassBodyDeclarationsopt
/.$putCase consumeEnumDeclarations(); $break ./
/:$readableName EnumDeclarations:/

EnumBodyDeclarationsopt ::= $empty
/.$putCase consumeEmptyEnumDeclarations(); $break ./
EnumBodyDeclarationsopt -> EnumDeclarations
/:$readableName EnumBodyDeclarationsopt:/

-----------------------------------------------
-- 1.5 features : enhanced for statement
-----------------------------------------------
EnhancedForStatement ::= EnhancedForStatementHeader Statement
/.$putCase consumeEnhancedForStatement(); $break ./
/:$readableName EnhancedForStatement:/

EnhancedForStatementNoShortIf ::= EnhancedForStatementHeader StatementNoShortIf
/.$putCase consumeEnhancedForStatement(); $break ./
/:$readableName EnhancedForStatementNoShortIf:/

EnhancedForStatementHeaderInit ::= 'for' '(' Type PushModifiers Identifier Dimsopt
/.$putCase consumeEnhancedForStatementHeaderInit(false); $break ./
/:$readableName EnhancedForStatementHeaderInit:/

EnhancedForStatementHeaderInit ::= 'for' '(' Modifiers Type PushRealModifiers Identifier Dimsopt
/.$putCase consumeEnhancedForStatementHeaderInit(true); $break ./
/:$readableName EnhancedForStatementHeaderInit:/

EnhancedForStatementHeader ::= EnhancedForStatementHeaderInit ':' Expression ')'
/.$putCase consumeEnhancedForStatementHeader(); $break ./
/:$readableName EnhancedForStatementHeader:/
/:$compliance 1.5:/

-----------------------------------------------
-- 1.5 features : static imports
-----------------------------------------------
SingleStaticImportDeclaration ::= SingleStaticImportDeclarationName ';'
/.$putCase consumeImportDeclaration(); $break ./
/:$readableName SingleStaticImportDeclaration:/

SingleStaticImportDeclarationName ::= 'import' 'static' Name
/.$putCase consumeSingleStaticImportDeclarationName(); $break ./
/:$readableName SingleStaticImportDeclarationName:/
/:$compliance 1.5:/

StaticImportOnDemandDeclaration ::= StaticImportOnDemandDeclarationName ';'
/.$putCase consumeImportDeclaration(); $break ./
/:$readableName StaticImportOnDemandDeclaration:/

StaticImportOnDemandDeclarationName ::= 'import' 'static' Name '.' '*'
/.$putCase consumeStaticImportOnDemandDeclarationName(); $break ./
/:$readableName StaticImportOnDemandDeclarationName:/
/:$compliance 1.5:/

-----------------------------------------------
-- 1.5 features : generics
-----------------------------------------------
TypeArguments ::= '<' TypeArgumentList1
/.$putCase consumeTypeArguments(); $break ./
/:$readableName TypeArguments:/
/:$compliance 1.5:/

OnlyTypeArguments ::= '<' TypeArgumentList1
/.$putCase consumeOnlyTypeArguments(); $break ./
/:$readableName TypeArguments:/
/:$compliance 1.5:/

TypeArgumentList1 -> TypeArgument1
/:$compliance 1.5:/
TypeArgumentList1 ::= TypeArgumentList ',' TypeArgument1
/.$putCase consumeTypeArgumentList1(); $break ./
/:$readableName TypeArgumentList1:/
/:$compliance 1.5:/

TypeArgumentList -> TypeArgument
/:$compliance 1.5:/
TypeArgumentList ::= TypeArgumentList ',' TypeArgument
/.$putCase consumeTypeArgumentList(); $break ./
/:$readableName TypeArgumentList:/
/:$compliance 1.5:/

TypeArgument ::= ReferenceType
/.$putCase consumeTypeArgument(); $break ./
/:$compliance 1.5:/
TypeArgument -> Wildcard
/:$readableName TypeArgument:/
/:$compliance 1.5:/

TypeArgument1 -> ReferenceType1
/:$compliance 1.5:/
TypeArgument1 -> Wildcard1
/:$readableName TypeArgument1:/
/:$compliance 1.5:/

ReferenceType1 ::= ReferenceType '>'
/.$putCase consumeReferenceType1(); $break ./
/:$compliance 1.5:/
ReferenceType1 ::= ClassOrInterface '<' TypeArgumentList2
/.$putCase consumeTypeArgumentReferenceType1(); $break ./
/:$readableName ReferenceType1:/
/:$compliance 1.5:/

TypeArgumentList2 -> TypeArgument2
/:$compliance 1.5:/
TypeArgumentList2 ::= TypeArgumentList ',' TypeArgument2
/.$putCase consumeTypeArgumentList2(); $break ./
/:$readableName TypeArgumentList2:/
/:$compliance 1.5:/

TypeArgument2 -> ReferenceType2
/:$compliance 1.5:/
TypeArgument2 -> Wildcard2
/:$readableName TypeArgument2:/
/:$compliance 1.5:/

ReferenceType2 ::= ReferenceType '>>'
/.$putCase consumeReferenceType2(); $break ./
/:$compliance 1.5:/
ReferenceType2 ::= ClassOrInterface '<' TypeArgumentList3
/.$putCase consumeTypeArgumentReferenceType2(); $break ./
/:$readableName ReferenceType2:/
/:$compliance 1.5:/

TypeArgumentList3 -> TypeArgument3
TypeArgumentList3 ::= TypeArgumentList ',' TypeArgument3
/.$putCase consumeTypeArgumentList3(); $break ./
/:$readableName TypeArgumentList3:/
/:$compliance 1.5:/

TypeArgument3 -> ReferenceType3
TypeArgument3 -> Wildcard3
/:$readableName TypeArgument3:/
/:$compliance 1.5:/

ReferenceType3 ::= ReferenceType '>>>'
/.$putCase consumeReferenceType3(); $break ./
/:$readableName ReferenceType3:/
/:$compliance 1.5:/

Wildcard ::= '?'
/.$putCase consumeWildcard(); $break ./
/:$compliance 1.5:/
Wildcard ::= '?' WildcardBounds
/.$putCase consumeWildcardWithBounds(); $break ./
/:$readableName Wildcard:/
/:$compliance 1.5:/

WildcardBounds ::= 'extends' ReferenceType
/.$putCase consumeWildcardBoundsExtends(); $break ./
/:$compliance 1.5:/
WildcardBounds ::= 'super' ReferenceType
/.$putCase consumeWildcardBoundsSuper(); $break ./
/:$readableName WildcardBounds:/
/:$compliance 1.5:/

Wildcard1 ::= '?' '>'
/.$putCase consumeWildcard1(); $break ./
/:$compliance 1.5:/
Wildcard1 ::= '?' WildcardBounds1
/.$putCase consumeWildcard1WithBounds(); $break ./
/:$readableName Wildcard1:/
/:$compliance 1.5:/

WildcardBounds1 ::= 'extends' ReferenceType1
/.$putCase consumeWildcardBounds1Extends(); $break ./
/:$compliance 1.5:/
WildcardBounds1 ::= 'super' ReferenceType1
/.$putCase consumeWildcardBounds1Super(); $break ./
/:$readableName WildcardBounds1:/
/:$compliance 1.5:/

Wildcard2 ::= '?' '>>'
/.$putCase consumeWildcard2(); $break ./
/:$compliance 1.5:/
Wildcard2 ::= '?' WildcardBounds2
/.$putCase consumeWildcard2WithBounds(); $break ./
/:$readableName Wildcard2:/
/:$compliance 1.5:/

WildcardBounds2 ::= 'extends' ReferenceType2
/.$putCase consumeWildcardBounds2Extends(); $break ./
/:$compliance 1.5:/
WildcardBounds2 ::= 'super' ReferenceType2
/.$putCase consumeWildcardBounds2Super(); $break ./
/:$readableName WildcardBounds2:/
/:$compliance 1.5:/

Wildcard3 ::= '?' '>>>'
/.$putCase consumeWildcard3(); $break ./
/:$compliance 1.5:/
Wildcard3 ::= '?' WildcardBounds3
/.$putCase consumeWildcard3WithBounds(); $break ./
/:$readableName Wildcard3:/
/:$compliance 1.5:/

WildcardBounds3 ::= 'extends' ReferenceType3
/.$putCase consumeWildcardBounds3Extends(); $break ./
/:$compliance 1.5:/
WildcardBounds3 ::= 'super' ReferenceType3
/.$putCase consumeWildcardBounds3Super(); $break ./
/:$readableName WildcardBound3:/
/:$compliance 1.5:/

TypeParameterHeader ::= Identifier
/.$putCase consumeTypeParameterHeader(); $break ./
/:$readableName TypeParameter:/
/:$compliance 1.5:/

TypeParameters ::= '<' TypeParameterList1
/.$putCase consumeTypeParameters(); $break ./
/:$readableName TypeParameters:/
/:$compliance 1.5:/

TypeParameterList -> TypeParameter
/:$compliance 1.5:/
TypeParameterList ::= TypeParameterList ',' TypeParameter
/.$putCase consumeTypeParameterList(); $break ./
/:$readableName TypeParameterList:/
/:$compliance 1.5:/

TypeParameter -> TypeParameterHeader
/:$compliance 1.5:/
TypeParameter ::= TypeParameterHeader 'extends' ReferenceType
/.$putCase consumeTypeParameterWithExtends(); $break ./
/:$compliance 1.5:/
TypeParameter ::= TypeParameterHeader 'extends' ReferenceType AdditionalBoundList
/.$putCase consumeTypeParameterWithExtendsAndBounds(); $break ./
/:$readableName TypeParameter:/
/:$compliance 1.5:/

AdditionalBoundList -> AdditionalBound
/:$compliance 1.5:/
AdditionalBoundList ::= AdditionalBoundList AdditionalBound
/.$putCase consumeAdditionalBoundList(); $break ./
/:$readableName AdditionalBoundList:/

AdditionalBound ::= '&' ReferenceType
/.$putCase consumeAdditionalBound(); $break ./
/:$readableName AdditionalBound:/
/:$compliance 1.5:/

TypeParameterList1 -> TypeParameter1
/:$compliance 1.5:/
TypeParameterList1 ::= TypeParameterList ',' TypeParameter1
/.$putCase consumeTypeParameterList1(); $break ./
/:$readableName TypeParameterList1:/
/:$compliance 1.5:/

TypeParameter1 ::= TypeParameterHeader '>'
/.$putCase consumeTypeParameter1(); $break ./
/:$compliance 1.5:/
TypeParameter1 ::= TypeParameterHeader 'extends' ReferenceType1
/.$putCase consumeTypeParameter1WithExtends(); $break ./
/:$compliance 1.5:/
TypeParameter1 ::= TypeParameterHeader 'extends' ReferenceType AdditionalBoundList1
/.$putCase consumeTypeParameter1WithExtendsAndBounds(); $break ./
/:$readableName TypeParameter1:/
/:$compliance 1.5:/

AdditionalBoundList1 -> AdditionalBound1
/:$compliance 1.5:/
AdditionalBoundList1 ::= AdditionalBoundList AdditionalBound1
/.$putCase consumeAdditionalBoundList1(); $break ./
/:$readableName AdditionalBoundList1:/
/:$compliance 1.5:/

AdditionalBound1 ::= '&' ReferenceType1
/.$putCase consumeAdditionalBound1(); $break ./
/:$readableName AdditionalBound1:/
/:$compliance 1.5:/

-------------------------------------------------
-- Duplicate rules to remove ambiguity for (x) --
-------------------------------------------------
PostfixExpression_NotName -> Primary
PostfixExpression_NotName -> PostIncrementExpression
PostfixExpression_NotName -> PostDecrementExpression
/:$readableName Expression:/

UnaryExpression_NotName -> PreIncrementExpression
UnaryExpression_NotName -> PreDecrementExpression
UnaryExpression_NotName ::= '+' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.PLUS); $break ./
UnaryExpression_NotName ::= '-' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.MINUS); $break ./
UnaryExpression_NotName -> UnaryExpressionNotPlusMinus_NotName
/:$readableName Expression:/

UnaryExpressionNotPlusMinus_NotName -> PostfixExpression_NotName
UnaryExpressionNotPlusMinus_NotName ::= '~' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.TWIDDLE); $break ./
UnaryExpressionNotPlusMinus_NotName ::= '!' PushPosition UnaryExpression
/.$putCase consumeUnaryExpression(OperatorIds.NOT); $break ./
UnaryExpressionNotPlusMinus_NotName -> CastExpression
/:$readableName Expression:/

MultiplicativeExpression_NotName -> UnaryExpression_NotName
MultiplicativeExpression_NotName ::= MultiplicativeExpression_NotName '*' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.MULTIPLY); $break ./
MultiplicativeExpression_NotName ::= Name '*' UnaryExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.MULTIPLY); $break ./
MultiplicativeExpression_NotName ::= MultiplicativeExpression_NotName '/' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.DIVIDE); $break ./
MultiplicativeExpression_NotName ::= Name '/' UnaryExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.DIVIDE); $break ./
MultiplicativeExpression_NotName ::= MultiplicativeExpression_NotName '%' UnaryExpression
/.$putCase consumeBinaryExpression(OperatorIds.REMAINDER); $break ./
MultiplicativeExpression_NotName ::= Name '%' UnaryExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.REMAINDER); $break ./
/:$readableName Expression:/

AdditiveExpression_NotName -> MultiplicativeExpression_NotName
AdditiveExpression_NotName ::= AdditiveExpression_NotName '+' MultiplicativeExpression
/.$putCase consumeBinaryExpression(OperatorIds.PLUS); $break ./
AdditiveExpression_NotName ::= Name '+' MultiplicativeExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.PLUS); $break ./
AdditiveExpression_NotName ::= AdditiveExpression_NotName '-' MultiplicativeExpression
/.$putCase consumeBinaryExpression(OperatorIds.MINUS); $break ./
AdditiveExpression_NotName ::= Name '-' MultiplicativeExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.MINUS); $break ./
/:$readableName Expression:/

ShiftExpression_NotName -> AdditiveExpression_NotName
ShiftExpression_NotName ::= ShiftExpression_NotName '<<'  AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.LEFT_SHIFT); $break ./
ShiftExpression_NotName ::= Name '<<'  AdditiveExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.LEFT_SHIFT); $break ./
ShiftExpression_NotName ::= ShiftExpression_NotName '>>'  AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.RIGHT_SHIFT); $break ./
ShiftExpression_NotName ::= Name '>>'  AdditiveExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.RIGHT_SHIFT); $break ./
ShiftExpression_NotName ::= ShiftExpression_NotName '>>>' AdditiveExpression
/.$putCase consumeBinaryExpression(OperatorIds.UNSIGNED_RIGHT_SHIFT); $break ./
ShiftExpression_NotName ::= Name '>>>' AdditiveExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.UNSIGNED_RIGHT_SHIFT); $break ./
/:$readableName Expression:/

RelationalExpression_NotName -> ShiftExpression_NotName
RelationalExpression_NotName ::= ShiftExpression_NotName '<'  ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.LESS); $break ./
RelationalExpression_NotName ::= Name '<'  ShiftExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.LESS); $break ./
RelationalExpression_NotName ::= ShiftExpression_NotName '>'  ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.GREATER); $break ./
RelationalExpression_NotName ::= Name '>'  ShiftExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.GREATER); $break ./
RelationalExpression_NotName ::= RelationalExpression_NotName '<=' ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.LESS_EQUAL); $break ./
RelationalExpression_NotName ::= Name '<=' ShiftExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.LESS_EQUAL); $break ./
RelationalExpression_NotName ::= RelationalExpression_NotName '>=' ShiftExpression
/.$putCase consumeBinaryExpression(OperatorIds.GREATER_EQUAL); $break ./
RelationalExpression_NotName ::= Name '>=' ShiftExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.GREATER_EQUAL); $break ./
/:$readableName Expression:/
-- <jml-start id="subtype-expression" />
--relational-expr ::= shift-expr '<:' shift-expr
RelationalExpression_NotName ::= Name '<:' ShiftExpression
/.$putCase /*jml*/consumeJmlSubtypeExpression(); $break ./
RelationalExpression_NotName ::= RelationalExpression_NotName '<:' ShiftExpression
/.$putCase /*jml*/consumeJmlSubtypeExpression(); $break ./
-- <jml-end id="subtype-expression" />
/:$readableName Expression:/

InstanceofExpression_NotName -> RelationalExpression_NotName
InstanceofExpression_NotName ::= Name 'instanceof' ReferenceType
/.$putCase consumeInstanceOfExpressionWithName(); $break ./
InstanceofExpression_NotName  ::= InstanceofExpression_NotName 'instanceof' ReferenceType
/.$putCase consumeInstanceOfExpression(); $break ./
/:$readableName Expression:/

EqualityExpression_NotName -> InstanceofExpression_NotName
EqualityExpression_NotName ::= EqualityExpression_NotName '==' InstanceofExpression
/.$putCase consumeEqualityExpression(OperatorIds.EQUAL_EQUAL); $break ./
EqualityExpression_NotName ::= Name '==' InstanceofExpression
/.$putCase consumeEqualityExpressionWithName(OperatorIds.EQUAL_EQUAL); $break ./
EqualityExpression_NotName ::= EqualityExpression_NotName '!=' InstanceofExpression
/.$putCase consumeEqualityExpression(OperatorIds.NOT_EQUAL); $break ./
EqualityExpression_NotName ::= Name '!=' InstanceofExpression
/.$putCase consumeEqualityExpressionWithName(OperatorIds.NOT_EQUAL); $break ./
/:$readableName Expression:/

AndExpression_NotName -> EqualityExpression_NotName
AndExpression_NotName ::= AndExpression_NotName '&' EqualityExpression
/.$putCase consumeBinaryExpression(OperatorIds.AND); $break ./
AndExpression_NotName ::= Name '&' EqualityExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.AND); $break ./
/:$readableName Expression:/

ExclusiveOrExpression_NotName -> AndExpression_NotName
ExclusiveOrExpression_NotName ::= ExclusiveOrExpression_NotName '^' AndExpression
/.$putCase consumeBinaryExpression(OperatorIds.XOR); $break ./
ExclusiveOrExpression_NotName ::= Name '^' AndExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.XOR); $break ./
/:$readableName Expression:/

InclusiveOrExpression_NotName -> ExclusiveOrExpression_NotName
InclusiveOrExpression_NotName ::= InclusiveOrExpression_NotName '|' ExclusiveOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.OR); $break ./
InclusiveOrExpression_NotName ::= Name '|' ExclusiveOrExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.OR); $break ./
/:$readableName Expression:/

ConditionalAndExpression_NotName -> InclusiveOrExpression_NotName
ConditionalAndExpression_NotName ::= ConditionalAndExpression_NotName '&&' InclusiveOrExpression
/.$putCase consumeBinaryExpression(OperatorIds.AND_AND); $break ./
ConditionalAndExpression_NotName ::= Name '&&' InclusiveOrExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.AND_AND); $break ./
/:$readableName Expression:/

ConditionalOrExpression_NotName -> ConditionalAndExpression_NotName
ConditionalOrExpression_NotName ::= ConditionalOrExpression_NotName '||' ConditionalAndExpression
/.$putCase consumeBinaryExpression(OperatorIds.OR_OR); $break ./
ConditionalOrExpression_NotName ::= Name '||' ConditionalAndExpression
/.$putCase consumeBinaryExpressionWithName(OperatorIds.OR_OR); $break ./
/:$readableName Expression:/

-- <jml-start id="level.0.expressions" />
ConditionalExpression_NotName -> EquivalenceExpression_NotName
ConditionalExpression_NotName ::= EquivalenceExpression_NotName '?' Expression ':' ConditionalExpression
-- <jml-end id="level.0.expressions" />
/.$putCase consumeConditionalExpression(OperatorIds.QUESTIONCOLON) ; $break ./
ConditionalExpression_NotName ::= Name '?' Expression ':' ConditionalExpression
/.$putCase consumeConditionalExpressionWithName(OperatorIds.QUESTIONCOLON) ; $break ./
/:$readableName Expression:/

AssignmentExpression_NotName -> ConditionalExpression_NotName
AssignmentExpression_NotName -> Assignment
/:$readableName Expression:/

Expression_NotName -> AssignmentExpression_NotName
/:$readableName Expression:/
-----------------------------------------------
-- 1.5 features : end of generics
-----------------------------------------------
-----------------------------------------------
-- 1.5 features : annotation - Metadata feature jsr175
-----------------------------------------------
AnnotationTypeDeclarationHeaderName ::= Modifiers '@' PushRealModifiers interface Identifier
/.$putCase consumeAnnotationTypeDeclarationHeaderName() ; $break ./
/:$compliance 1.5:/
AnnotationTypeDeclarationHeaderName ::= Modifiers '@' PushRealModifiers interface Identifier TypeParameters
/.$putCase consumeAnnotationTypeDeclarationHeaderNameWithTypeParameters() ; $break ./
/:$compliance 1.5:/
AnnotationTypeDeclarationHeaderName ::= '@' PushModifiersForHeader interface Identifier TypeParameters
/.$putCase consumeAnnotationTypeDeclarationHeaderNameWithTypeParameters() ; $break ./
/:$compliance 1.5:/
AnnotationTypeDeclarationHeaderName ::= '@' PushModifiersForHeader interface Identifier
/.$putCase consumeAnnotationTypeDeclarationHeaderName() ; $break ./
/:$readableName AnnotationTypeDeclarationHeaderName:/
/:$compliance 1.5:/

AnnotationTypeDeclarationHeader ::= AnnotationTypeDeclarationHeaderName ClassHeaderExtendsopt ClassHeaderImplementsopt
/.$putCase consumeAnnotationTypeDeclarationHeader() ; $break ./
/:$readableName AnnotationTypeDeclarationHeader:/
/:$compliance 1.5:/

AnnotationTypeDeclaration ::= AnnotationTypeDeclarationHeader AnnotationTypeBody
/.$putCase consumeAnnotationTypeDeclaration() ; $break ./
/:$readableName AnnotationTypeDeclaration:/
/:$compliance 1.5:/

AnnotationTypeBody ::= '{' AnnotationTypeMemberDeclarationsopt '}'
/:$readableName AnnotationTypeBody:/
/:$compliance 1.5:/

AnnotationTypeMemberDeclarationsopt ::= $empty
/.$putCase consumeEmptyAnnotationTypeMemberDeclarationsopt() ; $break ./
/:$compliance 1.5:/
AnnotationTypeMemberDeclarationsopt ::= NestedType AnnotationTypeMemberDeclarations
/.$putCase consumeAnnotationTypeMemberDeclarationsopt() ; $break ./
/:$readableName AnnotationTypeMemberDeclarations:/
/:$compliance 1.5:/

AnnotationTypeMemberDeclarations -> AnnotationTypeMemberDeclaration
/:$compliance 1.5:/
AnnotationTypeMemberDeclarations ::= AnnotationTypeMemberDeclarations AnnotationTypeMemberDeclaration
/.$putCase consumeAnnotationTypeMemberDeclarations() ; $break ./
/:$readableName AnnotationTypeMemberDeclarations:/
/:$compliance 1.5:/

AnnotationMethodHeaderName ::= Modifiersopt TypeParameters Type 'Identifier' '('
/.$putCase consumeMethodHeaderNameWithTypeParameters(true); $break ./
AnnotationMethodHeaderName ::= Modifiersopt Type 'Identifier' '('
/.$putCase consumeMethodHeaderName(true); $break ./
/:$readableName MethodHeaderName:/
/:$compliance 1.5:/

AnnotationMethodHeaderDefaultValueopt ::= $empty
/.$putCase consumeEmptyMethodHeaderDefaultValue() ; $break ./
/:$readableName MethodHeaderDefaultValue:/
/:$compliance 1.5:/
AnnotationMethodHeaderDefaultValueopt ::= DefaultValue
/.$putCase consumeMethodHeaderDefaultValue(); $break ./
/:$readableName MethodHeaderDefaultValue:/
/:$compliance 1.5:/

AnnotationMethodHeader ::= AnnotationMethodHeaderName FormalParameterListopt MethodHeaderRightParen MethodHeaderExtendedDims AnnotationMethodHeaderDefaultValueopt
/.$putCase consumeMethodHeader(); $break ./
/:$readableName AnnotationMethodHeader:/
/:$compliance 1.5:/

AnnotationTypeMemberDeclaration ::= AnnotationMethodHeader ';'
/.$putCase consumeAnnotationTypeMemberDeclaration() ; $break ./
/:$compliance 1.5:/
AnnotationTypeMemberDeclaration -> ConstantDeclaration
/:$compliance 1.5:/
AnnotationTypeMemberDeclaration -> ConstructorDeclaration
/:$compliance 1.5:/
AnnotationTypeMemberDeclaration -> TypeDeclaration
/:$readableName AnnotationTypeMemberDeclaration:/
/:$compliance 1.5:/

DefaultValue ::= 'default' MemberValue
/:$readableName DefaultValue:/
/:$compliance 1.5:/

Annotation -> NormalAnnotation
/:$compliance 1.5:/
Annotation -> MarkerAnnotation
/:$compliance 1.5:/
Annotation -> SingleMemberAnnotation
/:$readableName Annotation:/
/:$compliance 1.5:/

AnnotationName ::= '@' Name
/.$putCase consumeAnnotationName() ; $break ./
/:$readableName AnnotationName:/
/:$compliance 1.5:/

NormalAnnotation ::= AnnotationName '(' MemberValuePairsopt ')'
/.$putCase consumeNormalAnnotation() ; $break ./
/:$readableName NormalAnnotation:/
/:$compliance 1.5:/

MemberValuePairsopt ::= $empty
/.$putCase consumeEmptyMemberValuePairsopt() ; $break ./
/:$compliance 1.5:/
MemberValuePairsopt -> MemberValuePairs
/:$readableName MemberValuePairsopt:/
/:$compliance 1.5:/

MemberValuePairs -> MemberValuePair
/:$compliance 1.5:/
MemberValuePairs ::= MemberValuePairs ',' MemberValuePair
/.$putCase consumeMemberValuePairs() ; $break ./
/:$readableName MemberValuePairs:/
/:$compliance 1.5:/

MemberValuePair ::= SimpleName '=' EnterMemberValue MemberValue ExitMemberValue
/.$putCase consumeMemberValuePair() ; $break ./
/:$readableName MemberValuePair:/
/:$compliance 1.5:/

EnterMemberValue ::= $empty
/.$putCase consumeEnterMemberValue() ; $break ./
/:$readableName EnterMemberValue:/
/:$compliance 1.5:/

ExitMemberValue ::= $empty
/.$putCase consumeExitMemberValue() ; $break ./
/:$readableName ExitMemberValue:/
/:$compliance 1.5:/

MemberValue -> ConditionalExpression_NotName
/:$compliance 1.5:/
MemberValue ::= Name
/.$putCase consumeMemberValueAsName() ; $break ./
/:$compliance 1.5:/
MemberValue -> Annotation
/:$compliance 1.5:/
MemberValue -> MemberValueArrayInitializer
/:$readableName MemberValue:/
/:$recovery_template Identifier:/
/:$compliance 1.5:/

MemberValueArrayInitializer ::= EnterMemberValueArrayInitializer '{' PushLeftBrace MemberValues ',' '}'
/.$putCase consumeMemberValueArrayInitializer() ; $break ./
/:$compliance 1.5:/
MemberValueArrayInitializer ::= EnterMemberValueArrayInitializer '{' PushLeftBrace MemberValues '}'
/.$putCase consumeMemberValueArrayInitializer() ; $break ./
/:$compliance 1.5:/
MemberValueArrayInitializer ::= EnterMemberValueArrayInitializer '{' PushLeftBrace ',' '}'
/.$putCase consumeEmptyMemberValueArrayInitializer() ; $break ./
/:$compliance 1.5:/
MemberValueArrayInitializer ::= EnterMemberValueArrayInitializer '{' PushLeftBrace '}'
/.$putCase consumeEmptyMemberValueArrayInitializer() ; $break ./
/:$readableName MemberValueArrayInitializer:/
/:$compliance 1.5:/

EnterMemberValueArrayInitializer ::= $empty
/.$putCase consumeEnterMemberValueArrayInitializer() ; $break ./
/:$readableName EnterMemberValueArrayInitializer:/
/:$compliance 1.5:/

MemberValues -> MemberValue
/:$compliance 1.5:/
MemberValues ::= MemberValues ',' MemberValue
/.$putCase consumeMemberValues() ; $break ./
/:$readableName MemberValues:/
/:$compliance 1.5:/

MarkerAnnotation ::= AnnotationName
/.$putCase consumeMarkerAnnotation() ; $break ./
/:$readableName MarkerAnnotation:/
/:$compliance 1.5:/

SingleMemberAnnotationMemberValue ::= MemberValue
/.$putCase consumeSingleMemberAnnotationMemberValue() ; $break ./
/:$readableName MemberValue:/
/:$compliance 1.5:/

SingleMemberAnnotation ::= AnnotationName '(' SingleMemberAnnotationMemberValue ')'
/.$putCase consumeSingleMemberAnnotation() ; $break ./
/:$readableName SingleMemberAnnotation:/
/:$compliance 1.5:/
--------------------------------------
-- 1.5 features : end of annotation --
--------------------------------------

-----------------------------------
-- JML level 0-1-a : START       --
-----------------------------------
UnusedMarkerOfStartOfJmlSection ::= '*'

SpecExpression -> Expression

-- (should be) level 0
-- jml-primary // alternatives are presented in alphabetical order
--  ::=  '\elemtype' '(' spec-expression ')'
--   | '\fresh' '(' spec-expression-list ')'
--   | informal-description  
--   | '\nonnullelements' '(' spec-expression ')'
--   | old-expression
--   | quantified-expr
--   | '\result' 
--   | '\type' '(' spec-expression ')'
--   | '\typeof' '(' spec-expression ')'
--   | jml-store-ref-range

JmlPrimary
  ::= slash_elemtype '(' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlElemtypeExpression(OperatorIds.JML_ELEMTYPE); $break ./
	| slash_fresh '(' ArgumentList ')'
		/.$putCase /*jml*/consumeJmlFreshExpression(); $break ./
	| 'InformalDescription'
	| slash_nonnullelements '(' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NONNULLELEMENTS); $break ./
	| JmlOldExpression
	| JmlQuantifiedExpression
	| 'slash_result'
		/.$putCase /*jml*/consumeJmlPrimaryResult(); $break ./
	| 'slash_type' '(' Type ')'
		/.$putCase /*jml*/consumeJmlTypeExpression(OperatorIds.JML_TYPE); $break ./
	| slash_typeof '(' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlTypeofExpression(OperatorIds.JML_TYPEOF); $break ./
	| JmlOperationOverStoreRefs
	| JmlMultiReferenceExpression
	/:$readableName JmlPrimary:/

JmlOperationOverStoreRefs 
  ::= 'slash_not_assigned' JmlStoreRefListAsUnaryArgument
		/.$putCase /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NOT_ASSIGNED); $break ./
	| 'slash_not_modified' JmlStoreRefListAsUnaryArgument
		/.$putCase /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_NOT_MODIFIED); $break ./
--	| other operators like \only_assigned() ... can easily be addeded here.

JmlStoreRefListAsUnaryArgument ::= '(' StoreRefSeq ')'
	/.$putCase /*jml*/consumeJmlStoreRefSeqAsStoreRefListExpression(); $break ./

JmlStoreRefExpression -> JmlReferenceExpression

JmlReferenceExpression 
  ::= Name -- consumePostfixExpression() pops a Name and pushes an Expression.
		/.$putCase consumePostfixExpression(); $break ./
	| Primary

JmlMultiReferenceExpression ::= Name '.' '*'
		/.$putCase /*jml*/consumeJmlMultiReferenceExpressionAsNameDotStar(); $break ./
	| JmlMultiFieldAccess
	| JmlArrayRangeAccess

JmlMultiFieldAccess ::= Primary '.' '*'
		/.$putCase /*jml*/consumeJmlMultiFieldAccess(false); $break ./
	| 'super' '.' '*'
		/.$putCase /*jml*/consumeJmlMultiFieldAccess(true); $break ./

JmlArrayRangeAccess ::= Name '[' JmlArrayIndexRange ']'
		/.$putCase /*jml*/consumeJmlArrayRangeAccess(true); $break ./
	| PrimaryNoNewArray '[' JmlArrayIndexRange ']' -- PrimaryNoNewArray
		/.$putCase /*jml*/consumeJmlArrayRangeAccess(false); $break ./

JmlArrayIndexRange ::= '*'
		/.$putCase /*jml*/consumeJmlArrayIndexRange(0); $break ./
	| '..' Expression
		/.$putCase /*jml*/consumeJmlArrayIndexRange(1); $break ./
	| Expression '..'
		/.$putCase /*jml*/consumeJmlArrayIndexRange(-1); $break ./
	| Expression '..' Expression
		/.$putCase /*jml*/consumeJmlArrayIndexRange(2); $break ./

-- store-ref-seq ::= store-ref [ ',' store-ref ]...
StoreRefSeq ::= ArgumentList

StoreRefKeyword -> 'slash_nothing' | 'slash_everything' | 'slash_not_specified'

StoreRefSeqOrKeyword ::= StoreRefKeyword | StoreRefSeq
	/.$putCase /*jml*/consumeJmlStoreRefSeqAsStoreRefListExpression(); $break ./

-- old-expression ::= '\old' '(' spec-expression [ ',' ident ] ')'
--                 |  '\pre' '(' spec-expression ')'
JmlOldExpression ::= slash_old '(' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlPrimaryOldExpression(OperatorIds.JML_OLD); $break ./
	| slash_old '(' SpecExpression ',' Identifier ')'
		/.$putCase /*jml*/consumeJmlPrimaryLabeledOldExpression(OperatorIds.JML_OLD); $break ./
	| slash_pre '(' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlUnaryExpression(OperatorIds.JML_PRE); $break ./

--quantified-expr ::= '(' quantifier quantified-var-decls ';'
--                            [ [ predicate ] ';' ]
--                            spec-expression ')'
JmlQuantifiedExpression ::= '(' JmlQuantifier JmlTypeSpec JmlQuantifiedVarDeclarators ';' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlQuantifiedExpression(false); $break ./
	| '(' JmlQuantifier JmlTypeSpec JmlQuantifiedVarDeclarators ';' ';' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlQuantifiedExpression(false); $break ./
	| '(' JmlQuantifier JmlTypeSpec JmlQuantifiedVarDeclarators ';' Predicate ';' SpecExpression ')'
		/.$putCase /*jml*/consumeJmlQuantifiedExpression(true); $break ./

-- bound variable type-spec is restricted to primitive types and reference types, possibly with nullity modifiers
-- (but not with ownership modifiers, which is why we don't just use "Type" in the above productions)

JmlTypeSpec ::= PrimitiveType
		/.$putCase consumePrimitiveType(); $break ./
	| NullityModifier PrimitiveType
		/.$putCase consumePrimitiveType(); $break ./
	| ReferenceType
		/.$putCase /*jml*/consumeReferenceTypeWithoutOwnershipModifiers(); $break ./

--quantified-var-decls ::= [ bound-var-modifiers ] type-spec quantified-var-declarator
--                         [ , quantified-var-declarator ] ...
--quantified-var-declarator ::= ident [ dims ]

JmlQuantifiedVarDeclarators ::= Identifier Dimsopt
		/.$putCase /*jml*/consumeJmlQuantifiedVarDeclarators(true); $break ./
	| JmlQuantifiedVarDeclarators ',' Identifier Dimsopt
		/.$putCase /*jml*/consumeJmlQuantifiedVarDeclarators(false); $break ./

--spec-variable-declarators ::= spec-variable-declarator [ , spec-variable-declarator ] ...
--bound-var-modifiers ::= non_null | nullable

JmlQuantifier -> 'slash_forall' | 'slash_exists'
	| 'slash_max' | 'slash_min' 
	| 'slash_num_of' | 'slash_product' | 'slash_sum'

-- set-comprehension ::= { [ bound-var-modifiers ] type-spec quantified-var-declarator `|' set-comprehension-pred }
-- set-comprehension-pred ::= postfix-expr . has ( ident ) && predicate                                    
JmlSetComprehension ::= '{' JmlTypeSpec Identifier Dimsopt '|' PostfixExpression && Predicate '}'
	/.$putCase /*jml*/consumeJmlSetComprehension(); $break ./

-- ----------------------------------------------------------------------------
-- JML Type Body Declarations
--
--checked(jmlMember ::= mods (... jmlDeclaration... | axiom)(jmlDeclaration = "invariant" predicate)
--should be -> jml-declaration ::= modifiers invariant | modifiers history-constraint | modifiers represents-clause | modifiers initially-clause | modifiers monitors-for-clause | modifiers readable-if-clause | modifiers writable-if-clause | axiom-clause
--for level0-> jml-declaration ::= modifiers invariant |                                modifiers represents-clause | modifiers initially-clause
--for level1-> jml-declaration ::= modifiers invariant | modifiers history-constraint | modifiers represents-clause | modifiers initially-clause| axiom-clause
--for now is-> jml-declaration ::= modifiers invariant | modifiers history-constraint | modifiers represents-clause | modifiers initially-clause
JmlTypeBodyDeclaration ::= Modifiersopt JmlInvariantDeclaration
		/.$putCase /*jml*/consumeJmlTypeBodyDeclaration(); $break ./
	| Modifiersopt JmlConstraintDeclaration
		/.$putCase /*jml*/consumeJmlTypeBodyDeclaration(); $break ./
	| Modifiersopt JmlRepresentsClause
		/.$putCase /*jml*/consumeJmlTypeBodyDeclaration(); $break ./
	| Modifiersopt JmlInitiallyClause
		/.$putCase /*jml*/consumeJmlTypeBodyDeclaration(); $break ./

JmlInvariantDeclaration ::=  'invariant' Predicate ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

--should be -> history-constraint ::= constraint-keyword predicate [ for constrained-list ] ;
--for now is-> history-constraint ::= 'constraint' predicate                          ;
--should be -> constraint-keyword ::= constraint | constraint_redundantly
--for now is-> constraint-keyword ::= constraint
--should be -> constrained-list ::= method-name-list | \everything
--should be -> method-name-list ::= method-name [ , method-name ] ...
--should be -> method-name ::= method-ref [ ( [ param-disambig-list ] ) ] | method-ref-start . * 
--should be -> method-ref ::= method-ref-start [ . method-ref-rest ] ...
--                          | new reference-type
--should be -> method-ref-start ::=  super | this | ident
--should be -> method-ref-rest ::=  this | ident
--should be -> param-disambig-list ::= param-disambig [ , param-disambig ] ...
--should be -> param-disambig ::= type-spec [ ident [ dims ] ]
JmlConstraintDeclaration ::= 'constraint' Predicate ExitJmlClause ';'
	/.$putCase /*jml*/consumeConstraintDeclaration(); $break ./

--should be -> represents-clause ::= represents-keyword store-ref-expression l-arrow-or-eq spec-expression ';' // level 0
--                                |  represents-keyword store-ref-expression '\such_that' predicate ';'        // level 1
--for now is-> represents-clause ::= represents-keyword store-ref-expression l-arrow-or-eq spec-expression ';' // level 0
JmlRepresentsClause ::= RepresentsOrRepresentsRedundantly JmlStoreRefExpression '=' SpecExpression ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

--should be -> l-arrow-or-eq ::= '<-' | '='
--for now is-> l-arrow-or-eq ::= '='

RepresentsOrRepresentsRedundantly -> 'represents' | 'represents_redundantly' 

JmlInitiallyClause ::=  'initially' Predicate ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

--class-initializer-decl ::= [ method-specification ] [ static ] compound-statement
--        | method-specification static_initializer 
--        | method-specification initializer 
                  
-- method-specification ::= ['also'] ( spec-case-seq [ method-spec-redundant-part ] | method-spec-redundant-part )
MethodSpecification ::= 'also' SpecCaseSeq
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ false); $break ./
	| SpecCaseSeq
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ false); $break ./
	| 'also' SpecCaseSeq MethodSpecRedundantPart
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ true); $break ./
	| SpecCaseSeq MethodSpecRedundantPart
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ true, /*hasRedundantPart*/ true); $break ./
	| 'also' MethodSpecRedundantPart
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ true, /*hasSpecCaseSeq*/ false, /*hasRedundantPart*/ true); $break ./
	| MethodSpecRedundantPart
		/.$putCase /*jml*/consumeMethodSpecification(/*isExtending*/ false, /*hasSpecCaseSeq*/ false, /*hasRedundantPart*/ true); $break ./

--should be -> method-spec-redundant-part ::= 'implies_that' spec-case-seq [ examples ] | examples
MethodSpecRedundantPart ::= 'implies_that' SpecCaseSeq
	/.$putCase /*jml*/consumeMethodSpecRedundantPart(); $break ./

--spec-case-seq ::= spec-case [ 'also' spec-case ] ...
SpecCaseSeq ::= SpecCase | SpecCaseSeq 'also' SpecCase
	/.$putCase /*jml*/consumeSpecCaseSeq(); $break ./

--(for level 2 add) spec-case ::= model-program
SpecCase -> LightweightSpecCase | HeavyweightSpecCase

LightweightSpecCase ::= SpecCaseBody
	/.$putCase /*jml*/consumeLightweightSpecCase(); $break ./

--not checked
--should be -> heavyweight-spec-case ::= [ java-visibility-keyword ] [ 'code' ] behavior-keyword spec-case-body
--for now is-> heavyweight-spec-case ::= modifiers                              behavior-keyword spec-case-body
HeavyweightSpecCase ::= Modifiersopt 'BehaviorOrSynonym' SpecCaseBody
	/.$putCase /*jml*/consumeHeavyweightSpecCase(); $break ./

-- spec-case-body ::= spec-var-decls ( spec-case-header [ spec-case-rest ] | spec-case-rest )
SpecCaseBody ::= JmlSpecVarDecls SpecCaseRest
		/.$putCase /*jml*/consumeSpecCaseBody(/*hasHeader*/false, /*hasRest*/true); $break ./
	| JmlSpecVarDecls SpecCaseHeader
		/.$putCase /*jml*/consumeSpecCaseBody(/*hasHeader*/true, /*hasRest*/false); $break ./
	| JmlSpecVarDecls SpecCaseHeader SpecCaseRest
		/.$putCase /*jml*/consumeSpecCaseBody(/*hasHeader*/true, /*hasRest*/true); $break ./

--spec-var-decls ::= forall-var-decls old-var-decls
JmlSpecVarDecls ->  StartSpecVarDecls JmlForallVarDecls JmlOldVarDecls
StartSpecVarDecls ::= $empty /.$putCase /*jml*/consumeStartSpecVarDecls(); $break ./

--forall-var-decls ::= [ forall-var-declarator ] ...
JmlForallVarDecls ::= $empty 
		/.$putCase /*jml*/consumeEmptyJmlSpecVarDecls(); $break ./
	| JmlForallVarDecls JmlForallVarDecl
		/.$putCase /*jml*/consumeJmlVarDecls(); $break ./
--forall-var-declarator ::= 'forall' local-var-decl ';'
JmlForallVarDecl -> 'forall' LocalVariableDeclarationStatement

--old-var-decls ::= [ old-var-declarator ] ...
JmlOldVarDecls ::= $empty 
		/.$putCase /*jml*/consumeEmptyJmlSpecVarDecls(); $break ./
	| JmlOldVarDecls JmlOldVarDecl
		/.$putCase /*jml*/consumeJmlVarDecls(); $break ./
--old-var-declarator ::= 'old' local-var-decl ';'
JmlOldVarDecl -> 'old' LocalVariableDeclarationStatement

--(should be) level 1 (redundancy & examples)
--redundant-spec ::= implications [ examples ] | examples
--implications ::= implies_that spec-case-seq
--examples ::= for_example example [ 'also' example ]
--example ::= [ [ privacy ] example ] [ spec-var-decls ] [ spec-header ] simple-spec-body
--        | [ privacy ] exceptional_example [ spec-var-decls ] spec-header [ exceptional-example-body ]
--        | [ privacy ] exceptional_example [ spec-var-decls ] exceptional-example-body
--        | [ privacy ] normal_example [ spec-var-decls ] spec-header [ normal-example-body ]
--        | [ privacy ] normal_example [ spec-var-decls ] normal-example-body
--exceptional-example-body ::= exceptional-spec-clause [ exceptional-spec-clause ]
--normal-example-body ::= normal-spec-clause [ normal-spec-clause ]
                        
--checked (modified to allow old-var-declarations here)
--should be -> spec-case-header ::= (old-var-declarator | requires-clause) ...
--for now is-> spec-case-header ::= requires-clause-seq
SpecCaseHeader ::= RequiresClauseSeq
	/.$putCase /*jml*/consumeSpecCaseHeader(); $break ./

RequiresClauseSeq ::= RequiresClause
	| RequiresClauseSeq RequiresClause
		/.$putCase /*jml*/consumeRequiresClauseSeq(); $break ./

-- spec-case-rest ::= spec-case-rest-clause-seq | spec-case-block
SpecCaseRest ::= SpecCaseBlock
	| SpecCaseRestClauseSeq
		/.$putCase /*jml*/consumeSpecCaseRestAsClauseSeq(); $break ./

-- spec-case-block ::= '{|' spec-case-body [ 'also' spec-case-body ] ... '|}'
SpecCaseBlock ::= LBRACE_OR SpecCaseBodySeq OR_RBRACE
	/.$putCase /*jml*/consumeSpecCaseBlock(); $break ./

SpecCaseBodySeq ::= SpecCaseBody
	| SpecCaseBodySeq 'also' SpecCaseBody
		/.$putCase /*jml*/consumeSpecCaseBodySeq(); $break ./

-- spec-case-rest-clause-seq ::= spec-case-rest-clause [ spec-case-rest-clause ] ...
SpecCaseRestClauseSeq ::= SpecCaseRestClause
	| SpecCaseRestClauseSeq SpecCaseRestClause
		/.$putCase /*jml*/consumeSpecCaseRestClauseSeq(); $break ./
 
--should be -> spec-case-rest-clause ::= 
--               assignable-clause | captures-clause | diverges-clause | duration-clause
--             | ensures-clause | signals-only-clause | signals-clause
--             | when-clause | working-space-clause
--for now is-> spec-case-rest-clause ::= 
--               assignable-clause | diverges-clause | ensures-clause | signals-only-clause | signals-clause
SpecCaseRestClause -> AssignableClause  | DivergesClause | EnsuresClause 
	| SignalsClause | SignalsOnlyClause

-- assignable-clause ::= assignable-or-assignable-redundantly store-ref-list-or-keyword ';'
AssignableClause ::= AssignableOrAssignableRedundantly StoreRefSeqOrKeyword ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

AssignableOrAssignableRedundantly -> 'AssignableOrSynonym' | 'AssignableRedundantlyOrSynonym'

DivergesClause ::= DivergesOrDivergesRedundantly PredicateOrNotSpecified ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

DivergesOrDivergesRedundantly -> 'diverges' | 'diverges_redundantly'

EnsuresClause ::= EnsuresOrEnsuresRedundantly PredicateOrNotSpecified ExitJmlClause ';'
	/.$putCase /*jml*/consumeJmlClause(); $break ./

EnsuresOrEnsuresRedundantly -> 'EnsuresOrSynonym' | 'EnsuresRedundantlyOrSynonym'

-- requires-clause ::= requires-or-requires-redundantly ( predicate-or-not-specified | '\same' ) ';'
RequiresClause ::= 
	RequiresOrRequiresRedundantly PredicateOrNotSpecified ExitJmlClause ';'
		/.$putCase /*jml*/consumeJmlClause(); $break ./
	| RequiresOrRequiresRedundantly 'slash_same' ExitJmlClause ';'
		/.$putCase /*jml*/consumeJmlClause(); $break ./

RequiresOrRequiresRedundantly -> 'RequiresOrSynonym' | 'RequiresRedundantlyOrSynonym'

-- signals-clause ::= signals-keyword ( reference-type [ ident ] ) [ predicate-or-not-specified ] ';'
-- If we consider requiring ident, then use FormalParameter instead of ClassType 'Identifier'.
SignalsClause ::= 
	SignalsOrSignalsRedundantly '(' ClassType ')' PredicateOrNotSpecifiedopt ExitJmlClause ';'
		/.$putCase /*jml*/consumeSignalsClause(/*hasIdentifier*/false); $break ./
	| SignalsOrSignalsRedundantly '(' ClassType 'Identifier' ')' PredicateOrNotSpecifiedopt ExitJmlClause ';'
		/.$putCase /*jml*/consumeSignalsClause(/*hasIdentifier*/true); $break ./

PredicateOrNotSpecifiedopt ::= $empty /.$putCase consumeEmptyExpression(); $break ./
	| PredicateOrNotSpecified

--signals-keyword ::= signals | signals_redundantly | exsures | exsures_redundantly
SignalsOrSignalsRedundantly -> 'SignalsOrSynonym' | 'SignalsRedundantlyOrSynonym' 

--signals-only-clause ::= signals-only-keyword reference-type [ , reference-type ] ... ;
--                     | signals-only-keyword \nothing ;
SignalsOnlyClause 
  ::= SignalsOnlyOrSignalsOnlyRedundantly ClassTypeList ExitJmlClause ';'
		/.$putCase /*jml*/consumeSignalsOnlyClause(); $break ./
	| SignalsOnlyOrSignalsOnlyRedundantly 'slash_nothing' ExitJmlClause ';'
		/.$putCase /*jml*/consumeSignalsOnlyClauseNothing(); $break ./

SignalsOnlyOrSignalsOnlyRedundantly -> 'signals_only' | 'signals_only_redundantly' 

Predicate -> Expression
PredicateOrNotSpecified -> Predicate | 'slash_not_specified'

ExitJmlClause ::= $empty /.$putCase /*jml*/consumeExitJmlClause(); $break ./

JmlDataGroupClauseSeq ::= JmlDataGroupClause
	| JmlDataGroupClauseSeq JmlDataGroupClause
		/.$putCase /*jml*/consumeDataGroupClauseSeq(); $break ./

JmlDataGroupClause -> InDataGroupClause | MapsIntoClause

InDataGroupClause ::= InKeyword DataGroupNameList ExitJmlClause ';'
	/.$putCase /*jml*/consumeInDataGroupClause(); $break ./

InKeyword -> 'in' | 'in_redundantly'

--data-group-name-list ::= data-group-name [ , data-group-name ] ...
DataGroupNameList -> ArgumentList

MapsIntoClause ::= MapsKeyword MemberFieldRef 'slash_into' DataGroupNameList ExitJmlClause ';'
	/.$putCase /*jml*/consumeMapsIntoClause(); $break ./

MapsKeyword -> 'maps' | 'maps_redundantly'
MemberFieldRef -> JmlReferenceExpression

-----------------------------------
-- JML level 0-1-a : END         --
-----------------------------------

-----------------------------------
-- 1.5 features : recovery rules --
-----------------------------------
RecoveryMethodHeaderName ::= Modifiersopt TypeParameters Type 'Identifier' '('
/.$putCase consumeRecoveryMethodHeaderNameWithTypeParameters(); $break ./
/:$compliance 1.5:/
RecoveryMethodHeaderName ::= Modifiersopt Type 'Identifier' '('
/.$putCase consumeRecoveryMethodHeaderName(); $break ./
/:$readableName MethodHeaderName:/

RecoveryMethodHeader ::= RecoveryMethodHeaderName FormalParameterListopt MethodHeaderRightParen MethodHeaderExtendedDims AnnotationMethodHeaderDefaultValueopt
/.$putCase consumeMethodHeader(); $break ./
RecoveryMethodHeader ::= RecoveryMethodHeaderName FormalParameterListopt MethodHeaderRightParen MethodHeaderExtendedDims MethodHeaderThrowsClause
/.$putCase consumeMethodHeader(); $break ./
/:$readableName MethodHeader:/
-----------------------------------
-- 1.5 features : end of recovery rules --
-----------------------------------

/.	}
}./

$names

-- <jml-start id="level.0-1-a" />
LBRACE_OR ::= '{|'
OR_RBRACE ::= '|}'
-- <jml-end id="level.0-1-a" />
PLUS_PLUS ::=    '++'   
MINUS_MINUS ::=    '--'   
EQUAL_EQUAL ::=    '=='   
LESS_EQUAL ::=    '<='   
GREATER_EQUAL ::=    '>='   
NOT_EQUAL ::=    '!='   
LEFT_SHIFT ::=    '<<'   
RIGHT_SHIFT ::=    '>>'   
UNSIGNED_RIGHT_SHIFT ::=    '>>>'  
PLUS_EQUAL ::=    '+='   
MINUS_EQUAL ::=    '-='   
MULTIPLY_EQUAL ::=    '*='   
DIVIDE_EQUAL ::=    '/='   
AND_EQUAL ::=    '&='   
OR_EQUAL ::=    '|='   
XOR_EQUAL ::=    '^='   
REMAINDER_EQUAL ::=    '%='   
LEFT_SHIFT_EQUAL ::=    '<<='  
RIGHT_SHIFT_EQUAL ::=    '>>='  
UNSIGNED_RIGHT_SHIFT_EQUAL ::=    '>>>=' 
OR_OR ::=    '||'   
AND_AND ::=    '&&'
PLUS ::=    '+'    
MINUS ::=    '-'    
NOT ::=    '!'    
REMAINDER ::=    '%'    
XOR ::=    '^'    
AND ::=    '&'    
MULTIPLY ::=    '*'    
OR ::=    '|'    
TWIDDLE ::=    '~'    
DIVIDE ::=    '/'    
GREATER ::=    '>'    
LESS ::=    '<'    
LPAREN ::=    '('    
RPAREN ::=    ')'    
LBRACE ::=    '{'    
RBRACE ::=    '}'    
LBRACKET ::=    '['    
RBRACKET ::=    ']'    
SEMICOLON ::=    ';'    
QUESTION ::=    '?'    
COLON ::=    ':'    
COMMA ::=    ','    
DOT ::=    '.'    
EQUAL ::=    '='    
AT ::=    '@'    
ELLIPSIS ::=    '...'    
-- <jml-start id="assignableClause" />
DOTDOT ::= '..'
-- <jml-end id="assignableClause" />
-- <jml-start id="subtype-expression" />
SUBTYPE ::= '<:'
-- <jml-end id="subtype-expression" />
$end
-- need a carriage return after the $end
