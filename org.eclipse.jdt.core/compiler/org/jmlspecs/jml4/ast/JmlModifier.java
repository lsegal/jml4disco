package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.AnnotationBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeConstants;

/**
 * This class offers services for processing JML modifiers.
 * Note that non_null, nullable and the *_by_default modifiers are not handled here (yet).
 */
public class JmlModifier {

	private JmlModifier() {
		//@ assert false;
	}

	// Bit masks for JML modifiers
	public static final long CODE_BIGINT_MATH = ASTNode.Bit1;
	public static final long CODE_JAVA_MATH   = ASTNode.Bit2;
	public static final long CODE_SAFE_MATH   = ASTNode.Bit3;
	public static final long GHOST            = ASTNode.Bit4;
	public static final long HELPER           = ASTNode.Bit5;
	public static final long INSTANCE         = ASTNode.Bit6;
	public static final long MODEL            = ASTNode.Bit7;
	public static final long PURE             = ASTNode.Bit8;
	public static final long SPEC_PUBLIC      = ASTNode.Bit9;
	public static final long SPEC_PROTECTED   = ASTNode.Bit10;
	public static final long SPEC_BIGINT_MATH = ASTNode.Bit11;
	public static final long SPEC_JAVA_MATH   = ASTNode.Bit12;
	public static final long SPEC_SAFE_MATH   = ASTNode.Bit13;
	public static final long UNINITIALIZED    = ASTNode.Bit14;
	public static final long PEER             = ASTNode.Bit15;
	public static final long READONLY         = ASTNode.Bit16;
	public static final long REP              = ASTNode.Bit17;

	// JML modifier names
	private static final char[] JML_MODIFIER_CODE_BIGINT_MATH = "code_bigint_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_CODE_JAVA_MATH = "code_java_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_CODE_SAFE_MATH = "code_safe_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_GHOST = "ghost".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_HELPER = "helper".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_INSTANCE = "instance".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_MODEL ="model".toCharArray(); //$NON-NLS-1$
	// NONNULL and NULLABLE would go here
	private static final char[] JML_MODIFIER_PEER ="peer".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_PURE ="pure".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_READONLY ="readonly".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_REP ="rep".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_SPEC_BIGINT_MATH = "spec_bigint_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_SPEC_JAVA_MATH = "spec_java_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_SPEC_PROTECTED ="spec_protected".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_SPEC_PUBLIC ="spec_public".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_SPEC_SAFE_MATH = "spec_safe_math".toCharArray(); //$NON-NLS-1$
	private static final char[] JML_MODIFIER_UNINITIALIZED = "uninitialized".toCharArray(); //$NON-NLS-1$

	private final static JmlModifierInfo[] helper = {
			new JmlModifierInfo(JML_MODIFIER_CODE_BIGINT_MATH,	TypeConstants.JML_ANNOTATION_TYPE_CODE_BIGINT_MATH,	CODE_BIGINT_MATH),
			new JmlModifierInfo(JML_MODIFIER_CODE_JAVA_MATH,	TypeConstants.JML_ANNOTATION_TYPE_CODE_JAVA_MATH,	CODE_JAVA_MATH),
			new JmlModifierInfo(JML_MODIFIER_CODE_SAFE_MATH,	TypeConstants.JML_ANNOTATION_TYPE_CODE_SAFE_MATH,	CODE_SAFE_MATH),
			new JmlModifierInfo(JML_MODIFIER_GHOST,				TypeConstants.JML_ANNOTATION_TYPE_GHOST,			GHOST),
			new JmlModifierInfo(JML_MODIFIER_HELPER,			TypeConstants.JML_ANNOTATION_TYPE_HELPER,			HELPER),
			new JmlModifierInfo(JML_MODIFIER_INSTANCE,			TypeConstants.JML_ANNOTATION_TYPE_INSTANCE,			INSTANCE),
			new JmlModifierInfo(JML_MODIFIER_MODEL,				TypeConstants.JML_ANNOTATION_TYPE_MODEL,			MODEL),
			new JmlModifierInfo(JML_MODIFIER_PEER,				TypeConstants.JML_ANNOTATION_TYPE_PEER,				PEER),
			new JmlModifierInfo(JML_MODIFIER_PURE,				TypeConstants.JML_ANNOTATION_TYPE_PURE,				PURE),
			new JmlModifierInfo(JML_MODIFIER_READONLY,			TypeConstants.JML_ANNOTATION_TYPE_READONLY,			READONLY),
			new JmlModifierInfo(JML_MODIFIER_REP,				TypeConstants.JML_ANNOTATION_TYPE_REP,				REP),
			new JmlModifierInfo(JML_MODIFIER_SPEC_BIGINT_MATH,	TypeConstants.JML_ANNOTATION_TYPE_SPEC_BIGINT_MATH,	SPEC_BIGINT_MATH),
			new JmlModifierInfo(JML_MODIFIER_SPEC_JAVA_MATH,	TypeConstants.JML_ANNOTATION_TYPE_SPEC_JAVA_MATH,	SPEC_JAVA_MATH),
			new JmlModifierInfo(JML_MODIFIER_SPEC_PROTECTED,	TypeConstants.JML_ANNOTATION_TYPE_SPEC_PROTECTED,	SPEC_PROTECTED),
			new JmlModifierInfo(JML_MODIFIER_SPEC_PUBLIC,		TypeConstants.JML_ANNOTATION_TYPE_SPEC_PUBLIC,		SPEC_PUBLIC),
			new JmlModifierInfo(JML_MODIFIER_SPEC_SAFE_MATH,	TypeConstants.JML_ANNOTATION_TYPE_SPEC_SAFE_MATH,	SPEC_SAFE_MATH),
			new JmlModifierInfo(JML_MODIFIER_UNINITIALIZED,		TypeConstants.JML_ANNOTATION_TYPE_UNINITIALIZED,	UNINITIALIZED),
	};

	public static long getFromAnnotations(/*@nullable*/ Annotation[] annotations) {
		long result = 0;
		int length = (annotations == null ? 0 : annotations.length);
		for (int i = 0; i < length; i++) {
			Annotation annotation = annotations[i];
			result |= bitMask(annotation.type.getTypeName());
		}
		return result;
	}

	public static long getFromAnnotations(/*@nullable*/ AnnotationBinding[] annotations) {
		long result = 0;
		int length = (annotations == null ? 0 : annotations.length);
		for (int i = 0; i < length; i++) {
			AnnotationBinding annotation = annotations[i];
			result |= bitMask(annotation.getAnnotationType().compoundName);
		}
		return result;
	}

	private static long bitMask(char[][] qualifiedName) {
		for (int j = 0; j < helper.length; j++) {
			if (CharOperation.equals(qualifiedName, helper[j].jmlAnnotationCompoundName))
				return helper[j].bitMask;
		}
		return 0;
	}

	public static boolean isPure(long jmlModifiers) {
		return (jmlModifiers & PURE) == PURE;
	}
	public static boolean isHelper(long jmlModifiers) {
		return (jmlModifiers & HELPER) == HELPER;
	}
	public static boolean isPeer(long jmlModifiers) {
		return (jmlModifiers & PEER) == PEER;
	}
	public static boolean isReadonly(long jmlModifiers) {
		return (jmlModifiers & READONLY) == READONLY;
	}
	public static boolean isRep(long jmlModifiers) {
		return (jmlModifiers & REP) == REP;
	}
	public static boolean isInstance(long jmlModifiers) {
		return (jmlModifiers & INSTANCE) == INSTANCE;
	}
	public static boolean isGhost(long jmlModifiers) {
		return (jmlModifiers & GHOST) == GHOST;
	}
	public static boolean isModel(long jmlModifiers) {
		boolean result = (jmlModifiers & MODEL) == MODEL;
		return result;
	}

	/**
	 * If <code>origIdentifier</code> is the name of a JML modifier, then return
	 * a type reference to the Java 5 annotation class representing the
	 * modifier; otherwise return null;
	 * 
	 * @param origIdentifier
	 * @param pos
	 */
	public static /*@nullable*/ TypeReference identToTypeRef(/*@read_only*/char[] origIdentifier, long pos) {
		char[][] jml5AnnotationName = jml2ModifierNameToQualifiedJml5AnnotationTypeName(origIdentifier);
		if (jml5AnnotationName == null)
			return null;
		
		int length = jml5AnnotationName.length;
		long[] positions = new long[length];
		for (int i = 0; i < length; i++) {
			positions[i] = pos; // FIXME: can we do better?
		}
		return new QualifiedTypeReference(jml5AnnotationName, positions);
	}

	private static char[][] jml2ModifierNameToQualifiedJml5AnnotationTypeName(char[] modifierName) {
		for (int i = 0; i < helper.length; i++) {
			if (CharOperation.equals(modifierName, helper[i].jmlModifierName))
				return helper[i].jmlAnnotationCompoundName;
		}
		return null;
	}
}

/*private*/	class JmlModifierInfo { // JmlModifierInfo
	public final char[] jmlModifierName;
	public final char[] jmlAnnotationName;
	public final char[][] jmlAnnotationCompoundName;
	public final long bitMask;

	public JmlModifierInfo(char[] jmlModifierName,
			char[][] jmlAnnotationCompoundName, long bitMask) {
		this.bitMask = bitMask;
		this.jmlAnnotationCompoundName = jmlAnnotationCompoundName;
		this.jmlAnnotationName = jmlAnnotationCompoundName[TypeConstants.JML_ANNOTATION_PKG.length];
		this.jmlModifierName = jmlModifierName;
	}
}
