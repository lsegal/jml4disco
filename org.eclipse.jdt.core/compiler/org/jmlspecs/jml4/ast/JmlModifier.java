package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;

public class JmlModifier {

	private JmlModifier() {
		//@ assert false;
	}
	public static final String prefix = "org/jmlspecs/jml4/runtime/annotation"; //$NON-NLS-1$
	public static final String prefix_slash = prefix + "/"; //$NON-NLS-1$

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
	
    public static final String Code_bigint_math = "Code_bigint_math"; //$NON-NLS-1$
	public static final String Code_java_math   = "Code_java_math";   //$NON-NLS-1$
	public static final String Code_safe_math   = "Code_safe_math";   //$NON-NLS-1$
	public static final String Ghost            = "Ghost";            //$NON-NLS-1$
	public static final String Helper           = "Helper";           //$NON-NLS-1$
	public static final String Instance         = "Instance";         //$NON-NLS-1$
	public static final String Model            = "Model";            //$NON-NLS-1$
	public static final String Peer             = "Peer";             //$NON-NLS-1$
	public static final String Pure             = "Pure";             //$NON-NLS-1$
	public static final String Readonly         = "Readonly";         //$NON-NLS-1$
	public static final String Rep              = "Rep";              //$NON-NLS-1$
	public static final String Spec_public      = "Spec_public";      //$NON-NLS-1$
	public static final String Spec_protected   = "Spec_protected";   //$NON-NLS-1$
	public static final String Spec_bigint_math = "Spec_bigint_math"; //$NON-NLS-1$
	public static final String Spec_java_math   = "Spec_java_math";   //$NON-NLS-1$
	public static final String Spec_safe_math   = "Spec_safe_math";   //$NON-NLS-1$
	public static final String Uninitialized    = "Uninitialized";    //$NON-NLS-1$

	public static long getFromAnnotations(/*@ nullable */ Annotation[] annotations) {
		long result = 0;
		int length = (annotations == null ? 0 : annotations.length);
		for (int i = 0; i < length; i++) {
			Annotation annotation = annotations[i];
			TypeReference type = annotation.type;
			if (! (type instanceof QualifiedTypeReference))
				continue;
			
			String constantPoolName;
			if (annotation.resolvedType == null) {
				QualifiedTypeReference qualType = (QualifiedTypeReference) type;
				char[][] tokens = qualType.tokens;
				StringBuffer tokenBuffer = new StringBuffer();
				for (int j = 0; j < tokens.length; j++) {
					if (j > 0) tokenBuffer.append('/');
					tokenBuffer.append(tokens[j]);
				}
				constantPoolName = tokenBuffer.toString();
			} else {
				constantPoolName = new String(annotation.resolvedType.constantPoolName());
			}
			
			if (! constantPoolName.startsWith(prefix_slash))
				continue;
			String name = constantPoolName.substring(prefix_slash.length());
			if 		(name.equals(Code_bigint_math)) result |= CODE_BIGINT_MATH;
			else if (name.equals(Code_java_math))   result |= CODE_JAVA_MATH;
			else if (name.equals(Code_safe_math))   result |= CODE_SAFE_MATH;
			else if (name.equals(Ghost))            result |= GHOST;
			else if (name.equals(Helper))           result |= HELPER;
			else if (name.equals(Instance))         result |= INSTANCE;
			else if (name.equals(Model))            result |= MODEL;
			else if (name.equals(Pure))             result |= PURE;
			else if (name.equals(Peer))             result |= PEER;
			else if (name.equals(Readonly))         result |= READONLY;
			else if (name.equals(Rep))              result |= REP;
			else if (name.equals(Spec_public))      result |= SPEC_PUBLIC;
			else if (name.equals(Spec_protected))   result |= SPEC_PROTECTED;
			else if (name.equals(Spec_bigint_math)) result |= SPEC_BIGINT_MATH;
			else if (name.equals(Spec_java_math))   result |= SPEC_JAVA_MATH;
			else if (name.equals(Spec_safe_math))   result |= SPEC_SAFE_MATH;
			else if (name.equals(Uninitialized))    result |= UNINITIALIZED;
		}
		return result;
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
}
