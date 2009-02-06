// <jml-start id="distributed verification"/>
// DISCO empty class to allow easy serialization
package org.eclipse.jdt.internal.compiler.lookup;

import java.util.Set;

import org.eclipse.jdt.internal.compiler.ClassFile;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.env.AccessRestriction;
import org.eclipse.jdt.internal.compiler.env.IBinaryType;

public class LookupEnvironmentEmptyForSerialization extends LookupEnvironment {

	public LookupEnvironmentEmptyForSerialization() {
		super();
	}
	public ReferenceBinding askForType(char[][] compoundName) {
		return null;
	}
	ReferenceBinding askForType(PackageBinding packageBinding, char[] name) {
		return null;
	}
	public void buildTypeBindings(CompilationUnitDeclaration unit, AccessRestriction accessRestriction) {
	}
	public BinaryTypeBinding cacheBinaryType(IBinaryType binaryType, AccessRestriction accessRestriction) {
		return null;
	}
	public BinaryTypeBinding cacheBinaryType(IBinaryType binaryType,
			boolean needFieldsAndMethods, AccessRestriction accessRestriction) {
		return null;
	}
	public void completeTypeBindings() {
	}
	public void completeTypeBindings(CompilationUnitDeclaration parsedUnit,
			boolean buildFieldsAndMethods) {
	}
	public void completeTypeBindings(CompilationUnitDeclaration parsedUnit) {
	}
	public TypeBinding computeBoxingType(TypeBinding type) {
		return null;
	}
	public TypeBinding convertEliminatingTypeVariables(
			TypeBinding originalType, ReferenceBinding genericType, int rank, Set eliminatedVariables) {
		return null;
	}
	public ReferenceBinding convertToParameterizedType(
			ReferenceBinding originalType) {
		return null;
	}
	public TypeBinding convertToRawType(TypeBinding type,
			boolean forceRawEnclosingType) {
		return null;
	}
	public TypeBinding convertUnresolvedBinaryToRawType(TypeBinding type) {
		return null;
	}
	public AnnotationBinding createAnnotation(ReferenceBinding annotationType,
			ElementValuePair[] pairs) {
		return null;
	}
	public ArrayBinding createArrayType(TypeBinding leafComponentType,
			int dimensionCount) {
		return null;
	}
	public BinaryTypeBinding createBinaryTypeFrom(IBinaryType binaryType,
			PackageBinding packageBinding, AccessRestriction accessRestriction) {
		return null;
	}
	public BinaryTypeBinding createBinaryTypeFrom(IBinaryType binaryType,
			PackageBinding packageBinding, boolean needFieldsAndMethods,
			AccessRestriction accessRestriction) {
		return null;
	}
	public MissingTypeBinding createMissingType(PackageBinding packageBinding, char[][] compoundName) {
		return null;
	}
	public PackageBinding createPackage(char[][] compoundName) {
		return null;
	}
	public ParameterizedGenericMethodBinding createParameterizedGenericMethod(
			MethodBinding genericMethod, RawTypeBinding rawType) {
		return null;
	}
	public ParameterizedGenericMethodBinding createParameterizedGenericMethod(
			MethodBinding genericMethod, TypeBinding[] typeArguments) {
		return null;
	}
	public ParameterizedTypeBinding createParameterizedType(
			ReferenceBinding genericType, TypeBinding[] typeArguments, ReferenceBinding enclosingType) {
		return null;
	}
	public RawTypeBinding createRawType(ReferenceBinding genericType, ReferenceBinding enclosingType) {
		return null;
	}
	public WildcardBinding createWildcard(ReferenceBinding genericType,
			int rank, TypeBinding bound, TypeBinding[] otherBounds,	int boundKind) {
		return null;
	}
	public AccessRestriction getAccessRestriction(TypeBinding type) {
		return null;
	}
	public ReferenceBinding getCachedType(char[][] compoundName) {
		return null;
	}
	PackageBinding getPackage0(char[] name) {
		return null;
	}
	public ReferenceBinding getResolvedType(char[][] compoundName, Scope scope) {
		return null;
	}
	PackageBinding getTopLevelPackage(char[] name) {
		return null;
	}
	public ReferenceBinding getType(char[][] compoundName) {
		return null;
	}
	ReferenceBinding getTypeFromConstantPoolName(char[] signature, int start,
			int end, boolean isParameterized, char[][][] missingTypeNames) {
		return null;
	}
	TypeBinding getTypeFromSignature(char[] signature, int start, int end,
			boolean isParameterized, TypeBinding enclosingType,	char[][][] missingTypeNames) {
		return null;
	}
	public TypeBinding getTypeFromTypeSignature(SignatureWrapper wrapper,TypeVariableBinding[] staticVariables,
			ReferenceBinding enclosingType, char[][][] missingTypeNames) {
		return null;
	}
	TypeBinding getTypeFromVariantTypeSignature(SignatureWrapper wrapper,TypeVariableBinding[] staticVariables,
			ReferenceBinding enclosingType, ReferenceBinding genericType, int rank, char[][][] missingTypeNames) {
		return null;
	}
	boolean isPackage(char[][] compoundName, char[] name) {
		return false;
	}
	public MethodVerifier methodVerifier() {
		return null;
	}
	public PackageBinding public_computePackageFrom(char[][] constantPoolName, boolean isMissing) {
		return null;
	}
	public void releaseClassFiles(ClassFile[] classFiles) {
	}
	public void reset() {
	}
	public void setAccessRestriction(ReferenceBinding type, AccessRestriction accessRestriction) {
	}
	void updateCaches(UnresolvedReferenceBinding unresolvedType, ReferenceBinding resolvedType) {
	}

}
// <jml-end id="distributed verification"/>
