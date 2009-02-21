package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.Clinit;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.flow.InitializationFlowContext;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlClinit extends Clinit {

	public JmlClinit(CompilationResult compilationResult) {
		super(compilationResult);
	}

	public void analyseCode(ClassScope classScope,
			InitializationFlowContext staticInitializerFlowContext,
			FlowInfo flowInfo) {
		super.analyseCode(classScope, staticInitializerFlowContext, flowInfo);

		if (classScope.compilerOptions().useNonNullTypeSystem()) {
			// check missing blank non_null field initializations
			flowInfo = flowInfo.mergedWith(staticInitializerFlowContext.initsOnReturn);
			FieldBinding[] fields = scope.enclosingSourceType().fields();
			for (int i = 0, count = fields.length; i < count; i++) {
				FieldBinding field;
				if ((field = fields[i]).isStatic()
					&& (field.fieldDeclaration != null 
						&& field.fieldDeclaration.type != null
						&& field.fieldDeclaration.type.isDeclaredNonNull()
					    && ! Nullity.isPrimitiveType(field.type))
					&& (!flowInfo.isDefinitelyAssigned(fields[i]))) {
					scope.problemReporter().uninitializedBlankNonNullField(
						field,
						scope.referenceType().declarationOf(field.original()));
					// can complain against the field decl, since only one <clinit>
				}
			}
		}
	}

}
