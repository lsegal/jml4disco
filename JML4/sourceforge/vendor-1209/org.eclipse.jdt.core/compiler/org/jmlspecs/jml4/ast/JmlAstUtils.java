package org.jmlspecs.jml4.ast;

import java.util.Iterator;
import java.util.List;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.nonnull.Nullity;

final public class JmlAstUtils {

	private static final String NULLABLE_ANNOTATION_NAME = "@Nullable"; //$NON-NLS-1$
	private static final String NON_NULL_ANNOTATION_NAME = "@NonNull"; //$NON-NLS-1$
	public static final boolean useSupersToStringMethod = true;
//	public static boolean complainAboutNotUsingJmlOverrides = false;
	
	private JmlAstUtils() {
		//@ assert false;
	}

	public static String concatWith(char[][] tokens, char separator) {
		return new String(CharOperation.concatWith(tokens, separator));
	}

	public static Expression conjoin(List/*<Expression>*/ exprs) {
		Expression result = new TrueLiteral(0, 0);
		if (exprs == null)
		   return result;

		for (Iterator iterator = exprs.iterator(); iterator.hasNext();) {
			Expression pred = (Expression) iterator.next();
			Utils.assertTrue(pred.resolvedType == TypeBinding.BOOLEAN, "'"+pred+"' not a boolean but a '"+pred.resolvedType+"'");  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
			if (pred instanceof TrueLiteral) {
				/* leave result unchanged */
			} else if (result instanceof TrueLiteral) {
				result = pred;
			} else {
				result = new BinaryExpression(result, pred, OperatorIds.AND);
			}
		}
		return result;
	}

	public static void handleAnnotations(JmlTypeReference type, Annotation[] annotations, ProblemReporter problemReporter) {
		for (int i = 0; i < annotations.length; i++) {
			Annotation annotation = annotations[i];
			String annotationName = annotation.toString();
			if (annotationName.equals(NULLABLE_ANNOTATION_NAME)
			 || annotationName.equals(NON_NULL_ANNOTATION_NAME)) {
				//If nullity has already been set
				if (type.getNullity().hasExplicitNullity() ){
					problemReporter.duplicateAnnotation(annotation);
				} else {
					Nullity newNullity = annotationName.equals(NULLABLE_ANNOTATION_NAME)
					                   ? Nullity.nullable 
					                   : Nullity.non_null;
					type.setNullity(newNullity );
				}
			}
		} 
	}
	
    public static void assertTrue(boolean b, String msg) {
		if (!b)
			throw new RuntimeException(msg);
	}

	public static void assertNotNull(Object o, String msg) {
		if (o == null)
			throw new RuntimeException(msg);
	}
}
