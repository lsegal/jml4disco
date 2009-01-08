package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.JmlAllRangeExpression;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedThisReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.SuperReference;
import org.eclipse.jdt.internal.compiler.ast.ThisReference;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlAstUtils;

public class JmlStoreRefExpression extends JmlStoreRef {

	final private JmlName[] names;
	//@ invariant names.length > 0;
	public boolean suffixed;
	//@ invariant (!suffixed) ==> (names.length == 1);
	public Reference[] assignableReferences;

	//@ requires names.length > 0;
	//@ ensures  this.names == names;
	public JmlStoreRefExpression(JmlName[] names, boolean suffixed) {
		super();
		this.names = names;
		this.suffixed = suffixed;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		for (int i = 0; i < names.length; i++) {
			output.append(names[i].name);
			if (i < names.length - 1 && !names[i+1].isArraySuffix())
				output.append('.');
		}
		return output;
	}

	/**
	 * Accept the following patterns:
	 * 
	 * 1. single expressions: e.g., x
	 * 2. qualified expressions: e.g., x.y.z
	 * 3. array expressions: e.g., a[1], a[0..2], a[*]
	 * 4. "this" and "super" expressions. 
	 * 5. combinations of the above: e.g., x.a[*], x.a[0..2].y, this.a[1].y
	 * 
	 *   N.B. Currently, "this" and "super" must be placed at the beginning
	 *   of an expression. For example, A.this is not supported.
	 * 
	 *   6. wild-card expressions where wild cards are appended to the end of
	 *   the above expressions: e.g., x.*, x.y.*, a[0..2].*, this.a[1].*
	 **/
	public void resolve(BlockScope scope) {
		final JmlName firstStoreRefName = names[0];

		switch (firstStoreRefName.sort) {
			case JmlName.SORT_IDENT:
				resolveNameRef(scope, suffixed, this.names);
				break;
			case JmlName.SORT_THIS:
				ThisReference tr = new ThisReference(this.names[0].sourceStart, this.names[0].sourceEnd);
				JmlName[] rest = new JmlName[this.names.length - 1];
				System.arraycopy(this.names, 1, rest, 0, this.names.length - 1);
				if (rest.length > 0) {
					this.resolveFieldRef(scope, rest, tr);
					break;
				} else {
					JmlName id = this.names[0];
					SingleTypeReference t = new SingleTypeReference(id.name.toCharArray(), id.position);
					scope.problemReporter().invalidThisAsStoreRef(t);
					return;
				}
			case JmlName.SORT_SUPER:
				SuperReference sr = new SuperReference(this.names[0].sourceStart, this.names[0].sourceEnd);
				rest = new JmlName[this.names.length - 1];
				System.arraycopy(this.names, 1, rest, 0, this.names.length - 1);
				if (rest.length > 0) {
					this.resolveFieldRef(scope, rest, sr);
					break;
				} else {
					JmlName id = this.names[0];
					SingleTypeReference t = new SingleTypeReference(id.name.toCharArray(), id.position);
					scope.problemReporter().invalidSuperAsStoreRef(t);
					return;
				}
			default:
				/* Unreachable: the grammar described in java.g as of 2008.08.22 
				 * does not allow a store-ref expression to be started with types 
				 * other than id, this and super. 
				 * The following assertion is an alarm trigger 
				 * for possible future change of the above logic.  				
				 */
				JmlAstUtils.assertTrue(false, "store-ref expression doesn't start with an id, this, or super"); //$NON-NLS-1$
		}
	}

	//@ requires restSuffixed ==> refNames.length > 1 & refNames[0].sort == JmlName.SORT_INDENT;
	private void resolveNameRef(BlockScope scope, boolean restSuffixed, JmlName[] refNames) {
		if (!restSuffixed) {
			final JmlName singleStoreRefName = refNames[0];
			final SingleNameReference ref = new JmlSingleNameReference(
					singleStoreRefName.name.toCharArray(), singleStoreRefName.position);
			reset(ref);
			ref.resolveType(scope);
			this.assignableReferences = new Reference[]{ ref };
		} else {
			int numOfIds = 0;
			char[][] ids = new char[refNames.length][];
			long[] positions = new long[refNames.length];
			final int srcStrt = refNames[0].sourceStart;
			int srcEnd = refNames[0].sourceEnd;

			for (int i = 0; i < refNames.length; i++) {
				JmlName storeRefName = refNames[i];
				NameReference ref = null;
				if (storeRefName.sort != JmlName.SORT_IDENT) {
					ref = (numOfIds > 1)
                        ? (NameReference) getQNR(scope, ids, numOfIds, srcStrt, srcEnd, positions)
						: new JmlSingleNameReference(ids[0], positions[0]);
				}
				switch (storeRefName.sort) {
					case JmlName.SORT_WILDCARD:
						if (i < refNames.length - 1) {
							JmlName id = refNames[i];
							SingleTypeReference t = new SingleTypeReference(id.name.toCharArray(), id.position);
							scope.problemReporter().illegalUsageOfWildcard(t);
							return;
						}
						Reference[] rst = resolveWildCard(scope, ref);
						this.assignableReferences = rst;
						return;
					case JmlName.SORT_IDENT:
						numOfIds++;
						ids[i] = new char[storeRefName.name.length()];
						ids[i] = storeRefName.name.toCharArray();
						positions[i] = storeRefName.position;
						srcEnd = storeRefName.sourceEnd;
						break;
					case JmlName.SORT_POS:
						if (i < refNames.length - 1) {
							final int restSize = refNames.length - i - 1;
							final JmlName[] rest = new JmlName[restSize];
							System.arraycopy(refNames, i+1, rest, 0, restSize);
							final ArrayReference ar = new JmlArrayReference(ref, storeRefName.getPositionExp());
							resolveFieldRef(scope, rest, ar);
						} else {
							final ArrayReference ar = new JmlArrayReference(ref, storeRefName.getPositionExp());
							reset(ar);
							ar.resolveType(scope);
							this.assignableReferences = new Reference[]{ ar };
						}
						return;
					case JmlName.SORT_RANGE:
						if (i < refNames.length - 1) {
							final int restSize = refNames.length - i - 1;
							final JmlName[] rest = new JmlName[restSize];
							System.arraycopy(refNames, i+1, rest, 0, restSize);
							JmlRangeArrayReference rar = 
								new JmlRangeArrayReference(ref, storeRefName.getLowRange(), storeRefName.getHighRange());
							resolveFieldRef(scope, rest, rar);
							return;
						} else {
							JmlRangeArrayReference rar = 
								new JmlRangeArrayReference(ref, storeRefName.getLowRange(), storeRefName.getHighRange());
							reset(rar);
							rar.resolveType(scope);
							this.assignableReferences = new Reference[]{ rar };
							return;
						}
					case JmlName.SORT_ALL:
						if (i < refNames.length - 1) {
							final int restSize = refNames.length - i - 1;
							final JmlName[] rest = new JmlName[restSize];
							System.arraycopy(refNames, i+1, rest, 0, restSize);
							JmlRangeArrayReference rar = new JmlRangeArrayReference(ref, new JmlAllRangeExpression());
							resolveFieldRef(scope, rest, rar);
							return;
						} else {
							JmlRangeArrayReference rar = new JmlRangeArrayReference(ref, new JmlAllRangeExpression());
							reset(rar);
							rar.resolveType(scope);
							this.assignableReferences = new Reference[]{ rar };
							return;
						}
					case JmlName.SORT_THIS:
						if (i < refNames.length - 1) {
							final int restSize = refNames.length - i - 1;
							final JmlName[] rest = new JmlName[restSize];
							System.arraycopy(refNames, i+1, rest, 0, restSize);

							// tokens and positions already scanned.
							char[][] tokens = new char[i][];
							long[] poss = new long[i];
							for (int j = 0; j < i; j++) {
								tokens[j] = refNames[j].name.toCharArray();
								poss[j] = refNames[j].position;
							}

							final TypeReference tr;
							tr = (i > 1)
							   ? (TypeReference) new QualifiedTypeReference(tokens, poss)
							   : new SingleTypeReference(tokens[0], poss[0]);
						
							QualifiedThisReference qtr = new QualifiedThisReference(tr, srcStrt,refNames[refNames.length - 1].sourceEnd);
							resolveFieldRef(scope, rest, qtr);
							return;
						} else {
							SingleTypeReference t = new SingleTypeReference(storeRefName.name.toCharArray(), storeRefName.position);
							scope.problemReporter().invalidThisAsStoreRef(t);
							return;
						}
					case JmlName.SORT_SUPER:
					default:
						/* Unreachable: the grammar described in java.g as of 2008.08.22 
						 * does not allow "super" to be followed by ids. 
						 * The following assertion statement is an alarm trigger 
						 * for possible future change of the above logic.  				
						 */
						JmlAstUtils.assertTrue(false, "super cannot be followed by ids"); //$NON-NLS-1$
				}
			}

			final QualifiedNameReference ref = getQNR(scope, ids, numOfIds, srcStrt, srcEnd, positions);
			reset(ref);
			ref.resolveType(scope);
			this.assignableReferences = new Reference[]{ ref };
		}
	}

	private void resolveFieldRef(BlockScope scope, JmlName[] refNames, Reference initRcv) {
		FieldReference fr = null;
		Reference receiver = initRcv;
		for (int i = 0; i < refNames.length; i++) {
			JmlName storeRefName = refNames[i]; 
			switch (storeRefName.sort) {
				case JmlName.SORT_WILDCARD:
					if (i < refNames.length - 1) {
						JmlName id = refNames[i];
						SingleTypeReference t = new SingleTypeReference(id.name.toCharArray(), id.position);
						scope.problemReporter().illegalUsageOfWildcard(t);
						return;
					}
					Reference[] rst;
					rst = resolveWildCard(scope, receiver);
					this.assignableReferences = rst;
					return;
				case JmlName.SORT_IDENT:
					fr = new JmlFieldReference(storeRefName.name.toCharArray(), storeRefName.position);
					fr.receiver = receiver;
					receiver = fr;
					break;
				case JmlName.SORT_POS:
					if (i < refNames.length - 1) {
						receiver = new JmlArrayReference(receiver, storeRefName.getPositionExp());
						break;
					} else {
						final ArrayReference ar = new JmlArrayReference(receiver, storeRefName.getPositionExp());
						reset(ar);
						ar.resolveType(scope);
						this.assignableReferences = new Reference[]{ ar };
					return;
				}
				case JmlName.SORT_RANGE:
					if (i < refNames.length - 1) {
						receiver = 
							new JmlRangeArrayReference(receiver, storeRefName.getLowRange(), storeRefName.getHighRange());
						break;
					} else {
						JmlRangeArrayReference rar = 
							new JmlRangeArrayReference(receiver, storeRefName.getLowRange(), storeRefName.getHighRange());
						reset(rar);
						rar.resolveType(scope);
						this.assignableReferences = new Reference[]{ rar };
						return;
					}
				case JmlName.SORT_ALL:
					if (i < refNames.length - 1) {
						receiver = new JmlRangeArrayReference(receiver, new JmlAllRangeExpression());
						break;
					} else {
						JmlRangeArrayReference rar = new JmlRangeArrayReference(receiver, new JmlAllRangeExpression());
						reset(rar);
						rar.resolveType(scope);
						this.assignableReferences = new Reference[]{ rar };
						return;
					}
				case JmlName.SORT_THIS:
					JmlName id = refNames[i];
					SingleTypeReference t = new SingleTypeReference(id.name.toCharArray(), id.position);
					scope.problemReporter().illegalUsageOfThis(t);
					return;	
				case JmlName.SORT_SUPER:													
				default:
					/* Unreachable: the grammar described in java.g as of 2008.08.22 
					 * does not allow "super" to be followed by ids. 
					 * The following assertion is an alarm trigger 
					 * for possible future change of the above logic.  				
					 */
					JmlAstUtils.assertTrue(false, "super cannot be followed by ids"); //$NON-NLS-1$
			}
		}

		reset(receiver);
		receiver.resolveType(scope);
		this.assignableReferences = new Reference[]{ receiver };
	}

	private Reference[] resolveWildCard(BlockScope scope, Reference prefixRef) {
		final List leaves = collectFieldBindings(scope, prefixRef);
		final List refs = new ArrayList();
		for (int i = 0; i < leaves.size(); i++) {
			FieldBinding fb = (FieldBinding) leaves.get(i);
			if (prefixRef instanceof QualifiedNameReference) {
				QualifiedNameReference qualPrefixRef = (QualifiedNameReference) prefixRef;
				char[][] prefix = qualPrefixRef.tokens;
				int tokensLen = prefix.length + 1;
				char[][] tokens = new char[tokensLen][];
				System.arraycopy(prefix, 0, tokens, 0, prefix.length);
				tokens[prefix.length] = fb.name;

				int ss = qualPrefixRef.sourceEnd;
				int se = qualPrefixRef.sourceEnd + fb.name.length + 1;
				long[] positions = new long[qualPrefixRef.sourcePositions.length + 1];
				System.arraycopy(qualPrefixRef.sourcePositions, 0, positions, 0, qualPrefixRef.sourcePositions.length);
				positions[qualPrefixRef.sourcePositions.length] = (((long) ss) << 32) + (se - 1);
				QualifiedNameReference qnr = getQNR(scope, tokens, tokensLen, ss, se, positions);
				refs.add(qnr);
			} else if (prefixRef instanceof SingleNameReference) {
				SingleNameReference sngPrefixRef = (SingleNameReference) prefixRef;
				char[] prefix = sngPrefixRef.token;
				char[][] tokens = new char[2][];
				tokens[0] = prefix;
				tokens[1] = fb.name;

				int ss = sngPrefixRef.sourceEnd;
				int se = sngPrefixRef.sourceEnd + fb.name.length + 1;
				long[] positions = new long[2];

				positions[0] = (((long) sngPrefixRef.sourceStart) << 32) + (sngPrefixRef.sourceEnd - 1);
				positions[1] = (((long) ss) << 32) + (se - 1);
				QualifiedNameReference qnr = getQNR(scope, tokens, 2, ss, se, positions);
				refs.add(qnr);
			} else if (prefixRef instanceof ThisReference
					|| prefixRef instanceof FieldReference
					|| prefixRef instanceof ArrayReference) {
				int ss = prefixRef.sourceEnd;
				int se = prefixRef.sourceEnd + fb.name.length + 1;
				long pos =  (((long) ss) << 32) + (se - 1);
				FieldReference fr = new JmlFieldReference(fb.name, pos);
				fr.receiver = prefixRef;
				refs.add(fr);
			} else {
				// report a problem
				throw new RuntimeException();
			}
		}
		for (int i = 0; i < refs.size(); i++) {
			Reference r = (Reference) refs.get(i);
			reset(r);
			r.resolveType(scope);
		}
		Reference[] rst = new Reference[refs.size()];
		refs.toArray(rst);
		return rst;
	}

	private QualifiedNameReference getQNR(BlockScope scope, char[][] ids,
			int numOfIds, int srcStrt, int srcEnd, long[] positions) {
		char[][] packed_ids = new char[numOfIds][];
		System.arraycopy(ids, 0, packed_ids, 0, numOfIds);
		long[] packed_positions = new long[numOfIds];
		System.arraycopy(positions, 0, packed_positions, 0, numOfIds);
		final QualifiedNameReference ref = new JmlQualifiedNameReference(packed_ids, packed_positions, srcStrt, srcEnd);
		return ref;
	}

	private void reset(Expression exp) {
		// reset the bits of the receiver to resolve a field reference based on it
		// when otherwise the resolution fails.
		exp.bits &= ~ASTNode.RestrictiveFlagMASK;
		exp.bits |= Binding.LOCAL | Binding.FIELD;

		if (exp instanceof FieldReference) {
			Expression rcv = ((FieldReference) exp).receiver;
			reset(rcv);
		} else if (exp instanceof ArrayReference) {
			Expression rcv = ((ArrayReference) exp).receiver;
			reset(rcv);
		}
	}

	private List collectFieldBindings(BlockScope scope, Reference ref) {
		reset(ref);
		ref.resolveType(scope);
		TypeBinding tb = ref.resolvedType;
		final List buffer = new ArrayList();
		if (tb instanceof ReferenceBinding) {
			ReferenceBinding rb = (ReferenceBinding) tb;
			do {
				FieldBinding[] fs = rb.fields();
				for (int i = 0; i < rb.fieldCount(); i++) {
					buffer.add(fs[i]);
				}
				rb = rb.superclass();
			} while (rb != null);
		}

		reset(ref);
		return buffer;
	}

	public FlowInfo analyseAssignment(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo, Assignment assignment,
			boolean isCompound) {
		// TODO Auto-generated method stub
		return null;
	}

	public void generateAssignment(BlockScope currentScope,
			CodeStream codeStream, Assignment assignment, boolean valueRequired) {
		// TODO Auto-generated method stub

	}

	public void generateCompoundAssignment(BlockScope currentScope,
			CodeStream codeStream, Expression expression, int operator,
			int assignmentImplicitConversion, boolean valueRequired) {
		// TODO Auto-generated method stub

	}

	public void generatePostIncrement(BlockScope currentScope,
			CodeStream codeStream, CompoundAssignment postIncrement,
			boolean valueRequired) {
		// TODO Auto-generated method stub

	}
}
