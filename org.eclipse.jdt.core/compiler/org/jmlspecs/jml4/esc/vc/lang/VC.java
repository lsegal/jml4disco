package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.LookupEnvironmentEmptyForSerialization;
import org.eclipse.jdt.internal.compiler.lookup.SourceTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;
import org.jmlspecs.jml4.ast.JmlAstUtils;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;
// DISCO Serializable
public abstract class VC implements Comparable, Serializable {

	public static final VC[] EMPTY = new VC[0];
	private /*@nullable*/ String name;
	//DISCO transient for custom serialization
	transient public  TypeBinding type;
	public final int sourceStart;
	public final int sourceEnd;

	private /*@nullable*/ KindOfAssertion kindOfAssertion;
	protected int kindOfLabel;
	private boolean isImplication = false;
	//@ invariant label == kindOfAssertion <==> kindOfLabel == -1;
	private int labelStart = 0;

	public static final int NO_LBL = -1;
	public static final int NEGLBL =  1;
	
	public VC(TypeBinding type, /*@nullable*/ KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR_PRE && labelStart == 0), "LoopInv@0.b"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.PRE && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
//		Utils.assertTrue(sourceStart == 0 || sourceEnd == 0 || sourceStart <= sourceEnd, "source positions incorrect ("+sourceStart+">"+sourceEnd+")");   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		this.type = type;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.kindOfAssertion = kindOfAssertion;
		this.kindOfLabel = kindOfLabel;
		this.labelStart = labelStart;
	}

	public VC(TypeBinding type, int sourceStart, int sourceEnd) {
		this(type, null, NO_LBL, sourceStart, sourceEnd, 0);
	}

	public void setLabel(KindOfAssertion kindOfAssertion, int kindOfLabel, int labelStart) {
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR && labelStart == 0), "LoopInv@0.c"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.LOOP_INVAR_PRE && labelStart == 0), "LoopInv@0.d"); //$NON-NLS-1$
		Utils.assertTrue(!(kindOfAssertion==KindOfAssertion.PRE && labelStart == 0), "LoopInv@0.a"); //$NON-NLS-1$
		this.kindOfAssertion = kindOfAssertion;
		this.kindOfLabel = kindOfLabel;
		this.labelStart  = labelStart;
	}

	public KindOfAssertion kindOfAssertion() {
		return this.kindOfAssertion;
	}

	public int kindOfLabel() {
		return this.kindOfLabel;
	}
	
	public int labelStart() {
		return this.labelStart;
	}

	public abstract String toString();
	public String toStringWithName() {
		String toString = this.toString();
		return (this.name == null)
		     ? toString
			 : this.name + ": " + toString; //$NON-NLS-1$
			
	}
	public abstract String accept(ProverVisitor visitor);

	public String acceptAsTerm(ProverVisitor visitor) {
		return accept(visitor);
	}
	private final List/*VcVarDecl*/ decls = new ArrayList();
	public List/*VcVarDecl*/ decls() {
		return this.decls;
	}
	public void addDecl(VcVarDecl decl) {
		if (! this.decls.contains(decl))
			this.decls.add(decl);
	}
	public void addDecls(List/*<VcVarDecl>*/ newDecls) {
		if (newDecls == decls())
			return;
		for (Iterator iterator = newDecls.iterator(); iterator.hasNext();) {
			VcVarDecl varDecl = (VcVarDecl) iterator.next();
			this.addDecl(varDecl);
		}
	}
	public String visitVarDecls(ProverVisitor visitor) {
		VcVarDecl[] varDecls = (VcVarDecl[])this.decls().toArray(new VcVarDecl[0]);
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < varDecls.length; i++) {
			result.append(varDecls[i].accept(visitor));
		}
		return result.toString();
	}
	public String declString() {
		return //(this.name == null ? "" : this.name + ": ") +
//			   (this.kindOfAssertion == null ? "" : "{"+this.kindOfAssertion.toString()+"}\n") + //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			   (this.decls.size() == 0 ? "" : this.decls.toString() + "\n"); //$NON-NLS-1$ //$NON-NLS-2$
	}
	public String getName() {
		return this.name;
	}
	public boolean hasName() {
		return this.name != null;
	}
	private static List/*<String>*/ names = new ArrayList/*<String>*/();
	public void setName(String name) {
		Utils.assertTrue(this.name==null, "trying to rename VC "+this.name); //$NON-NLS-1$
		Utils.assertTrue(! names.contains(name), "name '"+name+"' already exists"); //$NON-NLS-1$ //$NON-NLS-2$
		this.name = name;
	}
	/*package*/ static void clearNameList() {
		names.clear();
	}

	/*package*/ List/*<VC>*/ vc2vcs() {
		return Arrays.asList(new VC[]{this});
	}

	/*package*/ VC inlineAndAddDecls(Map map) {
		VC inlined = this.inline(map);
		inlined.addDecls(this.decls());
		return inlined;
	}
	/*package*/ abstract VC inline(Map map);
	public abstract int hashCode();
	public boolean endsInImpliesTrue() {
		return false;
	}

	private /*nullable*/ String asString;
	/*package*/ int originalIndex;
	private synchronized String asString() {
		if (this.asString == null) {
			this.asString = this.toString();
		}
		return this.asString;
	}
	public int compareTo(Object o) {
		if (o instanceof VC) {
			VC other = (VC)o;
			return this.asString().compareTo(other.asString());
		} else {
			return -1;
		}
	}
	// equality basically compares the toString()s
	public boolean equals(Object obj) {
		return this.compareTo(obj) == 0;
	}

	public VC negateLastImplication() {
		return new VcNot(this, this.sourceStart, this.sourceEnd);
	}

	public void markAsImplication() {
		this.isImplication = true;
	}

	public boolean isImplication() {
		return isImplication;
	}
	// DISCO Custom Serialization overriding
	private void writeObject(ObjectOutputStream out) throws IOException{
		//default serialization
		out.defaultWriteObject();
		//additional field transient TypeBinding
		String str = serializeTypeBinding(type);
		out.writeObject(str);
	}
	// DISCO Custom Serialization overriding
	private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
		//default deserialization
		in.defaultReadObject();
		//reconstruct transient TypeBinding
		String str = (String) in.readObject();
		TypeBinding tb = deserializeTypeBinding(str);
		this.type = tb;
	}
	// DISCO Custom Serialization 
	//takes a TypeBinding and returns a string according to its type
	//the string will be added to the ObjectOutputStream for serialization
	private String serializeTypeBinding(TypeBinding tb) {
		if (tb.isBaseType()){
			return Integer.toString(tb.id);
		} else if(tb.isArrayType()) {
			return serializeTypeBinding(tb.leafComponentType()) + "["+tb.dimensions()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
		} else if ( tb instanceof SourceTypeBinding){
			SourceTypeBinding src = (SourceTypeBinding) tb;
			String ret = JmlAstUtils.concatWith(src.compoundName, '.'); 
			return ret + ".";	 //$NON-NLS-1$
		} else if ( tb instanceof BinaryTypeBinding){
			BinaryTypeBinding bin = (BinaryTypeBinding) tb;
			String ret = JmlAstUtils.concatWith(bin.compoundName, '.');
			return ret+ "."; //$NON-NLS-1$
		} else if ( tb instanceof VcTypeBinding) {
			VcTypeBinding vcTB = (VcTypeBinding) tb;
			String ret = JmlAstUtils.concatWith(vcTB.compoundName, '.');
			return ret+ "."; //$NON-NLS-1$
		}
		Utils.assertTrue(false, "TypeBinding cannot be serialized '" + tb.debugName() + "'"); //$NON-NLS-1$ //$NON-NLS-2$
		return null;
	}
	
	// DISCO Custom Serialization 
	//takes a string that has been deserialized from an ObjectInputStream
	//and returns a reconstructed TypeBinding
	private TypeBinding deserializeTypeBinding(String str) {
		if (str.endsWith("]")) {		 //$NON-NLS-1$
			int dims = Integer.parseInt(str.substring(str.indexOf('[') + 1, str.indexOf(']')));
			String strType = str.substring(0, str.indexOf('['));
			return new ArrayBinding(deserializeTypeBinding(strType), dims, new LookupEnvironmentEmptyForSerialization());
		} else if  (str.endsWith(".")) {	 //$NON-NLS-1$
			str = str.substring(0, str.length()-1);			 
			return new VcTypeBinding(CharOperation.splitOn('.', str.toCharArray()));			
		} else {
			return deserializeBaseType(str);
		}		
	}

	// DISCO Custom Serialization 
	private TypeBinding deserializeBaseType(String str) {
		int intValue = -1;
		try {
			intValue = Integer.parseInt(str);
		} catch (NumberFormatException e) {
			Utils.assertTrue(false, "BaseType not an int '" + str + "'"); //$NON-NLS-1$ //$NON-NLS-2$
			e.printStackTrace();
		}
		switch (intValue) {
			case TypeIds.T_boolean:
				return TypeBinding.BOOLEAN;
			case TypeIds.T_byte:
				return TypeBinding.BYTE;
			case TypeIds.T_char:
				return TypeBinding.CHAR;
			case TypeIds.T_short:
				return TypeBinding.SHORT;
			case TypeIds.T_double:
				return TypeBinding.DOUBLE;
			case TypeIds.T_float:
				return TypeBinding.FLOAT;
			case TypeIds.T_int:
				return TypeBinding.INT;
			case TypeIds.T_long:
				return TypeBinding.LONG;
		}
		Utils.assertTrue(false, "Unknown BaseType '" + str + "'"); //$NON-NLS-1$ //$NON-NLS-2$
		return null;
	}

}
