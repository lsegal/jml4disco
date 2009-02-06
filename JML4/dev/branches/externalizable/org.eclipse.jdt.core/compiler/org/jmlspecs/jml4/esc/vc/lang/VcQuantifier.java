package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.LookupEnvironmentEmptyForSerialization;
import org.eclipse.jdt.internal.compiler.lookup.SourceTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;
import org.jmlspecs.jml4.ast.JmlAstUtils;
import org.jmlspecs.jml4.esc.util.Utils;

//DISCO Serializable
public class VcQuantifier implements Externalizable {

	private static final String EXISTS_LEXEME  = "\\exists";  //$NON-NLS-1$
	private static final String FORALL_LEXEME  = "\\forall";  //$NON-NLS-1$
	private static final String SUM_LEXEME     = "\\sum";     //$NON-NLS-1$
	private static final String PRODUCT_LEXEME = "\\product"; //$NON-NLS-1$
	private static final String MIN_LEXEME     = "\\min";     //$NON-NLS-1$
	private static final String MAX_LEXEME     = "\\max";     //$NON-NLS-1$
	private static final String NUM_OF_LEXEME  = "\\num_of";  //$NON-NLS-1$

	public static final VcQuantifier FORALL = new VcQuantifier(FORALL_LEXEME, TypeBinding.BOOLEAN);

	//DISCO transient for custom serialization
	transient public TypeBinding type;
	public String lexeme;
	
	public VcQuantifier() {}  

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		this.lexeme = (String) in.readObject();
		String str = (String) in.readObject();
		this.type = deserializeTypeBinding(str);
	}
	public void writeExternal(ObjectOutput out) throws IOException {
		out.writeObject(this.lexeme);
		String str = serializeTypeBinding(this.type);
		out.writeObject(str);
	}

	public VcQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}
	public String toString() {
		return this.lexeme;
	}

	//DISCO changed from == to .equals 
	public boolean isForall() {
		return this.lexeme.equals(FORALL_LEXEME);
	}

	public boolean isExists() {
		return this.lexeme.equals(EXISTS_LEXEME);
	}

	public boolean isSum() {
		return this.lexeme.equals(SUM_LEXEME);
	}

	public boolean isProduct() {
		return this.lexeme.equals(PRODUCT_LEXEME);
	}

	public boolean isMin() {
		return this.lexeme.equals(MIN_LEXEME);
	}

	public boolean isMax() {
		return this.lexeme.equals(MAX_LEXEME);
	}

	public boolean isNumOf() {
		return this.lexeme.equals(NUM_OF_LEXEME);
	}

	public boolean isLogical() {
		return isForall() || isExists();
	}

	public boolean isNumeric() {
		return ! isLogical();
	}

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
