package org.jmlspecs.jml4.lookup;

import org.eclipse.jdt.internal.compiler.lookup.PackageBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlSpecialTypeBinding extends TypeBinding {

	public static final JmlSpecialTypeBinding INFORMAL_COMMENT_UNFIXED_TYPE
		= new JmlSpecialTypeBinding();
	public static final JmlSpecialTypeBinding MULTI_REFERENCE_MAYBE_WITH_INFORMAL_COMMENTS
		= new JmlSpecialTypeBinding();
	public static final JmlSpecialTypeBinding MULTI_VALUE
	= new JmlSpecialTypeBinding();
	
	private JmlSpecialTypeBinding() {
		// empty
	}

	public char[] constantPoolName() {
		// TODO Auto-generated method stub
		return null;
	}

	public PackageBinding getPackage() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isCompatibleWith(TypeBinding right) {
		// TODO Auto-generated method stub
		return false;
	}

	public char[] qualifiedSourceName() {
		// TODO Auto-generated method stub
		return null;
	}

	public char[] sourceName() {
		// TODO Auto-generated method stub
		return null;
	}

	public char[] readableName() {
		// TODO Auto-generated method stub
		return null;
	}

}
