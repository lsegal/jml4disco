package org.jmlspecs.jml4.esc.util;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;

public class Type {

	public static boolean isBoolean(TypeBinding binding) {
		return binding.id == TypeIds.T_boolean;
	}

	public static boolean isIntegral(TypeBinding binding) {
		switch (binding.id) {
		case TypeIds.T_int:
		case TypeIds.T_short:
		case TypeIds.T_byte:
		case TypeIds.T_long:
		case TypeIds.T_char:
			return true;
		default:
			return false;
		}
	}
}
