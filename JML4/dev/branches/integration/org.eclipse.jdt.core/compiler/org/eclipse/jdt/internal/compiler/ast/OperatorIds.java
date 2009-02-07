/*******************************************************************************
 * Copyright (c) 2000, 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.compiler.ast;

public interface OperatorIds {
	public static final int AND_AND = 0;
	public static final int OR_OR = 1;
	public static final int AND = 2; 
	public static final int OR = 3; 
	public static final int LESS = 4;
	public static final int LESS_EQUAL = 5;
	public static final int GREATER = 6;
	public static final int GREATER_EQUAL = 7;
	public static final int XOR = 8;
	public static final int DIVIDE = 9; 
	public static final int LEFT_SHIFT = 10;
	public static final int NOT = 11; 
	public static final int TWIDDLE = 12; 
	public static final int MINUS = 13; 
	public static final int PLUS = 14; 
	public static final int MULTIPLY = 15; 
	public static final int REMAINDER = 16;
	public static final int RIGHT_SHIFT = 17;
	public static final int EQUAL_EQUAL = 18;
	public static final int UNSIGNED_RIGHT_SHIFT= 19;
	public static final int NumberOfTables = 20;
	// <jml-start id="level.0.expression" />
	public static final int JML_IMPLIES = 20;
	public static final int JML_REV_IMPLIES = 21;
	// Note that only value 22 is left before we reach
	// the value of QUESTIONCOLON.
	public static final int NumberOfExtraTablesForJML = 2; // number of JML ops.
	// <jml-end id="level.0.expression" />
	public static final int QUESTIONCOLON = 23;

	public static final int NOT_EQUAL = 29;
	public static final int EQUAL = 30;
	public static final int INSTANCEOF = 31;
	public static final int PLUS_PLUS = 32;
	public static final int MINUS_MINUS = 33;

	// <jml-start id="level.0.expression" />
	// FIXME: write a JML4 test that uses reflection to ensure that JML_* constants
	// Do not use tag values allocated to non-JML constants.

	// Operators are partitioned into two groups:
	// (i) those for which which a type conversion table
	// needs to be defined (i.e. those in the series starting
	// at AND_AND and ending just before QUESTIONCOLON);
	// (ii) the rest

	public static final int JmlOtherOpIdStart = 40;
	public static final int JML_EQUIV = JmlOtherOpIdStart + 0;
	public static final int JML_NONNULLELEMENTS = JmlOtherOpIdStart + 1;
	public static final int JML_NOT_EQUIV = JmlOtherOpIdStart + 2;
	public static final int JML_OLD = JmlOtherOpIdStart + 3;
	public static final int JML_PRE = JmlOtherOpIdStart + 4;
	public static final int JML_TYPE = JmlOtherOpIdStart + 5;
	public static final int JML_TYPEOF = JmlOtherOpIdStart + 6;
	public static final int JML_ELEMTYPE = JmlOtherOpIdStart + 7;
	public static final int JML_NOT_ASSIGNED = JmlOtherOpIdStart + 8;
	public static final int JML_NOT_MODIFIED = JmlOtherOpIdStart + 9;
	// <jml-end id="level.0.expression" />
}
