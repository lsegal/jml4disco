/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.compiler.parser;

/*An interface that contains static declarations for some basic information
 about the parser such as the number of rules in the grammar, the starting state, etc...*/
public interface ParserBasicInformation {

	int ERROR_SYMBOL = 196,
		MAX_NAME_LENGTH = 41,
		NUM_STATES = 1362,

		NT_OFFSET = 196,
		SCOPE_UBOUND = 206,
		SCOPE_SIZE = 207,
		LA_STATE_OFFSET = 18375,
		MAX_LA = 1,
		NUM_RULES = 946,
		NUM_TERMINALS = 196,
		NUM_NON_TERMINALS = 396,
		NUM_SYMBOLS = 592,
		START_STATE = 1307,
		EOFT_SYMBOL = 97,
		EOLT_SYMBOL = 97,
		ACCEPT_ACTION = 18374,
		ERROR_ACTION = 18375;
}




