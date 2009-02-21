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

	int ERROR_SYMBOL = 202,
		MAX_NAME_LENGTH = 41,
		NUM_STATES = 1374,

		NT_OFFSET = 202,
		SCOPE_UBOUND = 215,
		SCOPE_SIZE = 216,
		LA_STATE_OFFSET = 19661,
		MAX_LA = 1,
		NUM_RULES = 950,
		NUM_TERMINALS = 202,
		NUM_NON_TERMINALS = 404,
		NUM_SYMBOLS = 606,
		START_STATE = 1082,
		EOFT_SYMBOL = 98,
		EOLT_SYMBOL = 98,
		ACCEPT_ACTION = 19660,
		ERROR_ACTION = 19661;
}




