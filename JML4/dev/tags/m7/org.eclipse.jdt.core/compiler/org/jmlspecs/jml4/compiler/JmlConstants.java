package org.jmlspecs.jml4.compiler;

public interface JmlConstants {

	// JML language levels:
	long JML_LEVEL_NO_JML = 0;
	long JML_LEVEL_NNTS = 1; // Non-Null Type System
	long JML_LEVEL_DBC = 2;
	
	// Misc
	char SLASH = '/';
	char SQUOTE = '\'';

	public static final char[] JML_ANON = "jml$anon".toCharArray(); //$NON-NLS-1$

	String EMPTY_STRING = ""; //$NON-NLS-1$
	String COMMA = ","; //$NON-NLS-1$
	String SPACE = " "; //$NON-NLS-1$
	String SEMICOLON = ";"; //$NON-NLS-1$

	// FIXME: the following two are already declared elsewhere ...
	String THIS = "this"; //$NON-NLS-1$
	String SUPER = "super"; //$NON-NLS-1$

	// Temporary global constants
	// Processing stages
	int PARSE = 10;
	int RESOLVE = 20;
	int CODE_ANALYSIS = 30;
	int CODE_GENERATION = 40;
	int ALL_PROCESSING_STAGES = 100;
	int LAST_PROCESSING_STAGE = ALL_PROCESSING_STAGES;
	
	boolean ENABLE_SPEC_MERGE = true;
}
