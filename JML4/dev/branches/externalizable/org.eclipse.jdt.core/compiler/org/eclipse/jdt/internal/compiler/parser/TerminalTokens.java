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

/**
 * IMPORTANT NOTE: These constants are dedicated to the internal Scanner implementation. 
 * It is mirrored in org.eclipse.jdt.core.compiler public package where it is API. 
 * The mirror implementation is using the backward compatible ITerminalSymbols constant 
 * definitions (stable with 2.0), whereas the internal implementation uses TerminalTokens 
 * which constant values reflect the latest parser generation state.
 */
/**
 * Maps each terminal symbol in the java-grammar into a unique integer. 
 * This integer is used to represent the terminal when computing a parsing action. 
 * 
 * Disclaimer : These constant values are generated automatically using a Java 
 * grammar, therefore their actual values are subject to change if new keywords 
 * were added to the language (for instance, 'assert' is a keyword in 1.4).
 */
public interface TerminalTokens {

	// special tokens not part of grammar - not autogenerated
	int TokenNameWHITESPACE = 1000,
		TokenNameCOMMENT_LINE = 1001,
		TokenNameCOMMENT_BLOCK = 1002,
		TokenNameCOMMENT_JAVADOC = 1003;

	int TokenNameIdentifier = 32,
		TokenNameabstract = 74,
		TokenNameassert = 133,
		TokenNameboolean = 36,
		TokenNamebreak = 134,
		TokenNamebyte = 37,
		TokenNamecase = 161,
		TokenNamecatch = 163,
		TokenNamechar = 38,
		TokenNameclass = 111,
		TokenNamecontinue = 135,
		TokenNameconst = 191,
		TokenNamedefault = 157,
		TokenNamedo = 126,
		TokenNamedouble = 39,
		TokenNameelse = 164,
		TokenNameenum = 155,
		TokenNameextends = 158,
		TokenNamefalse = 50,
		TokenNamefinal = 75,
		TokenNamefinally = 165,
		TokenNamefloat = 40,
		TokenNamefor = 127,
		TokenNamegoto = 192,
		TokenNameif = 136,
		TokenNameimplements = 173,
		TokenNameimport = 159,
		TokenNameinstanceof = 11,
		TokenNameint = 41,
		TokenNameinterface = 128,
		TokenNamelong = 42,
		TokenNamenative = 76,
		TokenNamenew = 48,
		TokenNamenull = 51,
		TokenNamepackage = 156,
		TokenNameprivate = 77,
		TokenNameprotected = 78,
		TokenNamepublic = 79,
		TokenNamereturn = 137,
		TokenNameshort = 43,
		TokenNamestatic = 72,
		TokenNamestrictfp = 80,
		TokenNamesuper = 46,
		TokenNameswitch = 138,
		TokenNamesynchronized = 73,
		TokenNamethis = 47,
		TokenNamethrow = 139,
		TokenNamethrows = 167,
		TokenNametransient = 81,
		TokenNametrue = 52,
		TokenNametry = 140,
		TokenNamevoid = 44,
		TokenNamevolatile = 82,
		TokenNamewhile = 122,
		TokenNameIntegerLiteral = 53,
		TokenNameLongLiteral = 54,
		TokenNameFloatingPointLiteral = 55,
		TokenNameDoubleLiteral = 56,
		TokenNameCharacterLiteral = 57,
		TokenNameStringLiteral = 58,
		TokenNamealso = 112,
		TokenNamejml_assert = 141,
		TokenNameassume = 142,
		TokenNamecode_bigint_math = 83,
		TokenNamecode_java_math = 84,
		TokenNamecode_safe_math = 85,
		TokenNameghost = 86,
		TokenNamehelper = 87,
		TokenNameinstance = 88,
		TokenNamemodel = 89,
		TokenNamenon_null = 99,
		TokenNamenon_null_by_default = 102,
		TokenNamenullable = 100,
		TokenNamenullable_by_default = 103,
		TokenNamemono_non_null = 101,
		TokenNamepure = 90,
		TokenNamespec_public = 91,
		TokenNamespec_protected = 92,
		TokenNamespec_bigint_math = 93,
		TokenNamespec_java_math = 94,
		TokenNamespec_safe_math = 95,
		TokenNameuninitialized = 96,
		TokenNameslash_rep = 104,
		TokenNameslash_peer = 105,
		TokenNameslash_readonly = 106,
		TokenNamerep = 107,
		TokenNamepeer = 108,
		TokenNamereadonly = 109,
		TokenNameAssignableOrSynonym = 113,
		TokenNameAssignableRedundantlyOrSynonym = 114,
		TokenNameaxiom = 193,
		TokenNameBehaviorOrSynonym = 162,
		TokenNameconstraint = 174,
		TokenNamediverges = 194,
		TokenNameEnsuresOrSynonym = 115,
		TokenNameEnsuresRedundantlyOrSynonym = 116,
		TokenNameimplies_that = 166,
		TokenNameinitially = 175,
		TokenNameinvariant = 176,
		TokenNameinvariant_redundantly = 195,
		TokenNamerepresents = 177,
		TokenNamerepresents_redundantly = 178,
		TokenNameRequiresOrSynonym = 123,
		TokenNameRequiresRedundantlyOrSynonym = 124,
		TokenNameSignalsOrSynonym = 117,
		TokenNameSignalsRedundantlyOrSynonym = 118,
		TokenNamesignals_only = 119,
		TokenNamesignals_only_redundantly = 120,
		TokenNameset = 143,
		TokenNameloop_invariant = 131,
		TokenNameloop_invariant_redundantly = 132,
		TokenNamedecreases = 129,
		TokenNamedecreases_redundantly = 130,
		TokenNameslash_everything = 179,
		TokenNameslash_nonnullelements = 59,
		TokenNameslash_nothing = 168,
		TokenNameslash_old = 60,
		TokenNameslash_pre = 61,
		TokenNameslash_result = 62,
		TokenNameslash_same = 180,
		TokenNameslash_not_specified = 160,
		TokenNameslash_forall = 181,
		TokenNameslash_fresh = 63,
		TokenNameslash_exists = 182,
		TokenNameslash_max = 183,
		TokenNameslash_min = 184,
		TokenNameslash_num_of = 185,
		TokenNameslash_product = 186,
		TokenNameslash_sum = 187,
		TokenNameslash_type = 64,
		TokenNameslash_typeof = 65,
		TokenNameslash_elemtype = 66,
		TokenNamein = 169,
		TokenNamein_redundantly = 170,
		TokenNamemaps = 171,
		TokenNamemaps_redundantly = 172,
		TokenNameslash_into = 188,
		TokenNameInformalDescription = 49,
		TokenNameDOTDOT = 110,
		TokenNameEQUIV = 30,
		TokenNameIMPLIES = 26,
		TokenNameLBRACE_OR = 125,
		TokenNameNOT_EQUIV = 31,
		TokenNameOR_RBRACE = 189,
		TokenNameREV_IMPLIES = 28,
		TokenNameSUBTYPE = 14,
		TokenNamePLUS_PLUS = 19,
		TokenNameMINUS_MINUS = 20,
		TokenNameEQUAL_EQUAL = 16,
		TokenNameLESS_EQUAL = 8,
		TokenNameGREATER_EQUAL = 9,
		TokenNameNOT_EQUAL = 17,
		TokenNameLEFT_SHIFT = 15,
		TokenNameRIGHT_SHIFT = 12,
		TokenNameUNSIGNED_RIGHT_SHIFT = 13,
		TokenNamePLUS_EQUAL = 144,
		TokenNameMINUS_EQUAL = 145,
		TokenNameMULTIPLY_EQUAL = 146,
		TokenNameDIVIDE_EQUAL = 147,
		TokenNameAND_EQUAL = 148,
		TokenNameOR_EQUAL = 149,
		TokenNameXOR_EQUAL = 150,
		TokenNameREMAINDER_EQUAL = 151,
		TokenNameLEFT_SHIFT_EQUAL = 152,
		TokenNameRIGHT_SHIFT_EQUAL = 153,
		TokenNameUNSIGNED_RIGHT_SHIFT_EQUAL = 154,
		TokenNameOR_OR = 25,
		TokenNameAND_AND = 24,
		TokenNamePLUS = 1,
		TokenNameMINUS = 2,
		TokenNameNOT = 69,
		TokenNameREMAINDER = 4,
		TokenNameXOR = 21,
		TokenNameAND = 18,
		TokenNameMULTIPLY = 3,
		TokenNameOR = 22,
		TokenNameTWIDDLE = 70,
		TokenNameDIVIDE = 5,
		TokenNameGREATER = 10,
		TokenNameLESS = 6,
		TokenNameLPAREN = 34,
		TokenNameRPAREN = 33,
		TokenNameLBRACE = 98,
		TokenNameRBRACE = 45,
		TokenNameLBRACKET = 23,
		TokenNameRBRACKET = 68,
		TokenNameSEMICOLON = 29,
		TokenNameQUESTION = 27,
		TokenNameCOLON = 67,
		TokenNameCOMMA = 35,
		TokenNameDOT = 7,
		TokenNameEQUAL = 121,
		TokenNameAT = 71,
		TokenNameELLIPSIS = 190,
		TokenNameEOF = 97,
		TokenNameERROR = 196;
}