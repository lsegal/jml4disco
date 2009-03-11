package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class BoogieAdapterTests extends InitialTests {

	public BoogieAdapterTests(String name) {
		super(name);
	}

	@Override
	protected void compareJavaToBoogie(String java, String boogie, String adapterOutput) {
		if (adapterOutput == null) return;

		// always run initial test first to validate boogie
		super.compareJavaToBoogie(java, boogie, adapterOutput);
		
		// run through adapter
		String key = JmlCompilerOptions.OPTION_JmlBoogieOutputOnly;
		getCompilerOptions().put(key, CompilerOptions.DISABLED);
		runNegativeTest(new String[] {"A.java", java}, adapterOutput);
		getCompilerOptions().put(key, CompilerOptions.ENABLED);
	}

	@Override
	public void test_001_assertFalse() {
		super.test_001_assertFalse();
	}

	@Override
	public void test_002_assertTrue() {
		super.test_002_assertTrue();
	}

	@Override
	public void test_003_assertParam() {
		super.test_003_assertParam();
	}

	@Override
	public void test_004_assert_sequence_and() {
		super.test_004_assert_sequence_and();
	}

	@Override
	public void test_005_assert_sequence_or() {
		super.test_005_assert_sequence_or();
	}

	@Override
	public void test_006_assert_sequence_and_or() {
		super.test_006_assert_sequence_and_or();
	}

	@Override
	public void test_007_assert_sequence_ft() {
		super.test_007_assert_sequence_ft();
	}

	@Override
	public void test_007_assert_sequence_or_and() {
		super.test_007_assert_sequence_or_and();
	}

	@Override
	public void test_008_assert_sequence_ff() {
		super.test_008_assert_sequence_ff();
	}

	@Override
	public void test_008_assert_sequence_tt() {
		super.test_008_assert_sequence_tt();
	}

	@Override
	public void test_009_assert_sequence_tf() {
		super.test_009_assert_sequence_tf();
	}

	@Override
	public void test_009_JavaAssertFalse() {
		super.test_009_JavaAssertFalse();
	}

	@Override
	public void test_010_JavaAssertTrue() {
		super.test_010_JavaAssertTrue();
	}

	@Override
	public void test_0100_assumeFalse() {
		super.test_0100_assumeFalse();
	}

	@Override
	public void test_0101_assumeTrue() {
		super.test_0101_assumeTrue();
	}

	@Override
	public void test_0110_JmlMethodDeclaration_EmptyMethod() {
		super.test_0110_JmlMethodDeclaration_EmptyMethod();
	}

	@Override
	public void test_0111_JmlMethodDefinition_EnsuresRequires() {
		super.test_0111_JmlMethodDefinition_EnsuresRequires();
	}

	@Override
	public void test_0200_sequence_assume_assert_tt() {
		super.test_0200_sequence_assume_assert_tt();
	}

	@Override
	public void test_0201_sequence_assume_assert_ff() {
		super.test_0201_sequence_assume_assert_ff();
	}

	@Override
	public void test_0202_sequence_assume_assert_ft() {
		super.test_0202_sequence_assume_assert_ft();
	}

	@Override
	public void test_0203_sequence_assume_assert_tf() {
		super.test_0203_sequence_assume_assert_tf();
	}

	@Override
	public void test_0296_LocalDeclaration_Blocks() {
		super.test_0296_LocalDeclaration_Blocks();
	}

	@Override
	public void test_0297_LocalDeclaration_multiVarName_diffScope() {
		super.test_0297_LocalDeclaration_multiVarName_diffScope();
	}

	@Override
	public void test_0298_LocalDeclaration() {
		super.test_0298_LocalDeclaration();
	}

	@Override
	public void test_0299_LocalDeclarationWithInitialization() {
		super.test_0299_LocalDeclarationWithInitialization();
	}

	@Override
	public void test_0300_IfCondition() {
		super.test_0300_IfCondition();
	}

	@Override
	public void test_0301_IfCondition_noBlock() {
		super.test_0301_IfCondition_noBlock();
	}

	@Override
	public void test_0302_IfCondition_ternary() {
		super.test_0302_IfCondition_ternary();
	}

	@Override
	public void test_0310_EmptyStatement() {
		super.test_0310_EmptyStatement();
	}

	@Override
	public void test_0320_UnaryExpression() {
		super.test_0320_UnaryExpression();
	}

	@Override
	public void test_0321_UnaryExpression() {
		super.test_0321_UnaryExpression();
	}

	@Override
	public void test_0350_while() {
		super.test_0350_while();
	}

	@Override
	public void test_0370_while_break_withlabel() {
		super.test_0370_while_break_withlabel();
	}

	@Override
	public void test_0371_while_break() {
		super.test_0371_while_break();
	}

	@Override
	public void test_1000_int_eq() {
		super.test_1000_int_eq();
	}

	@Override
	public void test_1000_int_localdeclaration() {
		super.test_1000_int_localdeclaration();
	}

	@Override
	public void test_1001_int_arith() {
		super.test_1001_int_arith();
	}

	@Override
	public void test_1002_arith_cond() {
		super.test_1002_arith_cond();
	}

	@Override
	public void test_1003_boolExpr_cond() {
		super.test_1003_boolExpr_cond();
	}

	@Override
	public void test_1004_implies() {
		super.test_1004_implies();
	}

	@Override
	public void test_2000_messageSend() {
		super.test_2000_messageSend();
	}

	@Override
	public void test_2001_messageSend() {
		super.test_2001_messageSend();
	}

	@Override
	public void test_2002_messageSend() {
		super.test_2002_messageSend();
	}

	@Override
	public void test_2003_messageSendStatic() {
		super.test_2003_messageSendStatic();
	}

	@Override
	public void test_2004_messageSendOnReceiver() {
		super.test_2004_messageSendOnReceiver();
	}

	@Override
	public void test_2005_messageSendOnField() {
		super.test_2005_messageSendOnField();
	}

	@Override
	public void test_2005_messageSendOnLocal() {
		super.test_2005_messageSendOnLocal();
	}

	@Override
	public void test_2005_messageSendOnThis() {
		super.test_2005_messageSendOnThis();
	}

	@Override
	public void test_400_do() {
		super.test_400_do();
	}

	@Override
	public void test_401_do_multiline() {
		super.test_401_do_multiline();
	}

	@Override
	public void test_501_for_multi_initialization() {
		super.test_501_for_multi_initialization();
	}

	@Override
	public void test_500_for() {
		super.test_500_for();
	}

	@Override
	public void test_600_postFixExpression() {
		super.test_600_postFixExpression();
	}

	@Override
	public void test_601_preFixExpression() {
		super.test_601_preFixExpression();
	}

	@Override
	public void test_602_pre_post_FixExpression() {
		super.test_602_pre_post_FixExpression();
	}

	@Override
	public void test_603_post_pre_FixExpression() {
		super.test_603_post_pre_FixExpression();
	}

	@Override
	public void test_604_multiAssignment() {
		super.test_604_multiAssignment();
	}

	@Override
	public void test_700_localVarDecl_order() {
		super.test_700_localVarDecl_order();
	}

	@Override
	public void test_800_FieldDeclaration() {
		super.test_800_FieldDeclaration();
	}

	@Override
	public void test_801_Static_FieldDeclaration() {
		super.test_801_Static_FieldDeclaration();
	}

	@Override
	public void testDoubleLiteral() {
		super.testDoubleLiteral();
	}

	@Override
	public void testFalseLiteral() {
		super.testFalseLiteral();
	}

	@Override
	public void testIntLiteral() {
		super.testIntLiteral();
	}

	@Override
	public void testMethodDefinition() {
		super.testMethodDefinition();
	}

	@Override
	public void testTrueLiteral() {
		super.testTrueLiteral();
	}
	
	

}
