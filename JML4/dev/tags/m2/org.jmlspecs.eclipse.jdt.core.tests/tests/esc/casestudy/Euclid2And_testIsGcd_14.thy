theory Euclid2And_testIsGcd_14
imports Main
begin

lemma main: "((True & True) --> (((gcd_isGcd_5_660_0::int) = (6 :: int)) --> (((a_isGcd_5_669_0::int) = (12 :: int)) --> (((b_isGcd_5_676_0::int) = (18 :: int)) --> (((a_divides_1_180_0::int) = (a_isGcd_5_669_0::int)) --> (((b_divides_1_187_0::int) = (gcd_isGcd_5_660_0::int)) --> ((((a_divides_1_180_0::int) >= (0 :: int)) & ((b_divides_1_187_0::int) > (0 :: int))) --> (((return_divides_1_0_0::bool) = ((((a_divides_1_180_0::int)) mod ((b_divides_1_187_0::int))) = (0 :: int))) --> (((a_divides_2_180_0::int) = (b_isGcd_5_676_0::int)) --> (((b_divides_2_187_0::int) = (gcd_isGcd_5_660_0::int)) --> ((((a_divides_2_180_0::int) >= (0 :: int)) & ((b_divides_2_187_0::int) > (0 :: int))) --> (((return_divides_2_0_0::bool) = ((((a_divides_2_180_0::int)) mod ((b_divides_2_187_0::int))) = (0 :: int))) --> (((return_isGcd_5_0_0::bool) = (((return_divides_1_0_0::bool) & (return_divides_2_0_0::bool)) & (ALL (d_428_0::int) . (((((0 :: int) < (d_428_0::int)) & ((d_428_0::int) <= (a_isGcd_5_669_0::int))) & ((d_428_0::int) <= (b_isGcd_5_676_0::int))) --> (((a_divides_3_180_0::int) = (a_isGcd_5_669_0::int)) --> (((b_divides_3_187_0::int) = (d_428_0::int)) --> ((((a_divides_3_180_0::int) >= (0 :: int)) & ((b_divides_3_187_0::int) > (0 :: int))) --> (((return_divides_3_0_0::bool) = ((((a_divides_3_180_0::int)) mod ((b_divides_3_187_0::int))) = (0 :: int))) --> (((a_divides_4_180_0::int) = (b_isGcd_5_676_0::int)) --> (((b_divides_4_187_0::int) = (d_428_0::int)) --> ((((a_divides_4_180_0::int) >= (0 :: int)) & ((b_divides_4_187_0::int) > (0 :: int))) --> (((return_divides_4_0_0::bool) = ((((a_divides_4_180_0::int)) mod ((b_divides_4_187_0::int))) = (0 :: int))) --> (((return_divides_3_0_0::bool) & (return_divides_4_0_0::bool)) --> ((d_428_0::int) <= (gcd_isGcd_5_660_0::int))))))))))))))) --> (((gcd_isGcd_10_660_0::int) = (2 :: int)) --> (((a_isGcd_10_669_0::int) = (4 :: int)) --> (((b_isGcd_10_676_0::int) = (14 :: int)) --> (((a_divides_6_180_0::int) = (a_isGcd_10_669_0::int)) --> (((b_divides_6_187_0::int) = (gcd_isGcd_10_660_0::int)) --> ((((a_divides_6_180_0::int) >= (0 :: int)) & ((b_divides_6_187_0::int) > (0 :: int))) --> (((return_divides_6_0_0::bool) = ((((a_divides_6_180_0::int)) mod ((b_divides_6_187_0::int))) = (0 :: int))) --> (((a_divides_7_180_0::int) = (b_isGcd_10_676_0::int)) --> (((b_divides_7_187_0::int) = (gcd_isGcd_10_660_0::int)) --> ((((a_divides_7_180_0::int) >= (0 :: int)) & ((b_divides_7_187_0::int) > (0 :: int))) --> (((return_divides_7_0_0::bool) = ((((a_divides_7_180_0::int)) mod ((b_divides_7_187_0::int))) = (0 :: int))) --> (((return_isGcd_10_0_0::bool) = (((return_divides_6_0_0::bool) & (return_divides_7_0_0::bool)) & (ALL (d_428_0::int) . (((((0 :: int) < (d_428_0::int)) & ((d_428_0::int) <= (a_isGcd_10_669_0::int))) & ((d_428_0::int) <= (b_isGcd_10_676_0::int))) --> (((a_divides_8_180_0::int) = (a_isGcd_10_669_0::int)) --> (((b_divides_8_187_0::int) = (d_428_0::int)) --> ((((a_divides_8_180_0::int) >= (0 :: int)) & ((b_divides_8_187_0::int) > (0 :: int))) --> (((return_divides_8_0_0::bool) = ((((a_divides_8_180_0::int)) mod ((b_divides_8_187_0::int))) = (0 :: int))) --> (((a_divides_9_180_0::int) = (b_isGcd_10_676_0::int)) --> (((b_divides_9_187_0::int) = (d_428_0::int)) --> ((((a_divides_9_180_0::int) >= (0 :: int)) & ((b_divides_9_187_0::int) > (0 :: int))) --> (((return_divides_9_0_0::bool) = ((((a_divides_9_180_0::int)) mod ((b_divides_9_187_0::int))) = (0 :: int))) --> (((return_divides_8_0_0::bool) & (return_divides_9_0_0::bool)) --> ((d_428_0::int) <= (gcd_isGcd_10_660_0::int))))))))))))))) --> (((gcd_isGcd_15_660_0::int) = (14 :: int)) --> (((a_isGcd_15_669_0::int) = (42 :: int)) --> (((b_isGcd_15_676_0::int) = (56 :: int)) --> (((a_divides_11_180_0::int) = (a_isGcd_15_669_0::int)) --> (((b_divides_11_187_0::int) = (gcd_isGcd_15_660_0::int)) --> ((((a_divides_11_180_0::int) >= (0 :: int)) & ((b_divides_11_187_0::int) > (0 :: int))) --> (((return_divides_11_0_0::bool) = ((((a_divides_11_180_0::int)) mod ((b_divides_11_187_0::int))) = (0 :: int))) --> (((a_divides_12_180_0::int) = (b_isGcd_15_676_0::int)) --> (((b_divides_12_187_0::int) = (gcd_isGcd_15_660_0::int)) --> ((((a_divides_12_180_0::int) >= (0 :: int)) & ((b_divides_12_187_0::int) > (0 :: int))) --> (((return_divides_12_0_0::bool) = ((((a_divides_12_180_0::int)) mod ((b_divides_12_187_0::int))) = (0 :: int))) --> (((return_isGcd_15_0_0::bool) = (((return_divides_11_0_0::bool) & (return_divides_12_0_0::bool)) & (ALL (d_428_0::int) . (((((0 :: int) < (d_428_0::int)) & ((d_428_0::int) <= (a_isGcd_15_669_0::int))) & ((d_428_0::int) <= (b_isGcd_15_676_0::int))) --> (((a_divides_13_180_0::int) = (a_isGcd_15_669_0::int)) --> (((b_divides_13_187_0::int) = (d_428_0::int)) --> ((((a_divides_13_180_0::int) >= (0 :: int)) & ((b_divides_13_187_0::int) > (0 :: int))) --> (((return_divides_13_0_0::bool) = ((((a_divides_13_180_0::int)) mod ((b_divides_13_187_0::int))) = (0 :: int))) --> (((a_divides_14_180_0::int) = (b_isGcd_15_676_0::int)) --> (((b_divides_14_187_0::int) = (d_428_0::int)) --> ((((a_divides_14_180_0::int) >= (0 :: int)) & ((b_divides_14_187_0::int) > (0 :: int))) --> (((return_divides_14_0_0::bool) = ((((a_divides_14_180_0::int)) mod ((b_divides_14_187_0::int))) = (0 :: int))) --> (((return_divides_13_0_0::bool) & (return_divides_14_0_0::bool)) --> ((d_428_0::int) <= (gcd_isGcd_15_660_0::int))))))))))))))) --> (return_isGcd_15_0_0::bool))))))))))))))))))))))))))))))))))))))" 
  oops

end