theory Euclid2And_isGcd_21
imports Main
begin

lemma main: "((True & ((((gcd_660_0::int) > (0 :: int)) & ((a_669_0::int) >= (0 :: int))) & ((b_676_0::int) >= (0 :: int)))) --> (((a_divides_1_180_0::int) = (a_669_0::int)) --> (((b_divides_1_187_0::int) = (gcd_660_0::int)) --> (((return_divides_1_0_0::bool) = ((((a_divides_1_180_0::int)) mod ((b_divides_1_187_0::int))) = (0 :: int))) --> (((a_divides_2_180_0::int) = (b_676_0::int)) --> (((b_divides_2_187_0::int) = (gcd_660_0::int)) --> (((return_divides_2_0_0::bool) = ((((a_divides_2_180_0::int)) mod ((b_divides_2_187_0::int))) = (0 :: int))) --> ((~ (~ ((return_divides_1_0_0::bool) & (return_divides_2_0_0::bool)))) --> (((i_766_0::int) = (2 :: int)) --> (((i_766_1::int) = (i_766_1::int)) --> ((((ALL (d_809_0::int) . ((((1 :: int) < (d_809_0::int)) & ((d_809_0::int) <= (i_766_1::int))) --> (((a_divides_4_180_1::int) = (a_669_0::int)) --> (((b_divides_4_187_1::int) = (d_809_0::int)) --> ((((a_divides_4_180_1::int) >= (0 :: int)) & ((b_divides_4_187_1::int) > (0 :: int))) & (((return_divides_4_0_0::bool) = ((((a_divides_4_180_1::int)) mod ((b_divides_4_187_1::int))) = (0 :: int))) --> (((a_divides_5_180_1::int) = (b_676_0::int)) --> (((b_divides_5_187_1::int) = (d_809_0::int)) --> ((((a_divides_5_180_1::int) >= (0 :: int)) & ((b_divides_5_187_1::int) > (0 :: int))) & (((return_divides_5_0_0::bool) = ((((a_divides_5_180_1::int)) mod ((b_divides_5_187_1::int))) = (0 :: int))) --> (((return_divides_4_0_0::bool) & (return_divides_5_0_0::bool)) --> ((d_809_0::int) <= (gcd_660_0::int))))))))))))) & (((2 :: int) <= (i_766_1::int)) & (((a_669_0::int) < (2 :: int)) | ((i_766_1::int) <= (((a_669_0::int)) + ((1 :: int))))))) & ((((((a_669_0::int)) - ((i_766_1::int)))) + ((2 :: int))) >= (0 :: int))) --> (((jmlWhile_3_var_0_1048_0::int) = (((((a_669_0::int)) - ((i_766_1::int)))) + ((2 :: int)))) --> (((i_766_1::int) <= (a_669_0::int)) --> (((a_divides_6_180_0::int) = (a_669_0::int)) --> (((b_divides_6_187_0::int) = (i_766_1::int)) --> (((return_divides_6_0_0::bool) = ((((a_divides_6_180_0::int)) mod ((b_divides_6_187_0::int))) = (0 :: int))) --> (((a_divides_7_180_0::int) = (b_676_0::int)) --> (((b_divides_7_187_0::int) = (i_766_1::int)) --> (((return_divides_7_0_0::bool) = ((((a_divides_7_180_0::int)) mod ((b_divides_7_187_0::int))) = (0 :: int))) --> ((~ (((return_divides_6_0_0::bool) & (return_divides_7_0_0::bool)) & ((i_766_1::int) > (gcd_660_0::int)))) --> (((i_766_2::int) = (((i_766_1::int)) + ((1 :: int)))) --> (ALL (d_809_0::int) . ((((1 :: int) < (d_809_0::int)) & ((d_809_0::int) <= (i_766_2::int))) --> (((a_divides_4_180_2::int) = (a_669_0::int)) --> (((b_divides_4_187_2::int) = (d_809_0::int)) --> ((((a_divides_4_180_2::int) >= (0 :: int)) & ((b_divides_4_187_2::int) > (0 :: int))) & (((return_divides_4_0_0::bool) = ((((a_divides_4_180_2::int)) mod ((b_divides_4_187_2::int))) = (0 :: int))) --> (((a_divides_5_180_2::int) = (b_676_0::int)) --> (((b_divides_5_187_2::int) = (d_809_0::int)) --> ((((a_divides_5_180_2::int) >= (0 :: int)) & ((b_divides_5_187_2::int) > (0 :: int))) & (((return_divides_5_0_0::bool) = ((((a_divides_5_180_2::int)) mod ((b_divides_5_187_2::int))) = (0 :: int))) --> (((return_divides_4_0_0::bool) & (return_divides_5_0_0::bool)) --> ((d_809_0::int) <= (gcd_660_0::int))))))))))))))))))))))))))))))))))" 
  oops

end
