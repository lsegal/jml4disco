theory Euclid2And_isGcd_7
imports Main
begin

lemma main: "((True & ((((gcd_660_0::int) > (0 :: int)) & ((a_669_0::int) >= (0 :: int))) & ((b_676_0::int) >= (0 :: int)))) --> (((a_divides_1_180_0::int) = (a_669_0::int)) --> (((b_divides_1_187_0::int) = (gcd_660_0::int)) --> (((return_divides_1_0_0::bool) = ((((a_divides_1_180_0::int)) mod ((b_divides_1_187_0::int))) = (0 :: int))) --> (((a_divides_2_180_0::int) = (b_676_0::int)) --> (((b_divides_2_187_0::int) = (gcd_660_0::int)) --> (((return_divides_2_0_0::bool) = ((((a_divides_2_180_0::int)) mod ((b_divides_2_187_0::int))) = (0 :: int))) --> ((~ (~ ((return_divides_1_0_0::bool) & (return_divides_2_0_0::bool)))) --> (((i_766_0::int) = (2 :: int)) --> (ALL (d_809_0::int) . ((((1 :: int) < (d_809_0::int)) & ((d_809_0::int) <= (i_766_0::int))) --> (((a_divides_4_180_0::int) = (a_669_0::int)) --> (((b_divides_4_187_0::int) = (d_809_0::int)) --> ((((a_divides_4_180_0::int) >= (0 :: int)) & ((b_divides_4_187_0::int) > (0 :: int))) & (((return_divides_4_0_0::bool) = ((((a_divides_4_180_0::int)) mod ((b_divides_4_187_0::int))) = (0 :: int))) --> (((a_divides_5_180_0::int) = (b_676_0::int)) --> (((b_divides_5_187_0::int) = (d_809_0::int)) --> ((((a_divides_5_180_0::int) >= (0 :: int)) & ((b_divides_5_187_0::int) > (0 :: int))) & (((return_divides_5_0_0::bool) = ((((a_divides_5_180_0::int)) mod ((b_divides_5_187_0::int))) = (0 :: int))) --> (((return_divides_4_0_0::bool) & (return_divides_5_0_0::bool)) --> ((d_809_0::int) <= (gcd_660_0::int))))))))))))))))))))))" 
  oops

end
