theory Euclid100_isGcd_7
imports Main
begin

lemma main: "((True & ((((gcd_659_0::int) > (0 :: int)) & ((a_668_0::int) >= (0 :: int))) & ((b_675_0::int) >= (0 :: int)))) --> (((a_divides_1_179_0::int) = (a_668_0::int)) --> (((b_divides_1_186_0::int) = (gcd_659_0::int)) --> (((return_divides_1_0_0::bool) = ((((a_divides_1_179_0::int)) mod ((b_divides_1_186_0::int))) = (0 :: int))) --> (((a_divides_2_179_0::int) = (b_675_0::int)) --> (((b_divides_2_186_0::int) = (gcd_659_0::int)) --> (((return_divides_2_0_0::bool) = ((((a_divides_2_179_0::int)) mod ((b_divides_2_186_0::int))) = (0 :: int))) --> ((~ (~ ((return_divides_1_0_0::bool) & (return_divides_2_0_0::bool)))) --> (((i_765_0::int) = (2 :: int)) --> (ALL (d_808_0::int) . ((((1 :: int) < (d_808_0::int)) & ((d_808_0::int) <= (i_765_0::int))) --> (((a_divides_4_179_0::int) = (a_668_0::int)) --> (((b_divides_4_186_0::int) = (d_808_0::int)) --> ((((a_divides_4_179_0::int) >= (0 :: int)) & ((b_divides_4_186_0::int) > (0 :: int))) & (((return_divides_4_0_0::bool) = ((((a_divides_4_179_0::int)) mod ((b_divides_4_186_0::int))) = (0 :: int))) --> (((a_divides_5_179_0::int) = (b_675_0::int)) --> (((b_divides_5_186_0::int) = (d_808_0::int)) --> ((((a_divides_5_179_0::int) >= (0 :: int)) & ((b_divides_5_186_0::int) > (0 :: int))) & (((return_divides_5_0_0::bool) = ((((a_divides_5_179_0::int)) mod ((b_divides_5_186_0::int))) = (0 :: int))) --> (((return_divides_4_0_0::bool) & (return_divides_5_0_0::bool)) --> ((d_808_0::int) <= (gcd_659_0::int))))))))))))))))))))))" 
  oops

end
