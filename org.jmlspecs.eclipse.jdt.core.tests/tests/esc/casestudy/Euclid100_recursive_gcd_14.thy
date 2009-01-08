theory Euclid100_recursive_gcd_14
imports Main
begin

lemma main: "((True & ((((a_2707_0::int) >= (0 :: int)) & ((b_2714_0::int) >= (0 :: int))) & (((b_2714_0::int) > (0 :: int)) | ((a_2707_0::int) > (0 :: int))))) --> (((b_2714_0::int) = (0 :: int)) --> (((return_0_0::int) = (a_2707_0::int)) --> (((gcd_isGcd_5_659_1::int) = (return_0_0::int)) --> (((a_isGcd_5_668_1::int) = (a_2707_0::int)) --> (((b_isGcd_5_675_1::int) = (b_2714_0::int)) --> (((a_divides_1_179_1::int) = (a_isGcd_5_668_0::int)) --> (((b_divides_1_186_1::int) = (gcd_isGcd_5_659_0::int)) --> ((((a_divides_1_179_0::int) >= (0 :: int)) & ((b_divides_1_186_0::int) > (0 :: int))) --> (((return_divides_1_0_0::bool) = ((((a_divides_1_179_0::int)) mod ((b_divides_1_186_0::int))) = (0 :: int))) --> (((a_divides_2_179_1::int) = (b_isGcd_5_675_0::int)) --> (((b_divides_2_186_1::int) = (gcd_isGcd_5_659_0::int)) --> ((((a_divides_2_179_0::int) >= (0 :: int)) & ((b_divides_2_186_0::int) > (0 :: int))) --> (((return_divides_2_0_0::bool) = ((((a_divides_2_179_0::int)) mod ((b_divides_2_186_0::int))) = (0 :: int))) --> (((return_isGcd_5_0_0::bool) = (((return_divides_1_0_0::bool) & (return_divides_2_0_0::bool)) & (ALL (d_427_0::int) . (((((0 :: int) < (d_427_0::int)) & ((d_427_0::int) <= (a_isGcd_5_668_0::int))) & ((d_427_0::int) <= (b_isGcd_5_675_0::int))) --> ((((0 :: int) < (d_427_0::int)) & ((d_427_0::int) <= (a_isGcd_5_668_0::int))) & ((d_427_0::int) <= (b_isGcd_5_675_0::int))))))) --> (return_isGcd_5_0_0::bool))))))))))))))))" 
  oops

end
