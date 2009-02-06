theory PMC_m2_4
imports UBP
begin

lemma main: "([| (True & True)|] ==>   (ALL (i_sq_p1_1_129_0::int) (return_sq_p1_1_0_0::int) . ((((i_sq_p1_1_129_0::int) = (6 :: int)) --> (((return_sq_p1_1_0_0::int) = (((((i_sq_p1_1_129_0::int)) * ((i_sq_p1_1_129_0::int)))) + ((1 :: int)))) --> (((n_334_0::int) = (6 :: int)) --> (ALL (return_sq_p1_2_0_0::int) (i_sq_p1_2_129_0::int) . ((((i_sq_p1_2_129_0::int) = (n_334_0::int)) --> (((return_sq_p1_2_0_0::int) = (((((i_sq_p1_2_129_0::int)) * ((i_sq_p1_2_129_0::int)))) + ((1 :: int)))) --> ((37 :: int) ~= (return_sq_p1_2_0_0::int))))))))))))" 
  oops

end
