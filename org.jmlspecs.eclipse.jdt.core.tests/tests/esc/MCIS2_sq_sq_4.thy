theory MCIS2_sq_sq_4
imports UBP
begin

lemma main: "([| (True & (((i_382_0::int) > (0 :: int)) & ((j_389_0::int) > (0 :: int)))); ((return_0_0::int) = (((((((i_382_0::int)) * ((i_382_0::int)))) * ((j_389_0::int)))) * ((j_389_0::int))))|] ==>   (ALL (return_sq_2_0_0::int) (return_sq_1_0_0::int) (i_sq_1_124_0::int) (i_sq_2_124_0::int) . ((((i_sq_1_124_0::int) = (i_382_0::int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_1_124_0::int) = (i_382_0::int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_2_124_0::int) = (j_389_0::int)) --> (((return_sq_2_0_0::int) = (((i_sq_2_124_0::int)) * ((i_sq_2_124_0::int)))) --> ((return_0_0::int) = (((return_sq_1_0_0::int)) * ((return_sq_2_0_0::int)))))))))))))" 
  oops

end
