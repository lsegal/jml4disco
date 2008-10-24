theory MCIS1_m2_3
imports UBP
begin

lemma main: "([| (True & ((i_413_0::int) > (1 :: int)))|] ==>   (ALL (i_sq_1_124_0::int) (i_cube_2_238_0::int) (return_sq_1_0_0::int) (return_cube_2_0_0::int) . ((((i_cube_2_238_0::int) = (i_413_0::int)) --> (((i_cube_2_238_0::int) = (i_413_0::int)) --> (((i_sq_1_124_0::int) = (i_cube_2_238_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((return_cube_2_0_0::int) = (((i_cube_2_238_0::int)) * ((return_sq_1_0_0::int)))) --> ((return_cube_2_0_0::int) = (((((i_413_0::int)) * ((i_413_0::int)))) + ((i_413_0::int)))))))))))))" 
  oops

end
