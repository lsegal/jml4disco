theory MCIS2_m1_1
imports UBP
begin

lemma main: "([| (True & True)|] ==>   (ALL (return_cube_5_0_0::int) (i_cube_5_238_0::int) (j_sq_sq_3_389_0::int) (return_sq_2_0_0::int) (i_sq_1_124_0::int) (return_sq_4_0_0::int) (return_sq_1_0_0::int) (i_sq_2_124_0::int) (return_sq_sq_3_0_0::int) (i_sq_4_124_0::int) (i_sq_sq_3_382_0::int) . ((ALL (i_474_0::int) (j_477_0::int) . ((if ((i_474_0::int) > (0 :: int)) then ((i_474_0::int) = (j_477_0::int)) else False ) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_2_124_0::int) = (j_sq_sq_3_389_0::int)) --> (((i_sq_2_124_0::int) > (0 :: int)) --> (((return_sq_2_0_0::int) = (((i_sq_2_124_0::int)) * ((i_sq_2_124_0::int)))) --> (((return_sq_sq_3_0_0::int) = (((return_sq_1_0_0::int)) * ((return_sq_2_0_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_2_124_0::int) = (j_sq_sq_3_389_0::int)) --> (((i_sq_2_124_0::int) > (0 :: int)) --> (((return_sq_2_0_0::int) = (((i_sq_2_124_0::int)) * ((i_sq_2_124_0::int)))) --> (((return_sq_sq_3_0_0::int) = (((return_sq_1_0_0::int)) * ((return_sq_2_0_0::int)))) --> (((i_cube_5_238_0::int) = (j_477_0::int)) --> (((i_cube_5_238_0::int) > (0 :: int)) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_2_124_0::int) = (j_sq_sq_3_389_0::int)) --> (((i_sq_2_124_0::int) > (0 :: int)) --> (((return_sq_2_0_0::int) = (((i_sq_2_124_0::int)) * ((i_sq_2_124_0::int)))) --> (((return_sq_sq_3_0_0::int) = (((return_sq_1_0_0::int)) * ((return_sq_2_0_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_sq_3_382_0::int) = (i_474_0::int)) --> (((j_sq_sq_3_389_0::int) = (j_477_0::int)) --> ((((i_sq_sq_3_382_0::int) > (0 :: int)) & ((j_sq_sq_3_389_0::int) > (0 :: int))) & (((i_sq_1_124_0::int) = (i_sq_sq_3_382_0::int)) --> (((i_sq_1_124_0::int) > (0 :: int)) --> (((return_sq_1_0_0::int) = (((i_sq_1_124_0::int)) * ((i_sq_1_124_0::int)))) --> (((i_sq_2_124_0::int) = (j_sq_sq_3_389_0::int)) --> (((i_sq_2_124_0::int) > (0 :: int)) --> (((return_sq_2_0_0::int) = (((i_sq_2_124_0::int)) * ((i_sq_2_124_0::int)))) --> (((return_sq_sq_3_0_0::int) = (((return_sq_1_0_0::int)) * ((return_sq_2_0_0::int)))) --> (((i_cube_5_238_0::int) = (j_477_0::int)) --> (((i_cube_5_238_0::int) > (0 :: int)) & (((i_sq_4_124_0::int) = (i_cube_5_238_0::int)) --> (((i_sq_4_124_0::int) > (0 :: int)) --> (((return_sq_4_0_0::int) = (((i_sq_4_124_0::int)) * ((i_sq_4_124_0::int)))) --> (((return_cube_5_0_0::int) = (((i_cube_5_238_0::int)) * ((return_sq_4_0_0::int)))) --> ((return_sq_sq_3_0_0::int) = (((i_474_0::int)) * ((return_cube_5_0_0::int)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))" 
  oops

end
