theory X_countDownWithSideEffect2_2
imports UBP
begin

lemma main: "([| (True & True); ((i_88_0::int) = (10 :: int)); ((i_88_1::int) = (i_88_1::int)); (((i_88_1::int) >= (0 :: int)) & ((i_88_1::int) >= (0 :: int))); ((i_88_2::int) = (((i_88_1::int)) - ((1 :: int)))); (~ ((0 :: int) < (i_88_2::int)))|] ==>   ((i_88_2::int) = (0 :: int)))" 
  oops

end
