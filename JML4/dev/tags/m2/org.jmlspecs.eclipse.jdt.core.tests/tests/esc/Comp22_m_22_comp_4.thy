theory Comp22_m_22_comp_4
imports UBP
begin

lemma main: "([| (True & (if ((y_142_0::int) >= (0 :: int)) then ((x_135_0::int) >= (0 :: int)) else False )); ((z_153_0::int) = (x_135_0::int)); ((w_166_0::int) = (y_142_0::int)); ((z_153_1::int) = (z_153_1::int)); ((w_166_1::int) = (w_166_1::int)); (((z_153_1::int) = (((((x_135_0::int)) + ((((y_142_0::int)) * ((y_142_0::int)))))) - ((((w_166_1::int)) * ((y_142_0::int)))))) & ((w_166_1::int) >= (0 :: int))); (~ ((w_166_1::int) > (0 :: int))); ((return_0_0::int) = (z_153_1::int))|] ==>   ((return_0_0::int) = (((x_135_0::int)) + ((((y_142_0::int)) * ((y_142_0::int)))))))" 
  oops

end
