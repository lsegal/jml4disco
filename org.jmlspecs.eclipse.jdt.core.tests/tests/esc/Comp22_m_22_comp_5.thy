theory Comp22_m_22_comp_5
imports UBP
begin

lemma main: "([| (True & (if ((y_142_0::int) >= (0 :: int)) then ((x_135_0::int) >= (0 :: int)) else False )); ((z_153_0::int) = (x_135_0::int)); ((w_166_0::int) = (y_142_0::int)); ((z_153_1::int) = (z_153_1::int)); ((w_166_1::int) = (w_166_1::int)); (((z_153_1::int) = (((((x_135_0::int)) + ((((y_142_0::int)) * ((y_142_0::int)))))) - ((((w_166_1::int)) * ((y_142_0::int)))))) & ((w_166_1::int) >= (0 :: int))); ((jmlWhile_1_var_0_269_0::int) = (w_166_1::int)); ((w_166_1::int) > (0 :: int)); ((z_153_2::int) = (((z_153_1::int)) + ((y_142_0::int)))); ((w_166_2::int) = (((w_166_1::int)) - ((1 :: int))))|] ==>   ((((((y_142_0::int)) * ((w_166_2::int)))) + ((z_153_2::int))) = (((x_135_0::int)) + ((((y_142_0::int)) * ((y_142_0::int)))))))" 
  oops

end
