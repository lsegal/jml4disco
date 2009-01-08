theory Quant1_m1_1
imports Main
begin

lemma main: "([| (True & True)|] ==>   (EX (i_93_0::int) (j_95_0::int) . ((((0 :: int) <= (i_93_0::int)) & ((j_95_0::int) < (10 :: int))) & ((i_93_0::int) < (j_95_0::int)))))" 
  apply (rule_tac x=5 in exI)
  apply (rule_tac x=9 in exI)
  apply simp
done

end
