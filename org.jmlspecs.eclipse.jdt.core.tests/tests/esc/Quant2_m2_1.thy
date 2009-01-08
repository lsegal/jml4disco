theory Quant2_m2_1
imports Main
begin

lemma main: "([| (True & True)|] ==>   (EX (i_93_0::int) (j_95_0::int) . ((if ((0 :: int) <= (i_93_0::int)) then ((j_95_0::int) < (10 :: int)) else False ) & ((i_93_0::int) < (j_95_0::int)))))" 
  apply (rule_tac x=5 in exI)
  apply (rule_tac x=9 in exI)
  apply simp
done

end
