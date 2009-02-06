theory AD_m9_1
imports Main
begin

lemma main: "((True & True) --> (((a_0::int) = (1 :: int)) --> (((b_0::int) = (2 :: int)) --> (((a_1::int) = (((a_0::int)) - ((b_0::int)))) --> (if ((a_1::int) ~= (((0 :: int)) - ((1 :: int)))) then True else ((b_0::int) ~= (2 :: int)) )))))" 
  oops
done

end
