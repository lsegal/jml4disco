theory AD_m13_1
imports Main
begin

lemma main: "((True & True) --> (((a_0::int) = (5 :: int)) --> (((b_0::int) = (2 :: int)) --> (((b_1::int) = (((b_0::int)) + ((1 :: int)))) --> (((a_1::int) = (b_1::int)) --> (if ((a_1::int) ~= (3 :: int)) then True else ((b_1::int) ~= (3 :: int)) ))))))" 
  oops
done

end
