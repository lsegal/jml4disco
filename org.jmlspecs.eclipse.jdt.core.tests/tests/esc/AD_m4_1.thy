theory AD_m4_1
imports Main
begin

lemma main: "((True & True) --> (((b_0::int) = (2 :: int)) --> (((a_0::int) = (((3 :: int)) + ((b_0::int)))) --> (if ((a_0::int) ~= (5 :: int)) then True else ((b_0::int) ~= (2 :: int)) ))))" 
  oops
done

end
