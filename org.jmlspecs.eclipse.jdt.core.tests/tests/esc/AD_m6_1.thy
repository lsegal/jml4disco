theory AD_m6_1
imports Main
begin

lemma main: "((True & True) --> (((b_0::int) = (1 :: int)) --> (((b_1::int) = (2 :: int)) --> (((b_2::int) = (3 :: int)) --> (((a_0::int) = (((((((((b_0::int)) + ((b_1::int)))) + ((b_1::int)))) + ((b_2::int)))) + ((b_2::int)))) --> (if ((a_0::int) ~= (11 :: int)) then True else ((b_2::int) ~= (3 :: int)) ))))))" 
  oops
done

end
