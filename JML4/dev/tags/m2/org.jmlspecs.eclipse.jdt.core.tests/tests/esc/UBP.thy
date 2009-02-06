theory UBP
imports Main
begin

fun sum_helper :: "nat => int => (int => int) => int"
where
  "sum_helper 0       lo body = 0"
| "sum_helper (Suc n) lo body = (body (int n + lo)) + (sum_helper n lo body)"

fun sum :: "int => int => (int => int) => int"
where
"sum lo hi body = sum_helper (nat (hi - lo + 1)) lo body"

fun product_helper :: "nat => int => (int => int) => int"
where
  "product_helper 0       lo body = 1"
| "product_helper (Suc n) lo body = (body (int n + lo)) * (product_helper n lo body)"

fun product :: "int => int => (int => int) => int"
where
"product lo hi body = product_helper (nat (hi - lo + 1)) lo body"

fun minn :: "int => int => int"
where
  "minn a b = (if (a <= b) then a else b)"
fun maxx :: "int => int => int"
where
  "maxx a b = (if (a >= b) then a else b)"

consts max_int :: int
       min_int :: int
defs
max_int_def[simp]: "max_int ==   2 ^ 31 - 1"
min_int_def[simp]: "min_int == -(2 ^ 31)"

lemma "100 < max_int"
 by simp

lemma "100 > min_int"
 by simp

fun max_helper :: "nat => int => (int => int) => int"
where
  "max_helper 0       lo body = min_int"
| "max_helper (Suc n) lo body = maxx (body (int n + lo)) (max_helper n lo body)"

fun max :: "int => int => (int => int) => int"
where
"max lo hi body = max_helper (nat (hi - lo + 1)) lo body"

fun min_helper :: "nat => int => (int => int) => int"
where
  "min_helper 0       lo body = max_int"
| "min_helper (Suc n) lo body = minn (body (int n + lo)) (min_helper n lo body)"

fun min :: "int => int => (int => int) => int"
where
"min lo hi body = min_helper (nat (hi - lo + 1)) lo body"

fun num_of_helper :: "nat => int => (int => bool) => int"
where
  "num_of_helper 0       lo body = 0"
| "num_of_helper (Suc n) lo body = (if (body (int n + lo)) then 1 else 0) + (num_of_helper n lo body)"

fun num_of :: "int => int => (int => bool) => int"
where
"num_of lo hi body = num_of_helper (nat (hi - lo + 1)) lo body"

lemma min_1_plus_i_eq_i_Min_1[simp]: "(-1 + i::int) = (i - 1)"
  by auto

lemma nat_Suc_i_Min_1_eq_i[simp]:
  "0 < i --> (Suc (nat (-1 + i))) = (nat i)"
  by auto

lemma nat_i_eq_nat_Suc_i_Min_1[simp]:
  "0 < i --> (nat i) = (Suc (nat (i - 1)))"
  by auto

lemma set_not_a_imp_b[simp]: "{u. u \<noteq> a --> u = b} = {a, b}"
  by auto

(*
lemma test_product "6 = product 1 3 (%x. x)"
  apply (simp add: nat_number)

lemma test_sum "6 = sum 1 3 (%x. x)"
  apply (simp add: nat_number)

lemma test_num_of: "5 = num_of 1 10 (%x. (x mod 2 = 1))"
  by (simp add: nat_number)

lemma test_max: "4 = max 1 10 (%x. (4 - (x - 3) * (x - 3)))"
  by (simp add: nat_number)
*)

end
