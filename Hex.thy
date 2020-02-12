theory Hex
  imports Main HOL.String "HOL-Word.Word"
begin

(* this file is going to contain some miscellaneous tools
such as hex reading/writing *)
definition hexread1_dom :: "char \<Rightarrow> bool" where
"hexread1_dom c = (c = CHR ''0'' \<or> c = CHR ''1'' \<or> c = CHR ''2'' \<or>
                   c = CHR ''3'' \<or> c = CHR ''4'' \<or> c = CHR ''5'' \<or>
                   c = CHR ''6'' \<or> c = CHR ''7'' \<or> c = CHR ''8'' \<or>
                   c = CHR ''9'' \<or> c = CHR ''A'' \<or> c = CHR ''B'' \<or>
                   c = CHR ''D'' \<or> c = CHR ''E'' \<or> c = CHR ''F'' \<or>
                   c = CHR ''a'' \<or> c = CHR ''b'' \<or> c = CHR ''d'' \<or>
                   c = CHR ''e'' \<or> c = CHR ''f'')"

definition hexread1 :: "char \<Rightarrow> nat" where
"hexread1 c = (if c = (CHR ''0'') then 0 else
               if c = (CHR ''1'') then 1 else
               if c = (CHR ''2'') then 2 else
               if c = (CHR ''3'') then 3 else
               if c = (CHR ''4'') then 4 else
               if c = (CHR ''5'') then 5 else
               if c = (CHR ''6'') then 6 else
               if c = (CHR ''7'') then 7 else
               if c = (CHR ''8'') then 8 else
               if c = (CHR ''9'') then 9 else
               if c = (CHR ''A'') then 10 else
               if c = (CHR ''B'') then 11 else
               if c = (CHR ''C'') then 12 else
               if c = (CHR ''D'') then 13 else
               if c = (CHR ''E'') then 14 else
               if c = (CHR ''F'') then 15 else
               if c = (CHR ''a'') then 10 else
               if c = (CHR ''b'') then 11 else
               if c = (CHR ''c'') then 12 else
               if c = (CHR ''d'') then 13 else
               if c = (CHR ''e'') then 14 else
               if c = (CHR ''f'') then 15 else
               undefined)"

definition hexwrite1_dom :: "nat \<Rightarrow> bool" where
"hexwrite1_dom n = (n < 16)"

definition hexwrite1_upper :: "nat \<Rightarrow> char" where
"hexwrite1_upper c = (if c = 0 then CHR ''0'' else
                if c = 1 then CHR ''1'' else
                if c = 2 then CHR ''2'' else
                if c = 3 then CHR ''3'' else
                if c = 4 then CHR ''4'' else
                if c = 5 then CHR ''5'' else
                if c = 6 then CHR ''6'' else
                if c = 7 then CHR ''7'' else
                if c = 8 then CHR ''8'' else
                if c = 9 then CHR ''9'' else
                if c = 10 then CHR ''A'' else
                if c = 11 then CHR ''B'' else
                if c = 12 then CHR ''C'' else
                if c = 13 then CHR ''D'' else
                if c = 14 then CHR ''E'' else
                if c = 15 then CHR ''F'' else undefined)"

definition hexwrite1 :: "nat \<Rightarrow> char" where
"hexwrite1 c = (if c = 0 then CHR ''0'' else
                if c = 1 then CHR ''1'' else
                if c = 2 then CHR ''2'' else
                if c = 3 then CHR ''3'' else
                if c = 4 then CHR ''4'' else
                if c = 5 then CHR ''5'' else
                if c = 6 then CHR ''6'' else
                if c = 7 then CHR ''7'' else
                if c = 8 then CHR ''8'' else
                if c = 9 then CHR ''9'' else
                if c = 10 then CHR ''a'' else
                if c = 11 then CHR ''b'' else
                if c = 12 then CHR ''c'' else
                if c = 13 then CHR ''d'' else
                if c = 14 then CHR ''e'' else
                if c = 15 then CHR ''f'' else undefined)"


value "(1 < (0::nat))"

(*
lemma hexread1_hexwrite1 : "hexread1_dom c \<Longrightarrow> hexwrite1 (hexread1 c) = c"
  apply (auto simp add:hexread1_dom_def hexread1_def hexwrite1_def)
  done
*)
lemma hexwrite1_help :
"n < 16 \<Longrightarrow>
    n \<noteq> 15 \<Longrightarrow>
    n \<noteq> 14 \<Longrightarrow>
    n \<noteq> 13 \<Longrightarrow>
    n \<noteq> 12 \<Longrightarrow>
    n \<noteq> 11 \<Longrightarrow>
    n \<noteq> 10 \<Longrightarrow>
    n \<noteq> 9 \<Longrightarrow>
    n \<noteq> 8 \<Longrightarrow>
    n \<noteq> 7 \<Longrightarrow>
    n \<noteq> 6 \<Longrightarrow>
    n \<noteq> 5 \<Longrightarrow>
    n \<noteq> 4 \<Longrightarrow>
    n \<noteq> 3 \<Longrightarrow>
    n \<noteq> 2 \<Longrightarrow>
    n \<noteq> Suc 0 \<Longrightarrow>
    0 < n \<Longrightarrow> False"
proof(induction n, auto)
qed 

(*
lemma hexwrite1_hexread1 : "hexwrite1_dom n \<Longrightarrow> hexread1 (hexwrite1 n) = n"
  apply(auto simp add:hexwrite1_dom_def hexwrite1_def)
                  apply(auto simp add:hexread1_def)
                  apply(insert hexwrite1_help, auto)
  done
*)

definition hexread2 :: "char \<Rightarrow> char \<Rightarrow> int" where
"hexread2 c1 c2 = (16 * (int (hexread1 c1)) + int (hexread1 c2))"

(* we need to reverse the input list? *)
(* TODO: later handle zero padding for odd numbers of bytes *)
fun hexread' :: "char list \<Rightarrow> int \<Rightarrow> int" where
"hexread' [] n = n"
| "hexread' [_] _ = undefined"
| "hexread' (n1#n2#t) a = hexread' t (hexread2 n1 n2 + 256 * a)"

definition hexread :: "char list \<Rightarrow> int" where
"hexread ls = hexread' ls 0"

fun hexwrite2 :: "8 word \<Rightarrow> (char * char)" where
"hexwrite2 w = 
  (case Divides.divmod_nat (Word.unat w) 16 of
       (d,m) \<Rightarrow> (hexwrite1 d, hexwrite1 m))"

(* TODO: make sure we aren't supposed to do the reverse of this *)
fun hexwrite :: "8 word list \<Rightarrow> char list" where
"hexwrite [] = []"
| "hexwrite (h#t) = (case hexwrite2 h of
                     (c1, c2) \<Rightarrow> c1#c2#(hexwrite t))"

value "List.n_lists 2 [1 :: nat, 2, 3]"

(* splitting a hex string into bytes *)

fun hex_split_bytes' :: "char list \<Rightarrow> char list list" where
"hex_split_bytes' [] = []"
| "hex_split_bytes' [h] = [[h]]" (* should never happen *)
| "hex_split_bytes' (h1#h2#t) =
    (h1#h2#[])#(hex_split_bytes' t)"

fun hex_split_bytes ::
  "char list \<Rightarrow> char list list" where
"hex_split_bytes ls =
  (case divmod_nat (length ls) 2 of
    (_, 0) \<Rightarrow> hex_split_bytes' ls
  | (_, _) \<Rightarrow> hex_split_bytes' ((CHR ''0'') # ls))"

value "hex_split_bytes
''000000000000000000000000000000000000000000000000000000000000002a''"

(* TODO: this will still choke if given non-hex characters. *)
fun hex_splits :: "char list \<Rightarrow> 8 word list" where
"hex_splits l =
  List.map (\<lambda> x . Word.word_of_int (hexread x)) (hex_split_bytes l)"

value "hex_splits
''000000000000000000000000000000000000000000000000000000000000002a''"


(* decimal reading/writing - for use in generating error messages *)

definition decwrite1_dom :: "nat \<Rightarrow> bool" where
"decwrite1_dom n = (n < 10)"

definition decwrite1 :: "nat \<Rightarrow> char" where
"decwrite1 c = (if c = 0 then CHR ''0'' else
                if c = 1 then CHR ''1'' else
                if c = 2 then CHR ''2'' else
                if c = 3 then CHR ''3'' else
                if c = 4 then CHR ''4'' else
                if c = 5 then CHR ''5'' else
                if c = 6 then CHR ''6'' else
                if c = 7 then CHR ''7'' else
                if c = 8 then CHR ''8'' else
                if c = 9 then CHR ''9'' else undefined)"

(*
lemma hexread1_hexwrite1 : "hexread1_dom c \<Longrightarrow> hexwrite1 (hexread1 c) = c"
  apply (auto simp add:hexread1_dom_def hexread1_def hexwrite1_def)
  done
*)
lemma decwrite1_help :
"n < 10 \<Longrightarrow>
    n \<noteq> 9 \<Longrightarrow>
    n \<noteq> 8 \<Longrightarrow>
    n \<noteq> 7 \<Longrightarrow>
    n \<noteq> 6 \<Longrightarrow>
    n \<noteq> 5 \<Longrightarrow>
    n \<noteq> 4 \<Longrightarrow>
    n \<noteq> 3 \<Longrightarrow>
    n \<noteq> 2 \<Longrightarrow>
    n \<noteq> Suc 0 \<Longrightarrow>
    0 < n \<Longrightarrow> False"
proof(induction n, auto)
qed 

fun decwrite2 :: "nat \<Rightarrow> (char * char)" where
"decwrite2 w = 
  (case Divides.divmod_nat w 10 of
       (d,m) \<Rightarrow> (decwrite1 d, decwrite1 m))"

function(sequential) decwrite' :: "nat \<Rightarrow> char list" where
"decwrite' n = (if n < 10 then [decwrite1 n] else
              (case Divides.divmod_nat n 10 of
                     (d, m) \<Rightarrow> (decwrite1 m # (decwrite' d))))"
  by pat_completeness auto

termination
  apply(relation "(measure (\<lambda> n . if n < 10 then 1 else Suc n))")
   apply(clarsimp)
  apply(clarsimp) apply(simp add:divmod_nat_def)
  done

fun decwrite :: "nat \<Rightarrow> char list" where
"decwrite n = rev (decwrite' n)"

(*
lemma hexwrite1_hexread1 : "hexwrite1_dom n \<Longrightarrow> hexread1 (hexwrite1 n) = n"
  apply(auto simp add:hexwrite1_dom_def hexwrite1_def)
                  apply(auto simp add:hexread1_def)
                  apply(insert hexwrite1_help, auto)
  done
*)


end