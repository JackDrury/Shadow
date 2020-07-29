theory Cream_Cake_example
  imports Main "~~/src/HOL/Library/LaTeXsugar" "Shadow_Semantics" "Utils"
begin


section \<open>Cream Cake Cryptographers\<close>
(*
value "REVEAL {{(a,b)|a b. a\<in>{True,False} \<and> b\<in>{True,False} \<and> (a = b) = k}|k. k\<in>{True,False}} ({True,False}{True,False})"
*)

lemma cream_cake_helper:
  assumes "A = {True,False}"
      and "B = {True,False}"
  shows
  "REVEAL {{(a,b)|a b. a\<in>A \<and> b\<in>B \<and> (a = b) = k}|k. k\<in>K} (X \<times> Y)
  =
  {{(a,b)|a b. a\<in>X \<and> b\<in>Y \<and> (a = b) = k}|k. k\<in>K}
  "
  using assms
  apply (-)
  unfolding REVEAL_def
  apply safe
  apply (rule_tac x="k" in exI)
  apply force
  apply (rule_tac x="{(a, b) |a b. a \<in> {True, False} \<and> b \<in> {True, False} \<and> (a = b) = k}" in exI)
  by auto

 
lemma cream_cake_helper1:
  shows
  "CHOOSE (\<lambda>(_, a, b). {(c, a, b) |c. c \<in> C}) ({t} \<times> X \<times> Y)
  =
  {C \<times> X \<times> Y}
  "
  unfolding CHOOSE_def
  by blast


lemma cream_cake_helper2:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
  shows
  "
  REVEAL {{(c, a, b) |c a b. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> (a = c) = k} |k. k \<in> K} (C \<times> X \<times> Y) 
  =
  {{(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> (a = c) = k} |k. k \<in> K}
  "
  using assms
  apply (-)
  unfolding REVEAL_def
  apply safe
  apply (rule_tac x="k" in exI)
  apply blast
  apply (rule_tac x="{(c, a, b) |c a b. a \<in> {True, False} \<and> b \<in> {True, False} \<and> c \<in> {True, False} \<and> (a = c) = k}" in exI)
  by auto


lemma cream_cake_helper3:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
  shows
"
REVEAL  {{(c, a, b) |c a b. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> (b = c) = k} |k. k \<in> K} ` 
        {{(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> (a = c) = k} |k. k \<in> K} 
=
{
REVEAL  {{(c, a, b) |c a b. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> (b = c) = k} |k. k \<in> K} 
         {(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> (a = c) = k} |k. k \<in> K
} 
"
  using assms
  apply (-)
  unfolding REVEAL_def
  apply safe
  by auto


lemma cream_cake_helper7:
"
{{(c, a, b) |c a b. a \<and> b \<and> (a = c) = k} \<inter> s |s. \<exists>k. s = {(c, a, b) |c a b. (b = c) = k}} 
= 
{z. \<exists>k1. z = {(c, a, b) |c a b. a \<and> b \<and> (b = c) = k1 \<and> (a = c) = k}}
"
  apply safe
  apply (induct k)
  apply (rule_tac x="k" in exI)
  apply blast
  apply (rule_tac x="k" in exI)
  apply blast
  apply (induct k)
  apply simp
  apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
  apply blast
  apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
  by auto


lemma cream_cake_helper6:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
      and "K = {True,False}"
      and "X\<subseteq>A"
      and "Y\<subseteq>B"
  shows
  "
  {
  REVEAL {{(c, a, b) |c a b. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> ((b = c) = k)} |k. k \<in> K} 
           {(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> ((a = c) = k)} |k. k \<in> K
  }
  =
  {
  {{(c,a,b)|c a b. a\<in>X \<and> b\<in>Y \<and> c\<in>C \<and> ((b=c) = k1) \<and> ((a = c) = k2)}|k1. k1\<in>K}
                                                                    |k2. k2\<in>K
  }
  "
  unfolding REVEAL_def
  apply safe
   apply (rule_tac x="k" in exI)
  using assms apply simp
   apply (-)
   apply (induct X rule:induct_H)
  apply blast
     apply safe[1]
      apply (rule_tac x="ka" in exI)
      apply blast
     apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
     apply blast
    apply safe[1]
     apply (rule_tac x="ka" in exI)
  apply blast
    apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
  apply blast
   apply safe[1]
    apply (rule_tac x="ka" in exI)
  apply blast
   apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
  apply blast
  using assms apply simp
  apply (rule_tac x="k2" in exI)
  apply safe
   apply (rule_tac x="{(c, a, b) |c a b. (b = c) = k1}" in exI)
  apply blast
  apply (rule_tac x="k" in exI)
  by auto


lemma cream_cake_helper8:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
      and "K = {True,False}"
      and "X\<subseteq>A"
      and "Y\<subseteq>B"
  shows
  "
  {
  {snd h |h. h \<in> s} |s. 
   s \<in> \<Union> {{{(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> (b = c) = k1 \<and> (a = c) = k2} |k1. k1 \<in> K} 
                                                                                     |k2. k2 \<in> K}
  }
  =
  \<Union> {{{(a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> c \<in> C \<and> (b = c) = k1 \<and> (a = c) = k2} |k1. k1 \<in> K} 
                                                                             |k2. k2 \<in> K}
  "
  apply safe
  apply simp
  apply blast
  using assms apply simp
  apply (rule_tac x="{(c, a, b) |c a b. a \<in> X \<and> b \<in> Y \<and> (b = c) = k1 \<and> (a = c) = k2}" in exI)
  by auto
  

lemma cream_cake:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
      and "K = {True,False}"
      and "X\<subseteq>A"
      and "Y\<subseteq>B"
  shows
  "
  REVEAL {{(a,b)|a b. a\<in>A \<and> b\<in>B \<and> (a = b) = k}|k. k\<in>K} (X \<times> Y)
  =
  (
  NewVar t (
             CHOOSE (\<lambda>(_,a,b). {(c,a,b)|c. c\<in>C}) ;; 
             REVEAL {{(c,a,b)|c a b. a\<in>A \<and> b\<in>B \<and> c\<in>C \<and> (a = c) = k}|k. k\<in>K} ;; 
             REVEAL {{(c,a,b)|c a b. a\<in>A \<and> b\<in>B \<and> c\<in>C \<and> (b = c) = k}|k. k\<in>K}
           )
  )
   (X \<times> Y)
  "
  apply (subst cream_cake_helper)
  using assms apply(simp+)[2]
  unfolding NewVar_def 
  unfolding COMPOSE_def
  apply (subst cream_cake_helper1)
  apply (subst union_comp_over_singleton) 
  apply (subst cream_cake_helper2)
  using assms apply(simp+)[3]
  apply (subst cream_cake_helper3)
  using assms apply(simp+)[3]
  apply (subst cream_cake_helper6)
  using assms apply(simp+)[6]
  apply (subst cream_cake_helper8)
  using assms apply(simp+)[6]
  apply safe
  using assms apply simp
  apply (rule_tac x="{z. \<exists>k1. z = {y. \<exists>c a b. y = (a, b) \<and> a \<in> X \<and> b \<in> Y \<and> (b = c) = k1 \<and> (a = c) = (k2)}}" in exI)
  apply safe
  apply (rule_tac x="k2" in exI)
  apply blast
  apply (rule_tac x="(k2 = k)" in exI)
  apply blast
  using assms apply simp
  apply (rule_tac x="(k2 = k1)" in exI)
  apply safe
  by metis+

(*Proving cream cake by using previously proven algebraic properties*)
lemma cream_cake2:
  assumes "A = {True,False}"
      and "B = {True,False}"
      and "C = {True,False}"
      and "K = {True,False}"
      and "X\<subseteq>A"
      and "Y\<subseteq>B"
  shows
  "
  REVEAL {{(a,b)|a b. a\<in>A \<and> b\<in>B \<and> (a = b) = k}|k. k\<in>K} (X \<times> Y)
  =
  (
  NewVar t (
             CHOOSE (\<lambda>(_,a,b). {(c,a,b)|c. c\<in>C}) ;; 
             REVEAL {{(c,a,b)|c a b. a\<in>A \<and> b\<in>B \<and> c\<in>C \<and> (a = c) = k}|k. k\<in>K} ;; 
             REVEAL {{(c,a,b)|c a b. a\<in>A \<and> b\<in>B \<and> c\<in>C \<and> (b = c) = k}|k. k\<in>K}
           )
  )
   (X \<times> Y)
  "
  apply (subst SKIP_then_p3) thm most_general_encryption_lemma
  apply (subst most_general_encryption_lemma[where t="t" and G="A" and K="K"])

(*  apply (subst most_general_encryption_lemma[where X="X" and Y="Y" and Z="Z"])*)
  sorry





section \<open>Proving Algebraic Steps for Cream Cake\<close>

(*
   See 1001 cryptographers paper for the motivation behind the chosen steps
*)

(* First step uses p = skip ; p*)
(* Already proven, but repeating here for convenience *)

lemma skip_p:
"p = SKIP ;; p"
  using SKIP_then_p3 by auto

(*
    second step uses the encryption lemma such that "SKIP = hid c:Bool; c:\<in>Bool; Reveal c XOR h
    Which we have already proven for the general case and boolean case but it also uses
    the fact that reveal (a = b) \<equiv> reveal (a XOR b)
*)

lemma reveal_xor_is_reveal_equals:
  "
  REVEAL {{(a,b)|a b. (a = b) = k}|k. k\<in>{True,False}} 
  = 
  REVEAL {{(a,b)|a b. (XOR a b) = k}|k. k\<in>{True,False}}
  "
  unfolding XOR_def REVEAL_def
  by blast


lemma reveal_xor_is_reveal_equals_3vars:
  "REVEAL {{(a,b,c)|a b c. (a = b) = k}|k. k\<in>{True,False}} = REVEAL {{(a,b,c)|a b c. (XOR a b) = k}|k. k\<in>{True,False}}"
  unfolding XOR_def REVEAL_def
  by blast


(* 
    Third step is scope adjustment, so first we must define a way to push things in and out of scope.
*)


(*


------------saving scope adjustment for later


*)


(*
   The fourth and final step uses the fact that for boolean a, b and c: 
   learning the result of a=b and a=c will determine a=c and b=c
*)


lemma equiv_reveals:
  shows
  "(
    REVEAL {{(a,b,c)|a b c. (a = c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}} ;;
    REVEAL {{(a,b,c)|a b c. (a = b) = k \<and> c\<in>{True,False}}|k. k\<in>{True,False}} 
   ) 
   = 
   (
    REVEAL {{(a,b,c)|a b c. (a = c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}} ;;
    REVEAL {{(a,b,c)|a b c. (c = b) = k \<and> a\<in>{True,False}}|k. k\<in>{True,False}}
   )"
  apply (rule ext)
  unfolding REVEAL_def COMPOSE_def
  apply simp
  apply safe
  apply simp
  apply (rule_tac x="x\<inter>({(a, b, c) |a b c. (a = c) = k})" in exI)
  apply (rule conjI)
  apply blast
  apply (rule_tac x=" {(a, b, c) |a b c. (c = b) = (k=ka)}" in exI)
  apply blast
  apply simp
  apply (rule_tac x="x\<inter>({(a, b, c) |a b c. (a = c) = k})" in exI)
  apply (rule conjI)
  apply blast
  apply (rule_tac x=" {z. \<exists>a b. (\<exists>c. z = (a, b, c)) \<and> (a = b) = (k=ka)}" in exI)
  by auto

  


end