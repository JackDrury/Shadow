theory Utils
  imports Main "~~/src/HOL/Library/LaTeXsugar" "Shadow_Semantics"
begin


section \<open>Helpers and Theorems\<close>

text 
\<open>   
A Shadow is the term for the set of states that the attacker believes are possible.
\<close>

type_synonym 'h shadow = "'h set"


text 
\<open>   
A HyperShadow is the result of applying a Shadow-program to an actual Shadow.

Hyper-Shadows are considered equal if they contain all the same elements, or if they only differ 
by the empty set. Therefore we define a type of reduced equality that reflects this.
\<close>

type_synonym 'h hypershadow = "('h set) set"


definition
    reducedHyper :: "'h hypershadow \<Rightarrow> 'h hypershadow"
where
    "reducedHyper S = S - {{}}"


definition
    reducedEquality :: "'h hypershadow \<Rightarrow> 'h hypershadow \<Rightarrow> bool" (infix "=:=" 60)
where
    "p =:= q \<equiv>reducedHyper p = reducedHyper q"


lemma union_over_singleton:
"\<Union> {X} = X"
  by simp


lemma union_comp_over_singleton:
"(\<Union>hs'\<in>{X}. f hs') = f X"
  by blast


lemma element_of_singleton:
"s\<in>{X} \<Longrightarrow> s=X"
  by simp


lemma skip_then_p:
"SKIP ;; p = p"
  unfolding SKIP_def COMPOSE_def
  by simp


lemma p_then_skip:
"p ;; SKIP = p"
  unfolding SKIP_def COMPOSE_def
  by simp


lemma skip_then_p1:
"(SKIP ;; p) H = p H"
  unfolding SKIP_def COMPOSE_def
  by simp


lemma p_then_skip1:
"(p ;; SKIP) H = p H"
  unfolding SKIP_def COMPOSE_def
  by simp


lemma SKIP_then_p2:
"p H = (SKIP ;; p) H"
  unfolding SKIP_def COMPOSE_def
  by simp


lemma SKIP_then_p3:
"p = (SKIP ;; p)"
  unfolding SKIP_def COMPOSE_def
  by simp

lemma COMPOSE_left_eq: 
  "p hs = p' hs \<Longrightarrow> COMPOSE p q hs = COMPOSE p' q hs"
  unfolding COMPOSE_def by simp

lemma COMPOSE_right_eq: 
  "(\<forall> hs'\<in> p hs. q hs' = q' hs') \<Longrightarrow> 
   (COMPOSE p q) hs = (COMPOSE p q') hs"
  unfolding COMPOSE_def by simp

lemma COMPOSE_left_right_eq: 
  "p hs = p' hs\<Longrightarrow>
  (\<forall> hs'\<in> p hs. q hs' = q' hs') \<Longrightarrow> 
   (COMPOSE p q) hs = (COMPOSE p' q') hs"
  unfolding COMPOSE_def by simp

lemma equality_implies_reducedEquality:
  shows "A = B \<Longrightarrow> A =:= B"
  unfolding reducedEquality_def reducedHyper_def
  by simp


lemma equality_implies_reducedEquality2:
  shows "A = B \<Longrightarrow> A H =:= B H"
  unfolding reducedEquality_def reducedHyper_def
  by simp


lemma equality_implies_applied_equality:
  shows "A = B \<Longrightarrow> A H = B H"
  unfolding reducedEquality_def reducedHyper_def
  by simp


lemma reveal_empty:
  "REVEAL {{}} H = {{}}"
  unfolding REVEAL_def
  by simp


lemma reveal_fn_equivalence:
"REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K} (G \<times> H)
=
{{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K}"
  unfolding REVEAL_def
  by blast


lemma reveal_fn_equivalence1:
"REVEAL {{h|h. h\<in>H \<and> f h = k}|k. k\<in>K} H
=
{{h|h. h\<in>H \<and> f h = k}|k. k\<in>K}"
  unfolding REVEAL_def
  by blast


lemma backtick_reveal_fn_equivalence:
"REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K} ` {G \<times> H}
=
{REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K} (G \<times> H)}
"
  unfolding REVEAL_def
  by blast


lemma backtick_reveal_fn_equivalence1:
"REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K} ` {G \<times> H}
=
{{{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K}}
"
  apply(subst backtick_reveal_fn_equivalence)
  apply(subst reveal_fn_equivalence)
  by simp


lemma choose_equiv:
 "CHOOSE (\<lambda>(_, h). {(k,h)|k. k\<in>K}) ({t} \<times> H) 
 =
 {K \<times> H}"
  unfolding CHOOSE_def
  by blast


lemma choose_equiv_fn:
shows
"CHOOSE (\<lambda>(_, h). {(f h, h)}) ({t} \<times> H) 
=
{{(f h, h)|h. h\<in>H}}"
  unfolding CHOOSE_def
  apply simp
  by blast


(* a couple of theorems on dropping the dummy variable from expressions *) 
lemma choose_equivalence:
 " CHOOSE (\<lambda>(_, h). {(k,h)|k. k\<in>K}) ({t} \<times> H) 
 =
 (\<lambda>X. {\<Union>{{(k,h1,h2)|k h1 h2. k\<in>K \<and> h1= fst x \<and> h2 = snd x}|x. x\<in>H}}) H"
  unfolding CHOOSE_def
  by simp


lemma choose_equivalence1:
 " CHOOSE (\<lambda>(_, h1,h2). {(k,h1,h2)|k. k\<in>K}) ({t} \<times> H) 
 =
 (\<lambda>X. {\<Union>{{(k,h1,h2)|k h1 h2. k\<in>K \<and> h1= fst x \<and> h2 = snd x}|x. x\<in>H}}) H"
  unfolding CHOOSE_def
  by simp


lemma choose_equiv_too_sepcific:
 " CHOOSE (\<lambda>(_, h1,h2). {(k,h1,h2)}) ({t} \<times> H) 
 =
 (\<lambda>X. {\<Union>{{(k,h1,h2)|h1 h2. h1= fst x \<and> h2 = snd x}|x. x\<in>H}}) H"
  unfolding CHOOSE_def
  by simp


lemma create_new_var_then_assign_value: (*assigning it "angelically" (internally) to something in K*)
"NewVar t (CHOOSE (\<lambda>(_,h). {(k,h)|k. k\<in>K})) H 
=
{{snd h |h. h\<in>s}|s. s\<in>((\<lambda>X. {\<Union>{{(k,h1,h2)|k h1 h2. k\<in>K \<and> h1= fst x \<and> h2 = snd x}|x. x\<in>H}}) H)}
"
  unfolding NewVar_def CHOOSE_def
  by force


lemma create_new_var_then_assign_then_p: (*assigning it "angelically" (internally) to something in K*)
"NewVar t (CHOOSE (\<lambda>(_,h). {(k,h)|k. k\<in>K}) ;; p) H 
=
{{snd h |h. h\<in>s}|s. s\<in>(\<Union>hs'\<in>((\<lambda>X. {\<Union>{{(k,h1,h2)|k h1 h2. k\<in>K \<and> h1= fst x \<and> h2 = snd x}|x. x\<in>H}}) H). p hs')}
"
  unfolding NewVar_def CHOOSE_def COMPOSE_def
  by force

 
lemma new_var_then_reveal_help1:
" \<Union> {{{(g, h) |g h. g \<in> G \<and> h \<in> H \<and> f g h = k} |k. k \<in> K}}
=
{{(g, h) |g h. g \<in> G \<and> h \<in> H \<and> f g h = k} |k. k \<in> K}
"
  by simp


lemma new_var_then_reveal_help2:
  assumes "\<forall>k\<in>K.\<forall>h\<in>H. \<exists>g\<in>G. f g h =k"
  shows
"{{snd x |x. x \<in> s} |s. s \<in> {{(g, h) |g h. g \<in> G \<and> h \<in> H \<and> f g h = k} |k. k \<in> K}}
=
{{h|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K}
"
  apply(safe)
  apply fastforce
  apply(rule_tac x="{(g, h) |g h. g \<in> G \<and> h \<in> H \<and> f g h = k}" in exI)
  by auto

  
(* assuming f(.,h) is a surjection*)
lemma new_var_then_reveal_encrypt: 
  assumes "\<forall>k\<in>K.\<forall>h\<in>H. \<exists>g\<in>G. f g h =k"
  shows
  "(NewVar t (CHOOSE (\<lambda>(_,h). {(g,h)|g. g\<in>G}) ;; 
  REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K})) H
  =
  {{h|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K}
  "
  unfolding NewVar_def COMPOSE_def
  apply (subst choose_equiv)
  apply (subst backtick_reveal_fn_equivalence1)
  apply (subst new_var_then_reveal_help1)
  apply (subst new_var_then_reveal_help2)
  using assms
  apply simp
  by blast


lemma general_encryption_lemma_help:
  assumes "\<forall>k\<in>K.\<forall>h\<in>H. \<exists>g\<in>G. f g h =k"
  shows
  "(NewVar t (CHOOSE (\<lambda>(_,h). {(g,h)|g. g\<in>G}) ;; 
  REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> (f g h) = k}|k. k\<in>K})) H
  =
  {H|k. k\<in>K}
  "
  apply (subst new_var_then_reveal_encrypt)
  using assms
  apply simp
  apply simp
  apply safe
  using assms apply blast
  using assms apply blast
  using assms apply blast
  done


(* 
   Skip is equivalent to creating a new var, g,  assigning it a random element in 
   G and then revealing the result of f applied to g and the hidden variable h

   Seems I also need to assume that the ouput of the function is non-empty
   and that the function is surjective.

   (TODO: can i do this without explicitly having g\<in>G and h\<in>H inside the reveal?)

*)
lemma general_encryption_lemma:
  assumes "\<forall>k\<in>K.\<forall>h\<in>H. \<exists>g\<in>G. (f g h) = k"
  and     "K\<noteq>{}" 
  shows
  "
  SKIP H
  =
  (
   NewVar t (
             CHOOSE (\<lambda>(_,h). {(g,h)|g. g\<in>G}) ;; 
             REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> ((f g h) = k)}|k. k\<in>K}
            )
  ) H
  "
  unfolding SKIP_def
  apply (subst general_encryption_lemma_help)
  using assms apply simp
  using assms apply blast
  done
  



(* 
   Difference to the previous general lemma is I want to say H is the type of H.
   And (even though it doesn't change the results, just makes it easier to use)
   hs is a subset of H.
*) 

lemma more_general_encryption_lemma:
  assumes "\<forall>k\<in>K.\<forall>h\<in>H. \<exists>g\<in>G. (f g h) = k"
  and     "K\<noteq>{}"
  and     "hs\<subseteq>H" 
  shows
  "
  SKIP hs
  =
  (
   NewVar t (
             CHOOSE (\<lambda>(_,h). {(g,h)|g. g\<in>G}) ;; 
             REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> ((f g h) = k)}|k. k\<in>K}
            )
  ) hs
  "
(* \<Union> (_Collect (_Collect (g, b) (g \<in> G)) (b \<in> hs)) \<inter> sa
_Collect (g, h) (g \<in> G \<and> h \<in> H \<and> f g h = k)*)
  unfolding SKIP_def NewVar_def REVEAL_def COMPOSE_def CHOOSE_def
  using assms
  apply (-)
  apply simp
  apply safe
  apply simp
  apply (rule_tac x="(\<Union> {{(g, b) |g. g \<in> G} |b. b \<in> hs})\<inter>({(g, h). g \<in> G \<and> h \<in> H \<and> f g h = x})" in exI)
  apply simp
  apply (rule conjI)
  apply safe
  apply (metis (mono_tags, lifting) CollectI subset_eq)
  apply (rule_tac x="{(g, h). g \<in> G \<and> h \<in> H \<and> f g h = x}" in exI)
  apply simp
  apply blast
  apply simp
  by (metis (mono_tags, lifting) CollectI subset_eq)  

definition
    XOR :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
    "XOR p q \<equiv> (p \<or> q) \<and> (\<not>p \<or> \<not>q)"

lemma XOR_commute:
"XOR p q = XOR q p"
  unfolding XOR_def
  by auto


lemma XOR_assoc:
"XOR (XOR p q) r = XOR p (XOR q r)"
  unfolding XOR_def
  by auto


lemma XOR_inv:
"XOR A False = A"
  unfolding XOR_def
  by simp


lemma XOR_inv1:
"XOR A A = False"
  unfolding XOR_def
  by simp


lemma XOR_inv2:
"XOR False A = A"
  unfolding XOR_def
  by simp


lemma XOR_inv3:
"XOR (XOR a b) a = b"
  unfolding XOR_def
  by auto


lemma XOR_inv4:
"XOR a (XOR b a) = b"
  unfolding XOR_def
  by auto


inductive_set set_of_bools :: "(bool set) set"
  where
  emptySB:  "{} \<in> set_of_bools"|
  insertSB: "A  \<in> set_of_bools \<and> b \<in> bool \<Longrightarrow> (insert b A) \<in> set_of_bools"


(* ======== Helpers for bool set induction ======== *)

lemma UNIV_boolSet:
  "UNIV = {{}, {True}, {False}, {True, False}}"
  by (smt Pow_UNIV Pow_empty Pow_insert UNIV_bool Un_insert_left Un_insert_right image_insert image_is_empty insert_is_Un)


lemma cases_H:
  shows "H = {} \<or> H = {True} \<or> H = {False} \<or> H = {True, False}"
  using UNIV_boolSet by blast

lemma induct_H:
  fixes H :: "bool set"
  shows "\<lbrakk>P {}; P {True}; P {False}; P {True, False}\<rbrakk> \<Longrightarrow> P H"
  using cases_H by metis


section \<open>Encryption Lemma\<close>


lemma induction_i:
shows "SKIP {} = NewVar t (CHOOSE (\<lambda>a. case a of (uu_, h) \<Rightarrow> {(True, h), (False, h)}) ;; REVEAL {{}}) {}"
  unfolding SKIP_def NewVar_def COMPOSE_def CHOOSE_def REVEAL_def reducedEquality_def
  by simp


lemma help1_induction_ii:
  shows
  "\<Union> {{(True,b),(False,b)} |b. b} = {(True,True),(False,True)} "
  by blast


lemma help2_induction_ii:
  shows
"{{(g, h) |g h. g \<in> {True, False} \<and> h \<in> {True} \<and> XOR g h = k} |k. k \<in> {True, False}} = {{(True,True)},{(False,True)}}"
  unfolding XOR_def 
  apply simp
  by blast


lemma induction_ii:
  shows 
  "SKIP {True} =
    NewVar t (CHOOSE (\<lambda>a. case a of (uu_, h) \<Rightarrow> {(True, h), (False, h)}) ;; REVEAL {{(g, h) |g h. g \<in> {True, False} \<and> h \<in> {True} \<and> XOR g h = k} |k. k \<in> {True, False}}) {True}"
  unfolding NewVar_def COMPOSE_def CHOOSE_def REVEAL_def SKIP_def reducedEquality_def reducedHyper_def XOR_def
  apply simp
  by blast


lemma induction_iii:
  shows
"SKIP {False} =
    NewVar t (CHOOSE (\<lambda>a. case a of (uu_, h) \<Rightarrow> {(True, h), (False, h)}) ;; REVEAL {{(g, h) |g h. g \<in> {True, False} \<and> h \<in> {False} \<and> XOR g h = k} |k. k \<in> {True, False}})
     {False}"
  unfolding NewVar_def COMPOSE_def CHOOSE_def REVEAL_def SKIP_def reducedEquality_def reducedHyper_def XOR_def
  apply simp
  by blast


lemma help1_induction_iv:
  shows
"CHOOSE (\<lambda>(_, h). {(True, h), (False, h)}) ({t} \<times> {True, False}) = {{(True,True),(False,True),(True,False),(False,False)}}"
  unfolding CHOOSE_def
  apply (induct t)
  by blast+


lemma help2_induction_iv:
  shows
"{a. \<exists>k. a = {(g, h). XOR g h = k}} = {{(True,False),(False,True)},{(True,True),(False,False)}}"
  unfolding XOR_def
  by blast


lemma induction_iv:
  shows 
    " SKIP {True, False} =
    NewVar t (CHOOSE (\<lambda>a. case a of (uu_, h) \<Rightarrow> {(True, h), (False, h)}) ;; REVEAL {{(g, h) |g h. g \<in> {True, False} \<and> h \<in> {True, False} \<and> XOR g h = k} |k. k \<in> {True, False}})
     {True, False}"
  unfolding NewVar_def
  unfolding COMPOSE_def
  apply (subst help1_induction_iv)
  apply simp
  unfolding REVEAL_def
  apply (subst help2_induction_iv)
  unfolding SKIP_def reducedEquality_def reducedHyper_def
  by blast


lemma bool_encryption_lemma:
  fixes t :: "bool"
    and H :: "bool set" 
  shows
    "SKIP H = 
    NewVar t (
              CHOOSE (\<lambda>(_,h). {(True,h),(False,h)}) ;; 
              REVEAL {{ (g,h) | g h. g\<in>{True,False} \<and> h\<in>H \<and> (XOR g h) = k}|k. k\<in>{True,False}}
             ) H"
  apply(induct H rule:induct_H)
  apply simp
  apply (rule induction_i)
  apply (rule induction_ii)  
  apply (rule induction_iii)
  using induction_iv
  by simp


lemma reveal_function_from_no_knowledge1:
"REVEAL {{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K} (G \<times> H)  =
{{(g,h)|g h. g\<in>G \<and> h\<in>H \<and> f g h = k}|k. k\<in>K}
"
  unfolding REVEAL_def
  by blast


lemma reveal_function_from_no_knowledge_general:
"REVEAL {{h|h. h\<in>H \<and> f h = k}|k. k\<in>K} H  =
{{h|h. h\<in>H \<and> f h = k}|k. k\<in>K}
"
  unfolding REVEAL_def
  by blast


section \<open>Reordering Statements\<close>


(* swap reveal statements *)
lemma swap_reveals0:
"(REVEAL r) ;; (REVEAL s) = (REVEAL s) ;; (REVEAL r)"
  unfolding COMPOSE_def REVEAL_def
  by blast


lemma swap_reveals1:
"(REVEAL r ;; REVEAL s) H = (REVEAL s ;; REVEAL r) H"
  by (simp add: swap_reveals0)


(* swap assignment statements *)

(* Check with Carroll that this could be a reasonable way to write assignments *) 

lemma swap_assignments0:
"CHOOSE (\<lambda>(_,y). {(x,y)|x. x\<in>X}) ;; CHOOSE (\<lambda>(x,_). {(x,y)|y. y\<in>Y}) = CHOOSE (\<lambda>(x,_). {(x,y)|y. y\<in>Y}) ;; CHOOSE (\<lambda>(_,y). {(x,y)|x. x\<in>X}) "
  unfolding COMPOSE_def CHOOSE_def
  apply simp
  by blast


lemma swap_assignments1:
"(CHOOSE (\<lambda>(_,y). {(x,y)|x. x\<in>X}) ;; CHOOSE (\<lambda>(x,_). {(x,y)|y. y\<in>Y})) H = (CHOOSE (\<lambda>(x,_). {(x,y)|y. y\<in>Y}) ;; CHOOSE (\<lambda>(_,y). {(x,y)|x. x\<in>X})) H"
  by (simp add: swap_assignments0)


(*
   In isabelle tuples are internally represented as nested pairs e.g (x,y,z) = (x,(y,z))
   Therefore adding a third component to the pair can be a stand in for many more components
*)
lemma general_assignment_swap0:
"CHOOSE (\<lambda>(_,y,z). {(x,y,z)|x. x\<in>X}) ;; CHOOSE (\<lambda>(x,_,z). {(x,y,z)|y. y\<in>Y}) = CHOOSE (\<lambda>(x,_,z). {(x,y,z)|y. y\<in>Y}) ;; CHOOSE (\<lambda>(_,y,z). {(x,y,z)|x. x\<in>X}) "
  unfolding COMPOSE_def CHOOSE_def
  apply simp
  by blast


lemma general_assignment_swap1:
"(CHOOSE (\<lambda>(_,y,z). {(x,y,z)|x. x\<in>X}) ;; CHOOSE (\<lambda>(x,_,z). {(x,y,z)|y. y\<in>Y})) H = (CHOOSE (\<lambda>(x,_,z). {(x,y,z)|y. y\<in>Y}) ;; CHOOSE (\<lambda>(_,y,z). {(x,y,z)|x. x\<in>X})) H"
  by (simp add: general_assignment_swap0)


(* in the case that we assign the variables to a single value rather than to a set of possible values *)
lemma singleton_assignment_swap:
  "
   CHOOSE (\<lambda>(_,y).{(c,y)}) ;; CHOOSE (\<lambda>(x,_).{(x,k)})
   =
   CHOOSE (\<lambda>(x,_).{(x,k)}) ;; CHOOSE (\<lambda>(_,y).{(c,y)})
  "
  unfolding COMPOSE_def CHOOSE_def reducedEquality_def reducedHyper_def
  apply simp
  by blast

  
(*
A shortcoming of the reveal statement (in this implementation) seems to be that it must refer
to the values of all other variables even if we are only interested in it acting on a single 
variable.

It cannot take in information from the state H, as it is given as the intersection between H
and what you want to reveal.
*)


(* for the identity case that f x = x, a.k.a revealing a variable *)
lemma reveal_is_ass_then_reveal1:
  "
   REVEAL {{x}|x. x\<in>X}  
   =
   NewVar t (CHOOSE (\<lambda>(_,x). {(x, x)}) ;; REVEAL {{(t,x)|x. x\<in>X}|t. t\<in>X}) 
  "
  unfolding COMPOSE_def CHOOSE_def reducedEquality_def reducedHyper_def REVEAL_def NewVar_def
  apply simp
  by blast


lemma reveal_is_ass_then_reveal2:
  "
   (REVEAL {{x}|x. x\<in>X}) H  
   =
   (NewVar t (CHOOSE (\<lambda>(_,x). {(x, x)}) ;; REVEAL {{(t,x)|x. x\<in>X}|t. t\<in>X})) H 
  "
  apply (subst reveal_is_ass_then_reveal1)
  unfolding NewVar_def
  by simp

  
lemma bool_fn_true:
  "f True \<Longrightarrow> f False \<Longrightarrow> f b = True"
  by (metis (full_types))


lemma bool_fn_false:
  "\<not> f True \<Longrightarrow> \<not> f False \<Longrightarrow> f b = False"
  by (metis (full_types))


lemma bool_fn_id:
  " f True \<Longrightarrow> \<not> f False \<Longrightarrow> f b = b"
  by (metis (full_types))


lemma bool_fn_opposite:
  " \<not> f True \<Longrightarrow> f False \<Longrightarrow> f b = (\<not>b)"
  by (metis (full_types))

lemma reveal_equals_assign_then_reveal_help1:
"REVEAL {{(t,h)|h. h\<in>H}|t. t\<in>K} {(f h, h)|h. h\<in>H}
=
{{(f h, h)|h. h\<in>H} \<inter> S |S. S\<in>{{(t,h)|h. h\<in>H}|t. t\<in>K}}
"
  unfolding REVEAL_def
  by blast


lemma reveal_equals_assign_then_reveal_help2:
"REVEAL {{(t,h)|h. h\<in>H}|t. t\<in>K} ` {{(f h, h)|h. h\<in>H}}
=
{{{(f h, h)|h. h\<in>H} \<inter> S |S. S\<in>{{(t,h)|h. h\<in>H}|t. t\<in>K}}}
"
  unfolding REVEAL_def
  by blast


lemma reveal_equals_assign_then_reveal_help4:
"\<Union> {{{(f h, h) |h. h \<in> H} \<inter> S |S. S \<in> {{(t, h) |h. h \<in> H} |t. t \<in> K}}}
=
{{(f h, h) |h. h \<in> H} \<inter> S |S. S \<in> {{(t, h) |h. h \<in> H} |t. t \<in> K}}
"
  by simp


lemma reveal_equals_assign_then_reveal_help5:
  shows
"{{(f h, h)|h. h\<in>H} \<inter> S |S. S\<in>{{(t,h)|h. h\<in>H}|t. t\<in>K}}
=
{{(f h, h)|h. h\<in>H \<and> f h = k}|k. k\<in>K}
"
  apply(safe)
  apply fast
  apply(rule_tac x="{(k,h) |h. h\<in>H}" in exI)
  by auto
  

lemma reveal_equals_assign_then_reveal_help6:
"\<Union> {{{(f h, h) |h. h \<in> H \<and> f h = k} |k. k \<in> K}}
=
{{(f h, h) |h. h \<in> H \<and> f h = k} |k. k \<in> K}
"
  by simp


lemma reveal_equals_assign_then_reveal_help7:
  shows
"{{snd x |x. x \<in> s} |s. s \<in> {{(f h, h) |h. h \<in> H \<and> f h = k} |k. k \<in> K}}
=
{{h|h. h\<in>H \<and> f h = k}|k. k\<in>K}
"
  apply safe
  apply fastforce
  apply (rule_tac x="{(f h, h) |h. h \<in> H \<and> f h = k}" in exI)
  by auto


lemma reveal_in_scope:
  fixes t::"'a"
  shows
  "  (
       (NewVar t p) ;; 
       REVEAL E
     ) H 
   = 
     (
       NewVar t (
                  p ;; 
                  REVEAL {(UNIV::'a set)\<times>e|e. e\<in>E}
                )
     ) H"
  unfolding NewVar_def REVEAL_def COMPOSE_def
  apply safe
  apply simp
  apply (rule_tac x="s\<inter>(UNIV\<times>sa)" in exI)
  apply simp
  apply (rule conjI)
  apply blast
  apply blast
  apply simp
  apply (rule_tac x="{z. \<exists>a. (a, z) \<in> hs'}" in exI)
  apply (rule conjI)
  apply blast
  apply (rule_tac x="e" in exI)
  by auto


(* 
  we spoke about how revealing a local variable does not impact the semantics
  so what if we try to prove this lemma again, but don't worry about leaving
  the first element of the statespace alone in the inner-scope reveal?
*)

lemma choose_in_scope:
  fixes t::"'a"
  shows
  "  (
       (NewVar t p) ;; 
       CHOOSE E
     ) H 
   = 
     (
       NewVar t (
                  p ;; 
                  CHOOSE (\<lambda>h. {(fst h, b)|b. b\<in>(E (snd h))})
                )
     ) H"
  unfolding NewVar_def CHOOSE_def COMPOSE_def
  apply safe
  apply simp
  apply (rule_tac x="\<Union> {{(a, ba) |ba. ba \<in> E b} |a b. (a, b) \<in> s}" in exI)
  apply simp
  apply (rule conjI)
  apply blast
  apply blast
  apply simp
  apply (rule_tac x="{z. \<exists>a. (a, z) \<in> hs'}" in exI)
  apply (rule conjI)
  by auto

lemma reveal_equals_assign_then_reveal:
  shows
  "
  REVEAL {{h|h. h\<in>H \<and> f h = k}|k. k\<in>K} H
  =
  NewVar t (CHOOSE (\<lambda>(_,h). {(f h, h)}) ;; REVEAL {{(t,h)|h. h\<in>H}|t. t\<in>K}) H
  "
  apply (subst reveal_fn_equivalence1)
  unfolding COMPOSE_def NewVar_def
  apply (subst choose_equiv_fn)
  apply (subst reveal_equals_assign_then_reveal_help2)
  apply (subst reveal_equals_assign_then_reveal_help5)
  apply (subst reveal_equals_assign_then_reveal_help6)
  apply (subst reveal_equals_assign_then_reveal_help7)
  by simp
  

lemma swap_reveal_assignment_help1:
"CHOOSE (\<lambda>h. {(k, snd h) |k. k = f (fst h)}) H
=
{{(k,snd h)|k h. h\<in>H \<and> k = f (fst h)}}
"
  unfolding CHOOSE_def
  by blast


lemma swap_reveal_assignment_help2:
"REVEAL {{h |h. h \<in> H \<and> g (snd h) = c} |c. c \<in> C} H
=
{{h|h. h\<in>H \<and> g (snd h) = c}|c. c\<in>C}
"
  using reveal_fn_equivalence1 by simp


lemma swap_reveal_assignment_help3:
  assumes "H\<subseteq>(X \<times> Y)"
  shows
  "REVEAL {{h |h. h \<in> (X \<times> Y) \<and> g (snd h) = c} |c. c \<in> C} H
  =
  {{h|h. h\<in>H \<and> g (snd h) = c}|c. c\<in>C}
  "
  unfolding REVEAL_def
  using assms
  apply (-)
  apply safe
  apply (rule_tac x="c" in exI)
  apply blast
  apply (rule_tac x="{h |h. h \<in> X \<times> Y \<and> g (snd h) = c}" in exI)
  by auto


lemma swap_reveal_assignment_help4:
  assumes   "H\<subseteq>(X \<times> Y)"
  and     "\<forall>x\<in>X. (f x)\<in>X"
  shows
  "REVEAL {{h |h. h \<in> (X \<times> Y) \<and> g (snd h) = c} |c. c \<in> C}    {(k, snd h) |k h. h \<in> H \<and> k = f (fst h)}
  =
  {{(k,snd h)|h k. h\<in>H \<and> k = f (fst h) \<and> g (snd h) = c}|c. c\<in>C}
  "
  unfolding REVEAL_def
  using assms
  apply (-)
  apply safe
  apply (rule_tac x="c" in exI)
  apply fastforce
  apply (rule_tac x="{h |h. h \<in> X \<times> Y \<and> g (snd h) = c}" in exI)
  by auto


lemma swap_reveal_assignment_help5:
  shows
  "REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} ` {{(k, snd h) |k h. h \<in> H \<and> k = f (fst h)}}
  =
  {REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} {(k, snd h) |k h. h \<in> H \<and> k = f (fst h)}}
  "
  unfolding REVEAL_def
  by blast


lemma swap_reveal_assignment_help6:
  assumes  "H\<subseteq>(X \<times> Y)"
  and     "\<forall>x\<in>X. (f x)\<in>X"
  shows
  "REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} ` {{(k, snd h) |k h. h \<in> H \<and> k = f (fst h)}}
  =
  {{{(k,snd h)|h k. h\<in>H \<and> k = f (fst h) \<and> g (snd h) = c}|c. c\<in>C}}
  "
  apply (subst swap_reveal_assignment_help5)
  apply (subst swap_reveal_assignment_help4)
  using assms apply(simp+)
  done


lemma swap_reveal_assignment_help7:
  "
  CHOOSE (\<lambda>h. {(k, snd h) |k. k = f (fst h)})
  =
  CHOOSE (\<lambda>h. {(f (fst h), snd h)})
  "
  unfolding CHOOSE_def
  by blast


lemma swap_reveal_assignment_help10:
  shows
  "
  CHOOSE (\<lambda>h. {(k, snd h) |k. k = f (fst h)}) ` {{h |h. h \<in> H \<and> g (snd h) = c} |c. c \<in> C}
  = 
  {(CHOOSE (\<lambda>h. {(k, snd h) |k. k = f (fst h)}) {h |h. h \<in> H \<and> g (snd h) = c}) |c. c \<in> C}
  "
  by blast


lemma swap_reveal_assignment_help11:
"CHOOSE (\<lambda>h. {(f (fst h), snd h)}) {h |h. h \<in> H \<and> g (snd h) = c}
=
{{(f (fst h), snd h) |h. h \<in> H \<and> g (snd h) = c}}
"
  unfolding CHOOSE_def
  by blast


(*
   Need to assume that f doesn't produce values
   outside the type of the variables and that the set we are
   REVEALING generates all possible values of h within its type. 
   The first two assumptions are basically the same thing
*)
lemma swap_reveal_assignment:
  assumes "H\<subseteq>(X \<times> Y)" 
  and     "\<forall>x\<in>X. (f x)\<in>X"
  shows
  "
  (
   CHOOSE (\<lambda>h. {(k,snd h)|k. k = f (fst h)}) ;;
   REVEAL {{h|h. h\<in>(X \<times> Y) \<and> g (snd h) = c}|c. c\<in>C}
  ) 
   H
  =
  (
   REVEAL {{h|h. h\<in>(X \<times> Y) \<and> g (snd h) = c}|c. c\<in>C} ;;
   CHOOSE (\<lambda>h. {(k,snd h)|k. k = f (fst h)})
  ) 
   H
  "
  unfolding COMPOSE_def
  apply (subst swap_reveal_assignment_help1)
  apply (subst swap_reveal_assignment_help3)
  using assms apply(simp+)[1]
  apply (subst swap_reveal_assignment_help6)
  using assms apply(simp+)[2]
  apply (subst union_over_singleton)
  apply (subst swap_reveal_assignment_help10)
  apply (subst swap_reveal_assignment_help7)
  apply (subst swap_reveal_assignment_help11)
  apply safe
  apply blast
  apply (rule_tac x="c" in exI)
  by auto



lemma sraf_help1:
"CHOOSE (\<lambda>h. {(k, snd h) |k. k = f h}) H = {{(k, snd h) |h k. h\<in>H \<and> k = f h}}"
  unfolding CHOOSE_def
  by blast

lemma sraf_help2:
"
CHOOSE (\<lambda>h. {(k, snd h) |k. k = f h}) ` {{h |h. h \<in> H \<and> g (snd h) = c} |c. c \<in> C}
= 
{
CHOOSE (\<lambda>h. {(k, snd h) |k. k = f h}) x|x. x\<in>{{h |h. h \<in> H \<and> g (snd h) = c} |c. c \<in> C}
}
"
  unfolding Set.image_def CHOOSE_def
  by blast


lemma sraf_help3:
"REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} ` {{(k, snd h) |h k. h \<in> H \<and> k = f h}}
=
{REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} {(k, snd h) |h k. h \<in> H \<and> k = f h}}"
  unfolding REVEAL_def
  by blast


lemma sraf_help4:
  assumes "H\<subseteq>(X \<times> Y)" 
  and     "\<forall>h\<in>(X \<times> Y). (f h)\<in>X"
  shows
"
REVEAL {{h |h. h \<in> X \<times> Y \<and> g (snd h) = c} |c. c \<in> C} {(k, snd h) |h k. h \<in> H \<and> k = f h}
=
{
{(k, snd h) |h k. h \<in> H \<and> (k = f h) \<and> (g (snd h) = c)}|c. c\<in>C
}
"
  unfolding REVEAL_def
  apply safe
  apply (rule_tac x="c" in exI)
  using assms apply fastforce
  apply (rule_tac x="{h |h. h \<in> X \<times> Y \<and> g (snd h) = c}" in exI)
  using assms by auto


lemma swap_reveal_assignment_f_acts_on_2_vars:
  assumes "H\<subseteq>(X \<times> Y)" 
  and     "\<forall>h\<in>(X \<times> Y). (f h)\<in>X"
  shows
  "
  (
   CHOOSE (\<lambda>h. {(k,snd h)|k. k = f h}) ;;
   REVEAL {{h|h. h\<in>(X \<times> Y) \<and> g (snd h) = c}|c. c\<in>C}
  ) 
   H
  =
  (
   REVEAL {{h|h. h\<in>(X \<times> Y) \<and> g (snd h) = c}|c. c\<in>C} ;;
   CHOOSE (\<lambda>h. {(k,snd h)|k. k = f h})
  ) 
   H
  "
  unfolding COMPOSE_def 
  apply (subst sraf_help1)
  apply (subst swap_reveal_assignment_help3)
  using assms apply simp
  apply (subst sraf_help3)
  apply (subst sraf_help4)
  using assms apply simp
  using assms apply simp
  apply (subst union_over_singleton)
  unfolding CHOOSE_def
  using assms by blast

end