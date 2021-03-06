theory Dining_Cryptographers_example
  imports Main "~~/src/HOL/Library/LaTeXsugar" "Shadow_Semantics" "Utils" "Cream_Cake_example"
begin


section \<open>Dining Cryptographers\<close>

(*
For this interpretation I want to say that REVEAL "a XOR b XOR c" is the same as 
declaring 3 new (extra) hidden variables, (x, y, z) and then REVEALING:
a XOR x XOR y
b XOR y XOR z
c XOR z XOR x
*)

lemma dining_help:
  assumes "G={True,False}"
  shows
"
REVEAL {
        {
         (a,b,c)| a b c. a\<in>G \<and> b\<in>G \<and> c\<in>G \<and>
          (g = (XOR (XOR a b) c))
        }
         |g. g\<in>G
       } (A\<times>B\<times>C)
=
       {
        {
         (a,b,c)| a b c. a\<in>A \<and> b\<in>B \<and> c\<in>C \<and>
          (g = (XOR (XOR a b) c))
        }
         |g. g\<in>G
       }
"
  unfolding REVEAL_def XOR_def
  apply safe
  apply (rule_tac x="g" in exI)
  using assms apply blast
  apply (rule_tac x="{(a, b, c) |a b c. a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> g = (((a \<or> b) \<and> (\<not> a \<or> \<not> b) \<or> c) \<and> (\<not> ((a \<or> b) \<and> (\<not> a \<or> \<not> b)) \<or> \<not> c))}" in exI)  
  using assms by blast


lemma dining_help1:
"
CHOOSE (\<lambda>(_, a, b, c). {((x, y, z), a, b, c) |x y z. x \<in> G \<and> y \<in> G \<and> z \<in> G}) ({t} \<times> A \<times> B \<times> C)
=
{(G\<times>G\<times>G)\<times>A\<times>B\<times>C}
"
  unfolding CHOOSE_def
  by blast


lemma dining_help2:
"
REVEAL {{((x, y, z), a, b, c) |x y z a b c. 
                               x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x} 
                                  |g k m. g \<in> G \<and> k \<in> G \<and> m \<in> G} `
             {(G \<times> G \<times> G) \<times> A \<times> B \<times> C}
=
{
REVEAL {{((x, y, z), a, b, c) |x y z a b c. 
                               x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x} 
                                  |g k m. g \<in> G \<and> k \<in> G \<and> m \<in> G}
             ((G \<times> G \<times> G) \<times> A \<times> B \<times> C)
}
"
  by blast


lemma dining_help3:
  assumes "G={True,False}"
  shows
"
{
REVEAL {{((x, y, z), a, b, c) |x y z a b c. 
                               x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x} 
                                  |g k m. g \<in> G \<and> k \<in> G \<and> m \<in> G}
             ((G \<times> G \<times> G) \<times> A \<times> B \<times> C)
}
=
{
{{((x, y, z), a, b, c) |x y z a b c. 
                               x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x} 
                                  |g k m. g \<in> G \<and> k \<in> G \<and> m \<in> G}
}
"
  unfolding REVEAL_def
  apply safe
  apply (rule_tac x="g" in exI)
  apply (rule_tac x="k" in exI)
  apply (rule_tac x="m" in exI)
  apply (unfold XOR_def)[1]
  using assms apply simp
  apply blast
  apply (rule_tac x="{((x, y, z), a, b, c) |x y z a b c. x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x}" in exI)
  using assms apply simp
  by blast
  

lemma dining_help4:
  assumes "G={True,False}"
  and     "A \<subseteq> G"
  and     "B \<subseteq> G"
  and     "C \<subseteq> G"
  and     "X \<subseteq> G"
  and     "Y \<subseteq> G"
  and     "Z \<subseteq> G"
  shows
"
{
  {snd h |h. h \<in> s} |s.
     s \<in> {
           {((x, y, z), a, b, c) 
               |x y z a b c. 
                x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x
           } |g k m.
           g \<in> G \<and> k \<in> G \<and> m \<in> G
         }
}
=
{
           {(a, b, c) 
               |x y z a b c. 
                x \<in> G \<and> y \<in> G \<and> z \<in> G \<and> a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> g = XOR (XOR a x) y \<and> k = XOR (XOR b y) z \<and> m = XOR (XOR c z) x
           } |g k m.
           g \<in> G \<and> k \<in> G \<and> m \<in> G
         }
"
  apply safe
  apply simp
  apply blast
  unfolding XOR_def
  using assms apply simp
  apply (rule_tac x="{((x, y, z), a, b, c) |x y z a b c.
                a \<in> A \<and>
                b \<in> B \<and>
                c \<in> C \<and>
                g = (((a \<or> x) \<and> (a \<longrightarrow> \<not> x) \<or> y) \<and> (\<not> a \<and> \<not> x \<or> a \<and> x \<or> \<not> y)) \<and>
                k = (((b \<or> y) \<and> (b \<longrightarrow> \<not> y) \<or> z) \<and> (\<not> b \<and> \<not> y \<or> b \<and> y \<or> \<not> z)) \<and> m = (((c \<or> z) \<and> (c \<longrightarrow> \<not> z) \<or> x) \<and> (\<not> c \<and> \<not> z \<or> c \<and> z \<or> \<not> x))}" in exI)
  by auto


lemma dining_cryptographers:
  assumes "G={True,False}"
  and     "A \<subseteq> G"
  and     "B \<subseteq> G"
  and     "C \<subseteq> G"
  and     "X \<subseteq> G"
  and     "Y \<subseteq> G"
  and     "Z \<subseteq> G"
  shows
"
REVEAL {
        {
         (a,b,c)| a b c. a\<in>G \<and> b\<in>G \<and> c\<in>G \<and>
          (g = (XOR (XOR a b) c))
        }
         |g. g\<in>G
       } (A\<times>B\<times>C)
=
NewVar t (
          CHOOSE (
                  \<lambda>(_,(a,b,c)). {((x,y,z),(a,b,c))|x y z. x\<in>G \<and> y\<in>G \<and> z\<in>G}
                 ) ;;
          REVEAL {
                  {
                   ((x,y,z),(a,b,c))|x y z a b c. x\<in>G \<and> y\<in>G \<and> z\<in>G \<and> a\<in>G \<and> b\<in>G \<and> c\<in>G \<and>
                                      (g = (XOR (XOR a x) y)) \<and>
                                      (k = (XOR (XOR b y) z)) \<and>
                                      (m = (XOR (XOR c z) x))
                  }|g k m. g\<in>G \<and> k\<in>G \<and> m\<in>G
                 }       
         ) (A\<times>B\<times>C)
"

  apply (subst dining_help)
  using assms apply simp
  unfolding NewVar_def
  unfolding COMPOSE_def
  apply (subst dining_help1)
  apply (subst dining_help2)
  apply (subst dining_help3)
  using assms apply simp
  apply (subst union_over_singleton)
  apply (subst dining_help4[where X="X" and Y="Y" and Z="Z"])
  using assms apply(simp+)[7]
  apply safe
  using assms apply simp
  apply (rule_tac x="g" in exI)
  apply (rule_tac x="g" in exI)
  apply (rule_tac x="g" in exI)
  apply (unfold XOR_def)[1]
  apply blast
  using assms apply simp
  apply (rule_tac x="XOR (XOR g k) m" in exI)
  unfolding XOR_def
  apply simp
  by blast


  
section \<open>Proving Algebraic Steps for 3 cryptographers\<close>
(*
   The first part of this in 1001 cryptographers uses the cream cake result
   with a difference that instead of showing reveal (a==b) ;; reveal (a==c) is
   equivalent to reveal (a==b) ;; reveal (b==c) we replace equality with XOR

   So I turn the equality into the exact one used above in equiv_reveals.
*)

lemma XOR_equiv_equality1:
"
 REVEAL {{(a,b,c)|a b c. (XOR a c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}}
 =
 REVEAL {{(a,b,c)|a b c. (a = c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}}
"
  apply (rule ext)
  unfolding REVEAL_def XOR_def
  apply simp
  apply safe
  apply simp
  apply (rule_tac x="{(a, b, c) |a b c. (a = c) = (\<not>k)}" in exI)
  apply blast
  apply simp
  apply (rule_tac x="{(a, b, c) |a b c. ((a \<or> c) \<and> (a \<longrightarrow> \<not> c)) = (\<not>k)}" in exI)
  by auto

 
lemma XOR_equiv_equality2:
"
 REVEAL {{(a,b,c)|a b c. (XOR a b) = k \<and> c\<in>{True,False}}|k. k\<in>{True,False}}
 =
 REVEAL {{(a,b,c)|a b c. (a = b) = k \<and> c\<in>{True,False}}|k. k\<in>{True,False}}
"
  apply (rule ext)
  unfolding REVEAL_def XOR_def
  apply simp
  apply safe
  apply simp
  apply (rule_tac x="{z. \<exists>a b. (\<exists>c. z = (a, b, c)) \<and> (a = b) = (\<not>k)}" in exI)
  apply blast
  apply simp
  apply (rule_tac x="{z. \<exists>a b. (\<exists>c. z = (a, b, c)) \<and> ((a \<or> b) \<and> (a \<longrightarrow> \<not> b)) = (\<not>k)}" in exI)
  by auto


lemma XOR_equiv_equality3:
"
  REVEAL {{(a,b,c)|a b c. (XOR c b) = k \<and> a\<in>{True,False}}|k. k\<in>{True,False}}
 =
  REVEAL {{(a,b,c)|a b c. (c = b) = k \<and> a\<in>{True,False}}|k. k\<in>{True,False}}
"
  apply (rule ext)
  unfolding REVEAL_def XOR_def
  apply simp
  apply safe
  apply simp
  apply (rule_tac x="{(a, b, c) |a b c. (c = b) = (\<not>k) }" in exI)
  apply blast
  apply simp
  apply (rule_tac x="{(a, b, c) |a b c. ((c \<or> b) \<and> (c \<longrightarrow> \<not> b)) = (\<not>k) }" in exI)
  by auto
  

lemma aXORb_aXORc_determines_aXORb_bXORc:
  shows
  "(
    REVEAL {{(a,b,c)|a b c. (XOR a c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}} ;;
    REVEAL {{(a,b,c)|a b c. (XOR a b) = k \<and> c\<in>{True,False}}|k. k\<in>{True,False}} 
   ) 
   = 
   (
    REVEAL {{(a,b,c)|a b c. (XOR a c) = k \<and> b\<in>{True,False}}|k. k\<in>{True,False}} ;;
    REVEAL {{(a,b,c)|a b c. (XOR c b) = k \<and> a\<in>{True,False}}|k. k\<in>{True,False}}
   )"
  apply (subst XOR_equiv_equality1)+
  apply (subst XOR_equiv_equality2)
  apply (subst XOR_equiv_equality3)
  using equiv_reveals by simp



(* 
   Now we have reached (10) in 1001 cryptos
 
   Next the implementation is constructed and the first step taken uses:

  reveal ((l XOR r) XOR (a XOR b)) ;; reveal ((l XOR r) XOR c)
  =
  reveal ((l XOR r) XOR (a XOR b)) ;; reveal ((a XOR b) XOR c)

  which is the same as something we did before (lemma aXORb_aXORc_determines_aXORb_bXORc)
 
  obvious if you let x = (l XOR r) and y = (a XOR b):


  reveal (x XOR y) ;; reveal (x XOR c)
  =
  reveal (x XOR y) ;; reveal (y XOR c)
  
  Isabelle doesn't believe it is true currently as it requires extra variables in the state-space...

*)




(*

   Then the encryption lemma is used with a declaration of two hidden variables l and r.
   
   We will translate this as declaring a new pair (which is made up of two variables)
 
   Then we can just use our most general encryption lemma to prove it:

*)

lemma double_encryption_lemma:
  assumes "BB ={(True,True),(True,False),(False,True),(False,False)}"  
          "hs \<subseteq> BB"
  shows
"
  SKIP hs
  =
  NewVar t (
             (
               CHOOSE (\<lambda>(_,x). {(lr,x)|lr. lr\<in>BB}) 
             ) ;;
               REVEAL {{(lr,x)|lr x. lr\<in>BB \<and> x\<in>BB 
                               \<and> (XOR 
                                      (XOR (fst lr) (snd lr)) 
                                      (XOR (fst x) (snd x)) 
                                 ) = k 
                       }|k. k\<in>{True,False}
                      }
           )
  hs
"
  apply (subst more_general_encryption_lemma[where K="{True,False}" and H="{(True,True),(True,False),(False,True),(False,False)}"
                               and f="(\<lambda>lra xa. XOR (XOR (fst lra) (snd lra)) (XOR (fst xa) (snd xa)) )"
                               and G="{(True,True),(True,False),(False,True),(False,False)}"
                               and hs="hs" and t="t"])
  unfolding XOR_def
  using assms by simp+
  
(*
   The final step in 1001 cryptos is just performing a substitution that was proven earlier
   (Cream Cake with the equalities changed to XORs)
*)


(*

Turning back to scope adjustment as that is the last thing left:

*)


(* 
  It is not going to be recursive, but
  I need to use pattern matching, therefore
  I cannot use "definition".
  Although, maybe I could use the recursiveness
  on COMPOSE...



definition lift_reveal :: "'h prog \<Rightarrow> ('t\<times>'h) prog"
  where
    "lift_reveal p \<equiv> case p of (REVEAL E) \<Rightarrow> REVEAL {Y\<times>e|e Y. e\<in>E} | p \<Rightarrow> (\<lambda>H. SKIP H)" 
*)



(* 
  can't seem to define a function even for the specific case of REVEAL, 
  so instead we just prove the lemma:
*)



end