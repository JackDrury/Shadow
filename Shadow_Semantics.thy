theory Shadow_Semantics
  imports Main
begin

text 
\<open>
The Shadow Semantics are used for reasoning about the security of a program.
They assume all variables are hidden and describe what an attacker can learn about 
the variables if they know the source code and can observe any outputs of the program.
They allow for nondeterministic behaviours in the program and leak information to an attacker
via an explicit REVEAL statement or as the result of a conditional (IfThenElse).

Using the REVEAL statement we are able to abstract from the cause of a leak and focus on the
information that is leaked instead. For example, we  don't care if information is leaked via a 
timing, electromagnetic or acoustic side-channel we only care about the information that is 
represented.

A Shadow program acts on a set S of some type 'h. The type 'h is all possible points in the
statespace (i.e. all possible combinations of values for the variables). The set S represents 
the ignorance of the attacker. If the attacker knows nothing (which is likely before the
execution of the program) then S is the set of all possible combinations of values for the
variables. As the attacker learns more about the variables the size of S will decrease and the only
values that remain in the set will be those that cannot be ruled out for certain. If S is 
a singleton then the attacker knows the exact value of all the variables in the statespace.

After acting on S, a Shadow program will return a set of sets of type 'h. The reason it is a set of
sets is to account for possible nondeterminism in the program. Each inner set of type 'h represents
the attackers knowledge of the statespace if a specific nondeterministic fork in the program is 
taken.
\<close>

section \<open>Semantic Definitions\<close>

text
\<open>  
We begin by making an alias for the type of a shadow program (prog).

A shadow program takes a set of type 'h to a set of sets of type 'h.
\<close>

type_synonym 'h prog = "'h set \<Rightarrow> ('h set) set"

text 
\<open>   
SKIP takes a set of type 'h and returns a singleton set containing its argument 
\<close>
definition
    SKIP ::"'h prog"
where
    "SKIP hs \<equiv> {hs}"

text 
\<open>   
REVEAL can be thought of as leaking the result of some function (f :: H \<Rightarrow> G) applied to the
statespace (where the statespace is of type H). To acheive this, the argument given to REVEAL
is a double set comprehension. This will partition the statespace into separate sets that are
grouped by the result of applying f to that point in the statespace. For the generic example of f
above the argument would be {{h | h. h\<in>H \<and> f h = g}| g. g\<in>G}.

It then leaks the information by taking the intersection of each possible outcome of f h (i.e. the
set of all points in the state space that could result in f h = g) with the set representing the 
ignorance of the attacker.
\<close>

definition
    REVEAL ::"('h set) set \<Rightarrow> 'h prog"
where
    "(REVEAL rs) hs \<equiv> {inter hs s | s. s\<in>rs}"


text 
\<open>   
CHOOSE is a generalised form of assignment. It is an internal (hidden from the attacker)
nondeterministic choice between alternatives. With ordinary assignment being a degenerate case.

The argument to CHOOSE is a function that takes in an element of the statespace and will return a
set of elements of the statespace. This function is applied to every element of the attackers set of
possible states and the union over all of these is taken. The result is a singleton containing the 
set of all possible states from the function as it is a hidden nondeterminism and the attacker 
cannot tell which assignment was actually made.
\<close>

definition
    CHOOSE ::"('h \<Rightarrow> 'h set) \<Rightarrow> 'h prog"
where
    "(CHOOSE f) hs \<equiv> {\<Union>y\<in>{f h | h. h\<in>hs}. y}"


text 
\<open>   
DEMONIC is a visible nondeterministic choice between two alternative programs. This means the 
attacker is able to tell which program was executed (the innermost sets returned by 'p hs' and 
'q hs' are kept separate by the union).
\<close>

definition
    DEMONIC ::"'h prog \<Rightarrow> 'h prog \<Rightarrow> 'h prog"
where
    "(DEMONIC p q) hs \<equiv> union (p hs) (q hs)"


text 
\<open>   
COMPOSE is simply sequential composition of programs.
\<close>

definition
    COMPOSE ::"'h prog \<Rightarrow> 'h prog \<Rightarrow> 'h prog" (infixr ";;" 60)
where
    "(COMPOSE p q) hs \<equiv> \<Union>hs'\<in>(p hs). (q hs')"


text 
\<open>   
IfThenElse is the usual 'if then else' statement except it leaks the value of the conditional 
(i.e. the attacker knows what the condition evaluated to and hence which path was executed).
\<close>

definition
    IfThenElse :: "('h \<Rightarrow> bool) \<Rightarrow> 'h prog \<Rightarrow> 'h prog \<Rightarrow> 'h prog"
where
    "(IfThenElse b p q) hs \<equiv> union (p {h. h\<in>hs \<and> b h}) (q {h'. h'\<in>hs \<and> \<not>(b h')})"


text 
\<open>   
NewVar introduces a new variable to the statespace. It allows us to define the scope of a variable.
\<close>

definition
    NewVar :: "'tau \<Rightarrow> ('tau \<times> 'h) prog \<Rightarrow> 'h prog"
where
    "(NewVar init p) hs \<equiv> {{snd h |h. h \<in> s} | s. s \<in>(p ({init} \<times> hs))}"

end