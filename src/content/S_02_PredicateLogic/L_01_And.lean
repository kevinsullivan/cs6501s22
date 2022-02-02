/-
You've already seen a lot in this class,
but the key ideas are that equality has
one introduction rule and one elimination
rule, that these rules reflect *axioms* of 
equality, and that you can now *use* these
axioms to prove theorems about additional
essential properties of equality: namely,
it is symmetric and transitive.

In this class, we introduce conjunction,
∧ (and), as connective that combines any
two propositions into a larger one; and
we show how we define the introduction and
elimination rules for this connective *so
that* it behaves in Lean as it behaves in
predicate logic: to prove P ∧ Q we need to
provide proofs of P and of Q, respectively
(the introduction rule), and given a proof
of P ∧ Q, we can *use* it to derive of proof
of P, and a proof of Q. These are of course
the elimination rules for ∧. 

Once we've defined these rules as "axioms" 
then we can use them to prove new theorems
about the properties of the ∧ connective,
that it's *commutative* and *associative*.

That's our agenda.
-/

/-
To get started, let assume that P and Q 
are arbitrary propositions. We'll use the
"axiom" keyword in Lean, which introduces
assumptions into the current environment,
which is here the "global" environment of
this file.
-/
axioms P Q : Prop

-- Now P ∧ Q is also a proposition 
#check P ∧ Q

-- And ∧ is just notation for "and"
#check and P Q

/-
∧ is a logical "connective." That means
it "connects" two propositions into one
larger proposition. Given the propositions
are types in our logic, "and" is basically
a polymorphic type building function that
takes two propositional types as arguments 
and yields one as a result. What, then, is 
the type of and, viewed as a function?
-/
#check @and 

/-
Right. It takes two propositions, P and Q, 
and gives us back a new proposition, P ∧ Q,
which means the same as (and P Q).
-/

/-
What we are now going to see is that ∧ is
implemented in Lean as a polymorphic type.
That is, it's going to be an inductive type
with two type arguments. The type arguments
are the two propositions to be connected. 
The constructor for this new type defines 
its introduction rule (the way to build a
proof object of this new type). Finally, 
the elimination rules allow us to derive
a proof of P from a proof of P ∧ Q, and to
derive a proof of Q, as well. 
-/

/-
Here's Lean's definition of and (∧):

structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)

New here is the use of "structure." This 
keyword can be used in place of "inductive" 
when a type has exactly one constructor. 
It allows the argument names, left and right, 
to be used as names of Lean-provided functions
to "access" the field values of an object of 
type P ∧ Q. So, if you have an object, pf, of 
type P ∧ Q (and P Q), then (and.left pf) and 
(and.right pf) give you proofs of P and of Q. 


In sum, the "intro" constructor for ∧ 
implements the introduction rule for ∧,
while the Lean-provided accessor functions,
left and right, implement the elimination
rules for ∧: left and right, respectively. 
-/

/-
To see what we can do with our new "rules"
let's assume that we now also have proofs
of P and of Q. Remembers the propositions
are the *types* P and Q. For proofs we want
values of these types. So let's just assume
"axiomatically" that (little) p and q are 
proofs of P and Q, respectively.
-/
axioms (p : P) (q : Q)

/-
Give that we're now in a (global) context
in which we have assumed P and Q are in Prop
and that p and q are proofs of them, we can
now claim that P ∧ Q is true, and we can
produce a proof to show that it is. 
-/
example : P ∧ Q := and.intro p q

/-
Yay. That's how we use the introduction 
rule for ∧ to prove propositions of the
form P ∧ Q (conjunctions).
-/

/-
Here's the equivalent formulation using 
ordinary function definition notation. We
define func (something we're just making 
up) to be a function that takes P, Q, p, 
and q as arguments and returns a proof of 
P ∧ Q.
-/
def func 
  (P Q : Prop) 
  (p : P) 
  (q : Q) : 
  P ∧ Q :=
and.intro p q

/-
We can also write our own functions to mimic
the elimination rules for and. 
-/
def and_elim_left 
  (P Q : Prop) 
  (pq : P ∧ Q) : 
  P 
  :=
and.elim_left pq

/- 
Homework #1: Define an analogous function,
and_elim_right.
-/ 

-- Here.

/-
From a proof of P ∧ Q we can derive a proof 
of P, and we can derive a proof of Q, using 
the elimination rules for ∧:

and.elim_left
and.elim_right
-/

#check @and.elim_left
#check @and.left 
#check @and.elim_right
#check @and.right

/-
and.left : ∀ {a b : Prop}, a ∧ b → a
and.right : ∀ {a b : Prop}, a ∧ b → b
-/

/-
So, yay! We now have the basic *axioms* for
creating and using proofs of *conjunctions*
(propositions built using ∧). With them we
can state and prove new *theorems* about the
behavior of the ∧ connective. For example,
it's "commutative": whenever we have a proof
of P ∧ Q we can derive a proof of Q and P!
-/


theorem and_commutes 
  (P Q : Prop) (pq : P ∧ Q) : Q ∧ P :=
  and.intro 
    (and.right pq)
    (and.left pq)

/-
The idea here is pretty simple. A proof of
P ∧ Q is of the form (and.intro p q), which
you can think of as a labelled order pair of
proofs. (The label is and.intro.) Given such
a proof, we use our elimination functions,
left and right, to extract p and q, then we
use and.intro to put them together again, in
the opposite order, to construct a proof,
⟨ q, p ⟩ of Q ∧ P. Yes, we just used a new
notation.

Here's another version of our proof. We use
example to avoid giving it a name. We specify
the same arguments (before the colon) and the
same return type (just after the colon). We
then write the "implementation" (after the :=)
using both angle-bracket and dot notation for
field access. Use \< and \> to get the angle
brackets in the VSCode Lean IDE.
-/

example (P Q : Prop) (pq : P ∧ Q) : Q ∧ P :=
  ⟨ pq.right, pq.left ⟩ 

/-
At this point, we've now seen the introduction
and elimination "rules" for both = and ∧. The 
introduction rules are eq.refl and and.intro,
while the elimination rules are eq.subst, and
and.left and and.right (aka and.elim_left and
and.elim_right).

We've also seen, implicitly, the introduction
and elimination rules for ∀ and →. The intro
rule says "assume the argument/premise and in
that context, show that you can construct and
"return" a proof of the conclusion/return type.
To prove P → Q, assume you're given a proof of 
P and in that context show that you can have a
proof of Q. That proves P → Q. Similarly, to
prove ∀ (p : P), Q, assume that you're given
a proof of P and show that you can construct
a proof of Q.

Do they sound similar? Yes, indeed. In Lean
these connectives are in fact essentially 
just different notations for the same idea!
Look at how Lean prints ∀ (p : P), Q. It's
just P → Q! (Recall we defined P and Q above.)
-/

#check ∀ (p : P), Q

/-
Homework #2: Formally state and prove the 
proposition that "∧ is associative" by
uncommenting and completing the following
definition.
-/

-- theorem and_assoc ...

