/-

This document is an extended essay on proofs of the theorem: ∀ a : Prop, a → ¬¬a.

This is the easier version of double-negation elimination because it has a proof
in constructive logic. The proof of it's reverse: ∀ a : Prop, ¬¬a → a requires
classical logic using the law of the excluded middle or its equivalent.

First, we will do the proof in Lean, using all convenience features and syntactic
sugar.

-/

theorem dne_right : a → ¬¬a := by
  -- ha is a conventional name for evidence for the hypothesis that a is true
  intro ha
  -- The evidence for the hypothesis ¬a is a function that takes evidence
  -- for a and yields false.
  intro not_a
  -- Apply the function to evidence for a and conclude false. Since every
  -- claim follows from false, we are done.
  apply not_a ha

-- The tactics above produce a term, which is evidence for the theorem,
-- that is a function.
#print dne_right

/-

Next, we will prove a theorem with exactly the same content, but we'll
eliminate the syntactic sugar to make it look as much like Calculus of
Constructions (COC) as possible. And we'll write the evidence for the
theorem directly instead of using tactics.

For the exact definition of COC that we're using, see Wikipedia:
https://en.wikipedia.org/wiki/Calculus_of_constructions

The COC version of ¬a is (∀ c : Prop, (∀ x : a, c)). It says explicitly
that for any proposition c, you can prove c if you can prove a. x is
the evidence that would allow you to prove a. Since there is no proposition
that implies every other except for "False", this mouthful says that
a → False, or equivalently ¬a.

-/

--                               |------------------------------- a → ¬¬a --------------------------|
--                                         |---------------------- ¬¬a ----------------------------|
--                                                               |------------ ¬a -----------|
theorem dne_right2 : ∀ a : Prop, (∀ _ : a, (∀ c₂ : Prop, (∀ x₂ : (∀ c₁ : Prop, (∀ x₁ : a, c₁)), c₂))) :=
  fun (a : Prop) =>
    fun (ha : a) =>
      fun (c : Prop) =>
        fun (not_a : (∀ c₁ : Prop, (∀ x₁ : a, c₁))) =>
          (not_a c) ha

/-

Now, we switch to pure COC, as described at:
https://en.wikipedia.org/wiki/Calculus_of_constructions

Lean can't help us here, so the rest of the work will be manual symbol manipulation.

In order to prove this claim in COC, we will construct a typing judgement ⊢ term : type
where the term is evidence that the claim holds. Each step of the proof will use one rule
given in the Wikipedia article. The term and the type come from the theorem dne_right2
that we just proved.


Goal)
⊢ (λ a : P. (λ ha : a. (λ c₂ : P. (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha)))) :
    (∀ a : P. (∀ ha : a. (∀ c₂ : P. (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂))))
                                            |---------- ¬a ----------|
                         |--------------------- ¬¬a -----------------------|
              |--------------------------- a → ¬¬a -------------------------|


We have to use the rules of COC to produce this judgement. Normally, there is only one
choice of rule to apply. In this case it must be rule 4, which introduces or eliminates
a ∀ quantifier. It's the only choice because the term starts with λ and the type starts
with ∀. Matching the bottom of rule 4 to our goal, we have the following bindings.

x = a
A = P
N = (λ ha : a. (λ c₂ : P. (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha)))
B = (∀ ha : a. (∀ c₂ : P. (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂)))

Now we construct the two sub-goals defined by rule 4.

i) ⊢ P : T                                 (Satisfied by axiom 1)

ii) a : P ⊢ (λ ha : a. (λ c₂ : P. (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha))) :
              (∀ ha : a. (∀ c₂ : P. (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂)))

NOTE ON INFERENCE RULES: The rules given in Wikipedia say "we use ... K, L to mean either P, T", which
denote the set of propositions and the set of types, respectively. I take that to mean that you may choose
either P or T each time you match a term to a rule containing K or L, as long as you do it consistently for
all appearances of K and L and that the rules remain valid for either choice. The choice is not mechanical
because K appears by itself in the condition of some rules, where it is not constrained by anything in the
goal. In sub-goal i), I made the choice that K = T because it's obvious that P is not in the type P.

Sub-goal i) just states that P is a type and this statement is an axiom (inference rule 1), so it is
satisfied immediately. In sub-goal ii), we have moved a : P from the λ abstraction to the typing context,
where we can actually make use of it via inference rule 2.

Because the term still starts with λ and the type with ∀, we apply rule 4 again. This time, we have
the bindings:

A = a
x = ha
N = (λ c₂ : P. (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha))
B = (∀ c₂ : P. (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂))

NAMING CHOICES: I've used c₁ and c₂ for arbitrary propositions, which appear where some other proposition
is false. Each instance of "not" in the theorem gives rise to one such arbitrary proposition.
"not_a" is a name for a function that is able to prove any proposition using evidence that
proposition "a" is true. In other words, it is evidence that "a" is false. And "ha" is evidence
that "a" is true. "hfoo" is a naming convention for "hypothesis that proposition foo is true".

We carry on with the two live sub-goals:

iii) a : P ⊢ a : P                         (Satisfied by axiom 2)

iv) a : P, ha : a ⊢ (λ c₂ : P. (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha)) :
                      (∀ c₂ : P. (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂))

This time, sub-goal iii) is immediately satisfied by rule 2, which says that a typing judgement holds
when that term is part of the typing context. In goal iv), we added another entry to the typing context
and we still have a λ term with a ∀ type to eliminate. That means we use rule 4 again, with bindings:

x = c₂
A = P
N = (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha)
B = (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂))

The two remaining sub-goals are:

v) a : P, ha : a ⊢ P : T                 (Satisfied by axiom 1)

vi) a : P, ha : a, c₂ : P ⊢ (λ not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)). (not_a c₂) ha) :
                              (∀ x₂ : (∀ c₁ : P. (∀ x₁ : a. c₁)). c₂))

Once more, apply rule 4, with bindings:

x = not_a
A = (∀ c₁ : P. (∀ x₁ : a. c₁))
N = (not_a c₂) ha
B = c₂

Notice that A picks off a large subterm in this case, because it's the type of the not_a function.
This type will move into the typing context where we will need it to deal with function application.

The two remaining sub-goals are:

vii) a : P, ha : a, c₂ : P ⊢ (∀ c₁ : P. (∀ x₁ : a. c₁)) : P

viii) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ (not_a c₂) ha : c₂

In this case, sub-goal vii) is not simply satisfied by an axiom. We need to prove it in multiple
steps. Those steps essentially prove that (∀ c₁ : P. (∀ x₁ : a. c₁)) is properly constructed out
of quantifiers applied to types already in the context. We'll do that proof first and come back
to sub-goal viii).

Sub-goal vii) matches inference rule 3, which permits the introduction of a ∀ quantified type.
We have the bindings:

x = c₁
A = P
B = (∀ x₁ : a. c₁)
L = P

This leads to two sub-goals, namely:

ix) a : P, ha : a, c₂ : P ⊢ P : T                      (Satisfied by axiom 1)

x) a : P, ha : a, c₂ : P, c₁ : P ⊢ (∀ x₁ : a. c₁) : P

We still have a ∀ quantifier at the start of the type, so apply rule 3 again with bindings:

x = x₁
A = a
B = c₁
L = P

This leads to two sub-goals:

xi) a : P, ha : a, c₂ : P, c₁ : P ⊢ a : P             (Satisfied by axiom 2)

xii) a : P, ha : a, c₂ : P, c₁ : P, x₁ : a ⊢ c₁ : P   (Satisfied by axiom 2)


Now we've finished proving sub-goal vii) and we'll go back to work on sub-goal viii).
To restate it, we have:

viii) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ (not_a c₂) ha : c₂

This is our first time encountering an application. We'll need to use rule 5 with
bindings:

M = (not_a c₂)
N = ha
B = c₂
A = a

Two points to mention here. First, the substitution B[x := N] in the rule is moot
because substitution doesn't affect B. Second, think of this rule as working function
application backwards. We're not going from a known function type to a result, instead
we're working from a result type and and argument type back to a required function type.

This leaves us with the sub-goals:

xiii) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ (not_a c₂) : (∀ x₁ : a. c₂)

xiv) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ ha : a                 (Satisfied by axiom 2)

Now we have a second function application requiring use of rule 5, which gives the bindings:

M = not_a
N = c₂
B = (∀ x₁ : a. c₂)
A = P

The two new sub-goals are:

xv) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ not_a : (∀ c₂ : P. (∀ x₁ : a. c₂))      (Satisfied by axiom 2)

xvi) a : P, ha : a, c₂ : P, not_a : (∀ c₁ : P. (∀ x₁ : a. c₁)) ⊢ c₂ : P                                 (Satisfied by axiom 2)


For sub-goal xv) I've ignored some naming differences in the type of not_a. I've basically reasoned
that the types are structurally identical and the names of bound variables within them don't matter.
That could be wrong and perhaps the inference rule 6 with it's undefined notion of β-equivalence
needs to be used.

We have now proved all of the sub-goals arising from the original goal, so the COC permits
us to conclude that it is a valid typing judgement, which means that we have evidence that
the proposition encoded by the type is true.
-/
