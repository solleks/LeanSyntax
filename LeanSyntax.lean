/-
 This file is a description of the Calculus of Constructions that follows the Wikipedia
 article at (https://en.wikipedia.org/wiki/Calculus_of_constructions).

 The plan is to copy out the Wikipedia description of CoC, comment on that in English
 and then illustrate it in Lean4 syntax.
-/

/-
              ***********Start quoting Wikipedia************
TERMS

A term in the calculus of constructions is constructed using the following rules:

o T is a term (also called type);
o P is a term (also called prop, the type of all propositions);
o Variables (x, y, ...) are terms;
o If A and B are terms, then so is (A B);
o If A and B are terms and x is a variable, then the following are also terms:
  o (λx : A. B)
  o (∀x : A. B)

In other words, the term syntax, in Backus-Naur form, is then:
  e ::= T | P | x | e e | λx: e. e | ∀x: e. e

             ***********Stop quoting Wikipedia************

I can match a lot of that description up with Lean syntax, but not everything.
-/

/-
  Lean has a hierarchy of universes, which they refer to as both Sorts (with indexes)
  and Types (with indexes one smaller).
  (https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/universes.html?highlight=Sort#prop-and-polymorphism)

  The bottom of the hierarchy is Prop = Sort 0, which is the universe containing
  propositions, which are those terms that could take on the values true or
  false. "Prop" itself is a term and it belongs to the universe Type 0 = Sort 1.
  In the 5 statements below, each term belongs to the universe mentioned in the
  next statement.
-/

#check 1 + 1 = 2
#check Prop
#check Type
#check Type 1
#check Type 2


/-
  Note that strings like "1" and "+" and "=" are not really fundamental parts
  of Lean's grammar, although they be handled specially for efficiency. "1" is
  treated as a special notation for a natural number constructor Nat.succ
  applied to another natural number constructor Nat.zero.

  Constructors are just functions and function application in Lean is just
  juxtaposition "f x" like it is in the Calculus of Constructions grammar above "e e"
  so that is what we use below.
-/

#eval Nat.succ Nat.zero

/-
  "+" seems to be an overloaded notation, but when applied to two natural numbers
  it should result in the application of Nat.add. The parentheses below are necessary
  to cause Nat.succ to be applied before Nat.add.
-/

#eval Nat.add (Nat.succ Nat.zero) (Nat.succ Nat.zero)

/-
  And "=" is notation that stands for creating a term of type Prop, which is the proposition
  that its first and second arguments are equal. Evaluating that term can yield the values
  true or false.
-/

#eval Eq (Nat.add (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))

/-
  Like the Calculus of Constructions, Lean supports both abstraction and quantification.
  To cover abstraction first, by writing "fun" or "λ" in front of a term, you define
  a new term that is a function that may be applied to an argument term. The type
  declarations "Nat" are not necessary here, but I'm leaving them in to match the
  Calculus of Constructions syntax (λx : A. B).
-/

#eval (fun (x : Nat) => x + 1) 3
#eval (λ (x : Nat) => x + 2) 3

/-
  You can write functions with multiple arguments, but they are treated just like multiple
  single-argument functions. This process is known as "currying".
-/

#eval (fun (x : Nat) => fun (y : Nat) => x + y) 1 1 = (fun (x y : Nat) => x + y) 1 1

/-
  Quantification with ∀ lets you define new propositions with variables in them.
  Existential quantification is not builtin. It uses a type named Exists that is
  defined in Lean itself.
-/

#check ∀ (x : Nat), x >= 0


/-
             ***********Start quoting Wikipedia************
The calculus of constructions allows proving typing judgements:

    x₁ : A₁, x₂ : A₂, ... ⊢ t : B,

which can be read as the implication

    If the variables x₁, x₂, ... have, respectively, types A₁, A₂, ..., then
    term t has type B.

The valid judgments for the calculus of constructions are derivable from a set
of inference rules. In the following we use Γ to mean a sequence of type assignments
x₁ : A₁, x₂ : A₂, ...; A, B, C, D to mean terms; and K, L to mean either P (propositions)
or T (all types). We shall write B[x := N] to mean the result of substituting the term
N for the free variable x in the term B.

An inference rule is written in the form

    Γ ⊢ A : B
  --------------
   Γ' ⊢ C : D

which means

    If Γ ⊢ A : B is a valid judgement, then so is Γ' ⊢ C : D
             ***********Stop quoting Wikipedia************

I'm used to hearing the Γs referred to as "type environments" because they contain
pairs of terms and their types. And you might read the sentence above as

    If A has type B in type environment Γ, then C had type D in type environment Γ'

Let's see if we can find some Lean analogs for the inference rules of the
calculus of constructions as given in Wikipedia.
-/

/-
  1.            -----------
                 Γ ⊢ P : T

This says that the type of propositions Prop has type Type in any type environment.
It's an axiom because there are no preconditions. The following command prints
Prop : Type.
-/

#check Prop

/-
  2.          ----------------------
               Γ, x : A, Γ' ⊢ x : A

This is another axiom that says that a type environment that contains x : A, then
in fact x : A is entailed. In the calculus of constructions, x is a variable that
can be either a term or a type. This is also true in Lean and we can introduce
variables into the current environment with variable declarations. Then we can
use #check to see that they have there declared types.
-/

variable (x : Nat)
variable (α : Type)

#check x
#check α

/-
  3.        Γ ⊢ A : K        Γ, x : A ⊢ B : L
           ------------------------------------
                 Γ ⊢ (∀ x : A. B): L

This rule governs when you can introduce a universal quantifier. It says that if
A is a type (entailed by Γ) and extending Γ with the fact that x has type A would
entail that B has type L, then you can conclude that for all x of type A, B is
of type L. Basically, because you can conclude B : L knowing nothing but the type
of x, you can go ahead and conclude ∀ x : A, B : L.
-/

-- This is a proof of a simple proposition by tactics. We start out knowing Nat : Type
-- in the current environment.
theorem nat_not_negative : ∀ (n : Nat), n = n := by
  -- This introduces the hypothesis n : Nat in the local environment of the proof.
  intro n
  -- This draws the conclusion that n = n is true, which suffices to satisfy the
  -- universally quantified goal.
  apply Eq.refl n


/-
  4.       Γ ⊢ A : K        Γ, x : A ⊢ N : B
          ------------------------------------
            Γ ⊢ (λ x : A. N) : (∀ x : A. B)

This rule governs when you can abstract over an expression (i.e. when you can introduce
a λ). It's not so interesting unless x appears in the term N, but when x does appear
in N, it is similar to the last rule because it says that if you can conclude N : B
while knowing only that x has type A, then you can abstract over that expression N,
capturing x as the argument to a function. And you know that the new function you've
created has type (∀ x : A. B), which is commonly written as A → B.
-/

-- Lean doesn't mind us redeclaring this variable.
variable (x : Nat)
-- In this environment where x : Nat, x + 1 also has type Nat.
#check x + 1
-- And λ (x : Nat) => x + 1 has type Nat -> Nat.
#check fun (x : Nat) => x + 1

/-
  5.        Γ ⊢ M : (∀ x : A. B)       Γ ⊢ N : A
           ---------------------------------------
                    Γ ⊢ M N : B[x := N]

This rule governs function application. If we know the type of the function M, which could
also be written A → B and know that N : A, then we can conclude that the expression M N
has type B after substituting N for every free occurence of x in B. Note that if you talk
about application in the lambda calculus, you normally consider substitution in the body
of the function M, but here we're only concerned with the resulting type of M N, which is
B after substitution.
-/

-- Here we have a polymorphic function whose result type is List α
def mk_list (α : Type) (a : α) : List α := [a, a, a]
-- When we apply it to a natural number, the result type is known to be List Nat.
#check mk_list Nat 3


/-
  6.        Γ ⊢ M : A      A =_β B      Γ ⊢ B : K
           --------------------------------------------
                       Γ ⊢ M : B

I believe that this rule gives a notion of type equivalence after beta reduction.
Beta reduction is a formal way to evaluate (maybe only partially evaluate) terms
in the lambda calculus. Since types in the Calculus of Constructions can contain
arbitrary terms, I think this is saying that you can conclude M : B if you know
that M : A and B is a type and A and B beta reduce to the same type.
-/

-- I'm not sure how to illustrate this one in Lean yet.
