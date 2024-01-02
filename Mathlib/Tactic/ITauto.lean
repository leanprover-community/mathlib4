/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Tactic.Hint

#align_import tactic.itauto from "leanprover-community/mathlib"@"dff8393cf1d1fc152d148e13fe57452fc37d4852"

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well known
`G4ip` algorithm:
[Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*][dyckhoff_1992].

All built in propositional connectives are supported: `true`, `false`, `and`, `or`, `implies`,
`not`, `iff`, `xor`, as well as `eq` and `ne` on propositions. Anything else, including definitions
and predicate logical connectives (`forall` and `exists`), are not supported, and will have to be
simplified or instantiated before calling this tactic.

The resulting proofs will never use any axioms except possibly `propext`, and `propext` is only
used if the input formula contains an equality of propositions `p = q`.

## Implementation notes

The core logic of the prover is in three functions:

* `prove : context → prop → state_t ℕ option proof`: The main entry point.
  Gets a context and a goal, and returns a `proof` object or fails, using `state_t ℕ` for the name
  generator.
* `search : context → prop → state_t ℕ option proof`: Same meaning as `proof`, called during the
  search phase (see below).
* `context.add : prop → proof → context → except (prop → proof) context`: Adds a proposition with
  its proof into the context, but it also does some simplifications on the spot while doing so.
  It will either return the new context, or if it happens to notice a proof of false, it will
  return a function to compute a proof of any proposition in the original context.

The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`.
  * `context.add`:
    * simplify `Γ, ⊤ ⊢ B` to `Γ ⊢ B`
    * `Γ, ⊥ ⊢ B` is true
    * simplify `Γ, A ∧ B ⊢ C` to `Γ, A, B ⊢ C`
    * simplify `Γ, ⊥ → A ⊢ B` to `Γ ⊢ B`
    * simplify `Γ, ⊤ → A ⊢ B` to `Γ, A ⊢ B`
    * simplify `Γ, A ∧ B → C ⊢ D` to `Γ, A → B → C ⊢ D`
    * simplify `Γ, A ∨ B → C ⊢ D` to `Γ, A → C, B → C ⊢ D`
  * `prove`:
    * `Γ ⊢ ⊤` is true
    * simplify `Γ ⊢ A → B` to `Γ, A ⊢ B`
  * `search`:
    * `Γ, P ⊢ P` is true
    * simplify `Γ, P, P → A ⊢ B` to `Γ, P, A ⊢ B`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
  * simplify `Γ ⊢ A ∧ B` to `Γ ⊢ A` and `Γ ⊢ B`
  * simplify `Γ, A ∨ B ⊢ C` to `Γ, A ⊢ C` and `Γ, B ⊢ C`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ A`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ B`
  * `Γ, (A₁ → A₂) → C ⊢ B` follows from `Γ, A₂ → C, A₁ ⊢ A₂` and `Γ, C ⊢ B`

This covers the core algorithm, which only handles `true`, `false`, `and`, `or`, and `implies`.
For `iff` and `eq`, we treat them essentially the same as `(p → q) ∧ (q → p)`, although we use
a different `prop` representation because we have to remember to apply different theorems during
replay. For definitions like `not` and `xor`, we just eagerly unfold them. (This could potentially
cause a blowup issue for `xor`, but it isn't used very often anyway. We could add it to the `prop`
grammar if it matters.)

## Tags

propositional logic, intuitionistic logic, decision procedure
-/


namespace Tactic

namespace Itauto

/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/
inductive AndKind
  | And
  | Iff
  | Eq
  deriving has_reflect, DecidableEq
#align tactic.itauto.and_kind Tactic.Itauto.AndKind

instance : Inhabited AndKind :=
  ⟨AndKind.and⟩

/-- A reified inductive type for propositional logic. -/
inductive Prop : Type
  | var : ℕ → prop-- propositional atoms P_i

  | True : prop-- ⊤

  | False : prop-- ⊥

  | and' : AndKind → prop → prop → prop-- p ∧ q, p ↔ q, p = q

  | Or : prop → prop → prop-- p ∨ q

  | imp : prop → prop → prop
  deriving has_reflect, DecidableEq
#align tactic.itauto.prop Tactic.Itauto.Prop

-- p → q
/-- Constructor for `p ∧ q`. -/
@[match_pattern]
def Prop.and : Prop → Prop → Prop :=
  Prop.and' AndKind.and
#align tactic.itauto.prop.and Tactic.Itauto.Prop.and

/-- Constructor for `p ↔ q`. -/
@[match_pattern]
def Prop.iff : Prop → Prop → Prop :=
  Prop.and' AndKind.iff
#align tactic.itauto.prop.iff Tactic.Itauto.Prop.iff

/-- Constructor for `p = q`. -/
@[match_pattern]
def Prop.eq : Prop → Prop → Prop :=
  Prop.and' AndKind.eq
#align tactic.itauto.prop.eq Tactic.Itauto.Prop.eq

/-- Constructor for `¬ p`. -/
@[match_pattern]
def Prop.not (a : Prop) : Prop :=
  a.imp Prop.false
#align tactic.itauto.prop.not Tactic.Itauto.Prop.not

/-- Constructor for `xor p q`. -/
@[match_pattern]
def Prop.xor (a b : Prop) : Prop :=
  (a.And b.Not).Or (b.And a.Not)
#align tactic.itauto.prop.xor Tactic.Itauto.Prop.xor

instance : Inhabited Prop :=
  ⟨Prop.true⟩

/-- Given the contents of an `and` variant, return the two conjuncts. -/
def AndKind.sides : AndKind → Prop → Prop → Prop × Prop
  | and_kind.and, A, B => (A, B)
  | _, A, B => (A.imp B, B.imp A)
#align tactic.itauto.and_kind.sides Tactic.Itauto.AndKind.sides

/-- Debugging printer for propositions. -/
unsafe def prop.to_format : Prop → format
  | prop.var i => f! "v{i}"
  | prop.true => f!"⊤"
  | prop.false => f!"⊥"
  | prop.and p q => f! "({p.to_format } ∧ {q.to_format})"
  | prop.iff p q => f! "({p.to_format } ↔ {q.to_format})"
  | prop.eq p q => f! "({p.to_format } = {q.to_format})"
  | prop.or p q => f! "({p.to_format } ∨ {q.to_format})"
  | prop.imp p q => f! "({p.to_format } → {q.to_format})"
#align tactic.itauto.prop.to_format tactic.itauto.prop.to_format

unsafe instance : has_to_format Prop :=
  ⟨prop.to_format⟩

section

open Ordering

/-- A comparator for `and_kind`. (There should really be a derive handler for this.) -/
def AndKind.cmp (p q : AndKind) : Ordering := by cases p <;> cases q;
  exacts [Eq, lt, lt, GT.gt, Eq, lt, GT.gt, GT.gt, Eq]
#align tactic.itauto.and_kind.cmp Tactic.Itauto.AndKind.cmp

/-- A comparator for propositions. (There should really be a derive handler for this.) -/
def Prop.cmp (p q : Prop) : Ordering :=
  by
  induction' p with _ ap _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ generalizing q <;> cases q
  case var.var => exact cmp p q
  case true.true => exact Eq
  case false.false => exact Eq
  case and'.and' aq q₁ q₂ => exact (ap.cmp aq).orElse ((p₁ q₁).orElse (p₂ q₂))
  case or.or q₁ q₂ => exact (p₁ q₁).orElse (p₂ q₂)
  case imp.imp q₁ q₂ => exact (p₁ q₁).orElse (p₂ q₂)
  exacts [lt, lt, lt, lt, lt, GT.gt, lt, lt, lt, lt, GT.gt, GT.gt, lt, lt, lt, GT.gt, GT.gt, GT.gt,
    lt, lt, GT.gt, GT.gt, GT.gt, GT.gt, lt, GT.gt, GT.gt, GT.gt, GT.gt, GT.gt]
#align tactic.itauto.prop.cmp Tactic.Itauto.Prop.cmp

instance : LT Prop :=
  ⟨fun p q => p.cmp q = lt⟩

instance : DecidableRel (@LT.lt Prop _) := fun _ _ => Ordering.decidableEq _ _

end

/-- A reified inductive proof type for intuitionistic propositional logic. -/
inductive Proof-- ⊢ A, causes failure during reconstruction

  | sorry : proof-- (n: A) ⊢ A

  | hyp (n : Name) : proof-- ⊢ ⊤

  | triv : proof-- (p: ⊥) ⊢ A

  | exfalso' (p : proof) : proof-- (p: (x: A) ⊢ B) ⊢ A → B

  | intro (x : Name) (p : proof) : proof-- ak = and:  (p: A ∧ B) ⊢ A
-- ak = iff:  (p: A ↔ B) ⊢ A → B
-- ak = eq:  (p: A = B) ⊢ A → B

  | and_left (ak : AndKind) (p : proof) : proof-- ak = and:  (p: A ∧ B) ⊢ B
-- ak = iff:  (p: A ↔ B) ⊢ B → A
-- ak = eq:  (p: A = B) ⊢ B → A

  | and_right (ak : AndKind) (p : proof) : proof-- ak = and:  (p₁: A) (p₂: B) ⊢ A ∧ B
-- ak = iff:  (p₁: A → B) (p₁: B → A) ⊢ A ↔ B
-- ak = eq:  (p₁: A → B) (p₁: B → A) ⊢ A = B

  | and_intro (ak : AndKind) (p₁ p₂ : proof) : proof-- ak = and:  (p: A ∧ B → C) ⊢ A → B → C
-- ak = iff:  (p: (A ↔ B) → C) ⊢ (A → B) → (B → A) → C
-- ak = eq:  (p: (A = B) → C) ⊢ (A → B) → (B → A) → C

  | curry (ak : AndKind) (p : proof) : proof-- This is a partial application of curry.
-- ak = and:  (p: A ∧ B → C) (q : A) ⊢ B → C
-- ak = iff:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C
-- ak = eq:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C

  | curry₂ (ak : AndKind) (p q : proof) : proof-- (p: A → B) (q: A) ⊢ B

  | app' : proof → proof → proof-- (p: A ∨ B → C) ⊢ A → C

  | or_imp_left (p : proof) : proof-- (p: A ∨ B → C) ⊢ B → C

  | or_imp_right (p : proof) : proof-- (p: A) ⊢ A ∨ B

  | or_inl (p : proof) : proof-- (p: B) ⊢ A ∨ B

  | or_inr (p : proof) : proof-- (p: B) ⊢ A ∨ B
-- (p₁: A ∨ B) (p₂: (x: A) ⊢ C) (p₃: (x: B) ⊢ C) ⊢ C

  |
  or_elim' (p₁ : proof) (x : Name) (p₂ p₃ : proof) :
    proof-- (p₁: decidable A) (p₂: (x: A) ⊢ C) (p₃: (x: ¬ A) ⊢ C) ⊢ C

  |
  decidable_elim (classical : Bool) (p₁ x : Name) (p₂ p₃ : proof) :
    proof-- classical = ff: (p: decidable A) ⊢ A ∨ ¬A
-- classical = tt: (p: Prop) ⊢ p ∨ ¬p

  |
  em (classical : Bool) (p : Name) :
    proof-- The variable x here names the variable that will be used in the elaborated proof
-- (p: ((x:A) → B) → C) ⊢ B → C

  | imp_imp_simp (x : Name) (p : proof) : proof
  deriving has_reflect
#align tactic.itauto.proof Tactic.Itauto.Proof

instance : Inhabited Proof :=
  ⟨Proof.triv⟩

/-- Debugging printer for proof objects. -/
unsafe def proof.to_format : Proof → format
  | proof.sorry => "sorry"
  | proof.hyp i => to_fmt i
  | proof.triv => "triv"
  | proof.exfalso' p => f! "(exfalso {p.to_format})"
  | proof.intro x p => f! "(λ {x }, {p.to_format})"
  | proof.and_left _ p => f! "{p.to_format} .1"
  | proof.and_right _ p => f! "{p.to_format} .2"
  | proof.and_intro _ p q => f! "⟨{p.to_format }, {q.to_format}⟩"
  | proof.curry _ p => f! "(curry {p.to_format})"
  | proof.curry₂ _ p q => f! "(curry {p.to_format } {q.to_format})"
  | proof.app' p q => f! "({p.to_format } {q.to_format})"
  | proof.or_imp_left p => f! "(or_imp_left {p.to_format})"
  | proof.or_imp_right p => f! "(or_imp_right {p.to_format})"
  | proof.or_inl p => f! "(or.inl {p.to_format})"
  | proof.or_inr p => f! "(or.inr {p.to_format})"
  | proof.or_elim' p x q r =>
    f! "({p.to_format }.elim (λ {x }, {q.to_format }) (λ {x }, {r.to_format})"
  | proof.em ff p => f! "(decidable.em {p})"
  | proof.em tt p => f! "(classical.em {p})"
  | proof.decidable_elim _ p x q r =>
    f! "({p }.elim (λ {x }, {q.to_format }) (λ {x }, {r.to_format})"
  | proof.imp_imp_simp _ p => f! "(imp_imp_simp {p.to_format})"
#align tactic.itauto.proof.to_format tactic.itauto.proof.to_format

unsafe instance : has_to_format Proof :=
  ⟨proof.to_format⟩

/-- A variant on `proof.exfalso'` that performs opportunistic simplification. -/
unsafe def proof.exfalso : Prop → Proof → Proof
  | prop.false, p => p
  | A, p => Proof.exfalso' p
#align tactic.itauto.proof.exfalso tactic.itauto.proof.exfalso

/-- A variant on `proof.or_elim` that performs opportunistic simplification. -/
unsafe def proof.or_elim : Proof → Name → Proof → Proof → Proof
  | proof.em cl p, x, q, r => Proof.decidable_elim cl p x q r
  | p, x, q, r => Proof.or_elim' p x q r
#align tactic.itauto.proof.or_elim tactic.itauto.proof.or_elim

/-- A variant on `proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
unsafe def proof.app : Proof → Proof → Proof
  | proof.curry ak p, q => Proof.curry₂ ak p q
  | proof.curry₂ ak p q, r => p.app (q.and_intro ak r)
  | proof.or_imp_left p, q => p.app q.or_inl
  | proof.or_imp_right p, q => p.app q.or_inr
  | proof.imp_imp_simp x p, q => p.app (Proof.intro x q)
  | p, q => p.app' q
#align tactic.itauto.proof.app tactic.itauto.proof.app

-- Note(Mario): the typechecker is disabled because it requires proofs to carry around additional
-- props. These can be retrieved from the git history if you want to re-enable this.
/-
/-- A typechecker for the `proof` type. This is not used by the tactic but can be used for
debugging. -/
meta def proof.check : name_map prop → proof → option prop
| Γ (proof.hyp i) := Γ.find i
| Γ proof.triv := some prop.true
| Γ (proof.exfalso' A p) := guard (p.check Γ = some prop.false) $> A
| Γ (proof.intro x A p) := do B ← p.check (Γ.insert x A), pure (prop.imp A B)
| Γ (proof.and_left ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).1
| Γ (proof.and_right ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).2
| Γ (proof.and_intro and_kind.and p q) := do
  A ← p.check Γ, B ← q.check Γ,
  pure (A.and B)
| Γ (proof.and_intro ak p q) := do
  prop.imp A B ← p.check Γ | none,
  C ← q.check Γ, guard (C = prop.imp B A) $> (A.and' ak B)
| Γ (proof.curry ak p) := do
  prop.imp (prop.and' ak' A B) C ← p.check Γ | none,
  let (A', B') := ak.sides A B,
  guard (ak = ak') $> (A'.imp $ B'.imp C)
| Γ (proof.curry₂ ak p q) := do
  prop.imp (prop.and' ak' A B) C ← p.check Γ | none,
  A₂ ← q.check Γ,
  let (A', B') := ak.sides A B,
  guard (ak = ak' ∧ A₂ = A') $> (B'.imp C)
| Γ (proof.app' p q) := do prop.imp A B ← p.check Γ | none, A' ← q.check Γ, guard (A = A') $> B
| Γ (proof.or_imp_left B p) := do
  prop.imp (prop.or A B') C ← p.check Γ | none,
  guard (B = B') $> (A.imp C)
| Γ (proof.or_imp_right A p) := do
  prop.imp (prop.or A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
| Γ (proof.or_inl B p) := do A ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_inr A p) := do B ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_elim p x q r) := do
  prop.or A B ← p.check Γ | none,
  C ← q.check (Γ.insert x A),
  C' ← r.check (Γ.insert x B),
  guard (C = C') $> C
| Γ (proof.imp_imp_simp x A p) := do
  prop.imp (prop.imp A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
-/
/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline]
unsafe def fresh_name : ℕ → Name × ℕ := fun n => (mkSimpleName ("h" ++ toString n), n + 1)
#align tactic.itauto.fresh_name tactic.itauto.fresh_name

/-- The context during proof search is a map from propositions to proof values. -/
unsafe def context :=
  native.rb_map Prop Proof
#align tactic.itauto.context tactic.itauto.context

/-- Debug printer for the context. -/
unsafe def context.to_format (Γ : context) : format :=
  Γ.fold "" fun P p f =>
    -- ++ " := " ++ p.to_format
          P.to_format ++
        ",\n" ++
      f
#align tactic.itauto.context.to_format tactic.itauto.context.to_format

unsafe instance : has_to_format context :=
  ⟨context.to_format⟩

/-- Insert a proposition and its proof into the context, as in `have : A := p`. This will eagerly
apply all level 1 rules on the spot, which are rules that don't split the goal and are validity
preserving: specifically, we drop `⊤` and `A → ⊤` hypotheses, close the goal if we find a `⊥`
hypothesis, split all conjunctions, and also simplify `⊥ → A` (drop), `⊤ → A` (simplify to `A`),
`A ∧ B → C` (curry to `A → B → C`) and `A ∨ B → C` (rewrite to `(A → C) ∧ (B → C)` and split). -/
unsafe def context.add : Prop → Proof → context → Except (Prop → Proof) context
  | prop.true, p, Γ => pure Γ
  | prop.false, p, Γ => Except.error fun A => proof.exfalso A p
  | prop.and' ak A B, p, Γ => do
    let (A, B) := ak.sides A B
    let Γ ← Γ.add A (p.and_left ak)
    Γ B (p ak)
  | prop.imp prop.false A, p, Γ => pure Γ
  | prop.imp prop.true A, p, Γ => Γ.add A (p.app Proof.triv)
  | prop.imp (prop.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (Prop.imp A (B.imp C)) (p.curry ak)
  | prop.imp (prop.or A B) C, p, Γ => do
    let Γ ← Γ.add (A.imp C) p.or_imp_left
    Γ (B C) p
  | prop.imp A prop.true, p, Γ => pure Γ
  | A, p, Γ => pure (Γ.insert A p)
#align tactic.itauto.context.add tactic.itauto.context.add

/-- Add `A` to the context `Γ` with proof `p`. This version of `context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline]
unsafe def context.with_add (Γ : context) (A : Prop) (p : Proof) (B : Prop)
    (f : context → Prop → ℕ → Bool × Proof × ℕ) (n : ℕ) : Bool × Proof × ℕ :=
  match Γ.add A p with
  | Except.ok Γ_A => f Γ_A B n
  | Except.error p => (true, p B, n)
#align tactic.itauto.context.with_add tactic.itauto.context.with_add

/-- Map a function over the proof (regardless of whether the proof is successful or not). -/
def mapProof (f : Proof → Proof) : Bool × Proof × ℕ → Bool × Proof × ℕ
  | (b, p, n) => (b, f p, n)
#align tactic.itauto.map_proof Tactic.Itauto.mapProof

/-- Convert a value-with-success to an optional value. -/
def isOk {α} : Bool × α → Option α
  | (ff, p) => none
  | (tt, p) => some p
#align tactic.itauto.is_ok Tactic.Itauto.isOk

/-- Skip the continuation and return a failed proof if the boolean is false. -/
def whenOk : Bool → (ℕ → Bool × Proof × ℕ) → ℕ → Bool × Proof × ℕ
  | ff, f, n => (false, Proof.sorry, n)
  | tt, f, n => f n
#align tactic.itauto.when_ok Tactic.Itauto.whenOk

/-- The search phase, which deals with the level 3 rules, which are rules that are not validity
preserving and so require proof search. One obvious one is the or-introduction rule: we prove
`A ∨ B` by proving `A` or `B`, and we might have to try one and backtrack.

There are two rules dealing with implication in this category: `p, p → C ⊢ B` where `p` is an
atom (which is safe if we can find it but often requires the right search to expose the `p`
assumption), and `(A₁ → A₂) → C ⊢ B`. We decompose the double implication into two subgoals: one to
prove `A₁ → A₂`, which can be written `A₂ → C, A₁ ⊢ A₂` (where we used `A₁` to simplify
`(A₁ → A₂) → C`), and one to use the consequent, `C ⊢ B`. The search here is that there are
potentially many implications to split like this, and we have to try all of them if we want to be
complete. -/
unsafe def search (prove : context → Prop → ℕ → Bool × Proof × ℕ) :
    context → Prop → ℕ → Bool × Proof × ℕ
  | Γ, B, n =>
    match Γ.find B with
    | some p => (true, p, n)
    | none =>
      let search₁ :=
        Γ.fold none fun A p r =>
          match r with
          | some r => some r
          | none =>
            match A with
            | prop.imp A' C =>
              match Γ.find A' with
              | some q => isOk <| context.with_add (Γ.eraseₓ A) C (p.app q) B prove n
              | none =>
                match A' with
                | prop.imp A₁ A₂ => do
                  let Γ : context := Γ.eraseₓ A
                  let (a, n) := fresh_name n
                  let (p₁, n) ←
                    isOk <|
                        Γ.with_add A₁ (Proof.hyp a) A₂
                          (fun Γ_A₁ A₂ =>
                            Γ_A₁.with_add (Prop.imp A₂ C) (Proof.imp_imp_simp a p) A₂ prove)
                          n
                  is_ok <| Γ C (p (proof.intro a p₁)) B prove n
                | _ => none
            | _ => none
      match search₁ with
      | some r => (true, r)
      | none =>
        match B with
        | prop.or B₁ B₂ =>
          match mapProof Proof.or_inl (prove Γ B₁ n) with
          | (ff, _) => mapProof Proof.or_inr (prove Γ B₂ n)
          | r => r
        | _ => (false, Proof.sorry, n)
#align tactic.itauto.search tactic.itauto.search

/-- The main prover. This receives a context of proven or assumed lemmas and a target proposition,
and returns a proof or `none` (with state for the fresh variable generator).
The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`

The level 1 rules on the right of the turnstile are `Γ ⊢ ⊤` and `Γ ⊢ A → B`, these are easy to
handle. The rule `Γ ⊢ A ∧ B` is a level 2 rule, also handled here. If none of these apply, we try
the level 2 rule `A ∨ B ⊢ C` by searching the context and splitting all ors we find. Finally, if
we don't make any more progress, we go to the search phase.
-/
unsafe def prove : context → Prop → ℕ → Bool × Proof × ℕ
  | Γ, prop.true, n => (true, Proof.triv, n)
  | Γ, prop.imp A B, n =>
    let (a, n) := fresh_name n
    mapProof (Proof.intro a) <| Γ.with_add A (Proof.hyp a) B prove n
  | Γ, prop.and' ak A B, n =>
    let (A, B) := ak.sides A B
    let (b, p, n) := prove Γ A n
    mapProof (p.and_intro ak) <| whenOk b (prove Γ B) n
  | Γ, B, n =>
    Γ.fold (fun b Γ => cond b prove (search prove) Γ B)
      (fun A p IH b Γ n =>
        match A with
        | prop.or A₁ A₂ =>
          let Γ : context := Γ.eraseₓ A
          let (a, n) := fresh_name n
          let (b, p₁, n) := Γ.with_add A₁ (Proof.hyp a) B (fun Γ _ => IH true Γ) n
          mapProof (proof.or_elim p a p₁) <|
            whenOk b (Γ.with_add A₂ (Proof.hyp a) B fun Γ _ => IH true Γ) n
        | _ => IH b Γ n)
      false Γ n
#align tactic.itauto.prove tactic.itauto.prove

/-- Reifies an atomic or otherwise unrecognized proposition. If it is defeq to a proposition we
have already allocated, we reuse it, otherwise we name it with a new index. -/
unsafe def reify_atom (atoms : ref (Buffer expr)) (e : expr) : tactic Prop := do
  let vec ← read_ref atoms
  let o ← try_core <| vec.iterate failure fun i e' r => r <|> is_def_eq e e' >> pure i.1
  match o with
    | none => write_ref atoms (vec e) $> prop.var vec
    | some i => pure <| prop.var i
#align tactic.itauto.reify_atom tactic.itauto.reify_atom

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Reify an `expr` into a `prop`, allocating anything non-propositional as an atom in the
      `atoms` list. -/
    unsafe
  def
    reify
    ( atoms : ref ( Buffer expr ) ) : expr → tactic Prop
    | q( True ) => pure Prop.true
      | q( False ) => pure Prop.false
      | q( ¬ $ ( a ) ) => Prop.not <$> reify a
      | q( $ ( a ) ∧ $ ( b ) ) => Prop.and <$> reify a <*> reify b
      | q( $ ( a ) ∨ $ ( b ) ) => Prop.or <$> reify a <*> reify b
      | q( $ ( a ) ↔ $ ( b ) ) => Prop.iff <$> reify a <*> reify b
      | q( Xor' $ ( a ) $ ( b ) ) => Prop.xor <$> reify a <*> reify b
      | q( @ Eq Prop $ ( a ) $ ( b ) ) => Prop.eq <$> reify a <*> reify b
      | q( @ Ne Prop $ ( a ) $ ( b ) ) => Prop.not <$> ( Prop.eq <$> reify a <*> reify b )
      | q( Implies $ ( a ) $ ( b ) ) => Prop.imp <$> reify a <*> reify b
      |
        e @ q( $ ( a ) → $ ( b ) )
        =>
        if b . has_var then reify_atom atoms e else Prop.imp <$> reify a <*> reify b
      | e => reify_atom atoms e
#align tactic.itauto.reify tactic.itauto.reify

/-- Once we have a proof object, we have to apply it to the goal. (Some of these cases are a bit
annoying because `applyc` gets the arguments wrong sometimes so we have to use `to_expr` instead.)
-/
unsafe def apply_proof : name_map expr → Proof → tactic Unit
  | Γ, proof.sorry => fail "itauto failed"
  | Γ, proof.hyp n => do
    let e ← Γ.find n
    exact e
  | Γ, proof.triv => triv
  | Γ, proof.exfalso' p => do
    let t ← mk_mvar
    to_expr ``(False.elim $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.intro x p => do
    let e ← intro_core x
    apply_proof (Γ x e) p
  | Γ, proof.and_left and_kind.and p => do
    let t ← mk_mvar
    to_expr ``(And.left $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_left and_kind.iff p => do
    let t ← mk_mvar
    to_expr ``(Iff.mp $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_left and_kind.eq p => do
    let t ← mk_mvar
    to_expr ``(cast $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_right and_kind.and p => do
    let t ← mk_mvar
    to_expr ``(And.right $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_right and_kind.iff p => do
    let t ← mk_mvar
    to_expr ``(Iff.mpr $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_right and_kind.eq p => do
    let t ← mk_mvar
    to_expr ``(cast (Eq.symm $(t))) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.and_intro and_kind.and p q => do
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    to_expr ``(And.intro $(t₁) $(t₂)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
  | Γ, proof.and_intro and_kind.iff p q => do
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    to_expr ``(Iff.intro $(t₁) $(t₂)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
  | Γ, proof.and_intro and_kind.eq p q => do
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    to_expr ``(propext (Iff.intro $(t₁) $(t₂))) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
  | Γ, proof.curry ak p => do
    let e ← intro_core `_
    let n := e.local_uniq_name
    apply_proof (Γ n e) (proof.curry₂ ak p (proof.hyp n))
  | Γ, proof.curry₂ ak p q => do
    let e ← intro_core `_
    let n := e.local_uniq_name
    apply_proof (Γ n e) (p (q ak (proof.hyp n)))
  | Γ, proof.app' p q => do
    let A ← mk_meta_var (expr.sort level.zero)
    let B ← mk_meta_var (expr.sort level.zero)
    let g₁ ← mk_meta_var q(($(A) : Prop) → ($(B) : Prop))
    let g₂ ← mk_meta_var A
    let g :: gs ← get_goals
    unify (g₁ g₂) g
    (set_goals (g₁ :: g₂ :: gs) >> apply_proof Γ p) >> apply_proof Γ q
  | Γ, proof.or_imp_left p => do
    let e ← intro_core `_
    let n := e.local_uniq_name
    apply_proof (Γ n e) (p (proof.hyp n).or_inl)
  | Γ, proof.or_imp_right p => do
    let e ← intro_core `_
    let n := e.local_uniq_name
    apply_proof (Γ n e) (p (proof.hyp n).or_inr)
  | Γ, proof.or_inl p => do
    let t ← mk_mvar
    to_expr ``(Or.inl $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.or_inr p => do
    let t ← mk_mvar
    to_expr ``(Or.inr $(t)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t :: gs)
    apply_proof Γ p
  | Γ, proof.or_elim' p x p₁ p₂ => do
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    let t₃ ← mk_mvar
    to_expr ``(Or.elim $(t₁) $(t₂) $(t₃)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: t₃ :: gs)
    apply_proof Γ p
    let e ← intro_core x
    apply_proof (Γ x e) p₁
    let e ← intro_core x
    apply_proof (Γ x e) p₂
  | Γ, proof.em ff n => do
    let e ← Γ.find n
    to_expr ``(@Decidable.em _ $(e)) >>= exact
  | Γ, proof.em tt n => do
    let e ← Γ.find n
    to_expr ``(@Classical.em $(e)) >>= exact
  | Γ, proof.decidable_elim ff n x p₁ p₂ => do
    let e ← Γ.find n
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    to_expr ``(@dite _ _ $(e) $(t₁) $(t₂)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: gs)
    let e ← intro_core x
    apply_proof (Γ x e) p₁
    let e ← intro_core x
    apply_proof (Γ x e) p₂
  | Γ, proof.decidable_elim tt n x p₁ p₂ => do
    let e ← Γ.find n
    let e ← to_expr ``(@Classical.dec $(e))
    let t₁ ← mk_mvar
    let t₂ ← mk_mvar
    to_expr ``(@dite _ _ $(e) $(t₁) $(t₂)) tt ff >>= exact
    let gs ← get_goals
    set_goals (t₁ :: t₂ :: gs)
    let e ← intro_core x
    apply_proof (Γ x e) p₁
    let e ← intro_core x
    apply_proof (Γ x e) p₂
  | Γ, proof.imp_imp_simp x p => do
    let e ← intro_core `_
    let n := e.local_uniq_name
    apply_proof (Γ n e) (p (proof.intro x (proof.hyp n)))
#align tactic.itauto.apply_proof tactic.itauto.apply_proof

end Itauto

open Itauto

/-- A decision procedure for intuitionistic propositional logic.

* `use_dec` will add `a ∨ ¬ a` to the context for every decidable atomic proposition `a`.
* `use_classical` will allow `a ∨ ¬ a` to be added even if the proposition is not decidable,
  using classical logic.
* `extra_dec` will add `a ∨ ¬ a` to the context for specified (not necessarily atomic)
  propositions `a`.
-/
unsafe def itauto (use_dec use_classical : Bool) (extra_dec : List expr) : tactic Unit :=
  using_new_ref mkBuffer fun atoms =>
    using_new_ref mk_name_map fun hs => do
      let t ← target
      let t ← condM (is_prop t) (reify atoms t) (tactic.exfalso $> Prop.false)
      let hyps ← local_context
      let (Γ, decs) ←
        hyps.foldlM
            (fun (Γ : Except (Prop → Proof) context × native.rb_map Prop (Bool × expr)) h => do
              let e ← infer_type h
              condM (is_prop e)
                  (do
                    let A ← reify atoms e
                    let n := h
                    read_ref hs >>= fun Γ => write_ref hs (Γ n h)
                    pure (Γ.1 >>= fun Γ' => Γ' A (proof.hyp n), Γ.2))
                  (match e with
                  | q(Decidable $(p)) =>
                    if use_dec then do
                      let A ← reify atoms p
                      let n := h
                      pure (Γ.1, Γ.2.insert A (ff, h))
                    else pure Γ
                  | _ => pure Γ))
            (Except.ok native.mk_rb_map, native.mk_rb_map)
      let add_dec (force : Bool) (decs : native.rb_map Prop (Bool × expr)) (e : expr) := do
        let A ← reify atoms e
        let dec_e ← mk_app `` Decidable [e]
        let res ← try_core (mk_instance dec_e)
        if res ∧ ¬use_classical then
            if force then do
              let m ← mk_meta_var dec_e
              (set_goals [m] >> apply_instance) >> failure
            else pure decs
          else pure (native.rb_map.insert decs A (res (tt, e) (Prod.mk ff)))
      let decs ← extra_dec.foldlM (add_dec true) decs
      let decs ←
        if use_dec then do
            let decided :=
              match Γ with
              | Except.ok Γ =>
                Γ.fold native.mk_rb_set fun p _ m =>
                  match p with
                  | prop.var i => m.insert i
                  | prop.not (prop.var i) => m.insert i
                  | _ => m
              | Except.error _ => native.mk_rb_set
            read_ref atoms >>= fun ats =>
                ats.2.iterate (pure decs) fun i e r =>
                  if decided i.1 then r else r >>= fun decs => add_dec ff decs e
          else pure decs
      let Γ ←
        decs.fold (pure Γ) fun A ⟨cl, pf⟩ r =>
            r >>= fun Γ => do
              let n ← mk_fresh_name
              read_ref hs >>= fun Γ => write_ref hs (Γ n pf)
              pure (Γ >>= fun Γ' => Γ' (A A) (proof.em cl n))
      let p :=
        match Γ with
        | Except.ok Γ => (prove Γ t 0).2.1
        | Except.error p => p t
      let hs ← read_ref hs
      apply_proof hs p
#align tactic.itauto tactic.itauto

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle (without the `!` option), and the proof search is
tailored for this use case. (`itauto!` will work as a classical SAT solver, but the algorithm is
not very good in this situation.)

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
`decidable a` and `decidable b`. `itauto *` will case on all decidable propositions that it can
find among the atomic propositions, and `itauto! *` will case on all propositional atoms.
*Warning:* This can blow up the proof search, so it should be used sparingly.
-/
unsafe def itauto (classical : parse (parser.optional (tk "!"))) :
    parse (parser.optional (some <$> pexpr_list <|> tk "*" *> pure none)) → tactic Unit
  | none => tactic.itauto False classical.isSome []
  | some none => tactic.itauto True classical.isSome []
  | some (some ls) => ls.mapM i_to_expr >>= tactic.itauto False classical.isSome
#align tactic.interactive.itauto tactic.interactive.itauto

add_hint_tactic itauto

add_tactic_doc
  { Name := "itauto"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.itauto]
    tags := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }

end Interactive

end Tactic
