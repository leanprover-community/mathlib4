/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.Hint
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Util.AtomM
import Mathlib.Init.Logic
import Mathlib.Control.Basic
import Qq

#align_import tactic.itauto from "leanprover-community/mathlib"@"dff8393cf1d1fc152d148e13fe57452fc37d4852"

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well known
`G4ip` algorithm:
[Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*][dyckhoff_1992].

All built in propositional connectives are supported: `True`, `False`, `And`, `Or`, `→`,
`Not`, `Iff`, `Xor'`, as well as `Eq` and `Ne` on propositions. Anything else, including definitions
and predicate logical connectives (`∀` and `∃`), are not supported, and will have to be
simplified or instantiated before calling this tactic.

The resulting proofs will never use any axioms except possibly `propext`, and `propext` is only
used if the input formula contains an equality of propositions `p = q`. Using `itauto!`, one can
enable the selective use of LEM for case splitting on specified propositions.

## Implementation notes

The core logic of the prover is in three functions:

* `prove : Context → IProp → StateM Nat (Bool × Proof)`: The main entry point.
  Gets a context and a goal, and returns a `proof` object or fails, using `StateM Nat` for the name
  generator.
* `search : Context → IProp → StateM Nat (Bool × Proof)`: Same meaning as `proof`, called during the
  search phase (see below).
* `Context.add : IProp → Proof → Context → Except (IProp → Proof) Context`: Adds a proposition with
  its proof into the context, but it also does some simplifications on the spot while doing so.
  It will either return the new context, or if it happens to notice a proof of false, it will
  return a function to compute a proof of any proposition in the original context.

The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `Context.add`, right rules in `prove`.
  * `Context.add`:
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

This covers the core algorithm, which only handles `True`, `False`, `And`, `Or`, and `→`.
For `Iff` and `Eq`, we treat them essentially the same as `(p → q) ∧ (q → p)`, although we use
a different `IProp` representation because we have to remember to apply different theorems during
replay. For definitions like `Not` and `Xor'`, we just eagerly unfold them. (This could potentially
cause a blowup issue for `Xor'`, but it isn't used very often anyway. We could add it to the `IProp`
grammar if it matters.)

## Tags

propositional logic, intuitionistic logic, decision procedure
-/


namespace Mathlib.Tactic.ITauto

/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/
inductive AndKind | and | iff | eq
  deriving Lean.ToExpr, DecidableEq
#align tactic.itauto.and_kind Mathlib.Tactic.ITauto.AndKind

instance : Inhabited AndKind := ⟨AndKind.and⟩

/-- A reified inductive type for propositional logic. -/
inductive IProp : Type
  | var : Nat → IProp            -- propositional atoms P_i
  | true : IProp                 -- ⊤
  | false : IProp                -- ⊥
  | and' : AndKind → IProp → IProp → IProp -- p ∧ q, p ↔ q, p = q
  | or : IProp → IProp → IProp   -- p ∨ q
  | imp : IProp → IProp → IProp  -- p → q
  deriving Lean.ToExpr, DecidableEq
#align tactic.itauto.prop Mathlib.Tactic.ITauto.IProp

/-- Constructor for `p ∧ q`. -/
@[match_pattern] def IProp.and : IProp → IProp → IProp := .and' .and
#align tactic.itauto.prop.and Mathlib.Tactic.ITauto.IProp.and

/-- Constructor for `p ↔ q`. -/
@[match_pattern] def IProp.iff : IProp → IProp → IProp := .and' .iff
#align tactic.itauto.prop.iff Mathlib.Tactic.ITauto.IProp.iff

/-- Constructor for `p = q`. -/
@[match_pattern] def IProp.eq : IProp → IProp → IProp := .and' .eq
#align tactic.itauto.prop.eq Mathlib.Tactic.ITauto.IProp.eq

/-- Constructor for `¬ p`. -/
@[match_pattern] def IProp.not (a : IProp) : IProp := a.imp .false
#align tactic.itauto.prop.not Mathlib.Tactic.ITauto.IProp.not

/-- Constructor for `xor p q`. -/
@[match_pattern] def IProp.xor (a b : IProp) : IProp := (a.and b.not).or (b.and a.not)
#align tactic.itauto.prop.xor Mathlib.Tactic.ITauto.IProp.xor

instance : Inhabited IProp := ⟨IProp.true⟩

/-- Given the contents of an `And` variant, return the two conjuncts. -/
def AndKind.sides : AndKind → IProp → IProp → IProp × IProp
  | .and, A, B => (A, B)
  | _, A, B => (A.imp B, B.imp A)
#align tactic.itauto.and_kind.sides Mathlib.Tactic.ITauto.AndKind.sides

/-- Debugging printer for propositions. -/
def IProp.format : IProp → Std.Format
  | .var i => f!"v{i}"
  | .true => f!"⊤"
  | .false => f!"⊥"
  | .and p q => f!"({p.format} ∧ {q.format})"
  | .iff p q => f!"({p.format} ↔ {q.format})"
  | .eq p q => f!"({p.format} = {q.format})"
  | .or p q => f!"({p.format} ∨ {q.format})"
  | .imp p q => f!"({p.format} → {q.format})"
#align tactic.itauto.prop.to_format Mathlib.Tactic.ITauto.IProp.format

instance : Std.ToFormat IProp := ⟨IProp.format⟩

/-- A comparator for `AndKind`. (There should really be a derive handler for this.) -/
def AndKind.cmp (p q : AndKind) : Ordering := by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]
#align tactic.itauto.and_kind.cmp Mathlib.Tactic.ITauto.AndKind.cmp

/-- A comparator for propositions. (There should really be a derive handler for this.) -/
def IProp.cmp (p q : IProp) : Ordering := by
  cases p <;> cases q
  case var.var p q => exact compare p q
  case true.true => exact .eq
  case false.false => exact .eq
  case and'.and' ap p₁ p₂ aq q₁ q₂ => exact (ap.cmp aq).then <| (p₁.cmp q₁).then (p₂.cmp q₂)
  case or.or p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  case imp.imp p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  exacts [.lt, .lt, .lt, .lt, .lt,
          .gt, .lt, .lt, .lt, .lt,
          .gt, .gt, .lt, .lt, .lt,
          .gt, .gt, .gt, .lt, .lt,
          .gt, .gt, .gt, .gt, .lt,
          .gt, .gt, .gt, .gt, .gt]
#align tactic.itauto.prop.cmp Mathlib.Tactic.ITauto.IProp.cmp

instance : LT IProp := ⟨fun p q => p.cmp q = .lt⟩

instance : DecidableRel (@LT.lt IProp _) := fun _ _ => inferInstanceAs (Decidable (_ = _))

open Lean (Name)

/-- A reified inductive proof type for intuitionistic propositional logic. -/
inductive Proof
  /-- `⊢ A`, causes failure during reconstruction -/
  | sorry : Proof
  /-- `(n: A) ⊢ A` -/
  | hyp (n : Name) : Proof
  /-- `⊢ ⊤` -/
  | triv : Proof
  /-- `(p: ⊥) ⊢ A` -/
  | exfalso' (p : Proof) : Proof
  /-- `(p: (x: A) ⊢ B) ⊢ A → B` -/
  | intro (x : Name) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B) ⊢ A`
  * `ak = .iff`: `(p: A ↔ B) ⊢ A → B`
  * `ak = .eq`: `(p: A = B) ⊢ A → B`
  -/
  | andLeft (ak : AndKind) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B) ⊢ B`
  * `ak = .iff`: `(p: A ↔ B) ⊢ B → A`
  * `ak = .eq`: `(p: A = B) ⊢ B → A`
  -/
  | andRight (ak : AndKind) (p : Proof) : Proof
  /--
  * `ak = .and`: `(p₁: A) (p₂: B) ⊢ A ∧ B`
  * `ak = .iff`: `(p₁: A → B) (p₁: B → A) ⊢ A ↔ B`
  * `ak = .eq`: `(p₁: A → B) (p₁: B → A) ⊢ A = B`
  -/
  | andIntro (ak : AndKind) (p₁ p₂ : Proof) : Proof
  /--
  * `ak = .and`: `(p: A ∧ B → C) ⊢ A → B → C`
  * `ak = .iff`: `(p: (A ↔ B) → C) ⊢ (A → B) → (B → A) → C`
  * `ak = .eq`: `(p: (A = B) → C) ⊢ (A → B) → (B → A) → C`
  -/
  | curry (ak : AndKind) (p : Proof) : Proof
  /-- This is a partial application of curry.
  * `ak = .and`: `(p: A ∧ B → C) (q : A) ⊢ B → C`
  * `ak = .iff`: `(p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C`
  * `ak = .eq`: `(p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C`
  -/
  | curry₂ (ak : AndKind) (p q : Proof) : Proof
  /-- `(p: A → B) (q: A) ⊢ B` -/
  | app' : Proof → Proof → Proof
  /-- `(p: A ∨ B → C) ⊢ A → C` -/
  | orImpL (p : Proof) : Proof
  /-- `(p: A ∨ B → C) ⊢ B → C` -/
  | orImpR (p : Proof) : Proof
  /-- `(p: A) ⊢ A ∨ B` -/
  | orInL (p : Proof) : Proof
  /-- `(p: B) ⊢ A ∨ B` -/
  | orInR (p : Proof) : Proof
  /-- `(p₁: A ∨ B) (p₂: (x: A) ⊢ C) (p₃: (x: B) ⊢ C) ⊢ C` -/
  | orElim' (p₁ : Proof) (x : Name) (p₂ p₃ : Proof) : Proof
  /-- `(p₁: Decidable A) (p₂: (x: A) ⊢ C) (p₃: (x: ¬ A) ⊢ C) ⊢ C` -/
  | decidableElim (classical : Bool) (p₁ x : Name) (p₂ p₃ : Proof) : Proof
  /--
  * `classical = false`: `(p: Decidable A) ⊢ A ∨ ¬A`
  * `classical = true`: `(p: Prop) ⊢ p ∨ ¬p`
  -/
  | em (classical : Bool) (p : Name) : Proof
  /-- The variable `x` here names the variable that will be used in the elaborated proof.
  * `(p: ((x:A) → B) → C) ⊢ B → C`
  -/
  | impImpSimp (x : Name) (p : Proof) : Proof
  deriving Lean.ToExpr
#align tactic.itauto.proof Mathlib.Tactic.ITauto.Proof

instance : Inhabited Proof := ⟨.triv⟩

/-- Debugging printer for proof objects. -/
def Proof.format : Proof → Std.Format
  | .sorry => "sorry"
  | .hyp i => Std.format i
  | .triv => "triv"
  | .exfalso' p => f!"(exfalso {p.format})"
  | .intro x p => f!"(fun {x} ↦ {p.format})"
  | .andLeft _ p => f!"{p.format} .1"
  | .andRight _ p => f!"{p.format} .2"
  | .andIntro _ p q => f!"⟨{p.format}, {q.format}⟩"
  | .curry _ p => f!"(curry {p.format})"
  | .curry₂ _ p q => f!"(curry {p.format} {q.format})"
  | .app' p q => f!"({p.format} {q.format})"
  | .orImpL p => f!"(orImpL {p.format})"
  | .orImpR p => f!"(orImpR {p.format})"
  | .orInL p => f!"(Or.inl {p.format})"
  | .orInR p => f!"(Or.inr {p.format})"
  | .orElim' p x q r => f!"({p.format}.elim (fun {x} ↦ {q.format}) (fun {x} ↦ {r.format})"
  | .em false p => f!"(Decidable.em {p})"
  | .em true p => f!"(Classical.em {p})"
  | .decidableElim _ p x q r => f!"({p}.elim (fun {x} ↦ {q.format}) (fun {x} ↦ {r.format})"
  | .impImpSimp _ p => f!"(impImpSimp {p.format})"
#align tactic.itauto.proof.to_format Mathlib.Tactic.ITauto.Proof.format

instance : Std.ToFormat Proof := ⟨Proof.format⟩

/-- A variant on `Proof.exfalso'` that performs opportunistic simplification. -/
def Proof.exfalso : IProp → Proof → Proof
  | .false, p => p
  | _, p => .exfalso' p
#align tactic.itauto.proof.exfalso Mathlib.Tactic.ITauto.Proof.exfalso

/-- A variant on `Proof.orElim'` that performs opportunistic simplification. -/
def Proof.orElim : Proof → Name → Proof → Proof → Proof
  | .em cl p, x, q, r => .decidableElim cl p x q r
  | p, x, q, r => .orElim' p x q r
#align tactic.itauto.proof.or_elim Mathlib.Tactic.ITauto.Proof.orElim

/-- A variant on `Proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
def Proof.app : Proof → Proof → Proof
  | .curry ak p, q => .curry₂ ak p q
  | .curry₂ ak p q, r => p.app (q.andIntro ak r)
  | .orImpL p, q => p.app q.orInL
  | .orImpR p, q => p.app q.orInR
  | .impImpSimp x p, q => p.app (.intro x q)
  | p, q => p.app' q
#align tactic.itauto.proof.app Mathlib.Tactic.ITauto.Proof.app

-- Note(Mario): the typechecker is disabled because it requires proofs to carry around additional
-- props. These can be retrieved from the git history if you want to re-enable this.
/-
/-- A typechecker for the `Proof` type. This is not used by the tactic but can be used for
debugging. -/
meta def proof.check : name_map prop → proof → option prop
| Γ (proof.hyp i) := Γ.find i
| Γ proof.triv := some prop.true
| Γ (proof.exfalso' A p) := guard (p.check Γ = some prop.false) $> A
| Γ (proof.intro x A p) := do B ← p.check (Γ.insert x A), pure (prop.imp A B)
| Γ (proof.andLeft ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).1
| Γ (proof.andRight ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).2
| Γ (proof.andIntro and_kind.and p q) := do
  A ← p.check Γ, B ← q.check Γ,
  pure (A.and B)
| Γ (proof.andIntro ak p q) := do
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
| Γ (proof.orImpL B p) := do
  prop.imp (prop.or A B') C ← p.check Γ | none,
  guard (B = B') $> (A.imp C)
| Γ (proof.orImpR A p) := do
  prop.imp (prop.or A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
| Γ (proof.orInL B p) := do A ← p.check Γ | none, pure (A.or B)
| Γ (proof.orInR A p) := do B ← p.check Γ | none, pure (A.or B)
| Γ (proof.orElim p x q r) := do
  prop.or A B ← p.check Γ | none,
  C ← q.check (Γ.insert x A),
  C' ← r.check (Γ.insert x B),
  guard (C = C') $> C
| Γ (proof.impImpSimp x A p) := do
  prop.imp (prop.imp A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
-/

/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline] def freshName : StateM Nat Name := fun n => (Name.mkSimple s!"h{n}", n + 1)
#align tactic.itauto.fresh_name Mathlib.Tactic.ITauto.freshName

/-- The context during proof search is a map from propositions to proof values. -/
def Context := Lean.RBMap IProp Proof IProp.cmp
#align tactic.itauto.context Mathlib.Tactic.ITauto.Context

/-- Debug printer for the context. -/
def Context.format (Γ : Context) : Std.Format :=
  Γ.fold (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f
#align tactic.itauto.context.to_format Mathlib.Tactic.ITauto.Context.format

instance : Std.ToFormat Context := ⟨Context.format⟩

/-- Insert a proposition and its proof into the context, as in `have : A := p`. This will eagerly
apply all level 1 rules on the spot, which are rules that don't split the goal and are validity
preserving: specifically, we drop `⊤` and `A → ⊤` hypotheses, close the goal if we find a `⊥`
hypothesis, split all conjunctions, and also simplify `⊥ → A` (drop), `⊤ → A` (simplify to `A`),
`A ∧ B → C` (curry to `A → B → C`) and `A ∨ B → C` (rewrite to `(A → C) ∧ (B → C)` and split). -/
partial def Context.add : IProp → Proof → Context → Except (IProp → Proof) Context
  | .true, _, Γ => pure Γ
  | .false, p, _ => throw fun A => .exfalso A p
  | .and' ak A B, p, Γ => do
    let (A, B) := ak.sides A B
    let Γ ← Γ.add A (p.andLeft ak)
    Γ.add B (p.andRight ak)
  | .imp .false _, _, Γ => pure Γ
  | .imp .true A, p, Γ => Γ.add A (p.app .triv)
  | .imp (.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (A.imp (B.imp C)) (p.curry ak)
  | .imp (.or A B) C, p, Γ => do
    let Γ ← Γ.add (A.imp C) p.orImpL
    Γ.add (B.imp C) p.orImpR
  | .imp _ .true, _, Γ => pure Γ
  | A, p, Γ => pure (Γ.insert A p)
#align tactic.itauto.context.add Mathlib.Tactic.ITauto.Context.add

/-- Add `A` to the context `Γ` with proof `p`. This version of `Context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline] def Context.withAdd (Γ : Context) (A : IProp) (p : Proof) (B : IProp)
    (f : Context → IProp → StateM Nat (Bool × Proof)) : StateM Nat (Bool × Proof) :=
  match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)
#align tactic.itauto.context.with_add Mathlib.Tactic.ITauto.Context.withAdd

/-- Map a function over the proof (regardless of whether the proof is successful or not). -/
def mapProof (f : Proof → Proof) : Bool × Proof → Bool × Proof
  | (b, p) => (b, f p)
#align tactic.itauto.map_proof Mathlib.Tactic.ITauto.mapProof

/-- Convert a value-with-success to an optional value. -/
def isOk : (Bool × Proof) × Nat → Option (Proof × Nat)
  | ((false, _), _) => none
  | ((true, p), n) => some (p, n)
#align tactic.itauto.is_ok Mathlib.Tactic.ITauto.isOk

/-- Skip the continuation and return a failed proof if the boolean is false. -/
def whenOk : Bool → StateM Nat (Bool × Proof) → StateM Nat (Bool × Proof)
  | false, _ => pure (false, .sorry)
  | true, f => f
#align tactic.itauto.when_ok Mathlib.Tactic.ITauto.whenOk

mutual

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
partial def search (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) := do
  if let some p := Γ.find? B then return (true, p)
  fun n =>
  let search₁ := Γ.fold (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ.find? A' then
      isOk <| Context.withAdd (Γ.erase A) C (p.app q) B prove n
    else
      let .imp A₁ A₂ := A' | none
      let Γ : Context := Γ.erase A
      let (a, n) := freshName n
      let (p₁, n) ← isOk <| Γ.withAdd A₁ (.hyp a) A₂ (fun Γ_A₁ A₂ =>
        Γ_A₁.withAdd (IProp.imp A₂ C) (.impImpSimp a p) A₂ prove) n
      isOk <| Γ.withAdd C (p.app (.intro a p₁)) B prove n
  if let some (r, n) := search₁ then
    ((true, r), n)
  else if let .or B₁ B₂ := B then
    match (mapProof .orInL <$> prove Γ B₁) n with
    | ((false, _), _) => (mapProof .orInR <$> prove Γ B₂) n
    | r => r
  else ((false, .sorry), n)

/-- The main prover. This receives a context of proven or assumed lemmas and a target proposition,
and returns a proof or `none` (with state for the fresh variable generator).
The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `Context.add`, right rules in `prove`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`

The level 1 rules on the right of the turnstile are `Γ ⊢ ⊤` and `Γ ⊢ A → B`, these are easy to
handle. The rule `Γ ⊢ A ∧ B` is a level 2 rule, also handled here. If none of these apply, we try
the level 2 rule `A ∨ B ⊢ C` by searching the context and splitting all ors we find. Finally, if
we don't make any more progress, we go to the search phase.
-/
partial def prove (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) :=
  match B with
  | .true => pure (true, .triv)
  | .imp A B => do
    let a ← freshName
    mapProof (.intro a) <$> Γ.withAdd A (.hyp a) B prove
  | .and' ak A B => do
    let (A, B) := ak.sides A B
    let (ok, p) ← prove Γ A
    mapProof (p.andIntro ak) <$> whenOk ok (prove Γ B)
  | B =>
    Γ.fold
      (init := fun found Γ => bif found then prove Γ B else search Γ B)
      (f := fun IH A p found Γ => do
        if let .or A₁ A₂ := A then
          let Γ : Context := Γ.erase A
          let a ← freshName
          let (ok, p₁) ← Γ.withAdd A₁ (.hyp a) B fun Γ _ => IH true Γ
          mapProof (.orElim p a p₁) <$>
            whenOk ok (Γ.withAdd A₂ (.hyp a) B fun Γ _ => IH true Γ)
        else IH found Γ)
      (found := false) (Γ := Γ)

end

#align tactic.itauto.search Mathlib.Tactic.ITauto.search
#align tactic.itauto.prove Mathlib.Tactic.ITauto.prove

open Lean Qq Meta

/-- Reify an `Expr` into a `IProp`, allocating anything non-propositional as an atom in the
`AtomM` state. -/
partial def reify (e : Q(Prop)) : AtomM IProp :=
  match e with
  | ~q(True) => return .true
  | ~q(False) => return .false
  | ~q(¬ $a) => return .not (← reify a)
  | ~q($a ∧ $b) => return .and (← reify a) (← reify b)
  | ~q($a ∨ $b) => return .or (← reify a) (← reify b)
  | ~q($a ↔ $b) => return .iff (← reify a) (← reify b)
  | ~q(Xor' $a $b) => return .xor (← reify a) (← reify b)
  | ~q(@Eq Prop $a $b) => return .eq (← reify a) (← reify b)
  | ~q(@Ne Prop $a $b) => return .not (.eq (← reify a) (← reify b))
  | e =>
    if e.isArrow then return .imp (← reify e.bindingDomain!) (← reify e.bindingBody!)
    else return .var (← AtomM.addAtom e)
#align tactic.itauto.reify Mathlib.Tactic.ITauto.reify

/-- Once we have a proof object, we have to apply it to the goal. -/
partial def applyProof (g : MVarId) : NameMap Expr → Proof → MetaM Unit
  | _, .sorry => throwError "itauto failed\n{g}"
  | Γ, .hyp n => do g.assignIfDefeq (← liftOption (Γ.find? n))
  | _, .triv => g.assignIfDefeq q(trivial)
  | Γ, .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefeq q(@False.elim $A $t)
    applyProof t.mvarId! Γ p
  | Γ, .intro x p => do
    let (e, g) ← g.intro x; g.withContext do
      applyProof g (Γ.insert x (.fvar e)) p
  | Γ, .andLeft .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefeq q(And.left $t)
    applyProof t.mvarId! Γ p
  | Γ, .andLeft .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefeq q(Iff.mp $t)
    applyProof t.mvarId! Γ p
  | Γ, .andLeft .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefeq q(cast $t)
    applyProof t.mvarId! Γ p
  | Γ, .andRight .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefeq q(And.right $t)
    applyProof t.mvarId! Γ p
  | Γ, .andRight .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefeq q(Iff.mpr $t)
    applyProof t.mvarId! Γ p
  | Γ, .andRight .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefeq q(cast (Eq.symm $t))
    applyProof t.mvarId! Γ p
  | Γ, .andIntro .and p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ (u := .zero) A
    let t₂ ← mkFreshExprMVarQ (u := .zero) B
    g.assignIfDefeq q(And.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | Γ, .andIntro .iff p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefeq q(Iff.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | Γ, .andIntro .eq p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefeq q(propext (Iff.intro $t₁ $t₂))
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | Γ, .curry ak p => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (.curry₂ ak p (.hyp e.name))
  | Γ, .curry₂ ak p q => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (q.andIntro ak (.hyp e.name)))
  | Γ, .app' p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ (u := .zero) A
    g.assignIfDefeq q($t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | Γ, .orImpL p => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.orInL (.hyp e.name)))
  | Γ, .orImpR p => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.orInR (.hyp e.name)))
  | Γ, .orInL p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ (u := .zero) A
    g.assignIfDefeq q(@Or.inl $A $B $t)
    applyProof t.mvarId! Γ p
  | Γ, .orInR p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ (u := .zero) B
    g.assignIfDefeq q(@Or.inr $A $B $t)
    applyProof t.mvarId! Γ p
  | Γ, .orElim' p x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let C ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A ∨ $B)
    let t₂ ← mkFreshExprMVarQ q($A → $C)
    let t₃ ← mkFreshExprMVarQ q($B → $C)
    g.assignIfDefeq q(Or.elim $t₁ $t₂ $t₃)
    applyProof t₁.mvarId! Γ p
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₁
    let (e, t₃) ← t₃.mvarId!.intro x; t₃.withContext do
      applyProof t₃ (Γ.insert x (.fvar e)) p₂
  | Γ, .em false n => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    g.assignIfDefeq q(@Decidable.em $A $e)
  | Γ, .em true n => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    g.assignIfDefeq q(@Classical.em $A)
  | Γ, .decidableElim false n x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefeq q(@dite $B $A $e $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | Γ, .decidableElim true n x p₁ p₂ => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefeq q(@Classical.byCases $A $B $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | Γ, .impImpSimp x p => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.intro x (.hyp e.name)))
#align tactic.itauto.apply_proof Mathlib.Tactic.ITauto.applyProof

/-- A decision procedure for intuitionistic propositional logic.

* `useDec` will add `a ∨ ¬ a` to the context for every decidable atomic proposition `a`.
* `useClassical` will allow `a ∨ ¬ a` to be added even if the proposition is not decidable,
  using classical logic.
* `extraDec` will add `a ∨ ¬ a` to the context for specified (not necessarily atomic)
  propositions `a`.
-/
def itautoCore (g : MVarId)
    (useDec useClassical : Bool) (extraDec : Array Expr) : MetaM Unit := do
  AtomM.run (← getTransparency) do
    let mut hs := mkRBMap ..
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp → Proof) ITauto.Context := .ok (mkRBMap ..)
    let mut decs := mkRBMap ..
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        let e := ldecl.type
        if ← isProp e then
          let A ← reify e
          let n := ldecl.fvarId.name
          hs := hs.insert n (Expr.fvar ldecl.fvarId)
          Γ := do (← Γ).add A (.hyp n)
        else
          if let .const ``Decidable _ := e.getAppFn then
            let p : Q(Prop) := e.appArg!
            if useDec then
              let A ← reify p
              decs := decs.insert A (false, Expr.fvar ldecl.fvarId)
    let addDec (force : Bool) (decs : RBMap IProp (Bool × Expr) IProp.cmp) (e : Q(Prop)) := do
      let A ← reify e
      let dec_e := q(Decidable $e)
      let res ← trySynthInstance q(Decidable $e)
      if !(res matches .some _) && !useClassical then
        if force then _ ← synthInstance dec_e
        pure decs
      else
        pure (decs.insert A (match res with | .some e => (false, e) | _ => (true, e)))
    decs ← extraDec.foldlM (addDec true) decs
    if useDec then
      let mut decided := mkRBTree Nat compare
      if let .ok Γ' := Γ then
        decided := Γ'.fold (init := decided) fun m p _ =>
          match p with
          | .var i => m.insert i
          | .not (.var i) => m.insert i
          | _ => m
      let ats := (← get).atoms
      for e in ats, i in [0:ats.size] do
        if !decided.contains i then
          decs ← addDec false decs e
    for (A, cl, pf) in decs do
      let n ← mkFreshId
      hs := hs.insert n pf
      Γ := return (← Γ).insert (A.or A.not) (.em cl n)
    let p : Proof :=
      match Γ with
      | .ok Γ => (prove Γ t 0).1.2
      | .error p => p t
    applyProof g hs p
#align tactic.itauto Mathlib.Tactic.ITauto.itautoCore

open Elab Tactic

/-- A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle (without the `!` option), and the proof search is
tailored for this use case. (`itauto!` will work as a classical SAT solver, but the algorithm is
not very good in this situation.)

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
`Decidable a` and `Decidable b`. `itauto *` will case on all decidable propositions that it can
find among the atomic propositions, and `itauto! *` will case on all propositional atoms.
*Warning:* This can blow up the proof search, so it should be used sparingly.
-/
syntax (name := itauto) "itauto" "!"? (" *" <|> (" [" term,* "]"))? : tactic

elab_rules : tactic
  | `(tactic| itauto $[!%$cl]?) => liftMetaTactic (itautoCore · false cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? *) => liftMetaTactic (itautoCore · true cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? [$hs,*]) => withMainContext do
    let hs ← hs.getElems.mapM (Term.elabTermAndSynthesize · none)
    liftMetaTactic (itautoCore · true cl.isSome hs *> pure [])

@[inherit_doc itauto] syntax (name := itauto!) "itauto!" (" *" <|> (" [" term,* "]"))? : tactic

macro_rules
  | `(tactic| itauto!) => `(tactic| itauto !)
  | `(tactic| itauto! *) => `(tactic| itauto ! *)
  | `(tactic| itauto! [$hs,*]) => `(tactic| itauto ! [$hs,*])

-- add_hint_tactic itauto

-- add_tactic_doc
--   { Name := "itauto"
--     category := DocCategory.tactic
--     declNames := [`tactic.interactive.itauto]
--     tags := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }
