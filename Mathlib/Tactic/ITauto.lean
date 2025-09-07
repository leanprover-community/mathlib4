/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Exact
import Batteries.Tactic.Init
import Mathlib.Logic.Basic
import Mathlib.Util.AtomM
import Qq

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


open Std (TreeMap TreeSet)

namespace Mathlib.Tactic.ITauto

/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/
inductive AndKind | and | iff | eq
  deriving Lean.ToExpr, DecidableEq

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

/-- Constructor for `p ∧ q`. -/
@[match_pattern] def IProp.and : IProp → IProp → IProp := .and' .and

/-- Constructor for `p ↔ q`. -/
@[match_pattern] def IProp.iff : IProp → IProp → IProp := .and' .iff

/-- Constructor for `p = q`. -/
@[match_pattern] def IProp.eq : IProp → IProp → IProp := .and' .eq

/-- Constructor for `¬ p`. -/
@[match_pattern] def IProp.not (a : IProp) : IProp := a.imp .false

/-- Constructor for `xor p q`. -/
@[match_pattern] def IProp.xor (a b : IProp) : IProp := (a.and b.not).or (b.and a.not)

instance : Inhabited IProp := ⟨IProp.true⟩

/-- Given the contents of an `And` variant, return the two conjuncts. -/
def AndKind.sides : AndKind → IProp → IProp → IProp × IProp
  | .and, A, B => (A, B)
  | _, A, B => (A.imp B, B.imp A)

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

instance : Std.ToFormat IProp := ⟨IProp.format⟩

/-- A comparator for `AndKind`. (There should really be a derive handler for this.) -/
def AndKind.cmp (p q : AndKind) : Ordering := by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]

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

instance : LT IProp := ⟨fun p q => p.cmp q = .lt⟩

instance : DecidableLT IProp := fun _ _ => inferInstanceAs (Decidable (_ = _))

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

instance : Inhabited Proof := ⟨Proof.triv⟩

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

instance : Std.ToFormat Proof := ⟨Proof.format⟩

/-- A variant on `Proof.exfalso'` that performs opportunistic simplification. -/
def Proof.exfalso : IProp → Proof → Proof
  | .false, p => p
  | _, p => .exfalso' p

/-- A variant on `Proof.orElim'` that performs opportunistic simplification. -/
def Proof.orElim : Proof → Name → Proof → Proof → Proof
  | .em cl p, x, q, r => .decidableElim cl p x q r
  | p, x, q, r => .orElim' p x q r

/-- A variant on `Proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
def Proof.app : Proof → Proof → Proof
  | .curry ak p, q => .curry₂ ak p q
  | .curry₂ ak p q, r => p.app (q.andIntro ak r)
  | .orImpL p, q => p.app q.orInL
  | .orImpR p, q => p.app q.orInR
  | .impImpSimp x p, q => p.app (.intro x q)
  | p, q => p.app' q

-- Note(Mario): the typechecker is disabled because it requires proofs to carry around additional
-- props. These can be retrieved from the git history (rev 6c96d2ff7) if you want to re-enable this.
/-
/-- A typechecker for the `Proof` type. This is not used by the tactic but can be used for
debugging. -/
def Proof.check : Lean.NameMap IProp → Proof → Option IProp
  | _, .sorry A => some A
  | Γ, .hyp i => Γ.find? i
  | _, triv => some .true
  | Γ, .exfalso' A p => guard (p.check Γ = some .false) *> pure A
  | Γ, .intro x A p => do let B ← p.check (Γ.insert x A); pure (.imp A B)
  | Γ, .andLeft ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).1
  | Γ, .andRight ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).2
  | Γ, .andIntro .and p q => do
    let A ← p.check Γ; let B ← q.check Γ
    pure (A.and B)
  | Γ, .andIntro ak p q => do
    let .imp A B ← p.check Γ | none
    let C ← q.check Γ; guard (C = .imp B A) *> pure (A.and' ak B)
  | Γ, .curry ak p => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let (A', B') := ak.sides A B
    guard (ak = ak') *> pure (A'.imp $ B'.imp C)
  | Γ, .curry₂ ak p q => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let A₂ ← q.check Γ
    let (A', B') := ak.sides A B
    guard (ak = ak' ∧ A₂ = A') *> pure (B'.imp C)
  | Γ, .app' p q => do
    let .imp A B ← p.check Γ | none
    let A' ← q.check Γ
    guard (A = A') *> pure B
  | Γ, .orImpL B p => do
    let .imp (.or A B') C ← p.check Γ | none
    guard (B = B') *> pure (A.imp C)
  | Γ, .orImpR A p => do
    let .imp (.or A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
  | Γ, .orInL B p => do let A ← p.check Γ; pure (A.or B)
  | Γ, .orInR A p => do let B ← p.check Γ; pure (A.or B)
  | Γ, .orElim' p x q r => do
    let .or A B ← p.check Γ | none
    let C ← q.check (Γ.insert x A)
    let C' ← r.check (Γ.insert x B)
    guard (C = C') *> pure C
  | _, .em _ _ A => pure (A.or A.not)
  | Γ, .decidableElim _ A _ x p₂ p₃ => do
    let C ← p₂.check (Γ.insert x A)
    let C' ← p₃.check (Γ.insert x A.not)
    guard (C = C') *> pure C
  | Γ, .impImpSimp _ A p => do
    let .imp (.imp A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
-/

/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline] def freshName : StateM Nat Name := fun n => (Name.mkSimple s!"h{n}", n + 1)

/-- The context during proof search is a map from propositions to proof values. -/
abbrev Context := TreeMap IProp Proof IProp.cmp

/-- Debug printer for the context. -/
def Context.format (Γ : Context) : Std.Format :=
  Γ.foldl (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f

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

/-- Add `A` to the context `Γ` with proof `p`. This version of `Context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline] def Context.withAdd (Γ : Context) (A : IProp) (p : Proof) (B : IProp)
    (f : Context → IProp → StateM Nat (Bool × Proof)) : StateM Nat (Bool × Proof) :=
  match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)

/-- Map a function over the proof (regardless of whether the proof is successful or not). -/
def mapProof (f : Proof → Proof) : Bool × Proof → Bool × Proof
  | (b, p) => (b, f p)

/-- Convert a value-with-success to an optional value. -/
def isOk : (Bool × Proof) × Nat → Option (Proof × Nat)
  | ((false, _), _) => none
  | ((true, p), n) => some (p, n)

/-- Skip the continuation and return a failed proof if the boolean is false. -/
def whenOk : Bool → IProp → StateM Nat (Bool × Proof) → StateM Nat (Bool × Proof)
  | false, _, _ => pure (false, .sorry)
  | true, _, f => f

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
  if let some p := Γ[B]? then return (true, p)
  fun n =>
  let search₁ := Γ.foldl (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ[A']? then
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
    mapProof (p.andIntro ak) <$> whenOk ok B (prove Γ B)
  | B =>
    Γ.foldl
      (init := fun found Γ => bif found then prove Γ B else search Γ B)
      (f := fun IH A p found Γ => do
        if let .or A₁ A₂ := A then
          let Γ : Context := Γ.erase A
          let a ← freshName
          let (ok, p₁) ← Γ.withAdd A₁ (.hyp a) B fun Γ _ => IH true Γ
          mapProof (.orElim p a p₁) <$>
            whenOk ok B (Γ.withAdd A₂ (.hyp a) B fun Γ _ => IH true Γ)
        else IH found Γ)
      (found := false) (Γ := Γ)

end

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
    else return .var (← AtomM.addAtom e).1

/-- Once we have a proof object, we have to apply it to the goal. -/
partial def applyProof (g : MVarId) (Γ : NameMap Expr) (p : Proof) : MetaM Unit :=
  match p with
  | .sorry => throwError "itauto failed\n{g}"
  | .hyp n => do g.assignIfDefEq (← liftOption (Γ.find? n))
  | .triv => g.assignIfDefEq q(trivial)
  | .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefEq q(@False.elim $A $t)
    applyProof t.mvarId! Γ p
  | .intro x p => do
    let (e, g) ← g.intro x; g.withContext do
      applyProof g (Γ.insert x (.fvar e)) p
  | .andLeft .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefEq q(And.left $t)
    applyProof t.mvarId! Γ p
  | .andLeft .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefEq q(Iff.mp $t)
    applyProof t.mvarId! Γ p
  | .andLeft .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefEq q(cast $t)
    applyProof t.mvarId! Γ p
  | .andRight .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefEq q(And.right $t)
    applyProof t.mvarId! Γ p
  | .andRight .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefEq q(Iff.mpr $t)
    applyProof t.mvarId! Γ p
  | .andRight .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefEq q(cast (Eq.symm $t))
    applyProof t.mvarId! Γ p
  | .andIntro .and p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A)
    let t₂ ← mkFreshExprMVarQ q($B)
    g.assignIfDefEq q(And.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .iff p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefEq q(Iff.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .eq p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefEq q(propext (Iff.intro $t₁ $t₂))
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .app' p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($A)
    g.assignIfDefEq q($t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .orInL p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A)
    g.assignIfDefEq q(@Or.inl $A $B $t)
    applyProof t.mvarId! Γ p
  | .orInR p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($B)
    g.assignIfDefEq q(@Or.inr $A $B $t)
    applyProof t.mvarId! Γ p
  | .orElim' p x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let C ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A ∨ $B)
    let t₂ ← mkFreshExprMVarQ q($A → $C)
    let t₃ ← mkFreshExprMVarQ q($B → $C)
    g.assignIfDefEq q(Or.elim $t₁ $t₂ $t₃)
    applyProof t₁.mvarId! Γ p
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₁
    let (e, t₃) ← t₃.mvarId!.intro x; t₃.withContext do
      applyProof t₃ (Γ.insert x (.fvar e)) p₂
  | .em false n => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    g.assignIfDefEq q(@Decidable.em $A $e)
  | .em true n => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    g.assignIfDefEq q(@Classical.em $A)
  | .decidableElim false n x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefEq q(@dite $B $A $e $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .decidableElim true n x p₁ p₂ => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefEq q(@Classical.byCases $A $B $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .curry .. | .curry₂ .. | .orImpL .. | .orImpR .. | .impImpSimp .. => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.hyp e.name))

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
    let mut hs := mkNameMap Expr
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp → Proof) ITauto.Context := .ok TreeMap.empty
    let mut decs := TreeMap.empty
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
    let addDec (force : Bool) (decs : TreeMap IProp (Bool × Expr) IProp.cmp) (e : Q(Prop)) := do
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
      let mut decided := TreeSet.empty (cmp := compare)
      if let .ok Γ' := Γ then
        decided := Γ'.foldl (init := decided) fun m p _ =>
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

end Mathlib.Tactic.ITauto
