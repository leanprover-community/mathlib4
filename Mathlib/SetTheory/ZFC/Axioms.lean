/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.ModelTheory.Syntax
set_option linter.style.header false
set_option linter.directoryDependency false

/-!
# The Axioms of ZFC

This file defines the language of set theory (with one relation `∈` and no functions), and defines
the axioms of ZFC.

## Main definitions

* `FirstOrder.Language.set`: the language of set theory, with one relation symbol `∈` with arity 2,
  and no function symbols.
* `FirstOrder.Set.Class`: a class is a formula with parameters and `n + 1` free variable, where the
  last free variable acts as the captured variable. This is an auxiliary definition to make the
  axioms of ZFC easier to state.
* `FirstOrder.Set.ZFC`: the axioms of ZFC, as a set of sentences in the language of set theory.

## References

* [Set Theory, Thomas Jech][Jech2003]
-/

universe u u'

-- MOVE?
/-- Applies the formula to the given terms. -/
def FirstOrder.Language.BoundedFormula.app {L : FirstOrder.Language} {α β m n}
    (f : L.BoundedFormula α m) (x : α ⊕ Fin m → L.Term (β ⊕ Fin n)) :
    L.BoundedFormula β n :=
  (f.toFormula.subst x).relabel id

namespace FirstOrder

-- MOVE?
/-- `#n` is notation for the `n`-th parameter of a bounded formula. -/
scoped[FirstOrder] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

-- MOVE?
/-- `&ᵈk` is notation for the `k`-th free variable of a bounded formula, counting from the last one.
This agrees with the de Bruijn indexing (0-indexed). -/
scoped[FirstOrder] notation:arg "&ᵈ" k:arg => FirstOrder.Language.Term.var (Sum.inr (Fin.rev k))

/-- The relation symbols in the language of sets. -/
inductive setRel : ℕ → Type
  /-- The relation symbol for membership. -/
  | mem : setRel 2
  deriving DecidableEq

/-- The language of sets has exactly one relation symbol `∈` called membership with arity 2, and
no other relation or function symbols. -/
def Language.set : Language.{0} :=
  { Functions _ := Empty
    Relations := setRel }
  deriving IsRelational

namespace Set

open Language

/-- `setRel.mem`, but with the defeq type `Language.set.Relations 2` instead of `setRel 2`. -/
abbrev memRel : set.Relations 2 := setRel.mem

/-- `setRel.mem`, but with the defeq type `Language.set.Relations 2` instead of `setRel 2`. -/
scoped[FirstOrder] notation:130 a:130 " ∈' " b:130 =>
  FirstOrder.Language.Relations.boundedFormula FirstOrder.Set.memRel ![a, b]

/-- The formal statement saying `a` is not a member of `b`. Negation of `memRel`. -/
scoped[FirstOrder] notation:130 a:130 " ∉' " b:130 => ∼(a ∈' b)

instance : Fintype set.Symbols :=
  ⟨⟨Multiset.ofList [Sum.inr ⟨2, .mem⟩], by decide⟩,
  by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩); decide ⟩

@[simp]
theorem card_set : card set = 1 := by
  simp [card, show Fintype.card set.Symbols = 1 from rfl]

/-- A class with parameters indexed by `α` is a formula `C` with `n + 1` free variables, which
intuitively inherently represents "`&n ∈ C`", i.e. `C` itself as a formula means that the last free
variable is a member of the class `C`.

Then `x ∈ᶜ C` is defined to mean `C[&n/x]`, and `C ᶜ∈ x` is defined to mean `∃ y, y =ᶜ C ∧ y ∈ x`,
and `x =ᶜ C` is defined to mean `∀ y, y ∈ x ↔ y ∈ᶜ C`. -/
abbrev Class (α : Type u) (n : ℕ) := set.BoundedFormula α (n + 1)

variable {α : Type u} {β : Type u'} {n k : ℕ}

namespace Class

/-- Converts the `k`th free variable itself to a class, so `&k` becomes the class `&n ∈' &k`. -/
def mkC (x : set.Term (α ⊕ Fin n)) : Class α n :=
  &ᵈ0 ∈' (Term.relabel (Sum.map id Fin.castSucc) x)

-- I tried this, but the coercion does not work.
-- instance : Coe (set.Term (α ⊕ Fin n)) (Class α n) where
--   coe := mkC

/-- Lift a class with `n` free variables to a class with `n+k` free variable. Only the hidden
free variable (`&n` which should not be accessed) is changed. The original bounded variables
are all lifted above `n+k`. -/
def lift (C : Class α n) : Class α (n + k) :=
  (C.liftAt k n).castLE (by omega)

@[inherit_doc] scoped[FirstOrder] prefix:200 "↑'" => FirstOrder.Set.Class.lift

@[inherit_doc] scoped[FirstOrder] notation:200 "↑'[" a:arg "]" b:arg =>
  FirstOrder.Set.Class.lift (k := a) b

example : lift (α := ℤ) (n := 3) (k := 7) ((#(-1) ∈' &0) ⊓ (&1 ∈' &3)) =
    ((#(-1) ∈' &0) ⊓ (&1 ∈' &10)) := by
  change (memRel.boundedFormula _) ⊓ (memRel.boundedFormula _) = _
  congr 2
  all_goals {
    rw [funext_iff, Fin.forall_fin_two]
    simp [Term.liftAt, Term.relabel] }

/-- Produce the formula that `&k` is in the given class (with `k < n`). -/
def app (k : Fin n) (C : Class α n) : set.BoundedFormula α n :=
  BoundedFormula.relabel (Sum.map id <| Fin.snoc id k) C.toFormula

-- TODO : simprocs?
example : (app 5 (mkC (α := ℤ) (n := 6) &3)) = (&5 ∈' &3) := by
  change BoundedFormula.rel memRel _ = BoundedFormula.rel memRel _
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  simp [BoundedFormula.relabelAux, finSumFinEquiv, Fin.snoc, Fin.ext_iff]

/-- The formula that `C₁` and `C₂` are equal (by extensionality). -/
def eqC (C₁ C₂ : Class α n) : set.BoundedFormula α n :=
  ∀' (C₁ ⇔ C₂)

@[inherit_doc] scoped[FirstOrder] infix:100 " =ᶜ " => FirstOrder.Set.Class.eqC

instance : Singleton (Class α n) (Class α n) where
  singleton C := .mkC &ᵈ0 =ᶜ ↑'C

/-- The formula that `C₁ ∈ᶜ C₂`, i.e. there exists (a set) `x` that `C₁` is equal to such that
`x ∈ C₂`. -/
def memC (C₁ C₂ : Class α n) : set.BoundedFormula α n :=
  ∃' ({C₁} ⊓ C₂)

@[inherit_doc] scoped[FirstOrder] infix:100 " ∈ᶜ " => FirstOrder.Set.Class.memC

/-- The negation of `memC`, saying that there is no set `x` equal to `C₁` (as class) satisfying
`x ∈ C₂`. -/
scoped[FirstOrder] notation:100 a:200 " ∉ᶜ " b:200 =>
  ∼(FirstOrder.Set.Class.memC a b)

/-- A class "exists" when it can be realised as a set. -/
def existsC (C : Class α n) : set.BoundedFormula α n :=
  ∃' {C}

/-- Binds the parameters. -/
def bind (C : Class α n) (f : α ⊕ Fin n → β ⊕ Fin k) : Class β k :=
  BoundedFormula.relabel (k := 0) (Sum.elim
    (Sum.elim Sum.inl (Sum.inr ∘ Fin.castSucc) ∘ f ∘ Sum.inl)
    (Fin.snoc (Sum.elim Sum.inl (Sum.inr ∘ Fin.castSucc) ∘ f ∘ Sum.inr)
      (Sum.inr <| Fin.last k))) C.toFormula

end Class

/-- `(x ∈ᶜ empty) := ⊥` -/
@[simp] def empty : Class α n :=
  ⊥

instance : EmptyCollection (Class α n) where
  emptyCollection := empty

variable (C C₁ C₂ : Class α n)

/-- `V` the universal class is the complement of `∅`. -/
def V : Class α n :=
  &ᵈ0 =' &ᵈ0

/-- `(x ∈ᶜ pow C) := (x ⊆ᶜ C) := (∀ y, y ∈ x → y ∈ᶜ C)` -/
def pow : Class α n :=
  ∀' (&ᵈ0 ∈' &ᵈ1 ⟹ .mkC &ᵈ0 ∈ᶜ ↑'[2]C)

/-- `(x ∈ᶜ union C₁ C₂) := (x ∈ᶜ C₁ ∨ x ∈ᶜ C₂)`. Notated as `C₁ ∪ C₂`. -/
@[simp] def union : Class α n :=
  C₁ ⊔ C₂

instance : Union (Class α n) where
  union := union

/-- `(x ∈ᶜ inter C₁ C₂) := (x ∈ᶜ C₁ ∧ x ∈ᶜ C₂)`. Notated as `C₁ ∩ C₂`. -/
@[simp] def inter : Class α n :=
  C₁ ⊓ C₂

instance : Inter (Class α n) where
  inter := inter

/-- `(x ∈ᶜ sUnion C) := (∃ y, x ∈ y ∧ y ∈ᶜ C)`. Notated as `⋃ᶜ C`. Input as `\U\^c C`. -/
def sUnion : Class α n :=
  ∃' (&ᵈ1 ∈' &ᵈ0 ⊓ .mkC &ᵈ0 ∈ᶜ ↑'[2]C)

@[inherit_doc] scoped[FirstOrder] prefix:120 "⋃ᶜ " => FirstOrder.Set.sUnion

/-- `(x ∈ᶜ sInter C) := (∀ y, y ∈ᶜ C → x ∈ y)`. Notated as `⋂ᶜ C`. Input as `\I\^c C`. -/
def sInter : Class α n :=
  ∀' (.mkC &ᵈ0 ∈ᶜ ↑'[2]C ⟹ &ᵈ1 ∈' &ᵈ0)

@[inherit_doc] scoped[FirstOrder] prefix:120 "⋂ᶜ " => FirstOrder.Set.sInter

/-- `(x ∈ᶜ sdiff C₁ C₂) := (x ∈ᶜ C₁ ∧ x ∉ᶜ C₂)`. Notated as `C₁ \ C₂`. -/
@[simp] def sdiff : Class α n :=
  C₁ ⊓ ∼C₂

instance : SDiff (Class α n) where
  sdiff := sdiff

/-- `succ C = C ∪ {C}`, the standard encoding for ordinal numbers. -/
def succ (C : Class α n) : Class α n :=
  C ∪ {C}

/-- `insert C₁ C₂ = {C₁} ∪ C₂`. -/
@[simp] def insert (C₁ C₂ : Class α n) : Class α n :=
  {C₁} ∪ C₂

instance : Insert (Class α n) (Class α n) where
  insert := insert

instance : NatCast (Class α n) where
  natCast := Nat.rec ∅ fun _ ↦ succ

instance (k : ℕ) : OfNat (Class α n) k where
  ofNat := k

example : (2 : Class α n) = ∅ ∪ {∅} ∪ {∅ ∪ {∅}} := rfl

/-- The class of all inductive sets. `x` is an inductive set when `0 ∈ x` and
`∀ n, n ∈ x → succ n ∈ x`. -/
def isInductive : Class α n :=
  (0 ∈ᶜ .mkC &ᵈ0) ⊓ ∀' (&ᵈ0 ∈' &ᵈ1 ⟹ succ (.mkC &ᵈ0) ∈ᶜ .mkC &ᵈ1)

/-- `ω` is the intersection of all inductive sets. -/
def omega : Class α n :=
  ⋂ᶜ isInductive

/-- The pair `(C₁, C₂)` (notated `⸨C₁, C₂⸩`, type using `\((\))`) is encoded as `{{C₁}, {C₁, C₂}}`.
This is the standard Kuratowski ordering. -/
def orderedPair : Class α n :=
  {{C₁}, {C₁, C₂}}

@[inherit_doc] scoped[FirstOrder] notation:140 "⸨" a:140 ", " b:140 "⸩" =>
  FirstOrder.Set.orderedPair a b

/-- Returns the first element of an ordered pair. -/
def fst : Class α n :=
  ⋂ᶜ C

/-- Returns the second element of an ordered pair. -/
def snd : Class α n :=
  ⋃ᶜ C ⊓ ∀' ∀' ((&ᵈ1 ∈' &ᵈ2 ⊓ &ᵈ0 ∈' &ᵈ2 ⊓ .mkC &ᵈ1 ∈ᶜ ↑'[3]C ⊓ .mkC &ᵈ0 ∈ᶜ ↑'[3]C) ⟹ &ᵈ1 =' &ᵈ0)

/-- The formula saying that `x` is an ordered pair. As a class, this is the class of all ordered
pairs. -/
def isPair : Class α n :=
  .mkC &ᵈ0 =ᶜ ⸨fst (.mkC &ᵈ0), snd (.mkC &ᵈ0)⸩

/-- The formula saying that `x` is a function, i.e. `x` consists of ordered pairs, and if
`(y, z₁) ∈ x` and `(y, z₂) ∈ x` then `z₁ = z₂`. As a class, this is the class of all functions.
Note that there is no statement here saying `x` is "total", which is impossible to attain. -/
def isFunction : Class α n :=
  (∀' &ᵈ0 ∈' &ᵈ1 ⟹ isPair) ⊓ ∀' ∀' ((&ᵈ1 ∈' &ᵈ2 ⊓ &ᵈ0 ∈' &ᵈ2 ⊓ fst (.mkC &ᵈ1) =ᶜ fst (.mkC &ᵈ2)) ⟹
    (snd (.mkC &ᵈ1) =ᶜ snd (.mkC &ᵈ1)))

/-- If `C₁` is a function and `C₂` is a set, then this is the class of all `x` that is the result of
applying `C₁` to `C₂`. (There should only be one such `x`.)

Other cases (if `C₁` is not a function) are undefined behaviour. The formula literally says that
the ordered pair `(C₂, x)` is a member of `C₁`. -/
def funcApp : Class α n :=
  ⸨↑'C₂, .mkC &ᵈ0⸩ ∈ᶜ ↑'C₁

/-- The domain of a class `C` (assumed to be a function) is the class of all `x` such that there
exists a `y` such that `(x, y) ∈ C`. This is the class of all first elements of ordered pairs in
`C`. -/
def domain : Class α n :=
  ∃' (.mkC &ᵈ0 ∈ᶜ ↑'[2]C ⊓ fst (.mkC &ᵈ0) =ᶜ .mkC &ᵈ1)

/-- `x` is a singleton. As a class, this is the class of all singletons. -/
def isSingleton : Class α n :=
  ∃' (&ᵈ0 ∈' &ᵈ1 ⊓ ∀' (&ᵈ0 ∈' &ᵈ2 ⟹ &ᵈ0 =' &ᵈ1))

end Set


namespace Language.Sentence

open Set

/-- If two sets have the same elements, then they are equal. -/
def extensionality : set.Sentence :=
  ∀' ∀' ((∀' ((&2 ∈' &0) ⇔ (&2 ∈' &1))) ⟹ (&0 =' &1))

/-- Given sets `x` and `y`, the set `{x, y}` exists. -/
def pairing : set.Sentence :=
  ∀' ∀' Class.existsC {.mkC &0, .mkC &1}

/-- Given set `x`, its union `⋃₀ x` exists. -/
def union : set.Sentence :=
  ∀' Class.existsC (⋃ᶜ (.mkC &0))

/-- Given set `x`, its powerset exists. -/
def powerset : set.Sentence :=
  ∀' Class.existsC (pow (.mkC &0))

/-- There is an inductive set, i.e. contains `∅` and closed under successsor `x ↦ x ∪ {x}`. -/
def infinity : set.Sentence :=
  ∃' ((0 ∈ᶜ .mkC &0) ⊓ ∀' (&1 ∈' &0 ⟹ succ (.mkC &1) ∈ᶜ .mkC &0))

/-- The membership relation is well-founded. -/
def regularity : set.Sentence :=
  ∀' ((∃' &1 ∈' &0) ⟹ ∃' (&1 ∈' &0 ⊓ ∀' (&2 ∈' &1 ⟹ &2 ∉' &0)))

/-- Given any class `C` and set `x`, the intersection `x ∩ C` is a set. -/
def separation (C : Class (Fin 1) 0) : set.Sentence :=
  ∀' ∀' Class.existsC (.mkC &0 ∩ C.bind (Sum.elim ![Sum.inr 1] Fin.elim0))

/-- The image of a set under any class function is a set. -/
def replacement (F : set.BoundedFormula (Fin 3) 0) : set.Sentence :=
  ∀' ((∀' ∀' ∀' (((F.app (Sum.elim ![&1, &2, &0] Fin.elim0)) ⊓
      (F.app (Sum.elim ![&1, &3, &0] Fin.elim0))) ⟹ &2 =' &3)) ⟹
    (∀' ∃' ∀' (&3 ∈' &2 ⇔ ∃' (&4 ∈' &1 ⊓
      F.app (Sum.elim ![&4, &3, &0] Fin.elim0)))))

/-- This is a version that avoids talking about functions. In words, it says that if `x` is a set
not containing the empty set, and the elements of `x` are pairwise disjoint, then there is a
set `t` whose intersection with any `y ∈ x` contains exactly one element. -/
def choice : set.Sentence :=
  ∀' (∅ ∉ᶜ .mkC &0 ⊓ (∀' ∀' ∀' ((&3 ∈' &1 ⊓ &1 ∈' &0 ⊓ &3 ∈' &2 ⊓ &2 ∈' &0) ⟹ &1 =' &2)) ⟹
      ∃' ∀' (&2 ∈' &0 ⟹ (.mkC &1 ∩ .mkC &2) ∈ᶜ isSingleton))

end Language.Sentence


namespace Set

open Language

/-- The axioms of ZFC: Extensionality, Pairing, Separation, Union, Power Set, Infinity,
Replacement, Regularity, and Choice.

Reference: [P.3, Set Theory, Thomas Jech][Jech2003] -/
inductive ZFC : set.Sentence → Prop
  | ext : ZFC .extensionality
  | pair : ZFC .pairing
  | separation (C : Class (Fin 1) 0) : ZFC <| .separation C
  | union : ZFC <| .union
  | power : ZFC <| .powerset
  | infinity : ZFC <| .infinity
  | replacement (F : set.BoundedFormula (Fin 3) 0) : ZFC <| .replacement F
  | regularity : ZFC <| .regularity
  | choice : ZFC <| .choice

end FirstOrder.Set
