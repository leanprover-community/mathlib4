/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
import Mathlib.Computability.Halting

#align_import computability.reduce from "leanprover-community/mathlib"@"d13b3a4a392ea7273dfa4727dbd1892e26cfd518"

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `Sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/


universe u v w

open Function

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)
#align many_one_reducible ManyOneReducible

-- mathport name: «expr ≤₀ »
@[inherit_doc ManyOneReducible]
infixl:1000 " ≤₀ " => ManyOneReducible

theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) : (fun a => q (f a)) ≤₀ q :=
  ⟨f, h, fun _ => Iff.rfl⟩
#align many_one_reducible.mk ManyOneReducible.mk

@[refl]
theorem manyOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p :=
  ⟨id, Computable.id, by simp⟩
                         -- 🎉 no goals
#align many_one_reducible_refl manyOneReducible_refl

@[trans]
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁,
      fun a => ⟨fun h => by erw [← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩
                            -- ⊢ p a
                                              -- 🎉 no goals
                                                                      -- 🎉 no goals
#align many_one_reducible.trans ManyOneReducible.trans

theorem reflexive_manyOneReducible {α} [Primcodable α] : Reflexive (@ManyOneReducible α α _ _) :=
  manyOneReducible_refl
#align reflexive_many_one_reducible reflexive_manyOneReducible

theorem transitive_manyOneReducible {α} [Primcodable α] : Transitive (@ManyOneReducible α α _ _) :=
  fun _ _ _ => ManyOneReducible.trans
#align transitive_many_one_reducible transitive_manyOneReducible

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)
#align one_one_reducible OneOneReducible

-- mathport name: «expr ≤₁ »
@[inherit_doc OneOneReducible]
infixl:1000 " ≤₁ " => OneOneReducible

theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) ≤₁ q :=
  ⟨f, h, i, fun _ => Iff.rfl⟩
#align one_one_reducible.mk OneOneReducible.mk

@[refl]
theorem oneOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p :=
  ⟨id, Computable.id, injective_id, by simp⟩
                                       -- 🎉 no goals
#align one_one_reducible_refl oneOneReducible_refl

@[trans]
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by erw [← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩
                   -- ⊢ p a
                                     -- 🎉 no goals
                                                             -- 🎉 no goals
#align one_one_reducible.trans OneOneReducible.trans

theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ q → p ≤₀ q
  | ⟨f, c, _, h⟩ => ⟨f, c, h⟩
#align one_one_reducible.to_many_one OneOneReducible.to_many_one

theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e) : (q ∘ e) ≤₁ q :=
  OneOneReducible.mk _ h e.injective
#align one_one_reducible.of_equiv OneOneReducible.of_equiv

theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β → Prop) (h : Computable e.symm) : q ≤₁ (q ∘ e) := by
  convert OneOneReducible.of_equiv _ h; funext; simp
  -- ⊢ q = (q ∘ ↑e) ∘ ↑e.symm
                                        -- ⊢ q x✝ = ((q ∘ ↑e) ∘ ↑e.symm) x✝
                                                -- 🎉 no goals
#align one_one_reducible.of_equiv_symm OneOneReducible.of_equiv_symm

theorem reflexive_oneOneReducible {α} [Primcodable α] : Reflexive (@OneOneReducible α α _ _) :=
  oneOneReducible_refl
#align reflexive_one_one_reducible reflexive_oneOneReducible

theorem transitive_oneOneReducible {α} [Primcodable α] : Transitive (@OneOneReducible α α _ _) :=
  fun _ _ _ => OneOneReducible.trans
#align transitive_one_one_reducible transitive_oneOneReducible

namespace ComputablePred

variable {α : Type*} {β : Type*} {σ : Type*}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

theorem computable_of_manyOneReducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q)
    (h₂ : ComputablePred q) : ComputablePred p := by
  rcases h₁ with ⟨f, c, hf⟩
  -- ⊢ ComputablePred p
  rw [show p = fun a => q (f a) from Set.ext hf]
  -- ⊢ ComputablePred fun a => q (f a)
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  -- ⊢ ComputablePred fun a => (fun a => g a = true) (f a)
  exact ⟨by infer_instance, by simpa using hg.comp c⟩
  -- 🎉 no goals
#align computable_pred.computable_of_many_one_reducible ComputablePred.computable_of_manyOneReducible

theorem computable_of_oneOneReducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p :=
  computable_of_manyOneReducible h.to_many_one
#align computable_pred.computable_of_one_one_reducible ComputablePred.computable_of_oneOneReducible

end ComputablePred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p
#align many_one_equiv ManyOneEquiv

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p
#align one_one_equiv OneOneEquiv

@[refl]
theorem manyOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p :=
  ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩
#align many_one_equiv_refl manyOneEquiv_refl

@[symm]
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p :=
  And.symm
#align many_one_equiv.symm ManyOneEquiv.symm

@[trans]
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align many_one_equiv.trans ManyOneEquiv.trans

theorem equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) :=
  ⟨manyOneEquiv_refl, fun {_ _} => ManyOneEquiv.symm, fun {_ _ _} => ManyOneEquiv.trans⟩
#align equivalence_of_many_one_equiv equivalence_of_manyOneEquiv

@[refl]
theorem oneOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p :=
  ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩
#align one_one_equiv_refl oneOneEquiv_refl

@[symm]
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p :=
  And.symm
#align one_one_equiv.symm OneOneEquiv.symm

@[trans]
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align one_one_equiv.trans OneOneEquiv.trans

theorem equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) :=
  ⟨oneOneEquiv_refl, fun {_ _} => OneOneEquiv.symm, fun {_ _ _} => OneOneEquiv.trans⟩
#align equivalence_of_one_one_equiv equivalence_of_oneOneEquiv

theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : OneOneEquiv p q → ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩
#align one_one_equiv.to_many_one OneOneEquiv.to_many_one

/-- a computable bijection -/
nonrec def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm
#align equiv.computable Equiv.Computable

theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable → e.symm.Computable :=
  And.symm
#align equiv.computable.symm Equiv.Computable.symm

theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩
#align equiv.computable.trans Equiv.Computable.trans

theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.ofNat _⟩
#align computable.eqv Computable.eqv

theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm
#align computable.equiv₂ Computable.equiv₂

theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩
#align one_one_equiv.of_equiv OneOneEquiv.of_equiv

theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one
#align many_one_equiv.of_equiv ManyOneEquiv.of_equiv

theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  ⟨h.2.trans, h.1.trans⟩
#align many_one_equiv.le_congr_left ManyOneEquiv.le_congr_left

theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align many_one_equiv.le_congr_right ManyOneEquiv.le_congr_right

theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  ⟨h.2.trans, h.1.trans⟩
#align one_one_equiv.le_congr_left OneOneEquiv.le_congr_left

theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align one_one_equiv.le_congr_right OneOneEquiv.le_congr_right

theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align many_one_equiv.congr_left ManyOneEquiv.congr_left

theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align many_one_equiv.congr_right ManyOneEquiv.congr_right

theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align one_one_equiv.congr_left OneOneEquiv.congr_left

theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align one_one_equiv.congr_right OneOneEquiv.congr_right

@[simp]
theorem ULower.down_computable {α} [Primcodable α] : (ULower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩
#align ulower.down_computable ULower.down_computable

theorem manyOneEquiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ ULower.up) p :=
  ManyOneEquiv.of_equiv ULower.down_computable.symm
#align many_one_equiv_up manyOneEquiv_up

-- mathport name: «expr ⊕' »
local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec

theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ p ⊕' q :=
  ⟨Sum.inl, Computable.sum_inl, fun _ _ => Sum.inl.inj_iff.1, fun _ => Iff.rfl⟩
#align one_one_reducible.disjoin_left OneOneReducible.disjoin_left

theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : q ≤₁ p ⊕' q :=
  ⟨Sum.inr, Computable.sum_inr, fun _ _ => Sum.inr.inj_iff.1, fun _ => Iff.rfl⟩
#align one_one_reducible.disjoin_right OneOneReducible.disjoin_right

theorem disjoin_manyOneReducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → (p ⊕' q) ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨Sum.elim f g,
      Computable.id.sum_casesOn (c₁.comp Computable.snd).to₂ (c₂.comp Computable.snd).to₂,
      fun x => by cases x <;> [apply h₁; apply h₂]⟩
                  -- 🎉 no goals
#align disjoin_many_one_reducible disjoin_manyOneReducible

theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : (p ⊕' q) ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r :=
  ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩
#align disjoin_le disjoin_le

variable {α : Type u} [Primcodable α] [Inhabited α]

variable {β : Type v} [Primcodable β] [Inhabited β]

variable {γ : Type w} [Primcodable γ] [Inhabited γ]

/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
def toNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode (α := α) n).getD default) }
#align to_nat toNat

@[simp]
theorem toNat_manyOneReducible {p : Set α} : toNat p ≤₀ p :=
  ⟨fun n => (Encodable.decode (α := α) n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩
#align to_nat_many_one_reducible toNat_manyOneReducible

@[simp]
theorem manyOneReducible_toNat {p : Set α} : p ≤₀ toNat p :=
  ⟨Encodable.encode, Computable.encode, by simp [toNat, setOf]⟩
                                           -- 🎉 no goals
#align many_one_reducible_to_nat manyOneReducible_toNat

@[simp]
theorem manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p ≤₀ toNat q ↔ p ≤₀ q :=
  ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩
#align many_one_reducible_to_nat_to_nat manyOneReducible_toNat_toNat

@[simp]
theorem toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p := by simp [ManyOneEquiv]
                                                                        -- 🎉 no goals
#align to_nat_many_one_equiv toNat_manyOneEquiv

@[simp]
theorem manyOneEquiv_toNat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by simp [ManyOneEquiv]
                                                              -- 🎉 no goals
#align many_one_equiv_to_nat manyOneEquiv_toNat

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set ℕ))
#align many_one_degree ManyOneDegree

namespace ManyOneDegree

/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : ManyOneDegree :=
  Quotient.mk'' (toNat p)
#align many_one_degree.of ManyOneDegree.of

@[elab_as_elim]
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree)
    (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotient.inductionOn' d h
#align many_one_degree.ind_on ManyOneDegree.ind_on

/-- Lifts a function on sets of natural numbers to many-one degrees.
-/
@[reducible] -- @[elab_as_elim] -- Porting note: unexpected eliminator resulting type
protected def liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotient.liftOn' d f h
#align many_one_degree.lift_on ManyOneDegree.liftOn

@[simp]
protected theorem liftOn_eq {φ} (p : Set ℕ) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : (of p).liftOn f h = f p :=
  rfl
#align many_one_degree.lift_on_eq ManyOneDegree.liftOn_eq

/-- Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[reducible, simp] -- @[elab_as_elim] -- Porting note: unexpected eliminator resulting type
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun q₁ q₂ hq => h _ _ _ _ (by rfl) hq)
                                                                    -- 🎉 no goals
    (by
      intro p₁ p₂ hp
      -- ⊢ (fun p => ManyOneDegree.liftOn d₂ (f p) (_ : ∀ (q₁ q₂ : ℕ → Prop), ManyOneEq …
      induction d₂ using ManyOneDegree.ind_on
      -- ⊢ (fun p => ManyOneDegree.liftOn (of p✝) (f p) (_ : ∀ (q₁ q₂ : ℕ → Prop), Many …
      apply h
      -- ⊢ ManyOneEquiv p₁ p₂
      assumption
      -- ⊢ ManyOneEquiv (toNat p✝) (toNat p✝)
      rfl)
      -- 🎉 no goals
#align many_one_degree.lift_on₂ ManyOneDegree.liftOn₂

@[simp]
protected theorem liftOn₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl
#align many_one_degree.lift_on₂_eq ManyOneDegree.liftOn₂_eq

@[simp]
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by
  rw [of, of, Quotient.eq'']
  -- ⊢ Setoid.r (toNat p) (toNat q) ↔ ManyOneEquiv p q
  unfold Setoid.r
  -- ⊢ { r := ManyOneEquiv, iseqv := proof_1 }.1 (toNat p) (toNat q) ↔ ManyOneEquiv …
  simp
  -- 🎉 no goals
#align many_one_degree.of_eq_of ManyOneDegree.of_eq_of

instance instInhabited : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩
#align many_one_degree.inhabited ManyOneDegree.instInhabited

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance instLE : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩
#align many_one_degree.has_le ManyOneDegree.instLE

@[simp]
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  manyOneReducible_toNat_toNat
#align many_one_degree.of_le_of ManyOneDegree.of_le_of

private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on; simp; rfl
  -- ⊢ of p✝ ≤ of p✝
                                          -- ⊢ p✝ ≤₀ p✝
                                                -- 🎉 no goals

private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ := by
  induction d₁ using ManyOneDegree.ind_on
  -- ⊢ of p✝ ≤ d₂ → d₂ ≤ of p✝ → of p✝ = d₂
  induction d₂ using ManyOneDegree.ind_on
  -- ⊢ of p✝¹ ≤ of p✝ → of p✝ ≤ of p✝¹ → of p✝¹ = of p✝
  intro hp hq
  -- ⊢ of p✝¹ = of p✝
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and_iff]
  -- 🎉 no goals

private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  -- ⊢ of p✝ ≤ d₂ → d₂ ≤ d₃ → of p✝ ≤ d₃
  induction d₂ using ManyOneDegree.ind_on
  -- ⊢ of p✝¹ ≤ of p✝ → of p✝ ≤ d₃ → of p✝¹ ≤ d₃
  induction d₃ using ManyOneDegree.ind_on
  -- ⊢ of p✝² ≤ of p✝¹ → of p✝¹ ≤ of p✝ → of p✝² ≤ of p✝
  apply ManyOneReducible.trans
  -- 🎉 no goals

instance instPartialOrder : PartialOrder ManyOneDegree where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
#align many_one_degree.partial_order ManyOneDegree.instPartialOrder

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
instance instAdd : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a ⊕' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        -- ⊢ (fun a b => of (a ⊕' b)) a c = (fun a b => of (a ⊕' b)) b d
        rw [of_eq_of]
        -- ⊢ ManyOneEquiv (a ⊕' c) (b ⊕' d)
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_many_one),
            disjoin_manyOneReducible (hr₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hr₂.trans OneOneReducible.disjoin_right.to_many_one)⟩)⟩
#align many_one_degree.has_add ManyOneDegree.instAdd

@[simp]
theorem add_of (p : Set α) (q : Set β) : of (p ⊕' q) = of p + of q :=
  of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_left.to_many_one)
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_right.to_many_one)⟩
#align many_one_degree.add_of ManyOneDegree.add_of

@[simp]
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  -- ⊢ of p✝ + d₂ ≤ d₃ ↔ of p✝ ≤ d₃ ∧ d₂ ≤ d₃
  induction d₂ using ManyOneDegree.ind_on
  -- ⊢ of p✝¹ + of p✝ ≤ d₃ ↔ of p✝¹ ≤ d₃ ∧ of p✝ ≤ d₃
  induction d₃ using ManyOneDegree.ind_on
  -- ⊢ of p✝² + of p✝¹ ≤ of p✝ ↔ of p✝² ≤ of p✝ ∧ of p✝¹ ≤ of p✝
  simpa only [← add_of, of_le_of] using disjoin_le
  -- 🎉 no goals
#align many_one_degree.add_le ManyOneDegree.add_le

@[simp]
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).1
                              -- 🎉 no goals
#align many_one_degree.le_add_left ManyOneDegree.le_add_left

@[simp]
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).2
                              -- 🎉 no goals
#align many_one_degree.le_add_right ManyOneDegree.le_add_right

instance instSemilatticeSup : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }
#align many_one_degree.semilattice_sup ManyOneDegree.instSemilatticeSup

end ManyOneDegree
