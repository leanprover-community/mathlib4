/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathlib.Data.PFunctor.Multivariate.Basic

#align_import data.qpf.multivariate.basic from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive ListShape (a b : Type)
  | nil : ListShape
  | cons : a -> b -> ListShape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def List (a : Type) := fix ListShape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def Multiset (a : Type) := QPF.quot List.perm List a -- not the actual notion
```

And `Multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive Tree (a : Type)
  | node : a -> Multiset Tree -> Tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive Tree' (a : Type)
| node : a -> Multiset Tree' -> Tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`Tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * Fix
   * Cofix
   * Quot
   * Comp
   * Sigma / Pi
   * Prj
   * Const

each proves that some operations on functors preserves the QPF structure

## Reference

! * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open MvFunctor

/-- Multivariate quotients of polynomial functors.
-/
class MvQPF {n : ℕ} (F : TypeVec.{u} n → Type*) [MvFunctor F] where
  P : MvPFunctor.{u} n
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P α), abs (f <$$> p) = f <$$> abs p
#align mvqpf MvQPF

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type*} [MvFunctor F] [q : MvQPF F]

open MvFunctor (LiftP LiftR)

/-!
### Show that every MvQPF is a lawful MvFunctor.
-/


protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map]
  rfl
#align mvqpf.id_map MvQPF.id_map

@[simp]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x]
  cases' repr x with a f
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl
#align mvqpf.comp_map MvQPF.comp_map

instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F where
  id_map := @MvQPF.id_map n F _ _
  comp_map := @comp_map n F _ _
#align mvqpf.is_lawful_mvfunctor MvQPF.lawfulMvFunctor

-- Lifting predicates and relations
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    cases' h : repr y with a f
    use a, fun i j => (f i j).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]; rfl
    intro i j
    apply (f i j).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
  rw [← abs_map, h₀]; rfl
#align mvqpf.liftp_iff MvQPF.liftP_iff

theorem liftR_iff {α : TypeVec n} (r : ∀ /- ⦃i⦄ -/ {i}, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    cases' h : repr u with a f
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  dsimp; constructor
  · rw [xeq, ← abs_map]; rfl
  rw [yeq, ← abs_map]; rfl
#align mvqpf.liftr_iff MvQPF.liftR_iff

open Set

open MvFunctor (LiftP LiftR)

theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u ∈ f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  intro h p; rw [liftP_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
#align mvqpf.mem_supp MvQPF.mem_supp

theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } := by ext; apply mem_supp
#align mvqpf.supp_eq MvQPF.supp_eq

theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (∀ p, LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ := by
  constructor
  · intro h
    have : LiftP (supp x) x := by rw [h]; introv; exact id
    rw [liftP_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro hu u ⟨j, _h₂, hfi⟩
    have hh : u ∈ supp x a' := by rw [← hfi]; apply h'
    exact (mem_supp x _ u).mp hh _ _ hu
  rintro ⟨a, f, xeq, h⟩ p; rw [liftP_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ i u usuppx
    rcases (mem_supp x _ u).mp (@usuppx) a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine ⟨a, f, xeq.symm, ?_⟩; intro j y
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h _ a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)
#align mvqpf.has_good_supp_iff MvQPF.has_good_supp_iff

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ
#align mvqpf.is_uniform MvQPF.IsUniform

/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x
#align mvqpf.liftp_preservation MvQPF.LiftPPreservation

/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P α), supp (abs x) = supp x
#align mvqpf.supp_preservation MvQPF.SuppPreservation

theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
    ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
#align mvqpf.supp_eq_of_is_uniform MvQPF.supp_eq_of_isUniform

theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : ∀ i, α i → Prop) :
    LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u := by
  rw [liftP_iff, ← abs_repr x]
  cases' repr x with a f; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun _ i => h' _ _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩
#align mvqpf.liftp_iff_of_is_uniform MvQPF.liftP_iff_of_isUniform

theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i := by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, ← image_comp]
  rfl
#align mvqpf.supp_map MvQPF.supp_map

theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]
#align mvqpf.supp_preservation_iff_uniform MvQPF.suppPreservation_iff_isUniform

theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPreservation := by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_isUniform] at h'
    dsimp only [SuppPreservation, supp] at h
    simp only [liftP_iff_of_isUniform, supp_eq_of_isUniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
  · rintro α ⟨a, f⟩
    simp only [LiftPPreservation] at h
    ext
    simp only [supp, h, mem_setOf_eq]
#align mvqpf.supp_preservation_iff_liftp_preservation MvQPF.suppPreservation_iff_liftpPreservation

theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_isUniform]
#align mvqpf.liftp_preservation_iff_uniform MvQPF.liftpPreservation_iff_uniform

/-- Any type function `F` that is (extensionally) equivalent to a QPF, is itself a QPF,
assuming that the functorial map of `F` behaves similar to `MvFunctor.ofEquiv eqv` -/
def ofEquiv {F F' : TypeVec.{u} n → Type*} [MvFunctor F'] [q : MvQPF F'] [MvFunctor F]
    (eqv : ∀ α, F α ≃ F' α)
    (map_eq : ∀ (α β : TypeVec n) (f : α ⟹ β) (a : F α),
      f <$$> a = ((eqv _).symm <| f <$$> eqv _ a) := by intros; rfl) :
    MvQPF F where
  P         := q.P
  abs α     := (eqv _).symm <| q.abs α
  repr α    := q.repr <| eqv _ α
  abs_repr  := by simp [q.abs_repr]
  abs_map   := by simp [q.abs_map, map_eq]

end MvQPF

/-- Every polynomial functor is a (trivial) QPF -/
instance MvPFunctor.instMvQPFObj {n} (P : MvPFunctor n) : MvQPF P where
  P := P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl
