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
  abs : ∀ {α}, P.Obj α → F α
  repr : ∀ {α}, F α → P.Obj α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P.Obj α), abs (f <$$> p) = f <$$> abs p
#align mvqpf MvQPF

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type*} [MvFunctor F] [q : MvQPF F]

open MvFunctor (LiftP LiftR)

/-!
### Show that every MvQPF is a lawful MvFunctor.
-/


protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x]
  -- ⊢ TypeVec.id <$$> abs (repr x) = abs (repr x)
  cases' repr x with a f
  -- ⊢ TypeVec.id <$$> abs { fst := a, snd := f } = abs { fst := a, snd := f }
  rw [← abs_map]
  -- ⊢ abs (TypeVec.id <$$> { fst := a, snd := f }) = abs { fst := a, snd := f }
  rfl
  -- 🎉 no goals
#align mvqpf.id_map MvQPF.id_map

@[simp]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x]
  -- ⊢ (g ⊚ f) <$$> abs (repr x) = g <$$> f <$$> abs (repr x)
  cases' repr x with a f
  -- ⊢ (g ⊚ f✝) <$$> abs { fst := a, snd := f } = g <$$> f✝ <$$> abs { fst := a, sn …
  rw [← abs_map, ← abs_map, ← abs_map]
  -- ⊢ abs ((g ⊚ f✝) <$$> { fst := a, snd := f }) = abs (g <$$> f✝ <$$> { fst := a, …
  rfl
  -- 🎉 no goals
#align mvqpf.comp_map MvQPF.comp_map

instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F where
  id_map := @MvQPF.id_map n F _ _
  comp_map := @comp_map n F _ _
#align mvqpf.is_lawful_mvfunctor MvQPF.lawfulMvFunctor

-- Lifting predicates and relations
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  -- ⊢ LiftP p x → ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPF …
  · rintro ⟨y, hy⟩
    -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P  …
    cases' h : repr y with a f
    -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P  …
    use a, fun i j => (f i j).val
    -- ⊢ x = abs { fst := a, snd := fun i j => ↑(f i j) } ∧ ∀ (i : Fin2 n) (j : MvPFu …
    constructor
    -- ⊢ x = abs { fst := a, snd := fun i j => ↑(f i j) }
    · rw [← hy, ← abs_repr y, h, ← abs_map]; rfl
      -- ⊢ abs ((fun i => Subtype.val) <$$> { fst := a, snd := f }) = abs { fst := a, s …
                                             -- 🎉 no goals
    intro i j
    -- ⊢ p ↑(f i j)
    apply (f i j).property
    -- 🎉 no goals
  rintro ⟨a, f, h₀, h₁⟩
  -- ⊢ LiftP p x
  use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
  -- ⊢ (fun i => Subtype.val) <$$> abs { fst := a, snd := fun i j => { val := f i j …
  rw [← abs_map, h₀]; rfl
  -- ⊢ abs ((fun i => Subtype.val) <$$> { fst := a, snd := fun i j => { val := f i  …
                      -- 🎉 no goals
#align mvqpf.liftp_iff MvQPF.liftP_iff

theorem liftR_iff {α : TypeVec n} (r : ∀ /- ⦃i⦄ -/ {i}, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  -- ⊢ LiftR (fun {i} => r) x y → ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y =  …
  · rintro ⟨u, xeq, yeq⟩
    -- ⊢ ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y = abs { fst := a, snd := f₁ } …
    cases' h : repr u with a f
    -- ⊢ ∃ a f₀ f₁, x = abs { fst := a, snd := f₀ } ∧ y = abs { fst := a, snd := f₁ } …
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    -- ⊢ x = abs { fst := a, snd := fun i j => (↑(f i j)).fst } ∧ y = abs { fst := a, …
    constructor
    -- ⊢ x = abs { fst := a, snd := fun i j => (↑(f i j)).fst }
    · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
      -- ⊢ abs ((fun i t => (↑t).fst) <$$> { fst := a, snd := f }) = abs { fst := a, sn …
                                              -- 🎉 no goals
    constructor
    -- ⊢ y = abs { fst := a, snd := fun i j => (↑(f i j)).snd }
    · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
      -- ⊢ abs ((fun i t => (↑t).snd) <$$> { fst := a, snd := f }) = abs { fst := a, sn …
                                              -- 🎉 no goals
    intro i j
    -- ⊢ r (↑(f i j)).fst (↑(f i j)).snd
    exact (f i j).property
    -- 🎉 no goals
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  -- ⊢ LiftR (fun {i} => r) x y
  use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  -- ⊢ (fun i t => (↑t).fst) <$$> abs { fst := a, snd := fun i j => { val := (f₀ i  …
  dsimp; constructor
  -- ⊢ (fun i t => (↑t).fst) <$$> abs { fst := a, snd := fun i j => { val := (f₀ i  …
         -- ⊢ (fun i t => (↑t).fst) <$$> abs { fst := a, snd := fun i j => { val := (f₀ i  …
  · rw [xeq, ← abs_map]; rfl
    -- ⊢ abs ((fun i t => (↑t).fst) <$$> { fst := a, snd := fun i j => { val := (f₀ i …
                         -- 🎉 no goals
  rw [yeq, ← abs_map]; rfl
  -- ⊢ abs ((fun i t => (↑t).snd) <$$> { fst := a, snd := fun i j => { val := (f₀ i …
                       -- 🎉 no goals
#align mvqpf.liftr_iff MvQPF.liftR_iff

open Set

open MvFunctor (LiftP LiftR)

theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ := by
  rw [supp]; dsimp; constructor
  -- ⊢ u ∈ {y | ∀ ⦃P : (i : Fin2 n) → α i → Prop⦄, LiftP P x → P i y} ↔ ∀ (a : (P F …
             -- ⊢ (∀ ⦃P : (i : Fin2 n) → α i → Prop⦄, LiftP P x → P i u) ↔ ∀ (a : (P F).A) (f  …
                    -- ⊢ (∀ ⦃P : (i : Fin2 n) → α i → Prop⦄, LiftP P x → P i u) → ∀ (a : (P F).A) (f  …
  · intro h a f haf
    -- ⊢ u ∈ f i '' univ
    have : LiftP (fun i u => u ∈ f i '' univ) x := by
      rw [liftP_iff]
      refine' ⟨a, f, haf.symm, _⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
    -- 🎉 no goals
  intro h p; rw [liftP_iff]
  -- ⊢ LiftP p x → p i u
             -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P …
  rintro ⟨a, f, xeq, h'⟩
  -- ⊢ p i u
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  -- ⊢ p i✝ u
  rw [← hi]; apply h'
  -- ⊢ p i✝ (f i✝ i)
             -- 🎉 no goals
#align mvqpf.mem_supp MvQPF.mem_supp

theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } := by ext; apply mem_supp
                                                                     -- ⊢ x✝ ∈ supp x i ↔ x✝ ∈ {u | ∀ (a : (P F).A) (f : MvPFunctor.B (P F) a ⟹ α), ab …
                                                                          -- 🎉 no goals
#align mvqpf.supp_eq MvQPF.supp_eq

theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (∀ p, LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ := by
  constructor
  -- ⊢ (∀ (p : (i : Fin2 n) → α i → Prop), LiftP p x ↔ ∀ (i : Fin2 n) (u : α i), u  …
  · intro h
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (i : Fin2 n) (a' : (P F).A) (f' :  …
    have : LiftP (supp x) x := by rw [h]; introv; exact id
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (i : Fin2 n) (a' : (P F).A) (f' :  …
    rw [liftP_iff] at this
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (i : Fin2 n) (a' : (P F).A) (f' :  …
    rcases this with ⟨a, f, xeq, h'⟩
    -- ⊢ ∃ a f, abs { fst := a, snd := f } = x ∧ ∀ (i : Fin2 n) (a' : (P F).A) (f' :  …
    refine' ⟨a, f, xeq.symm, _⟩
    -- ⊢ ∀ (i : Fin2 n) (a' : (P F).A) (f' : MvPFunctor.B (P F) a' ⟹ α), abs { fst := …
    intro a' f' h''
    -- ⊢ abs { fst := f', snd := h'' } = x → f a' '' univ ⊆ h'' a' '' univ
    rintro hu u ⟨j, _h₂, hfi⟩
    -- ⊢ u ∈ h'' a' '' univ
    have hh : u ∈ supp x a' := by rw [← hfi]; apply h'
    -- ⊢ u ∈ h'' a' '' univ
    refine' (mem_supp x _ u).mp hh _ _ hu
    -- 🎉 no goals
  rintro ⟨a, f, xeq, h⟩ p; rw [liftP_iff]; constructor
  -- ⊢ LiftP p x ↔ ∀ (i : Fin2 n) (u : α i), u ∈ supp x i → p i u
                           -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P …
                                           -- ⊢ (∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P …
  · rintro ⟨a', f', xeq', h'⟩ i u usuppx
    -- ⊢ p i u
    rcases(mem_supp x _ u).mp (@usuppx) a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    -- ⊢ p i✝ u
    rw [← f'ieq]
    -- ⊢ p i✝ (f' i✝ i)
    apply h'
    -- 🎉 no goals
  intro h'
  -- ⊢ ∃ a f, x = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPFunctor.B (P  …
  refine' ⟨a, f, xeq.symm, _⟩; intro j y
  -- ⊢ ∀ (i : Fin2 n) (j : MvPFunctor.B (P F) a i), p i (f i j)
                               -- ⊢ p j (f j y)
  apply h'; rw [mem_supp]
  -- ⊢ f j y ∈ supp x j
            -- ⊢ ∀ (a : (P F).A) (f_1 : MvPFunctor.B (P F) a ⟹ α), abs { fst := a, snd := f_1 …
  intro a' f' xeq'
  -- ⊢ f j y ∈ f' j '' univ
  apply h _ a' f' xeq'
  -- ⊢ f j y ∈ f j '' univ
  apply mem_image_of_mem _ (mem_univ _)
  -- 🎉 no goals
#align mvqpf.has_good_supp_iff MvQPF.has_good_supp_iff

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ
#align mvqpf.is_uniform MvQPF.IsUniform

/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P.Obj α), LiftP p (abs x) ↔ LiftP p x
#align mvqpf.liftp_preservation MvQPF.LiftPPreservation

/-- does `abs` preserve `supp`? -/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P.Obj α), supp (abs x) = supp x
#align mvqpf.supp_preservation MvQPF.SuppPreservation

theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
    ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro; ext u; rw [mem_supp]; constructor
  -- ⊢ supp (abs { fst := a, snd := f }) i✝ = f i✝ '' univ
         -- ⊢ u ∈ supp (abs { fst := a, snd := f }) i✝ ↔ u ∈ f i✝ '' univ
                -- ⊢ (∀ (a_1 : (P F).A) (f_1 : MvPFunctor.B (P F) a_1 ⟹ α), abs { fst := a_1, snd …
                               -- ⊢ (∀ (a_1 : (P F).A) (f_1 : MvPFunctor.B (P F) a_1 ⟹ α), abs { fst := a_1, snd …
  · intro h'
    -- ⊢ u ∈ f i✝ '' univ
    apply h' _ _ rfl
    -- 🎉 no goals
  intro h' a' f' e
  -- ⊢ u ∈ f' i✝ '' univ
  rw [← h _ _ _ _ e.symm]; apply h'
  -- ⊢ u ∈ f i✝ '' univ
                           -- 🎉 no goals
#align mvqpf.supp_eq_of_is_uniform MvQPF.supp_eq_of_isUniform

theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : ∀ i, α i → Prop) :
    LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u := by
  rw [liftP_iff, ← abs_repr x]
  -- ⊢ (∃ a f, abs (repr x) = abs { fst := a, snd := f } ∧ ∀ (i : Fin2 n) (j : MvPF …
  cases' repr x with a f; constructor
  -- ⊢ (∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀  …
                          -- ⊢ (∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀  …
  · rintro ⟨a', f', abseq, hf⟩ u
    -- ⊢ ∀ (u_1 : α u), u_1 ∈ supp (abs { fst := a, snd := f }) u → p u u_1
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    -- ⊢ ∀ (u_1 : α u), u_1 ∈ f' u '' univ → p u u_1
    rintro b ⟨i, _, hi⟩
    -- ⊢ p u b
    rw [← hi]
    -- ⊢ p u (f' u i)
    apply hf
    -- 🎉 no goals
  intro h'
  -- ⊢ ∃ a_1 f_1, abs { fst := a, snd := f } = abs { fst := a_1, snd := f_1 } ∧ ∀ ( …
  refine' ⟨a, f, rfl, fun _ i => h' _ _ _⟩
  -- ⊢ f x✝ i ∈ supp (abs { fst := a, snd := f }) x✝
  rw [supp_eq_of_isUniform h]
  -- ⊢ f x✝ i ∈ f x✝ '' univ
  exact ⟨i, mem_univ i, rfl⟩
  -- 🎉 no goals
#align mvqpf.liftp_iff_of_is_uniform MvQPF.liftP_iff_of_isUniform

theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i := by
  rw [← abs_repr x]; cases' repr x with a f; rw [← abs_map, MvPFunctor.map_eq]
  -- ⊢ supp (g <$$> abs (repr x)) i = g i '' supp (abs (repr x)) i
                     -- ⊢ supp (g <$$> abs { fst := a, snd := f }) i = g i '' supp (abs { fst := a, sn …
                                             -- ⊢ supp (abs { fst := a, snd := g ⊚ f }) i = g i '' supp (abs { fst := a, snd : …
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, ← image_comp]
  -- ⊢ (g ⊚ f) i '' univ = g i ∘ f i '' univ
  rfl
  -- 🎉 no goals
#align mvqpf.supp_map MvQPF.supp_map

theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  -- ⊢ SuppPreservation → IsUniform
  · intro h α a a' f f' h' i
    -- ⊢ f i '' univ = f' i '' univ
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
    -- 🎉 no goals
  · rintro h α ⟨a, f⟩
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    ext
    -- ⊢ x✝ ∈ supp (abs { fst := a, snd := f }) x✝¹ ↔ x✝ ∈ supp { fst := a, snd := f  …
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]
    -- 🎉 no goals
#align mvqpf.supp_preservation_iff_uniform MvQPF.suppPreservation_iff_isUniform

theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPreservation := by
  constructor <;> intro h
  -- ⊢ SuppPreservation → LiftPPreservation
                  -- ⊢ LiftPPreservation
                  -- ⊢ SuppPreservation
  · rintro α p ⟨a, f⟩
    -- ⊢ LiftP p (abs { fst := a, snd := f }) ↔ LiftP p { fst := a, snd := f }
    have h' := h
    -- ⊢ LiftP p (abs { fst := a, snd := f }) ↔ LiftP p { fst := a, snd := f }
    rw [suppPreservation_iff_isUniform] at h'
    -- ⊢ LiftP p (abs { fst := a, snd := f }) ↔ LiftP p { fst := a, snd := f }
    dsimp only [SuppPreservation, supp] at h
    -- ⊢ LiftP p (abs { fst := a, snd := f }) ↔ LiftP p { fst := a, snd := f }
    simp only [liftP_iff_of_isUniform, supp_eq_of_isUniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
    -- ⊢ (∀ (i : Fin2 n) (u : α i) (x : MvPFunctor.B (P F) a i), f i x = u → p u) → ∀ …
                    -- ⊢ p (f i✝ x✝)
                    -- ⊢ p u✝
                               -- ⊢ p (f i✝ x✝)
                               -- ⊢ p (f i✝ x✝)
                                              -- 🎉 no goals
                                              -- 🎉 no goals
  · rintro α ⟨a, f⟩
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    simp only [LiftPPreservation] at h
    -- ⊢ supp (abs { fst := a, snd := f }) = supp { fst := a, snd := f }
    ext
    -- ⊢ x✝ ∈ supp (abs { fst := a, snd := f }) x✝¹ ↔ x✝ ∈ supp { fst := a, snd := f  …
    simp only [supp, h, mem_setOf_eq]
    -- 🎉 no goals
#align mvqpf.supp_preservation_iff_liftp_preservation MvQPF.suppPreservation_iff_liftpPreservation

theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_isUniform]
  -- 🎉 no goals
#align mvqpf.liftp_preservation_iff_uniform MvQPF.liftpPreservation_iff_uniform

end MvQPF
