/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.big_operators.pi
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Ring.Pi

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/


open BigOperators

namespace Pi

@[to_additive]
theorem list_prod_apply {α : Type _} {β : α → Type _} [∀ a, Monoid (β a)] (a : α)
    (l : List (∀ a, β a)) : l.prod a = (l.map fun f : ∀ a, β a ↦ f a).prod :=
  (evalMonoidHom β a).map_list_prod _
#align pi.list_prod_apply Pi.list_prod_apply
#align pi.list_sum_apply Pi.list_sum_apply

@[to_additive]
theorem multiset_prod_apply {α : Type _} {β : α → Type _} [∀ a, CommMonoid (β a)] (a : α)
    (s : Multiset (∀ a, β a)) : s.prod a = (s.map fun f : ∀ a, β a ↦ f a).prod :=
  (evalMonoidHom β a).map_multiset_prod _
#align pi.multiset_prod_apply Pi.multiset_prod_apply
#align pi.multiset_sum_apply Pi.multiset_sum_apply

end Pi

@[to_additive (attr:=simp)]
theorem Finset.prod_apply {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoid (β a)] (a : α)
    (s : Finset γ) (g : γ → ∀ a, β a) : (∏ c in s, g c) a = ∏ c in s, g c a :=
  (Pi.evalMonoidHom β a).map_prod _ _
#align finset.prod_apply Finset.prod_apply
#align finset.sum_apply Finset.sum_apply

/-- An 'unapplied' analogue of `Finset.prod_apply`. -/
@[to_additive "An 'unapplied' analogue of `Finset.sum_apply`."]
theorem Finset.prod_fn {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoid (β a)] (s : Finset γ)
    (g : γ → ∀ a, β a) : (∏ c in s, g c) = fun a ↦ ∏ c in s, g c a :=
  funext fun _ ↦ Finset.prod_apply _ _ _
#align finset.prod_fn Finset.prod_fn
#align finset.sum_fn Finset.sum_fn

@[to_additive]
theorem Fintype.prod_apply {α : Type _} {β : α → Type _} {γ : Type _} [Fintype γ]
    [∀ a, CommMonoid (β a)] (a : α) (g : γ → ∀ a, β a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g
#align fintype.prod_apply Fintype.prod_apply
#align fintype.sum_apply Fintype.sum_apply

@[to_additive prod_mk_sum]
theorem prod_mk_prod {α β γ : Type _} [CommMonoid α] [CommMonoid β] (s : Finset γ) (f : γ → α)
    (g : γ → β) : (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x) :=
  haveI := Classical.decEq γ
  Finset.induction_on s rfl (by simp (config := { contextual := true }) [Prod.ext_iff])
#align prod_mk_prod prod_mk_prod
#align prod_mk_sum prod_mk_sum

section Single

variable {I : Type _} [DecidableEq I] {Z : I → Type _}

variable [∀ i, AddCommMonoid (Z i)]

-- As we only defined `single` into `add_monoid`, we only prove the `Finset.sum` version here.
theorem Finset.univ_sum_single [Fintype I] (f : ∀ i, Z i) : (∑ i, Pi.single i (f i)) = f := by
  ext a
  simp
#align finset.univ_sum_single Finset.univ_sum_single

theorem AddMonoidHom.functions_ext [Finite I] (G : Type _) [AddCommMonoid G] (g h : (∀ i, Z i) →+ G)
    (H : ∀ i x, g (Pi.single i x) = h (Pi.single i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_sum_single k, g.map_sum, h.map_sum]
  simp only [H]
#align add_monoid_hom.functions_ext AddMonoidHom.functions_ext

/-- This is used as the ext lemma instead of `AddMonoidHom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem AddMonoidHom.functions_ext' [Finite I] (M : Type _) [AddCommMonoid M]
    (g h : (∀ i, Z i) →+ M)
    (H : ∀ i, g.comp (AddMonoidHom.single Z i) = h.comp (AddMonoidHom.single Z i)) : g = h :=
  have := fun i ↦ FunLike.congr_fun (H i)
  g.functions_ext M h this
#align add_monoid_hom.functions_ext' AddMonoidHom.functions_ext'

end Single

section RingHom

open Pi

variable {I : Type _} [DecidableEq I] {f : I → Type _}

variable [∀ i, NonAssocSemiring (f i)]

@[ext]
theorem RingHom.functions_ext [Finite I] (G : Type _) [NonAssocSemiring G] (g h : (∀ i, f i) →+* G)
    (H : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ f _ _ G _ (g : (∀ i, f i) →+ G) h H
#align ring_hom.functions_ext RingHom.functions_ext

end RingHom

namespace Prod

variable {α β γ : Type _} [CommMonoid α] [CommMonoid β] {s : Finset γ} {f : γ → α × β}

@[to_additive]
theorem fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1 :=
  (MonoidHom.fst α β).map_prod f s
#align prod.fst_prod Prod.fst_prod
#align prod.fst_sum Prod.fst_sum

@[to_additive]
theorem snd_prod : (∏ c in s, f c).2 = ∏ c in s, (f c).2 :=
  (MonoidHom.snd α β).map_prod f s
#align prod.snd_prod Prod.snd_prod
#align prod.snd_sum Prod.snd_sum

end Prod
