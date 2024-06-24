/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Pi
import Mathlib.GroupTheory.GroupAction.Pi

#align_import algebra.big_operators.pi from "leanprover-community/mathlib"@"fa2309577c7009ea243cffdf990cd6c84f0ad497"

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/


namespace Pi

@[to_additive]
theorem list_prod_apply {α : Type*} {β : α → Type*} [∀ a, Monoid (β a)] (a : α)
    (l : List (∀ a, β a)) : l.prod a = (l.map fun f : ∀ a, β a ↦ f a).prod :=
  map_list_prod (evalMonoidHom β a) _
#align pi.list_prod_apply Pi.list_prod_apply
#align pi.list_sum_apply Pi.list_sum_apply

@[to_additive]
theorem multiset_prod_apply {α : Type*} {β : α → Type*} [∀ a, CommMonoid (β a)] (a : α)
    (s : Multiset (∀ a, β a)) : s.prod a = (s.map fun f : ∀ a, β a ↦ f a).prod :=
  (evalMonoidHom β a).map_multiset_prod _
#align pi.multiset_prod_apply Pi.multiset_prod_apply
#align pi.multiset_sum_apply Pi.multiset_sum_apply

end Pi

@[to_additive (attr := simp)]
theorem Finset.prod_apply {α : Type*} {β : α → Type*} {γ} [∀ a, CommMonoid (β a)] (a : α)
    (s : Finset γ) (g : γ → ∀ a, β a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a :=
  map_prod (Pi.evalMonoidHom β a) _ _
#align finset.prod_apply Finset.prod_apply
#align finset.sum_apply Finset.sum_apply

/-- An 'unapplied' analogue of `Finset.prod_apply`. -/
@[to_additive "An 'unapplied' analogue of `Finset.sum_apply`."]
theorem Finset.prod_fn {α : Type*} {β : α → Type*} {γ} [∀ a, CommMonoid (β a)] (s : Finset γ)
    (g : γ → ∀ a, β a) : ∏ c ∈ s, g c = fun a ↦ ∏ c ∈ s, g c a :=
  funext fun _ ↦ Finset.prod_apply _ _ _
#align finset.prod_fn Finset.prod_fn
#align finset.sum_fn Finset.sum_fn

@[to_additive]
theorem Fintype.prod_apply {α : Type*} {β : α → Type*} {γ : Type*} [Fintype γ]
    [∀ a, CommMonoid (β a)] (a : α) (g : γ → ∀ a, β a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g
#align fintype.prod_apply Fintype.prod_apply
#align fintype.sum_apply Fintype.sum_apply

@[to_additive prod_mk_sum]
theorem prod_mk_prod {α β γ : Type*} [CommMonoid α] [CommMonoid β] (s : Finset γ) (f : γ → α)
    (g : γ → β) : (∏ x ∈ s, f x, ∏ x ∈ s, g x) = ∏ x ∈ s, (f x, g x) :=
  haveI := Classical.decEq γ
  Finset.induction_on s rfl (by simp (config := { contextual := true }) [Prod.ext_iff])
#align prod_mk_prod prod_mk_prod
#align prod_mk_sum prod_mk_sum

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Semiring R]
    (x : ι → R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  simp
#align pi_eq_sum_univ pi_eq_sum_univ

section MulSingle

variable {I : Type*} [DecidableEq I] {Z : I → Type*}
variable [∀ i, CommMonoid (Z i)]

@[to_additive]
theorem Finset.univ_prod_mulSingle [Fintype I] (f : ∀ i, Z i) :
    (∏ i, Pi.mulSingle i (f i)) = f := by
  ext a
  simp
#align finset.univ_prod_mul_single Finset.univ_prod_mulSingle
#align finset.univ_sum_single Finset.univ_sum_single

@[to_additive]
theorem MonoidHom.functions_ext [Finite I] (G : Type*) [CommMonoid G] (g h : (∀ i, Z i) →* G)
    (H : ∀ i x, g (Pi.mulSingle i x) = h (Pi.mulSingle i x)) : g = h := by
  cases nonempty_fintype I
  ext k
  rw [← Finset.univ_prod_mulSingle k, map_prod, map_prod]
  simp only [H]
#align monoid_hom.functions_ext MonoidHom.functions_ext
#align add_monoid_hom.functions_ext AddMonoidHom.functions_ext

/-- This is used as the ext lemma instead of `MonoidHom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext)
      "\nThis is used as the ext lemma instead of `AddMonoidHom.functions_ext` for reasons
      explained in note [partially-applied ext lemmas]."]
theorem MonoidHom.functions_ext' [Finite I] (M : Type*) [CommMonoid M] (g h : (∀ i, Z i) →* M)
    (H : ∀ i, g.comp (MonoidHom.mulSingle Z i) = h.comp (MonoidHom.mulSingle Z i)) : g = h :=
  g.functions_ext M h fun i => DFunLike.congr_fun (H i)
#align monoid_hom.functions_ext' MonoidHom.functions_ext'
#align add_monoid_hom.functions_ext' AddMonoidHom.functions_ext'

end MulSingle

section RingHom

open Pi

variable {I : Type*} [DecidableEq I] {f : I → Type*}
variable [∀ i, NonAssocSemiring (f i)]

@[ext]
theorem RingHom.functions_ext [Finite I] (G : Type*) [NonAssocSemiring G] (g h : (∀ i, f i) →+* G)
    (H : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_addMonoidHom_injective <|
    @AddMonoidHom.functions_ext I _ f _ _ G _ (g : (∀ i, f i) →+ G) h H
#align ring_hom.functions_ext RingHom.functions_ext

end RingHom

namespace Prod

variable {α β γ : Type*} [CommMonoid α] [CommMonoid β] {s : Finset γ} {f : γ → α × β}

@[to_additive]
theorem fst_prod : (∏ c ∈ s, f c).1 = ∏ c ∈ s, (f c).1 :=
  map_prod (MonoidHom.fst α β) f s
#align prod.fst_prod Prod.fst_prod
#align prod.fst_sum Prod.fst_sum

@[to_additive]
theorem snd_prod : (∏ c ∈ s, f c).2 = ∏ c ∈ s, (f c).2 :=
  map_prod (MonoidHom.snd α β) f s
#align prod.snd_prod Prod.snd_prod
#align prod.snd_sum Prod.snd_sum

end Prod
