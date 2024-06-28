/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Set.Pointwise.Basic

#align_import algebra.hom.freiman from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms and isomorphism.

An `n`-Freiman homomorphism from `A` to `B` is a function `f : α → β` such that `f '' A ⊆ B` and
`f x₁ * ... * f xₙ = f y₁ * ... * f yₙ` for all `x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that
`x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any `MulHom` is a Freiman homomorphism.

An `n`-Freiman isomorphism from `A` to `B` is a function `f : α → β` bijective between `A` and `B`
such that `f x₁ * ... * f xₙ = f y₁ * ... * f yₙ ↔ x₁ * ... * xₙ = y₁ * ... * yₙ` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A`. In particular, any `MulEquiv` is a Freiman isomorphism.

They are of interest in additive combinatorics.

## Main declaration

* `IsMulFreimanHom`: Predicate for a function to be a multiplicative Freiman homomorphism.
* `IsAddFreimanHom`: Predicate for a function to be an additive Freiman homomorphism.
* `IsMulFreimanIso`: Predicate for a function to be a multiplicative Freiman isomorphism.
* `IsAddFreimanIso`: Predicate for a function to be an additive Freiman isomorphism.

## Implementation notes

In the context of combinatorics, we are interested in Freiman homomorphisms over sets which are not
necessarily closed under addition/multiplication. This means we must parametrize them with a set in
an `AddMonoid`/`Monoid` instead of the `AddMonoid`/`Monoid` itself.

## References

[Yufei Zhao, *18.225: Graph Theory and Additive Combinatorics*](https://yufeizhao.com/gtac/)

## TODO

* `MonoidHomClass.isMulFreimanHom` could be relaxed to `MulHom.toFreimanHom` by proving
  `(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.
* Affine maps are Freiman homs.
-/

open Multiset Set
open scoped Pointwise

variable {F α β γ : Type*}

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [CommMonoid γ] {A A₁ A₂ : Set α}
  {B B₁ B₂ : Set β} {C : Set γ} {f f₁ f₂ : α → β} {g : β → γ} {m n : ℕ}

/-- An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves sums
of `n` elements. -/
structure IsAddFreimanHom [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) (A : Set α) (B : Set β)
    (f : α → β) : Prop where
  mapsTo : MapsTo f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.sum = t.sum) :
    (s.map f).sum = (t.map f).sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
structure IsMulFreimanHom (n : ℕ) (A : Set α) (B : Set β) (f : α → β) : Prop where
  mapsTo : MapsTo f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.prod = t.prod) :
    (s.map f).prod = (t.map f).prod
#align map_prod_eq_map_prod IsMulFreimanHom.map_prod_eq_map_prod
#align map_sum_eq_map_sum IsAddFreimanHom.map_sum_eq_map_sum

/-- An additive `n`-Freiman homomorphism from a set `A` to a set `B` is a bijective map which
preserves sums of `n` elements. -/
structure IsAddFreimanIso [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) (A : Set α) (B : Set β)
    (f : α → β) : Prop where
  bijOn : BijOn f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).sum = (t.map f).sum ↔ s.sum = t.sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
structure IsMulFreimanIso (n : ℕ) (A : Set α) (B : Set β) (f : α → β) : Prop where
  bijOn : BijOn f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).prod = (t.map f).prod ↔ s.prod = t.prod

@[to_additive]
lemma IsMulFreimanIso.isMulFreimanHom (hf : IsMulFreimanIso n A B f) : IsMulFreimanHom n A B f where
  mapsTo := hf.bijOn.mapsTo
  map_prod_eq_map_prod _s _t hsA htA hs ht := (hf.map_prod_eq_map_prod hsA htA hs ht).2

@[to_additive]
lemma IsMulFreimanHom.mul_eq_mul (hf : IsMulFreimanHom 2 A B f) {a b c d : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (h : a * b = c * d) :
    f a * f b = f c * f d := by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]
#align map_mul_map_eq_map_mul_map IsMulFreimanHom.mul_eq_mul
#align map_add_map_eq_map_add_map IsAddFreimanHom.add_eq_add

@[to_additive]
lemma IsMulFreimanIso.mul_eq_mul (hf : IsMulFreimanIso 2 A B f) {a b c d : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    f a * f b = f c * f d ↔ a * b = c * d := by
  simp_rw [← prod_pair]
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) <;> simp [ha, hb, hc, hd]

/-- Characterisation of `2`-Freiman homs. -/
@[to_additive "Characterisation of `2`-Freiman homs."]
lemma isMulFreimanHom_two :
    IsMulFreimanHom 2 A B f ↔ MapsTo f A B ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a * b = c * d → f a * f b = f c * f d where
  mp hf := ⟨hf.mapsTo, fun a ha b hb c hc d hd ↦ hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp [Multiset.card_eq_two])⟩

@[to_additive] lemma isMulFreimanHom_id (hA : A₁ ⊆ A₂) : IsMulFreimanHom n A₁ A₂ id where
  mapsTo := hA
  map_prod_eq_map_prod s t _ _ _ _ h := by simpa using h

@[to_additive] lemma isMulFreimanIso_id : IsMulFreimanIso n A A id where
  bijOn := bijOn_id _
  map_prod_eq_map_prod s t _ _ _ _ := by simp

@[to_additive] lemma IsMulFreimanHom.comp (hg : IsMulFreimanHom n B C g)
    (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A C (g ∘ f) where
  mapsTo := hg.mapsTo.comp hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [← map_map, ← map_map]
    refine hg.map_prod_eq_map_prod ?_ ?_ (by rwa [card_map]) (by rwa [card_map])
      (hf.map_prod_eq_map_prod hsA htA hs ht h)
    · simpa using fun a h ↦ hf.mapsTo (hsA h)
    · simpa using fun a h ↦ hf.mapsTo (htA h)

@[to_additive] lemma IsMulFreimanIso.comp (hg : IsMulFreimanIso n B C g)
    (hf : IsMulFreimanIso n A B f) : IsMulFreimanIso n A C (g ∘ f) where
  bijOn := hg.bijOn.comp hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [← map_map, ← map_map]
    rw[ hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
      hf.map_prod_eq_map_prod hsA htA hs ht]
    · simpa using fun a h ↦ hf.bijOn.mapsTo (hsA h)
    · simpa using fun a h ↦ hf.bijOn.mapsTo (htA h)

@[to_additive] lemma IsMulFreimanHom.subset (hA : A₁ ⊆ A₂) (hf : IsMulFreimanHom n A₂ B₂ f)
    (hf' : MapsTo f A₁ B₁) : IsMulFreimanHom n A₁ B₁ f where
  mapsTo := hf'
  __ := hf.comp (isMulFreimanHom_id hA)

@[to_additive] lemma IsMulFreimanHom.superset (hB : B₁ ⊆ B₂) (hf : IsMulFreimanHom n A B₁ f) :
    IsMulFreimanHom n A B₂ f := (isMulFreimanHom_id hB).comp hf

@[to_additive] lemma IsMulFreimanIso.subset (hA : A₁ ⊆ A₂) (hf : IsMulFreimanIso n A₂ B₂ f)
    (hf' : BijOn f A₁ B₁) : IsMulFreimanIso n A₁ B₁ f where
  bijOn := hf'
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine hf.map_prod_eq_map_prod (fun a ha ↦ hA (hsA ha)) (fun a ha ↦ hA (htA ha)) hs ht

@[to_additive]
lemma isMulFreimanHom_const {b : β} (hb : b ∈ B) : IsMulFreimanHom n A B fun _ ↦ b where
  mapsTo _ _ := hb
  map_prod_eq_map_prod s t _ _ hs ht _ := by simp only [map_const', hs, prod_replicate, ht]

@[to_additive (attr := simp)]
lemma isMulFreimanIso_empty : IsMulFreimanIso n (∅ : Set α) (∅ : Set β) f where
  bijOn := bijOn_empty _
  map_prod_eq_map_prod s t hs ht := by
    simp [eq_zero_of_forall_not_mem hs, eq_zero_of_forall_not_mem ht]

@[to_additive] lemma IsMulFreimanHom.mul (h₁ : IsMulFreimanHom n A B₁ f₁)
    (h₂ : IsMulFreimanHom n A B₂ f₂) : IsMulFreimanHom n A (B₁ * B₂) (f₁ * f₂) where
  -- TODO: Extract `Set.MapsTo.mul` from this proof
  mapsTo a ha := mul_mem_mul (h₁.mapsTo ha) (h₂.mapsTo ha)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.mul_def, prod_map_mul, prod_map_mul, h₁.map_prod_eq_map_prod hsA htA hs ht h,
      h₂.map_prod_eq_map_prod hsA htA hs ht h]

@[to_additive] lemma MonoidHomClass.isMulFreimanHom [FunLike F α β] [MonoidHomClass F α β] (f : F)
    (hfAB : MapsTo f A B) : IsMulFreimanHom n A B f where
  mapsTo := hfAB
  map_prod_eq_map_prod s t _ _ _ _ h := by rw [← map_multiset_prod, h, map_multiset_prod]

@[to_additive] lemma MulEquivClass.isMulFreimanIso [EquivLike F α β] [MulEquivClass F α β] (f : F)
    (hfAB : BijOn f A B) : IsMulFreimanIso n A B f where
  bijOn := hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod, ← map_multiset_prod, EquivLike.apply_eq_iff_eq]

end CommMonoid

section CancelCommMonoid
variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.mono (hmn : m ≤ n) (hf : IsMulFreimanHom n A B f) :
    IsMulFreimanHom m A B f where
  mapsTo := hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    obtain rfl | hm := m.eq_zero_or_pos
    · rw [card_eq_zero] at hs ht
      rw [hs, ht]
    simp only [← hs, card_pos_iff_exists_mem] at hm
    obtain ⟨a, ha⟩ := hm
    suffices ((s + replicate (n - m) a).map f).prod = ((t + replicate (n - m) a).map f).prod by
      simp_rw [Multiset.map_add, prod_add] at this
      exact mul_right_cancel this
    replace ha := hsA ha
    refine hf.map_prod_eq_map_prod (fun a ha ↦ ?_) (fun a ha ↦ ?_) ?_ ?_ ?_
    · rw [Multiset.mem_add] at ha
      obtain ha | ha := ha
      · exact hsA ha
      · rwa [eq_of_mem_replicate ha]
    · rw [Multiset.mem_add] at ha
      obtain ha | ha := ha
      · exact htA ha
      · rwa [eq_of_mem_replicate ha]
    · rw [_root_.map_add, card_replicate, hs, Nat.add_sub_cancel' hmn]
    · rw [_root_.map_add, card_replicate, ht, Nat.add_sub_cancel' hmn]
    · rw [prod_add, prod_add, h]
#align map_prod_eq_map_prod_of_le IsMulFreimanHom.mono
#align map_sum_eq_map_sum_of_le IsAddFreimanHom.mono

end CancelCommMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
lemma IsMulFreimanIso.mono {hmn : m ≤ n} (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso m A B f where
  bijOn := hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    obtain rfl | hm := m.eq_zero_or_pos
    · rw [card_eq_zero] at hs ht
      simp [hs, ht]
    simp only [← hs, card_pos_iff_exists_mem] at hm
    obtain ⟨a, ha⟩ := hm
    suffices
      ((s + replicate (n - m) a).map f).prod = ((t + replicate (n - m) a).map f).prod ↔
      (s + replicate (n - m) a).prod = (t + replicate (n - m) a).prod by
      simpa only [Multiset.map_add, prod_add, mul_right_cancel_iff] using this
    replace ha := hsA ha
    refine hf.map_prod_eq_map_prod (fun a ha ↦ ?_) (fun a ha ↦ ?_) ?_ ?_
    · rw [Multiset.mem_add] at ha
      obtain ha | ha := ha
      · exact hsA ha
      · rwa [eq_of_mem_replicate ha]
    · rw [Multiset.mem_add] at ha
      obtain ha | ha := ha
      · exact htA ha
      · rwa [eq_of_mem_replicate ha]
    · rw [_root_.map_add, card_replicate, hs, Nat.add_sub_cancel' hmn]
    · rw [_root_.map_add, card_replicate, ht, Nat.add_sub_cancel' hmn]

end CancelCommMonoid

section DivisionCommMonoid
variable [CommMonoid α] [DivisionCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.inv (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A B⁻¹ f⁻¹ where
  -- TODO: Extract `Set.MapsTo.inv` from this proof
  mapsTo a ha := inv_mem_inv.2 (hf.mapsTo ha)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.inv_def, prod_map_inv, prod_map_inv, hf.map_prod_eq_map_prod hsA htA hs ht h]

@[to_additive] lemma IsMulFreimanHom.div {β : Type*} [DivisionCommMonoid β] {B₁ B₂ : Set β}
    {f₁ f₂ : α → β} (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ / B₂) (f₁ / f₂) where
  -- TODO: Extract `Set.MapsTo.div` from this proof
  mapsTo a ha := div_mem_div (h₁.mapsTo ha) (h₂.mapsTo ha)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.div_def, prod_map_div, prod_map_div, h₁.map_prod_eq_map_prod hsA htA hs ht h,
      h₂.map_prod_eq_map_prod hsA htA hs ht h]

end DivisionCommMonoid

section Prod
variable {α₁ α₂ β₁ β₂ : Type*} [CommMonoid α₁] [CommMonoid α₂] [CommMonoid β₁] [CommMonoid β₂]
  {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.prod (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂) :
    IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) where
  mapsTo := h₁.mapsTo.prodMap h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp only [mem_prod, forall_and, Prod.forall] at hsA htA
    simp only [Prod.ext_iff, fst_prod, snd_prod, map_map, Function.comp_apply, Prod.map_fst,
      Prod.map_snd] at h ⊢
    rw [← Function.comp_def, ← map_map, ← map_map, ← Function.comp_def f₂, ← map_map, ← map_map]
    exact ⟨h₁.map_prod_eq_map_prod (by simpa using hsA.1) (by simpa using htA.1) (by simpa)
      (by simpa) h.1, h₂.map_prod_eq_map_prod (by simpa [@forall_swap α₁] using hsA.2)
      (by simpa [@forall_swap α₁] using htA.2) (by simpa) (by simpa) h.2⟩

@[to_additive]
lemma IsMulFreimanIso.prod (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreimanIso n A₂ B₂ f₂) :
    IsMulFreimanIso n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) where
  bijOn := h₁.bijOn.prodMap h₂.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    simp only [mem_prod, forall_and, Prod.forall] at hsA htA
    simp only [Prod.ext_iff, fst_prod, map_map, Function.comp_apply, Prod.map_fst, snd_prod,
      Prod.map_snd]
    rw [← Function.comp_def, ← map_map, ← map_map, ← Function.comp_def f₂, ← map_map, ← map_map,
      h₁.map_prod_eq_map_prod (by simpa using hsA.1) (by simpa using htA.1) (by simpa) (by simpa),
      h₂.map_prod_eq_map_prod (by simpa [@forall_swap α₁] using hsA.2)
      (by simpa [@forall_swap α₁] using htA.2) (by simpa) (by simpa)]

end Prod

namespace Fin
variable {k m n : ℕ}

private lemma aux (hm : m ≠ 0) (hkmn : m * k ≤ n) : k < (n + 1) :=
  Nat.lt_succ_iff.2 $ le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn

/-- **No wrap-around principle**.

The first `k + 1` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the first `k + 1` elements
of `ℕ` assuming there is no wrap-around. -/
lemma isAddFreimanIso_Iic (hm : m ≠ 0) (hkmn : m * k ≤ n) :
    IsAddFreimanIso m (Iic (k : Fin (n + 1))) (Iic k) val where
  bijOn.left := by simp [MapsTo, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt, aux hm hkmn]
  bijOn.right.left := val_injective.injOn
  bijOn.right.right x (hx : x ≤ _) :=
    ⟨x, by simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn, hx.trans_lt]⟩
  map_sum_eq_map_sum s t hsA htA hs ht := by
    have (u : Multiset (Fin (n + 1))) : Nat.castRingHom _ (u.map val).sum = u.sum := by simp
    rw [← this, ← this]
    have {u : Multiset (Fin (n + 1))} (huk : ∀ x ∈ u, x ≤ k) (hu : card u = m) :
        (u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 $ hkmn.trans' $ by
      rw [← hu, ← card_map]
      refine sum_le_card_nsmul (u.map val) k ?_
      simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn] using huk
    exact ⟨congr_arg _, CharP.natCast_injOn_Iio _ (n + 1) (this hsA hs) (this htA ht)⟩

/-- **No wrap-around principle**.

The first `k` elements of `Fin (n + 1)` are `m`-Freiman isomorphic to the first `k` elements of `ℕ`
assuming there is no wrap-around. -/
lemma isAddFreimanIso_Iio (hm : m ≠ 0) (hkmn : m * k ≤ n) :
    IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val := by
  obtain _ | k := k
  · simp [← bot_eq_zero]; simp [← _root_.bot_eq_zero, -Nat.bot_eq_zero, -bot_eq_zero']
  have hkmn' : m * k ≤ n := (Nat.mul_le_mul_left _ k.le_succ).trans hkmn
  convert isAddFreimanIso_Iic hm hkmn' using 1 <;> ext x
  · simp [lt_iff_val_lt_val, le_iff_val_le_val, -val_fin_le, -val_fin_lt, Nat.mod_eq_of_lt,
      aux hm hkmn']
    simp_rw [← Nat.cast_add_one]
    rw [Fin.val_cast_of_lt (aux hm hkmn), Nat.lt_succ_iff]
  · simp [Nat.succ_eq_add_one, Nat.lt_succ_iff]

end Fin

#noalign add_freiman_hom
#noalign freiman_hom
#noalign add_freiman_hom_class
#noalign freiman_hom_class
#noalign freiman_hom.fun_like
#noalign add_freiman_hom.fun_like
#noalign freiman_hom.freiman_hom_class
#noalign add_freiman_hom.freiman_hom_class
#noalign freiman_hom.to_fun_eq_coe
#noalign add_freiman_hom.to_fun_eq_coe
#noalign freiman_hom.ext
#noalign add_freiman_hom.ext
#noalign freiman_hom.coe_mk
#noalign add_freiman_hom.coe_nat_eq_mk
#noalign freiman_hom.mk_coe
#noalign add_freiman_hom.mk_coe
#noalign add_freiman_hom.id
#noalign freiman_hom.id_apply
#noalign freiman_hom.comp
#noalign add_freiman_hom.comp
#noalign freiman_hom.coe_comp
#noalign add_freiman_hom.coe_comp
#noalign freiman_hom.comp_apply
#noalign add_freiman_hom.comp_apply
#noalign freiman_hom.comp_assoc
#noalign add_freiman_hom.comp_assoc
#noalign freiman_hom.cancel_right
#noalign add_freiman_hom.cancel_right
#noalign freiman_hom.cancel_right_on
#noalign add_freiman_hom.cancel_right_on
#noalign freiman_hom.cancel_left_on
#noalign add_freiman_hom.cancel_left_on
#noalign freiman_hom.comp_id
#noalign add_freiman_hom.comp_id
#noalign freiman_hom.id_comp
#noalign add_freiman_hom.id_comp
#noalign freiman_hom.const
#noalign add_freiman_hom.const
#noalign freiman_hom.const_apply
#noalign add_freiman_hom.const_apply
#noalign freiman_hom.const_comp
#noalign add_freiman_hom.const_comp
#noalign freiman_hom.one_apply
#noalign add_freiman_hom.zero_apply
#noalign freiman_hom.one_comp
#noalign add_freiman_hom.zero_comp
#noalign freiman_hom.mul_apply
#noalign add_freiman_hom.add_apply
#noalign freiman_hom.mul_comp
#noalign add_freiman_hom.add_comp
#noalign freiman_hom.inv_apply
#noalign add_freiman_hom.neg_apply
#noalign freiman_hom.inv_comp
#noalign add_freiman_hom.neg_comp
#noalign freiman_hom.div_apply
#noalign add_freiman_hom.sub_apply
#noalign freiman_hom.div_comp
#noalign add_freiman_hom.sub_comp
#noalign freiman_hom.comm_monoid
#noalign add_freiman_hom.add_comm_monoid
#noalign freiman_hom.comm_group
#noalign add_freiman_hom.add_comm_group
#noalign monoid_hom.freiman_hom_class
#noalign add_monoid_hom.freiman_hom_class
#noalign monoid_hom.to_freiman_hom
#noalign add_monoid_hom.to_add_freiman_hom
#noalign monoid_hom.to_freiman_hom_coe
#noalign add_monoid_hom.to_freiman_hom_coe
#noalign monoid_hom.to_freiman_hom_injective
#noalign add_monoid_hom.to_freiman_hom_injective
#noalign freiman_hom.to_freiman_hom
#noalign add_freiman_hom.to_add_freiman_hom
#noalign freiman_hom.freiman_hom_class_of_le
#noalign add_freiman_hom.add_freiman_hom_class_of_le
#noalign freiman_hom.to_freiman_hom_coe
#noalign add_freiman_hom.to_add_freiman_hom_coe
#noalign freiman_hom.to_freiman_hom_injective
#noalign add_freiman_hom.to_freiman_hom_injective
