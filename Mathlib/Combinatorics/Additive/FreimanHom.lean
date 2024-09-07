/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Pointwise.Set
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.ZMod.Defs

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms and isomorphism.

An `n`-Freiman homomorphism from `A` to `B` is a function `f : α → β` such that `f '' A ⊆ B` and
`f x₁ * ... * f xₙ = f y₁ * ... * f yₙ` for all `x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that
`x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any `MulHom` is a Freiman homomorphism.

Note a `0`- or `1`-Freiman homomorphism is simply a map, thus a `2`-Freiman homomorphism is the
first interesting case (and the most common). As `n` increases further, the property of being
an `n`-Freiman homomorphism between abelian groups becomes increasingly stronger.

An `n`-Freiman isomorphism from `A` to `B` is a function `f : α → β` bijective between `A` and `B`
such that `f x₁ * ... * f xₙ = f y₁ * ... * f yₙ ↔ x₁ * ... * xₙ = y₁ * ... * yₙ` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A`. In particular, any `MulEquiv` is a Freiman isomorphism.

They are of interest in additive combinatorics.

## Main declarations

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

lemma IsMulFreimanHom.congr (hf₁ : IsMulFreimanHom n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanHom n A B f₂ where
  mapsTo := hf₁.mapsTo.congr h
  map_prod_eq_map_prod s t hsA htA hs ht h' := by
    rw [map_congr rfl fun x hx => (h (hsA hx)).symm, map_congr rfl fun x hx => (h (htA hx)).symm,
      hf₁.map_prod_eq_map_prod hsA htA hs ht h']

lemma IsMulFreimanIso.congr (hf₁ : IsMulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanIso n A B f₂ where
  bijOn := hf₁.bijOn.congr h
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [map_congr rfl fun x hx => h.symm (hsA hx), map_congr rfl fun x hx => h.symm (htA hx),
      hf₁.map_prod_eq_map_prod hsA htA hs ht]

/--
Given a Freiman isomorphism `f` from `A` to `B`, if `g` maps `B` into `A`, and is a right inverse
to `f` on `B`, then `g` is a Freiman isomorphism from `B` to `A`.
-/
@[to_additive]
lemma IsMulFreimanIso.symm {g : β → α} (hg₁ : MapsTo g B A) (hg₂ : RightInvOn g f B)
    (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A g where
  bijOn := hf.bijOn.symm ⟨hg₂, InjOn.rightInvOn_of_leftInvOn hf.bijOn.injOn hg₂ hf.bijOn.mapsTo hg₁⟩
  map_prod_eq_map_prod := fun s t hsB htB hs ht => by
    rw [←hf.map_prod_eq_map_prod _ _ (by simp [hs]) (by simp [ht]), map_map, map_congr rfl, map_id,
      map_map, map_congr rfl, map_id]
    all_goals aesop

/--
If the inverse of a Freiman homomorphism is itself a Freiman homomorphism, then it is a Freiman
isomorphism.
-/
@[to_additive]
lemma IsMulFreimanHom.toIsMulFreimanIso {g : β → α} (h : InvOn g f A B)
    (hf : IsMulFreimanHom n A B f) (hg : IsMulFreimanHom n B A g) :
    IsMulFreimanIso n A B f where
  bijOn := h.bijOn hf.mapsTo hg.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine ⟨fun h' => ?_, hf.map_prod_eq_map_prod hsA htA hs ht⟩
    have : (map g (map f s)).prod = (map g (map f t)).prod := by
      have := hf.mapsTo
      refine hg.map_prod_eq_map_prod ?_ ?_ ?_ ?_ h' <;> aesop (add simp MapsTo)
    rwa [map_map, map_congr rfl fun x hx => ?g1, map_id,
      map_map, map_congr rfl fun x hx => ?g2, map_id] at this
    case g1 => exact h.1 (hsA hx)
    case g2 => exact h.1 (htA hx)

@[to_additive]
lemma IsMulFreimanIso.isMulFreimanIso_invFunOn (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A (f.invFunOn A) :=
  hf.symm hf.bijOn.surjOn.mapsTo_invFunOn hf.bijOn.surjOn.rightInvOn_invFunOn

/-- A version of the Freiman homomorphism condition expressed using `Finset`s, for practicality. -/
@[to_additive] lemma IsMulFreimanHom.prod_apply (hf : IsMulFreimanHom n A B f) {s t : Finset α}
    {hsA : s.toSet ⊆ A} {htA : t.toSet ⊆ A}
    (hs : s.card = n) (ht : t.card = n) :
    ∏ i ∈ s, i = ∏ i ∈ t, i → ∏ i in s, f i = ∏ i in t, f i := by
  simpa using hf.map_prod_eq_map_prod hsA htA hs ht

@[to_additive]
lemma IsMulFreimanHom.mul_eq_mul (hf : IsMulFreimanHom 2 A B f) {a b c d : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (h : a * b = c * d) :
    f a * f b = f c * f d := by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]

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
    rw [hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
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
lemma isMulFreimanHom_zero_iff : IsMulFreimanHom 0 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop⟩⟩

@[to_additive (attr := simp)]
lemma isMulFreimanIso_zero_iff : IsMulFreimanIso 0 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by aesop⟩⟩

@[to_additive (attr := simp) isAddFreimanHom_one_iff]
lemma isMulFreimanHom_one_iff : IsMulFreimanHom 1 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop (add simp card_eq_one)⟩⟩

@[to_additive (attr := simp) isAddFreimanIso_one_iff]
lemma isMulFreimanIso_one_iff : IsMulFreimanIso 1 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by aesop (add simp [card_eq_one, BijOn])⟩⟩

@[to_additive (attr := simp)]
lemma isMulFreimanHom_empty : IsMulFreimanHom n (∅ : Set α) B f where
  mapsTo := mapsTo_empty f B
  map_prod_eq_map_prod s t := by aesop (add simp eq_zero_of_forall_not_mem)

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

theorem List.length_eq_succ {α : Type*} {n} {l : List α} :
    l.length = n + 1 ↔ ∃ h t, h :: t = l ∧ t.length = n := by cases l <;> aesop

theorem card_eq_succ {α : Type*} {s : Multiset α} :
    card s = n + 1 ↔ ∃ a t, a ::ₘ t = s ∧ card t = n := by
  refine ⟨?_, by aesop⟩
  induction s using Quot.inductionOn with
  | h s =>
      simp only [quot_mk_to_coe'', coe_card, List.length_eq_succ, forall_exists_index, and_imp]
      rintro a s rfl rfl
      exact ⟨a, s, rfl, rfl⟩

@[to_additive] lemma MulHomClass.isMulFreimanHom [FunLike F α β] [MulHomClass F α β] (f : F)
    (hfAB : MapsTo f A B) : IsMulFreimanHom n A B f :=
  match n with
  | 0 => by simpa
  | n + 1 => IsMulFreimanHom.mk hfAB fun s t hsA htA hs ht h => by
      rw [← map_multiset_prod_ne_zero _ (by aesop), h, map_multiset_prod_ne_zero _ (by aesop)]

@[to_additive] lemma MulEquivClass.isMulFreimanIso [EquivLike F α β] [MulEquivClass F α β] (f : F)
    (hfAB : BijOn f A B) : IsMulFreimanIso n A B f where
  bijOn := hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod, ← map_multiset_prod, EquivLike.apply_eq_iff_eq]

end CommMonoid

section CancelCommMonoid
variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
lemma isMulFreimanHom_antitone : Antitone (IsMulFreimanHom · A B f) :=
  antitone_nat_of_succ_le fun n hf =>
  { mapsTo := hf.mapsTo,
    map_prod_eq_map_prod := fun s t hsA htA hs _ h => match n with
      | 0 => by aesop
      | n + 1 =>
          have ⟨a, ha⟩ : ∃ a, a ∈ s := card_pos_iff_exists_mem.1 (by simp [hs])
          by simpa [*] using hf.map_prod_eq_map_prod (s := a ::ₘ s) (t := a ::ₘ t)
              (by simpa [hsA ha]) (by simpa [hsA ha]) }

@[to_additive]
lemma IsMulFreimanHom.mono (hmn : m ≤ n) (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom m A B f :=
  isMulFreimanHom_antitone hmn hf

end CancelCommMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α → β} {m n : ℕ}

@[to_additive]
lemma IsMulFreimanIso.mono {hmn : m ≤ n} (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso m A B f :=
  (hf.isMulFreimanHom.mono hmn).toIsMulFreimanIso hf.bijOn.invOn_invFunOn
    (hf.isMulFreimanIso_invFunOn.isMulFreimanHom.mono hmn)

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

@[to_additive]
lemma IsMulFreimanHom.fst [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : ℕ} :
    IsMulFreimanHom n (A ×ˢ B) A Prod.fst :=
  MulHomClass.isMulFreimanHom (MonoidHom.fst _ _) mapsTo_fst

@[to_additive]
lemma IsMulFreimanHom.snd [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : ℕ} :
    IsMulFreimanHom n (A ×ˢ B) B Prod.snd :=
  MulHomClass.isMulFreimanHom (MonoidHom.snd _ _) mapsTo_snd

section

variable {α β₁ β₂ : Type*} [CommMonoid α] [CommMonoid β₁] [CommMonoid β₂]
  {A : Set α} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂} {n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.prodMk (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ ×ˢ B₂) (fun x => (f₁ x, f₂ x)) where
  mapsTo := fun x hx => mk_mem_prod (h₁.mapsTo hx) (h₂.mapsTo hx)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp [Prod.ext_iff, fst_prod, snd_prod,
      h₁.map_prod_eq_map_prod hsA htA hs ht h, h₂.map_prod_eq_map_prod hsA htA hs ht h]

end

section

variable {α₁ α₂ β₁ β₂ : Type*} [CommMonoid α₁] [CommMonoid α₂] [CommMonoid β₁] [CommMonoid β₂]
  {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.prodMap (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂) :
    IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.comp .fst).prodMk (h₂.comp .snd)

@[to_additive]
lemma IsMulFreimanIso.prodMap (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreimanIso n A₂ B₂ f₂) :
    IsMulFreimanIso n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.isMulFreimanHom.prodMap h₂.isMulFreimanHom).toIsMulFreimanIso
    (h₁.bijOn.invOn_invFunOn.prodMap h₂.bijOn.invOn_invFunOn)
    (h₁.isMulFreimanIso_invFunOn.isMulFreimanHom.prodMap
     h₂.isMulFreimanIso_invFunOn.isMulFreimanHom)

end

end Prod

namespace Fin
variable {k m n : ℕ}

private lemma aux (hm : m ≠ 0) (hkmn : m * k ≤ n) : k < (n + 1) :=
  Nat.lt_succ_iff.2 <| le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn

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
        (u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 <| hkmn.trans' <| by
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
  · simp [Nat.lt_succ_iff]

end Fin
