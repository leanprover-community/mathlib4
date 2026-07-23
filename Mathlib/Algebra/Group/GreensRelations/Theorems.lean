/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.MulSeq
public import Mathlib.Data.Fintype.Card

/-!
# Main Theorems of Green's Relations

This file proves the major structural theorems regarding Green's relations,
including Green's theorem (bijections between H-classes), the equivalence of D and J
in finite semigroups, and conditions for H-classes to be subgroups.
## References

* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

public section

variable {S : Type*} [Semigroup S]

open MulSeq

section MonotonicityAndCommutativity

/-- Right multiplication preserves Green's `L`-relation. -/
theorem isGreenL_mul_right {a b c : S} (h : IsGreenL a b) :
IsGreenL (a * c) (b * c) := IsGreenL.mul_right c h

/-- Left multiplication preserves Green's `R`-relation. -/
theorem isGreenR_mul_left {a b c : S} (h : IsGreenR a b) :
    IsGreenR (c * a) (c * b) := IsGreenR.mul_left c h

/-- Equivalence of `L ∘ R` and `R ∘ L` compositions in the definition of Green's `D`-relation. -/
theorem isGreenD_commutes_L_R {a b : S} :
    (∃ c, IsGreenL a c ∧ IsGreenR c b) ↔ (∃ c', IsGreenR a c' ∧ IsGreenL c' b) :=
  ⟨fun ⟨_, hL, hR⟩ ↦ isGreenL_commutes_isGreenR hL hR,
   fun ⟨_, hR, hL⟩ ↦ by
     obtain ⟨z, hRz, hLz⟩ := isGreenL_commutes_isGreenR hL.symm hR.symm
     exact ⟨z, hLz.symm, hRz.symm⟩⟩

end MonotonicityAndCommutativity

section RegularDClassesCharacterizations

/-- A `D`-class is regular if and only if it contains an idempotent. -/
theorem isRegularDClass_iff_exists_idempotent (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · intro hReg
    obtain ⟨s, hs⟩ := hReg x₀ (IsGreenD.refl x₀)
    exact ⟨x₀ * s, ⟨x₀ * s, IsGreenL.refl _, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨x₀, hs.symm⟩⟩⟩,
      by rw [← mul_assoc, hs]⟩
  · rintro ⟨e, heD, he_idem⟩ y hyD
    let ⟨z, hL_yz, hR_ze⟩ := hyD.trans heD.symm
    have h_ez_z : e * z = z := by
      rcases hR_ze.left with rfl | ⟨v, rfl⟩
      · exact he_idem
      · rw [← mul_assoc, he_idem]
    obtain ⟨u, hu_z⟩ : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, rfl⟩
      · exact ⟨e, by rw [he_idem, he_idem]⟩
      · exact ⟨u, h_ez_z⟩
    have hy_uz : y * u * z = y := by
      rcases hL_yz.left with rfl | ⟨p, rfl⟩
      · exact hu_z
      · rw [mul_assoc p, mul_assoc, hu_z]
    rcases hL_yz.right with rfl | ⟨q, rfl⟩
    · exact ⟨u, hy_uz⟩
    · exact ⟨u * q, by simpa [mul_assoc] using hy_uz⟩

/-- A `D`-class is regular if and only if every `L`-class inside it contains an idempotent. -/
theorem isRegularDClass_iff_forall_LClass_has_idempotent
    (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∀ L : Set S, (∃ x ∈ D, L = IsGreenL.eqvClass x) → ∃ e ∈ L, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · rintro hReg L ⟨x, hx, rfl⟩
    exact exists_idempotent_in_greenL_of_regular (hReg x hx)
  · intro H x hx
    obtain ⟨e, he, he_idem⟩ := H (IsGreenL.eqvClass x) ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, e = u * x := by
      rcases he.left with h | ⟨u, hu⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨u, hu⟩
    obtain ⟨v, hv⟩ : ∃ v, x = v * e := by
      rcases he.right with h | ⟨v, hv⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨v, hv⟩
    exact ⟨u, by rw [mul_assoc, ← hu, hv, mul_assoc, he_idem]⟩

/-- A `D`-class is regular if and only if every `R`-class inside it contains an idempotent. -/
theorem isRegularDClass_iff_forall_RClass_has_idempotent
    (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∀ R : Set S, (∃ x ∈ D, R = IsGreenR.eqvClass x) → ∃ e ∈ R, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · rintro hReg R ⟨x, hx, rfl⟩
    exact exists_idempotent_in_greenR_of_regular (hReg x hx)
  · intro H x hx
    obtain ⟨e, he, he_idem⟩ := H (IsGreenR.eqvClass x) ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, e = x * u := by
      rcases he.left with h | ⟨u, hu⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨u, hu⟩
    obtain ⟨v, hv⟩ : ∃ v, x = e * v := by
      rcases he.right with h | ⟨v, hv⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨v, hv⟩
    exact ⟨u, by rw [← hu, hv, ← mul_assoc, he_idem]⟩

end RegularDClassesCharacterizations

section BijectionsAndCardinalities

/-- A bijection between the `H`-classes of two `L`-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h_L_ab : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases ha_eq_b : a = b
  · exact ha_eq_b ▸ Equiv.refl _
  · choose w hw using h_L_ab.left.resolve_left ha_eq_b
    choose z hz using h_L_ab.right.resolve_left (Ne.symm ha_eq_b)
    have hwza : w * z * a = a := by simp only [mul_assoc, ← hz, ← hw]
    have hzwb : z * w * b = b := by simp only [mul_assoc, ← hw, ← hz]
    exact {
      toFun := fun ⟨x, hL, hR⟩ ↦ ⟨z * x, ⟨IsGreenL.trans ⟨Or.inr ⟨z, rfl⟩,
        Or.inr ⟨w, by simpa [← mul_assoc] using (IsGreenR.cancellation hR hwza).symm⟩⟩
        (hL.trans h_L_ab), hz.symm ▸ IsGreenR.mul_left z hR⟩⟩
      invFun := fun ⟨y, hL, hR⟩ ↦ ⟨w * y, ⟨IsGreenL.trans ⟨Or.inr ⟨w, rfl⟩,
        Or.inr ⟨z, by simpa [← mul_assoc] using (IsGreenR.cancellation hR hzwb).symm⟩⟩
        (hL.trans h_L_ab.symm), hw.symm ▸ IsGreenR.mul_left w hR⟩⟩
      left_inv := fun ⟨x, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hwza
      right_inv := fun ⟨y, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hzwb
    }

open MulOpposite in
/-- A bijection between the `H`-classes of two `R`-related elements. -/
noncomputable def equivHClassOfIsGreenR {a b : S} (h : IsGreenR a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b :=
  (IsGreenH.equivHClassOp a).trans
      ((equivHClassOfIsGreenL (isGreenR_iff_isGreenL_op.mp h)).trans
      (IsGreenH.equivHClassOp b).symm)

open Classical in
/-- Any two `H`-classes within the same `D`-class have the same cardinality. -/
theorem card_greenHClass_eq_of_isGreenD [Fintype S] {a b : S} (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) :=
  let ⟨_, hL, hR⟩ := h
  Eq.trans (Fintype.card_congr (equivHClassOfIsGreenL hL))
    (Fintype.card_congr (equivHClassOfIsGreenR hR))

/-- If `a` and `b` are `J`-related in a finite semigroup, they are also `D`-related. -/
theorem isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b :=
  match h.left, h.right with
  | .of_eq h1, _ => h1 ▸ IsGreenD.refl a
  | _, .of_eq h2 => h2.symm ▸ IsGreenD.refl b
  | .mul_left _ hu1, .mul_left _ hu2 => isGreenD_of_left_left hu1 hu2
  | .mul_left _ hu1, .mul_right _ hv2 => isGreenD_of_left_right hu1 hv2
  | .mul_left _ hu1, .mul_both _ _ huv2 => isGreenD_of_JRel_left_both hu1 huv2
  | .mul_right _ hv1, .mul_left _ hu2 => isGreenD_of_right_left hv1 hu2
  | .mul_right _ hv1, .mul_right _ hv2 => isGreenD_of_right_right hv1 hv2
  | .mul_right _ hv1, .mul_both _ _ huv2 => isGreenD_of_JRel_right_both hv1 huv2
  | .mul_both _ _ huv1, .mul_left _ hu2 => (isGreenD_of_JRel_left_both hu2 huv1).symm
  | .mul_both _ _ huv1, .mul_right _ hv2 => (isGreenD_of_JRel_right_both hv2 huv1).symm
  | .mul_both _ _ huv1, .mul_both _ _ huv2 => isGreenD_of_JRel_both huv1 huv2

/-- If `a` and `b` are `D`-related, they satisfy the basic `J`-relation step. -/
theorem isGreenJRel_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJRel a b :=
  let ⟨z, hL, hR⟩ := h
  match hL.left, hR.left with
  | .inl rfl, .inl rfl => .of_eq rfl
  | .inl rfl, .inr ⟨v, hv⟩ => .mul_right v hv
  | .inr ⟨u, hu⟩, .inl rfl => .mul_left u hu
  | .inr ⟨u, hu⟩, .inr ⟨v, hv⟩ => .mul_both u v (hu ▸ hv ▸ (mul_assoc u b v).symm)

/-- If `a` and `b` are `D`-related, they are also `J`-related. -/
theorem isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b :=
  ⟨isGreenJRel_of_isGreenD h, isGreenJRel_of_isGreenD h.symm⟩

/-- In a finite semigroup, Green's `D` relation and Green's `J` relation are equal. -/
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ :=
  funext₂ fun _ _ => propext ⟨isGreenJ_of_isGreenD, isGreenD_of_isGreenJ⟩

open MulOpposite in
/-- If `b` and `a * b` are `D`-related in a finite semigroup, they are `L`-related. -/
theorem isGreenL_sl_of_isGreenD_sl [Finite S] {a b : S} (h : IsGreenD b (a * b)) :
    IsGreenL b (a * b) := by
  constructor
  · rcases h with ⟨z', hL_bz', hR_z'ab⟩
    obtain ⟨z, hR_bz, hL_zab⟩ := isGreenL_commutes_isGreenR hL_bz' hR_z'ab
    obtain ⟨c, rfl⟩ : ∃ c, z = c * b := by
      rcases hL_zab.left with rfl | ⟨w, hw⟩
      · exact ⟨a, rfl⟩
      · exact ⟨w * a, by rw [hw, mul_assoc]⟩
    rcases hR_bz.left with h_eq | ⟨d, hd⟩
    · exact (IsGreenL.trans (h_eq ▸ IsGreenL.refl _) hL_zab).left
    · exact (IsGreenL.trans (greenL_of_eq_mul_mul hd) hL_zab).left
  · exact Or.inr ⟨a, rfl⟩

open MulOpposite in
/-- If `a` and `a * b` are `D`-related in a finite semigroup, they are `R`-related. -/
theorem isGreenR_sr_of_isGreenD_sr [Finite S] {a b : S} (h : IsGreenD a (a * b)) :
    IsGreenR a (a * b) := by
  rw [isGreenR_iff_isGreenL_op, op_mul]
  apply isGreenL_sl_of_isGreenD_sl
  rw [← op_mul, ← IsGreenD.isGreenD_iff_isGreenD_op]
  exact h

/-- If `a`, `b`, and `a * b` are all in the same regular `D`-class,
    then `a` is `R`-related to `a * b`, `b` is `L`-related to `a * b`,
    and there exists an idempotent `e` in the `D`-class such that `a`
    is `L`-related to `e` and `b` is `R`-related to `e`. -/
theorem mul_mem_isGreenD_eqvClass_properties
    [Finite S] {D : Set S} (hD_exists : ∃ x, D = IsGreenD.eqvClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  rcases hD_exists with ⟨x₀, rfl⟩
  constructor
  · exact ⟨isGreenR_sr_of_isGreenD_sr (ha.trans hab.symm),
      isGreenL_sl_of_isGreenD_sl (hb.trans hab.symm)⟩
  · rcases (isGreenR_sr_of_isGreenD_sr (ha.trans hab.symm)).left with ha_eq | ⟨u, hu⟩
    · rcases (isGreenL_sl_of_isGreenD_sl (hb.trans hab.symm)).left with hb_eq | ⟨v, hv⟩
      · have hab_eq : a = b := ha_eq.trans hb_eq.symm
        exact ⟨a, ha, by nth_rw 2 [hab_eq]; rw [← ha_eq], IsGreenL.refl a,
          hab_eq ▸ IsGreenR.refl a⟩
      · have h_b_eq_va : b = v * a := by nth_rw 1 [hv]; rw [← ha_eq]
        exact ⟨b, hb, by nth_rw 1 [h_b_eq_va]; rw [mul_assoc, ← hv],
          ⟨Or.inr ⟨a, ha_eq⟩, Or.inr ⟨v, h_b_eq_va⟩⟩, IsGreenR.refl b⟩
    · rcases (isGreenL_sl_of_isGreenD_sl (hb.trans hab.symm)).left with hb_eq | ⟨v, hv⟩
      · have h_a_eq_bu : a = b * u := by nth_rw 1 [hu]; rw [← hb_eq]
        exact ⟨a, ha, by nth_rw 2 [h_a_eq_bu]; rw [← mul_assoc, ← hb_eq, ← h_a_eq_bu],
          IsGreenL.refl a, ⟨Or.inr ⟨b, hb_eq⟩, Or.inr ⟨u, h_a_eq_bu⟩⟩⟩
      · have h_va_eq_bu : v * a = b * u := by rw [hu, ← mul_assoc, ← hv]
        have hLae : IsGreenL a (v * a) := ⟨Or.inr ⟨a, by grind⟩, Or.inr ⟨v, rfl⟩⟩
        exact ⟨v * a, IsGreenD.trans ⟨a, IsGreenL.symm hLae, IsGreenR.refl a⟩ ha, by grind,
          hLae, ⟨Or.inr ⟨b, by grind⟩, Or.inr ⟨u, h_va_eq_bu⟩⟩⟩

/-- A `D`-class is regular if and only if there exist
two elements in it whose product is also in the `D`-class. -/
theorem isRegularDClass_iff_exists_mul_mem
    [Finite S] (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ a ∈ D, ∃ b ∈ D, a * b ∈ D := by
  constructor
  · intro hReg
    obtain ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact ⟨e, heD, e, heD, by rwa [he_idem]⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨_, h_exists⟩ := mul_mem_isGreenD_eqvClass_properties hD a b ha hb hab
    rcases h_exists with ⟨e, heD, he_idem, _⟩
    exact (isRegularDClass_iff_exists_idempotent D hD).mpr ⟨e, heD, he_idem⟩

/-- A predicate stating that a set `H : Set S` forms a group under
    the semigroup multiplication restricted to `H`. -/
def IsGroup (H : Set S) : Prop := Nonempty (Group H)

/-- An `H`-class either contains no idempotents and is not closed under multiplication,
    or contains an idempotent and is closed under multiplication. -/
theorem isGreenH_eqvClass_disjoint_or_exists_idempotent
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
    x * y ∉ IsGreenH.eqvClass a
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    obtain ⟨_, e, _, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties ⟨a, rfl⟩ x₀ y₀
        ⟨a, hx₀.1, IsGreenR.refl _⟩ ⟨a, hy₀.1, IsGreenR.refl _⟩ ⟨a, hxy₀.1, IsGreenR.refl _⟩
    have heH : e ∈ IsGreenH.eqvClass a :=
      ⟨hLx₀e.symm.trans hx₀.1, hRy₀e.symm.trans hy₀.2⟩
    exact ⟨e, heH, he_idem, fun u v huH hvH ↦
      ⟨IsGreenL.trans (by
          simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (hvH.trans heH.symm) he_idem]
            using IsGreenL.mul_right v (huH.trans heH.symm).1) hvH.1,
       IsGreenR.trans (by
          simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (huH.trans heH.symm) he_idem]
            using IsGreenR.mul_left u (hvH.trans heH.symm).2) huH.2⟩⟩

/-- An `H`-class containing an idempotent forms a group. -/
theorem isGreenH_eqvClass_isGroup_of_idempotent
    [Finite S] {H : Set S} (hH : ∃ a, H = IsGreenH.eqvClass a)
    {e : S} (heH : e ∈ H) (he_idem : e * e = e) :
    IsGroup H := by
  obtain ⟨a, rfl⟩ := hH
  have h_closed : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
      x * y ∈ IsGreenH.eqvClass a := fun u v hu hv ↦ ⟨
    IsGreenL.trans (by
      simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (hv.trans heH.symm) he_idem]
        using IsGreenL.mul_right v (hu.trans heH.symm).1) hv.1,
    IsGreenR.trans (by
      simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent (hu.trans heH.symm) he_idem]
        using IsGreenR.mul_left u (hv.trans heH.symm).2) hu.2⟩
  have h_inj : ∀ x : IsGreenH.eqvClass a, Function.Injective (fun u : IsGreenH.eqvClass a ↦
    (⟨u.1 * x.1, h_closed u.1 x.1 u.2 x.2⟩ : IsGreenH.eqvClass a)) :=
      fun x u v h ↦ Subtype.ext <| by
    have h1 : u.1 * x.1 = v.1 * x.1 := Subtype.ext_iff.mp h
    rcases (x.2.trans heH.symm).right.right with rfl | ⟨k, hk⟩
    · exact (MulSeq.mul_eq_self_of_isGreenH_idempotent (u.2.trans heH.symm) he_idem).1.symm.trans <|
        h1.trans (MulSeq.mul_eq_self_of_isGreenH_idempotent (v.2.trans heH.symm) he_idem).1
    · have h2 : u.1 * x.1 * k = v.1 * x.1 * k := by rw [h1]
      simp only [mul_assoc, ← hk] at h2
      exact (MulSeq.mul_eq_self_of_isGreenH_idempotent (u.2.trans heH.symm) he_idem).1.symm.trans <|
        h2.trans (MulSeq.mul_eq_self_of_isGreenH_idempotent (v.2.trans heH.symm) he_idem).1
  refine ⟨{
    mul := fun x y ↦ ⟨x.1 * y.1, h_closed x.1 y.1 x.2 y.2⟩
    mul_assoc := fun x y z ↦ Subtype.ext (mul_assoc x.1 y.1 z.1)
    one := ⟨e, heH⟩
    one_mul := fun x ↦ Subtype.ext (MulSeq.mul_eq_self_of_isGreenH_idempotent
      (x.2.trans heH.symm) he_idem).2
    mul_one := fun x ↦ Subtype.ext (MulSeq.mul_eq_self_of_isGreenH_idempotent
      (x.2.trans heH.symm) he_idem).1
    inv := fun x ↦ Classical.choose
      (Finite.injective_iff_bijective.mp (h_inj x) |>.surjective ⟨e, heH⟩)
    inv_mul_cancel := fun x ↦ Subtype.ext
      (Subtype.ext_iff.mp (Classical.choose_spec
        (Finite.injective_iff_bijective.mp (h_inj x) |>.surjective ⟨e, heH⟩)))
  }⟩

/-- An `H`-class is either never closed under multiplication or forms a group. -/
theorem isGreenH_eqvClass_dichotomy
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    ((∀ x y, x ∈ H → y ∈ H → x * y ∈ H) ∧ IsGroup H) := by
  rcases isGreenH_eqvClass_disjoint_or_exists_idempotent H hH with
    h_disj | ⟨e, heH, he_idem, h_closed⟩
  · left
    exact h_disj
  · right
    exact ⟨h_closed, isGreenH_eqvClass_isGroup_of_idempotent hH heH he_idem⟩

end BijectionsAndCardinalities
