/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Applications of Maschke's theorem

This proves some properties of representations that follow from Maschke's
theorem.

We prove that, if `G` is a finite group whose order is invertible in a field `k`,
then every object of `Rep k G` (resp. `FDRep k G`) is injective and projective.

We also give two simpleness criteria for an object `V` of `FDRep k G`, when `k` is
an algebraically closed field in which the order of `G` is invertible:
* `FDRep.simple_iff_end_is_rank_one`: `V` is simple if and only `V ⟶ V` is a `k`-vector
  space of dimension `1`.
* `FDRep.simple_iff_char_is_norm_one`: when `k` is characteristic zero, `V` is simple
  if and only if `∑ g : G, V.character g * V.character g⁻¹ = Fintype.card G`.

-/

@[expose] public section

universe u v w

variable {k : Type u} [Field k] {G : Type u} [Finite G] [Group G]

open CategoryTheory Limits

namespace Rep

variable [NeZero (Nat.card G : k)]

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is injective.
-/
instance (V : Rep.{w} k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is projective.
-/
-- Will this clash with the previously defined `Projective` instances?
instance (V : Rep.{u} k G) : Projective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff,
    ← IsProjective.iff_projective]
  exact Module.projective_of_isSemisimpleRing _ _

end Rep

namespace FDRep

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is injective.
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Injective V :=
  (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`FDRep k G` is projective.
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Projective V :=
  (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective inferInstance

variable [IsAlgClosed k]

/--
If `G` is finite and its order is nonzero in an algebraically closed field `k`,
then an object of `FDRep k G` is simple if and only if its space of endomorphisms is
a `k`-vector space of dimension `1`.
-/
lemma simple_iff_end_is_rank_one [NeZero (Nat.card G : k)] (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι ≠ 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V := (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

omit [Finite G] in
/--
If `G` is finite and `k` an algebraically closed field of characteristic `0`,
then an object of `FDRep k G` is simple if and only if its character has norm `1`.
-/
lemma simple_iff_char_is_norm_one [CharZero k] [Fintype G] (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G where
  mp h := by
    have : NeZero (Nat.card G : k) := by
      rw [← @Fintype.card_eq_nat_card G (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    classical
    have : ⅟(Nat.card G : k) • ∑ g, V.character g * V.character g⁻¹ = 1 := by
      simpa only [Nonempty.intro (Iso.refl V), ↓reduceIte, Fintype.card_eq_nat_card]
      using char_orthonormal V V
    apply_fun (· * (Fintype.card G : k)) at this
    rwa [mul_comm, ← smul_eq_mul, smul_smul, Fintype.card_eq_nat_card, mul_invOf_self, smul_eq_mul,
      one_mul, one_mul] at this
  mpr h := by
    have : NeZero (Nat.card G : k) := by
      rw [← @Fintype.card_eq_nat_card G (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible, Fintype.card_eq_nat_card]
      at eq
    rw [simple_iff_end_is_rank_one, ← Nat.cast_inj (R := k), ← eq, Nat.cast_one]

end FDRep
