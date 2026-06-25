/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Span rank under operations

In this file we show how operations on submodules interact with `Submodule.spanRank`.

# Main Results

* `Submodule.spanRank_baseChange_le`: Base change doesn't increase the span rank.

* `TensorProduct.spanFinrank_top_eq_of_residueField`: For a finitely generated module over
  a local ring, the dimension of the base change to the residue field is equal to its span rank.

* `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`: The minimal number of
  generators of the unique maximal ideal is equal to the dimension of the cotangent space.

-/

public section

open IsLocalRing TensorProduct Submodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

lemma Submodule.spanRank_baseChange_le : (N.baseChange A).spanRank ≤ N.spanRank.lift := by
  obtain ⟨s, hs₁, hs₂⟩ := N.exists_span_set_card_eq_spanRank
  grw [← hs₁, ← hs₂, baseChange_span, spanRank_span_le_card]
  convert! Cardinal.mk_image_le_lift (f := TensorProduct.mk R A M 1) (s := s)
  · exact (Cardinal.lift_id' _).symm
  · exact Cardinal.lift_umax.symm

lemma Submodule.FG.spanFinrank_baseChange_le (fg : N.FG) :
    (N.baseChange A).spanFinrank ≤ N.spanFinrank := by
  grw [spanFinrank, spanRank_baseChange_le, Cardinal.toNat_lift, spanFinrank]
  simp [Cardinal.lift_lt_aleph0, spanRank_finite_iff_fg.mpr fg]

lemma TensorProduct.spanRank_top_le : (⊤ : Submodule A (A ⊗[R] N)).spanRank ≤ N.spanRank.lift := by
  grw [← Submodule.baseChange_top, ← N.spanRank_top, spanRank_baseChange_le]

lemma TensorProduct.spanFinrank_top_le_of_fg (fg : N.FG) :
    (⊤ : Submodule A (A ⊗[R] N)).spanFinrank ≤ N.spanFinrank := by
  grw [← Submodule.baseChange_top, ← N.spanFinrank_top, (N.fg_top.mpr fg).spanFinrank_baseChange_le]

variable [IsLocalRing R]
local notation "𝓀" => ResidueField R

lemma TensorProduct.spanFinrank_top_eq_of_residueField (fg : N.FG) :
    (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).spanFinrank = N.spanFinrank := by
  let : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  apply (TensorProduct.spanFinrank_top_le_of_fg N fg).antisymm
  obtain ⟨s, hs₁, hs₂⟩ := (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).exists_span_set_card_eq_spanRank
  have hs₃ : s.Finite := Cardinal.mk_lt_aleph0_iff.mp (by simpa [hs₁] using Module.Finite.fg_top)
  let t := Function.surjInv (mk_surjective R N 𝓀 residue_surjective) '' s
  have ht₁ : mk R 𝓀 N 1 '' t = s := by rw [← Set.image_comp, Function.comp_surjInv, s.image_id]
  have ht₂ : span R t = ⊤ := by
    rwa [← restrictScalars_eq_top_iff R, restrictScalars_span _ _ (by exact residue_surjective),
      ← ht₁, ← map_span, map_tensorProduct_mk_eq_top] at hs₂
  grw [← N.spanFinrank_top, ← ht₂, spanFinrank_span_le_ncard_of_finite (hs₃.image _), spanFinrank,
    ← hs₁, Set.ncard_image_le hs₃]
  rfl

namespace IsLocalRing

set_option backward.isDefEq.respectTransparency false in
lemma spanFinrank_eq_finrank_quotient (N : Submodule R M) (fg : N.FG) :
    N.spanFinrank =
      Module.finrank (R ⧸ maximalIdeal R) (N ⧸ (maximalIdeal R) • (⊤ : Submodule R N)) := by
  let : Module 𝓀 (N ⧸ maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) _)
  let : IsScalarTower R 𝓀 (N ⧸ maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) _)
  rw [← spanFinrank_top_eq_of_residueField N fg, ← Module.finrank_eq_spanFinrank_of_free]
  let e : 𝓀 ⊗[R] N ≃ₗ[𝓀] N ⧸ (maximalIdeal R) • (⊤ : Submodule R N) :=
    (quotTensorEquivQuotSMul N (maximalIdeal R)).extendScalarsOfSurjective residue_surjective
  exact e.finrank_eq

lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIdeal R).FG) :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_eq_finrank_quotient _ fg

variable (R) in
lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace [IsNoetherianRing R] :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (maximalIdeal R).fg_of_isNoetherianRing

end IsLocalRing

lemma IsLocalRing.spanFinrank_maximalIdeal_add_finrank_eq_of_surjective
    [IsNoetherianRing R] {S : Type*} [CommRing S] [IsLocalRing S] [Algebra R S]
    (surj : Function.Surjective (algebraMap R S)) [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).spanFinrank + Module.finrank (ResidueField R)
      ((Submodule.comap (maximalIdeal R).subtype (RingHom.ker (algebraMap R S))).map
        (toCotangentSpace R)) = (maximalIdeal R).spanFinrank := by
  have : IsNoetherianRing S := isNoetherianRing_of_surjective R S (algebraMap R S) surj
  let f := (maximalIdeal R).mapCotangent (maximalIdeal S) (Algebra.ofId R S) (fun x hx ↦ by simpa)
  have eqsup : (maximalIdeal S).comap (algebraMap R S) =
    RingHom.ker (algebraMap R S) ⊔ (maximalIdeal R) := by
    simpa [maximalIdeal_comap] using le_maximalIdeal (RingHom.ker_ne_top _)
  let toCot := (Submodule.comap (maximalIdeal R).subtype (RingHom.ker (algebraMap R S))).map
    (toCotangentSpace R)
  let Q := (CotangentSpace R) ⧸ toCot
  have ker : (LinearMap.ker f : Set (maximalIdeal R).Cotangent) = toCot := by
    rw [Ideal.mapCotangent_ker_of_surjective surj eqsup]
    simp [toCot, toCotangentSpace]
  let f' : Q →+ CotangentSpace S :=
    QuotientAddGroup.lift _ f (fun x hx ↦ (Set.ext_iff.mp ker x).mpr hx)
  have bij : Function.Bijective f' := by
    constructor
    · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact (QuotientAddGroup.eq_zero_iff _).mpr ((Set.ext_iff.mp ker x).mp hx)
    · apply QuotientAddGroup.lift_surjective_of_surjective
      exact Ideal.mapCotangent_surjective_of_comap_eq surj eqsup
  let e : Q ≃+ CotangentSpace S := AddEquiv.ofBijective f' bij
  have (r : ResidueField R) (m : Q) : e (r • m) = (ResidueField.map (algebraMap R S)) r • e m := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨r, rfl⟩ := residue_surjective r
    exact (map_smul f r m).trans (algebraMap_smul S r _).symm
  have bij' : Function.Bijective (ResidueField.map (algebraMap R S)) :=
    ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
      (Ideal.Quotient.mk_surjective.comp surj)⟩
  have rk := lift_rank_eq_of_equiv_equiv (ResidueField.map (algebraMap R S)) e bij' this
  have frk : Module.finrank (ResidueField R) Q =
    Module.finrank (ResidueField S) (CotangentSpace S) := by
    simpa [Module.finrank] using! congrArg Cardinal.toNat rk
  simp only [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  rw [← frk, Submodule.finrank_quotient_add_finrank]
