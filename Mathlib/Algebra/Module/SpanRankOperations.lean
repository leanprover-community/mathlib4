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

@[expose] public section

open IsLocalRing TensorProduct Submodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

lemma Submodule.spanRank_baseChange_le : (N.baseChange A).spanRank ≤ N.spanRank.lift := by
  obtain ⟨s, hs₁, hs₂⟩ := N.exists_span_set_card_eq_spanRank
  grw [← hs₁, ← hs₂, baseChange_span, spanRank_span_le_card]
  convert Cardinal.mk_image_le_lift (f := TensorProduct.mk R A M 1) (s := s)
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
