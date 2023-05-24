/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot

! This file was ported from Lean 3 source module topology.instances.complex
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.FieldTheory.IntermediateField
import Mathbin.Topology.Algebra.UniformRing

/-!
# Some results about the topology of ℂ
-/


section ComplexSubfield

open Complex Set

open ComplexConjugate

/-- The only closed subfields of `ℂ` are `ℝ` and `ℂ`. -/
theorem Complex.subfield_eq_of_closed {K : Subfield ℂ} (hc : IsClosed (K : Set ℂ)) :
    K = ofReal.fieldRange ∨ K = ⊤ :=
  by
  suffices range (coe : ℝ → ℂ) ⊆ K
    by
    rw [range_subset_iff, ← coe_algebra_map] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_set_eq] at this⊢
    convert this using 2
    simpa only [RingHom.coe_fieldRange, Algebra.coe_bot, coe_algebra_map]
  suffices range (coe : ℝ → ℂ) ⊆ closure (Set.range ((coe : ℝ → ℂ) ∘ (coe : ℚ → ℝ)))
    by
    refine' subset_trans this _
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, of_real_rat_cast, SetLike.mem_coe, SubfieldClass.coe_rat_mem]
  nth_rw 2 [range_comp]
  refine' subset_trans _ (image_closure_subset_closure_image continuous_of_real)
  rw [DenseRange.closure_range rat.dense_embedding_coe_real.dense]
  simp only [image_univ]
#align complex.subfield_eq_of_closed Complex.subfield_eq_of_closed

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc2.lean:304:22: continuitity! not supported at the moment -/
/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc2.lean:304:22: continuitity! not supported at the moment -/
/-- Let `K` a subfield of `ℂ` and let `ψ : K →+* ℂ` a ring homomorphism. Assume that `ψ` is uniform
continuous, then `ψ` is either the inclusion map or the composition of the inclusion map with the
complex conjugation. -/
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield ℂ) {ψ : K →+* ℂ}
    (hc : UniformContinuous ψ) : ψ.toFun = K.Subtype ∨ ψ.toFun = conj ∘ K.Subtype :=
  by
  letI : TopologicalDivisionRing ℂ := TopologicalDivisionRing.mk
  letI : TopologicalRing K.topological_closure :=
    Subring.topologicalRing K.topological_closure.to_subring
  set ι : K → K.topological_closure := Subfield.inclusion K.le_topological_closure
  have ui : UniformInducing ι :=
    ⟨by
      erw [uniformity_subtype, uniformity_subtype, Filter.comap_comap]
      congr ⟩
  let di := ui.dense_inducing _
  · -- extψ : closure(K) →+* ℂ is the extension of ψ : K →+* ℂ
    let extψ := DenseInducing.extendRingHom ui di.dense hc
    haveI := (uniformContinuous_uniformly_extend ui di.dense hc).Continuous
    cases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K)
    · left
      let j := RingEquiv.subfieldCongr h
      -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : closure (K) ≃+* ℝ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := RingHom.comp extψ (RingHom.comp j.symm.to_ring_hom of_real.range_restrict)
      ext1 x
      rsuffices ⟨r, hr⟩ : ∃ r : ℝ, of_real.range_restrict r = j (ι x)
      · have :=
          RingHom.congr_fun (ring_hom_eq_of_real_of_continuous (by continuity : Continuous ψ₁)) r
        rw [RingHom.comp_apply, RingHom.comp_apply, hr, RingEquiv.toRingHom_eq_coe] at this
        convert this using 1
        · exact (DenseInducing.extend_eq di hc.continuous _).symm
        · rw [← of_real.coe_range_restrict, hr]
          rfl
      obtain ⟨r, hr⟩ := SetLike.coe_mem (j (ι x))
      exact ⟨r, Subtype.ext hr⟩
    · -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `closure (K) ≃+* ℂ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ :=
        RingHom.comp extψ
          (RingHom.comp (RingEquiv.subfieldCongr h).symm.toRingHom
            (@Subfield.topEquiv ℂ _).symm.toRingHom)
      cases' ring_hom_eq_id_or_conj_of_continuous (by continuity : Continuous ψ₁) with h h
      · left
        ext1 z
        convert RingHom.congr_fun h z using 1
        exact (DenseInducing.extend_eq di hc.continuous z).symm
      · right
        ext1 z
        convert RingHom.congr_fun h z using 1
        exact (DenseInducing.extend_eq di hc.continuous z).symm
  · let j : { x // x ∈ closure (id '' { x | (K : Set ℂ) x }) } → (K.topological_closure : Set ℂ) :=
      fun x =>
      ⟨x, by
        convert x.prop
        simpa only [id.def, Set.image_id'] ⟩
    convert DenseRange.comp (Function.Surjective.denseRange _)
        (DenseEmbedding.subtype denseEmbedding_id (K : Set ℂ)).dense (by continuity : Continuous j)
    rintro ⟨y, hy⟩
    use
      ⟨y, by
        convert hy
        simpa only [id.def, Set.image_id'] ⟩
    simp only [Subtype.mk_eq_mk, Subtype.coe_mk]
#align complex.uniform_continuous_ring_hom_eq_id_or_conj Complex.uniformContinuous_ringHom_eq_id_or_conj

end ComplexSubfield

