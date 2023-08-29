/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IntermediateField
import Mathlib.Topology.Algebra.UniformRing

#align_import topology.instances.complex from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Some results about the topology of ℂ
-/


section ComplexSubfield

open Complex Set

open ComplexConjugate

/-- The only closed subfields of `ℂ` are `ℝ` and `ℂ`. -/
theorem Complex.subfield_eq_of_closed {K : Subfield ℂ} (hc : IsClosed (K : Set ℂ)) :
    K = ofReal.fieldRange ∨ K = ⊤ := by
  suffices range (ofReal' : ℝ → ℂ) ⊆ K by
    rw [range_subset_iff, ← coe_algebraMap] at this
    have :=
      (Subalgebra.isSimpleOrder_of_finrank finrank_real_complex).eq_bot_or_eq_top
        (Subfield.toIntermediateField K this).toSubalgebra
    simp_rw [← SetLike.coe_set_eq] at this ⊢
    convert this using 2
    simp only [RingHom.coe_fieldRange, Algebra.coe_bot, coe_algebraMap]
    rfl
  suffices range (ofReal' : ℝ → ℂ) ⊆ closure (Set.range ((ofReal' : ℝ → ℂ) ∘ ((↑) : ℚ → ℝ))) by
    refine' subset_trans this _
    rw [← IsClosed.closure_eq hc]
    apply closure_mono
    rintro _ ⟨_, rfl⟩
    simp only [Function.comp_apply, ofReal_rat_cast, SetLike.mem_coe, SubfieldClass.coe_rat_mem]
  nth_rw 1 [range_comp]
  -- ⊢ range ofReal' ⊆ closure (ofReal' '' range Rat.cast)
  refine' subset_trans _ (image_closure_subset_closure_image continuous_ofReal)
  -- ⊢ range ofReal' ⊆ ofReal' '' closure (range Rat.cast)
  rw [DenseRange.closure_range Rat.denseEmbedding_coe_real.dense]
  -- ⊢ range ofReal' ⊆ ofReal' '' univ
  simp only [image_univ]
  -- ⊢ range ofReal' ⊆ range ofReal'
  rfl
  -- 🎉 no goals
#align complex.subfield_eq_of_closed Complex.subfield_eq_of_closed

/-- Let `K` a subfield of `ℂ` and let `ψ : K →+* ℂ` a ring homomorphism. Assume that `ψ` is uniform
continuous, then `ψ` is either the inclusion map or the composition of the inclusion map with the
complex conjugation. -/
theorem Complex.uniformContinuous_ringHom_eq_id_or_conj (K : Subfield ℂ) {ψ : K →+* ℂ}
    (hc : UniformContinuous ψ) : ψ.toFun = K.subtype ∨ ψ.toFun = conj ∘ K.subtype := by
  letI : TopologicalDivisionRing ℂ := TopologicalDivisionRing.mk
  -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
  letI : TopologicalRing K.topologicalClosure :=
    Subring.instTopologicalRing K.topologicalClosure.toSubring
  set ι : K → K.topologicalClosure := ⇑(Subfield.inclusion K.le_topologicalClosure)
  -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
  have ui : UniformInducing ι :=
    ⟨by
      erw [uniformity_subtype, uniformity_subtype, Filter.comap_comap]
      congr ⟩
  let di := ui.denseInducing (?_ : DenseRange ι)
  -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
  · -- extψ : closure(K) →+* ℂ is the extension of ψ : K →+* ℂ
    let extψ := DenseInducing.extendRingHom ui di.dense hc
    -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
    haveI hψ := (uniformContinuous_uniformly_extend ui di.dense hc).continuous
    -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
    cases' Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure K) with h h
    -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
    · left
      -- ⊢ ψ.toFun = ↑(Subfield.subtype K)
      let j := RingEquiv.subfieldCongr h
      -- ⊢ ψ.toFun = ↑(Subfield.subtype K)
      -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : closure (K) ≃+* ℝ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := RingHom.comp extψ (RingHom.comp j.symm.toRingHom ofReal.rangeRestrict)
      -- ⊢ ψ.toFun = ↑(Subfield.subtype K)
      -- porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using hψ.comp ((continuous_algebraMap ℝ ℂ).subtype_mk _)
      ext1 x
      -- ⊢ OneHom.toFun (↑↑ψ) x = ↑(Subfield.subtype K) x
      rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ofReal.rangeRestrict r = j (ι x)
      -- ⊢ OneHom.toFun (↑↑ψ) x = ↑(Subfield.subtype K) x
      · have :=
          RingHom.congr_fun (ringHom_eq_ofReal_of_continuous hψ₁) r
        rw [RingHom.comp_apply, RingHom.comp_apply, hr, RingEquiv.toRingHom_eq_coe] at this
        -- ⊢ OneHom.toFun (↑↑ψ) x = ↑(Subfield.subtype K) x
        convert this using 1
        -- ⊢ OneHom.toFun (↑↑ψ) x = ↑extψ (↑↑(RingEquiv.symm j) (↑j (ι x)))
        · exact (DenseInducing.extend_eq di hc.continuous _).symm
          -- 🎉 no goals
        · rw [← ofReal.coe_rangeRestrict, hr]
          -- ⊢ ↑(Subfield.subtype K) x = ↑(↑j (ι x))
          rfl
          -- 🎉 no goals
      obtain ⟨r, hr⟩ := SetLike.coe_mem (j (ι x))
      -- ⊢ ∃ r, ↑(RingHom.rangeRestrict ofReal) r = ↑j (ι x)
      exact ⟨r, Subtype.ext hr⟩
      -- 🎉 no goals
    · -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `closure (K) ≃+* ℂ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ :=
        RingHom.comp extψ
          (RingHom.comp (RingEquiv.subfieldCongr h).symm.toRingHom
            (@Subfield.topEquiv ℂ _).symm.toRingHom)
      -- porting note: was `by continuity!` and was used inline
      have hψ₁ : Continuous ψ₁ := by
        simpa only [RingHom.coe_comp] using hψ.comp (continuous_id.subtype_mk _)
      cases' ringHom_eq_id_or_conj_of_continuous hψ₁ with h h
      -- ⊢ ψ.toFun = ↑(Subfield.subtype K) ∨ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.su …
      · left
        -- ⊢ ψ.toFun = ↑(Subfield.subtype K)
        ext1 z
        -- ⊢ OneHom.toFun (↑↑ψ) z = ↑(Subfield.subtype K) z
        convert RingHom.congr_fun h z using 1
        -- ⊢ OneHom.toFun (↑↑ψ) z = ↑ψ₁ ↑z
        exact (DenseInducing.extend_eq di hc.continuous z).symm
        -- 🎉 no goals
      · right
        -- ⊢ ψ.toFun = ↑(starRingEnd ℂ) ∘ ↑(Subfield.subtype K)
        ext1 z
        -- ⊢ OneHom.toFun (↑↑ψ) z = (↑(starRingEnd ℂ) ∘ ↑(Subfield.subtype K)) z
        convert RingHom.congr_fun h z using 1
        -- ⊢ OneHom.toFun (↑↑ψ) z = ↑ψ₁ ↑z
        exact (DenseInducing.extend_eq di hc.continuous z).symm
        -- 🎉 no goals
  · let j : { x // x ∈ closure (id '' { x | (K : Set ℂ) x }) } → (K.topologicalClosure : Set ℂ) :=
      fun x =>
      ⟨x, by
        convert x.prop
        simp only [id.def, Set.image_id']
        rfl ⟩
    convert DenseRange.comp (Function.Surjective.denseRange _)
        (DenseEmbedding.subtype denseEmbedding_id (K : Set ℂ)).dense (by continuity : Continuous j)
    rintro ⟨y, hy⟩
    -- ⊢ ∃ a, j a = { val := y, property := hy }
    use
      ⟨y, by
        convert hy
        simp only [id.def, Set.image_id']
        rfl ⟩
#align complex.uniform_continuous_ring_hom_eq_id_or_conj Complex.uniformContinuous_ringHom_eq_id_or_conj

end ComplexSubfield
