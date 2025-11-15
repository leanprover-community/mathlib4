import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Field.Subfield.Basic

instance : Subsingleton (Subfield ℚ) := by
  refine ⟨fun F G ↦ Subfield.ext fun x ↦ ?_⟩
  change (algebraMap ℚ F x).val ∈ _ ↔ (algebraMap ℚ G x).val ∈ _
  simp_rw [SetLike.coe_mem]

theorem Subfield.bot_eq_of_charZero {K : Type*} [Field K] [CharZero K] :
    (⊥ : Subfield K) = (algebraMap ℚ K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap ℚ K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]

-- variable {G : Type*} (K L : Type*) [Group G] [Finite G] [Field K] [Field L] [Algebra K L]
--   [MulSemiringAction G L] [IsGaloisGroup G K L]

-- def IsGaloisGroup.fixedField (H : Subgroup G) : IntermediateField K L :=
--     .fixedField <| (IsGaloisGroup.mulEquivAlgEquiv G K L).mapSubgroup H

-- theorem IsGaloisGroup.mem_fixedField_iff (H : Subgroup G) (x : L) :
--     x ∈ IsGaloisGroup.fixedField K L H ↔ ∀ σ ∈ H, σ • x = x := by
--   simp [fixedField]

-- theorem IsGaloisGroup.of_subgroup (H : Subgroup G) :
--     IsGaloisGroup H (IsGaloisGroup.fixedField K L H) L where
--   faithful :=
--     have : FaithfulSMul G L := IsGaloisGroup.faithful K
--     inferInstance
--   commutes := ⟨by
--     intro ⟨σ, hσ⟩ ⟨x, hx⟩ a
--     rw [IsGaloisGroup.mem_fixedField_iff] at hx
--     simp [IntermediateField.smul_def, hx, hσ]⟩
--   isInvariant := ⟨by
--     intro x hx
--     refine ⟨⟨x, ?_⟩, by rw [IntermediateField.algebraMap_apply]⟩
--     · rw [IsGaloisGroup.mem_fixedField_iff]
--       exact fun σ hσ ↦ hx ⟨σ, hσ⟩⟩

#exit

refine ⟨?_⟩
        rintro ⟨τ, hτ⟩ ⟨x, hx⟩ a
        rw [IntermediateField.mem_fixedField_iff] at hx
        simp_rw [IntermediateField.smul_def, Subgroup.smul_def, AlgEquiv.smul_def, smul_eq_mul,
          map_mul]
        rw [hx _ hτ]
      · refine ⟨?_⟩
        intro x hx
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · use x
        · exact hx
        · simp
