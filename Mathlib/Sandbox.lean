import Mathlib

variable (E F : Type*) [Field E] [Field F] [Algebra F E] (K L : IntermediateField F E)
  [Normal F K]

namespace IntermediateField

noncomputable def restrictRestrictMapHom :
    (E ≃ₐ[L] E) →* (K ≃ₐ[F] K) :=
  (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut (E ≃ₐ[L] E) F E)


@[simp]
theorem restrictRestrictMapHom_apply (φ : E ≃ₐ[L] E) (x : K) :
    restrictRestrictMapHom E F K L φ x = φ x := by
  simp [restrictRestrictMapHom, AlgEquiv.restrictNormalHom_apply]

theorem restrictRestrictMapHom_injective (h : K ⊔ L = ⊤) :
    Function.Injective (restrictRestrictMapHom E F K L) := by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ ↦ ?_
  have : φ ∈ fixingSubgroup ⊤ := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun _ hx ↦ ?_
    rw [← SetLike.mem_coe, ← coe_restrictScalars F, restrictScalars_top, ← h,
          SetLike.mem_coe, sup_def] at hx
    induction hx using adjoin_induction F with
    | mem x hx =>
      obtain hx | hx := hx
      · rw [← Subtype.coe_mk x hx, ← restrictRestrictMapHom_apply,
          congr_arg ((↑) : K → E) (AlgEquiv.congr_fun hφ _), AlgEquiv.one_apply]
      · rw [← Subtype.coe_mk x hx, ← algebraMap_apply, AlgEquiv.commutes, algebraMap_apply]
    | algebraMap x => rw [IsScalarTower.algebraMap_apply F L E, AlgEquiv.commutes]
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  rwa [fixingSubgroup_top, Subgroup.mem_bot] at this

theorem restrictRestrictMapHom_surjective [FiniteDimensional F K] [FiniteDimensional L E]
    [IsGalois L E] (h : K ⊓ L = ⊥) :
    Function.Surjective (restrictRestrictMapHom E F K L) := by
  suffices fixedField (restrictRestrictMapHom E F K L).range = ⊥ from
     MonoidHom.range_eq_top.mp <|
      fixingSubgroup_fixedField (restrictRestrictMapHom E F K L).range ▸ this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ ↦ ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x ∈ Set.range (algebraMap L E) := by
    refine mem_bot.mp <| (IsGalois.mem_bot_iff_fixed _).mpr fun φ ↦ ?_
    rw [← restrictRestrictMapHom_apply E F K L φ ⟨x, hx₁⟩]
    rw [mem_fixedField_iff] at hx₂
    exact congr_arg ((↑) : K → E) <| hx₂ (restrictRestrictMapHom E F K L φ) ⟨φ, rfl⟩
  obtain ⟨z, rfl⟩ : y ∈ (⊥ : IntermediateField F E) := h ▸ mem_inf.mpr ⟨hx₁, hy⟩
  exact mem_bot.mp ⟨z, rfl⟩



theorem restrictScalars_inj (K : Type*) {L L' : Type*} [Field K] [Field L]
    [Field L'] [Algebra K L] [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L]
    {E E' : IntermediateField L' L} :
    E.restrictScalars K = E'.restrictScalars K ↔ E = E' :=
  (restrictScalars_injective K).eq_iff

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (K L : IntermediateField F E)
   [hN : IsGalois F K] (h : K ⊔ L = ⊤)

open IntermediateField

theorem _root_.IsGalois.sup [FiniteDimensional F K] (h : L ⊔ K = ⊤) : IsGalois L E := by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field F K
  let T' := Polynomial.map (algebraMap F L) T
  have : T'.IsSplittingField L E := by
    refine isSplittingField_iff_intermediateField.mpr ⟨?_, ?_⟩
    · rw [Polynomial.splits_map_iff, ← IsScalarTower.algebraMap_eq]
      exact Polynomial.splits_of_algHom hT₂.1 (IsScalarTower.toAlgHom _ _ _)
    · suffices K = adjoin F (T'.rootSet E) by
        rw [← restrictScalars_inj F, restrictScalars_adjoin, restrictScalars_top, adjoin_union,
          adjoin_self, ← h, this]
      apply eq_adjoin_of_eq_algebra_adjoin
      convert (congr_arg (Subalgebra.map (IsScalarTower.toAlgHom F K E)) hT₂.2).symm
      · ext; simp
      · have : T'.rootSet E = T.rootSet E := by
          ext
          rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet', Polynomial.map_map,
            ← IsScalarTower.algebraMap_eq, Polynomial.aeval_map_algebraMap]
        rw [← Algebra.adjoin_image, Polynomial.image_rootSet hT₂.1, this]
  exact IsGalois.of_separable_splitting_field (p := T') <| Polynomial.Separable.map hT₁

open IntermediateField

-- example (h : K ⊔ L = ⊤) : 1 = 0 := by
--     let f : (E ≃ₐ[L] E) →* (K ≃ₐ[F] K) :=
--       (AlgEquiv.restrictNormalHom (E := K)).comp (MulSemiringAction.toAlgAut (E ≃ₐ[L] E) F E)
--     have : Function.Injective f := by
--       refine (injective_iff_map_eq_one _).mpr ?_
--       intro φ hφ
--       have : φ ∈ fixingSubgroup ⊤ := by
--         rw [IntermediateField.mem_fixingSubgroup_iff]
--         intro _ hx
--         rw [← SetLike.mem_coe, ← coe_restrictScalars F, restrictScalars_top, ← h,
--           SetLike.mem_coe, sup_def] at hx
--         induction hx using adjoin_induction F with
--         | mem x hx =>
--             obtain hx | hx := hx
--             · change φ (algebraMap K E ⟨x, hx⟩) = _
--               have := congr_arg ((↑) : K → E) (AlgEquiv.congr_fun hφ ⟨x, hx⟩)
--               simpa [MonoidHom.coe_comp, Function.comp_apply, MulSemiringAction.toAlgAut_apply,
--                 AlgEquiv.one_apply, f, AlgEquiv.restrictNormalHom_apply] using this
--             · change φ (algebraMap L E ⟨x, hx⟩) = _
--               rw [AlgEquiv.commutes, IntermediateField.algebraMap_apply]
--         | algebraMap x => rw [IsScalarTower.algebraMap_apply F L E, AlgEquiv.commutes]
--         | add x y _ _ hx hy => rw [map_add, hx, hy]
--         | inv x _ hx => rw [map_inv₀, hx]
--         | mul x y _ _ hx hy => rw [map_mul, hx, hy]
--       rwa [fixingSubgroup_top, Subgroup.mem_bot] at this

theorem linearDisjoint_inf_eq_bot' [FiniteDimensional F E]
    (h₁ : K ⊔ L = ⊤) (h₂ : K ⊓ L = ⊥) :
    K.LinearDisjoint L := by
  apply LinearDisjoint.of_finrank_sup
  rw [h₁, finrank_top', ← Module.finrank_mul_finrank F L E, mul_comm, mul_left_inj'
    Module.finrank_pos.ne']
  have : IsGalois L E := by
    apply IsGalois.sup F E K L
    rwa [sup_comm]
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  refine Fintype.card_congr ?_
  refine Equiv.ofBijective (restrictRestrictMapHom E F K L) ⟨?_, ?_⟩
  · exact restrictRestrictMapHom_injective E F K L h₁
  · exact restrictRestrictMapHom_surjective E F K L h₂

@[simp]
theorem map_val_eq_lift {F E : Type*} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    (K : IntermediateField F L) :
    map L.val K = lift K := rfl

theorem lift_sup {K L : Type*} [Field K] [Field L] [Algebra K L] {F : IntermediateField K L}
    {E₁ E₂ : IntermediateField K F} :
    lift (E₁ ⊔ E₂) = (lift E₁) ⊔ (lift E₂) := by
  simp_rw [lift, ← map_sup]

theorem linearDisjoint_inf_eq_bot [FiniteDimensional F E] (h : K ⊓ L = ⊥) :
    K.LinearDisjoint L := by
--  convert LinearDisjoint.map ?_ (K ⊔ L).val
  let M : IntermediateField F E := K ⊔ L
  let K' : IntermediateField F M := K.restrict le_sup_left
  let L' : IntermediateField F M := L.restrict le_sup_right
  have : IsGalois F K' := by
    unfold K'
    refine isGalois_iff.mpr ⟨?_, ?_⟩
    · exact AlgEquiv.Algebra.isSeparable (restrict_algEquiv le_sup_left)
    · exact Normal.of_algEquiv (restrict_algEquiv le_sup_left)
  have : K'.LinearDisjoint L' := by
    apply linearDisjoint_inf_eq_bot'
    · apply lift_injective
      simp [K', L']
      ext x


      ext ⟨x, hx⟩
      simp [K', L']
      rw [← mem_lift]
      sorry
    · convert h
      sorry
  let f := M.val
  have := IntermediateField.LinearDisjoint.map this f
  simp only [map_val_eq_lift, lift_restrict, f, K', L', M] at this
  convert this
  all_goals simp



#exit

open nonZeroDivisors NumberField

theorem FractionalIdeal.inv_le_inv_iff {A K : Type*} [CommRing A] [Field K] [IsDedekindDomain A]
    [Algebra A K] [IsFractionRing A K] {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I⁻¹ ≤ J⁻¹ ↔ J ≤ I := by
  rw [le_inv_comm (inv_ne_zero hI) hJ, inv_inv]

-- instance (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F] [Algebra F K] :
--     IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) (𝓞 F)⁰) K := by
--   refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) _ ?_ ?_
--   · rintro _ ⟨a, ha, rfl⟩
--     exact ⟨a, by simpa using ne_zero ha, by simp⟩
--   · rintro _ ⟨x, hx, rfl⟩
--     simpa using ne_zero hx


#exit

section not_clean




variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] (L₁ L₂ : IntermediateField K M)
  (h : IsCoprime (Ideal.under (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L₁)))
    (Ideal.under (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L₂))))

-- theorem Submodule.traceDual_span_of_basis (A : Type*) {K L B : Type*}
--     [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
--     [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
--     [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) {ι : Type*} [Finite ι]
--     [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
--     (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
--   rw [traceDual_restrictScalars, hb]
--   exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

example (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) (I : Submodule (𝓞 L₂) L₂) {ι : Type*}
    [Finite ι] (b : Basis ι K L₂)
    (hI : I.restrictScalars (𝓞 K) = Submodule.span (𝓞 K) (Set.range b)) : 1 = 0:= by
  classical
  have : Nonempty ι := sorry
  have t₁ := I.traceDual_span_of_basis (b := b) (𝓞 K) hI
  let B := b.ofLinearDisjoint h₁ h₂
  have hI' : (Submodule.span (𝓞 M) (algebraMap L₂ M '' I)).restrictScalars (𝓞 L₁) =
    Submodule.span (𝓞 L₁) (Set.range B) := sorry
  have t₂ := (Submodule.span (𝓞 M) (algebraMap L₂ M '' I)).traceDual_span_of_basis (b := B)
    (𝓞 L₁) hI'
  have := Submodule.span (𝓞 L₁) (Set.range B.traceDual)

  sorry

example : IsCoprime ((differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)))
    ((differentIdeal (𝓞 K) (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 M))) := by
  rw [Ideal.isCoprime_iff_exists] at h ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨algebraMap (𝓞 K) (𝓞 M) x, ?_, algebraMap (𝓞 K) (𝓞 M) y, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨algebraMap (𝓞 K) (𝓞 L₁) x, hx, rfl⟩
  · apply Submodule.subset_span
    exact ⟨algebraMap (𝓞 K) (𝓞 L₂) y, hy, rfl⟩
  · rw [← map_add, hxy, map_one]

example : IsCoprime (differentIdeal (𝓞 L₁) (𝓞 M)) (differentIdeal (𝓞 L₂) (𝓞 M)) := by
  rw [Ideal.isCoprime_iff_exists] at h ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨algebraMap (𝓞 K) (𝓞 M) x, ?_, algebraMap (𝓞 K) (𝓞 M) y, ?_, ?_⟩
  · have : algebraMap (𝓞 K) M x ∈ (differentIdeal (𝓞 L₁) (𝓞 M) : FractionalIdeal (𝓞 M)⁰ M) := by
      simp at hx
      replace hx : (algebraMap (𝓞 K) L₁) y ∈
        (differentIdeal (𝓞 K) (𝓞 L₁) : FractionalIdeal (𝓞 L₁)⁰ L₁) := sorry
      rw [coeIdeal_differentIdeal (𝓞 K) K, mem_inv_iff] at hx
      rw [coeIdeal_differentIdeal (𝓞 L₁) L₁, mem_inv_iff]
      intro m hm
      simp [mem_dual] at hx hm



      sorry


    sorry
  ·
    sorry
  · rw [← map_add, hxy, map_one]

theorem useful :
    differentIdeal (𝓞 L₁) (𝓞 M) ∣ (differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)) := by
  sorry
  -- rw [Ideal.dvd_iff_le]

  -- rw [← FractionalIdeal.coeIdeal_le_coeIdeal M]
  -- rw [coeIdeal_differentIdeal (𝓞 L₁) L₁]
  -- suffices (Ideal.map (algebraMap (𝓞 L₁) (𝓞 M))
  --     (differentIdeal (𝓞 K) (𝓞 L₁)) : FractionalIdeal (𝓞 M)⁰ M) *
  --       (dual (𝓞 L₁) (L₁) 1) ≤ 1 by
  --   have := FractionalIdeal.mul_right_mono (dual (𝓞 L₁) (L₁) (1 : FractionalIdeal (𝓞 M)⁰ M))⁻¹ this
  --   simpa using this
  -- rw [mul_comm]
  -- rw [← FractionalIdeal.dual_inv]

  -- rw [FractionalIdeal.le_inv_comm]
  -- rw [← FractionalIdeal.extended_coeIdeal_eq_map (M := (𝓞 L₁)⁰) (N := (𝓞 M)⁰) (K := L₁) M]
  -- rw [← FractionalIdeal.extended_inv]
  -- rw [coeIdeal_differentIdeal (𝓞 K) K, inv_inv]
  -- have : (dual (𝓞 L₁) (L₁) (1 : FractionalIdeal (𝓞 M)⁰ M) : Submodule (𝓞 M) M) ≤
  --     (extended M sorry (M := (𝓞 L₁)⁰) (N := (𝓞 M)⁰) (K := L₁) (f := algebraMap (𝓞 L₁) (𝓞 M))
  --       (dual (𝓞 K) K (1 : FractionalIdeal (𝓞 L₁)⁰ L₁)) : Submodule (𝓞 M) M) := by
  --   simp
  --   intro x hx
  --   rw [Submodule.mem_traceDual] at hx
  --   refine Submodule.subset_span ?_
  --   refine ⟨?_, ?_, ?_⟩


  -- exact this

-- That's true only on `ℚ` because of the norm, and in fact probably not
-- example : (differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)) =
--     differentIdeal (𝓞 L₂) (𝓞 M) := by
--   have main := (differentIdeal_eq_differentIdeal_mul_differentIdeal
--     (𝓞 K) K (𝓞 L₁) L₁ (𝓞 M) M).symm.trans
--     (differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) K (𝓞 L₂) L₂ (𝓞 M) M)
--   apply dvd_antisymm'
--   · have h' : IsCoprime (differentIdeal (𝓞 L₂) (𝓞 M)) (differentIdeal (𝓞 L₁) (𝓞 M)) := by
--       have t₁ := useful L₁
--       have t₂ := useful L₂
--       refine IsCoprime.of_isCoprime_of_dvd_left ?_ t₂
--       refine IsCoprime.of_isCoprime_of_dvd_right ?_ t₁
--       exact h.symm
--     have := dvd_of_mul_right_eq _ main.symm
--     exact h'.dvd_of_dvd_mul_left (dvd_of_mul_right_eq _ main.symm)
--   · exact h.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ main)

end not_clean

open Submodule

-- example : (algebraMap (𝓞 E) (𝓞 K)).range ⊔ (algebraMap (𝓞 F) (𝓞 K)).range = ⊤ := by
--   classical
--   have main := (1 : FractionalIdeal (𝓞 K)⁰ K).dual_dual (𝓞 E) E
--   have h₁ : (1 : FractionalIdeal (𝓞 K)⁰ K).dual (𝓞 E) E =
--     span (𝓞 K) (algebraMap F K '' ((1 : FractionalIdeal (𝓞 F)⁰ F).dual ℤ ℚ)) := sorry
--   rw [← coeToSubmodule_inj, coe_dual, h₁, coe_one] at main
--   have : ((1 : FractionalIdeal (𝓞 F)⁰ F).dual ℤ ℚ : Set F) =
--     Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := sorry
--   rw [this] at main
--   let b := NumberField.integralBasis F
--   have h₂ := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) b sorry
--   have h₃ : (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F) =
--       span ℤ (Set.range ⇑b.traceDual) := sorry
--   rw [h₃] at main
--   have : (algebraMap F K : F → K) = (algebraMap F K).toIntAlgHom.toLinearMap := rfl
--   rw [this] at main
--   rw [← map_coe] at main
--   rw [map_span] at main
--   rw [← Set.range_comp] at main
--   let b₀ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → K := fun i ↦ algebraMap F K (b i)
--   rw [span_span_of_tower] at main
--   let B : Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) E K := by

--     sorry
--   have h₆ : Set.range ((algebraMap F K).toIntAlgHom.toLinearMap ∘ b.traceDual) =
--       Set.range B.traceDual := by

--   rw [h₆] at main
--   have := Submodule.traceDual_span_of_basis (A := 𝓞 E) (B := 𝓞 K) (K := E) (L := K)
--     (I := span (𝓞 K) (Set.range B.traceDual)) (b := B.traceDual) sorry
--   rw [← restrictScalars_inj (𝓞 E), this] at main
--   simp at main

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] (L₁ L₂ : IntermediateField K M)
  (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
  {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι] (b : Basis ι K L₂)
  (hmain : (differentIdeal (𝓞 K) (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 M)) =
    differentIdeal (𝓞 L₁) (𝓞 M))
  (hb : span (𝓞 K) (Set.range b) = (1 : Submodule (𝓞 L₂) L₂).restrictScalars (𝓞 K))

include hmain in -- Is only inclusion good enough?
theorem aux₁ : span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K)) =
    (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ := by
  rw [← FractionalIdeal.coeIdeal_inj (R := (𝓞 M)) (K := M)] at hmain
  rw [coeIdeal_differentIdeal (𝓞 L₁) L₁, ← inv_eq_iff_eq_inv] at hmain
  rw [← coeToSubmodule_inj] at hmain
  rw [← hmain]
  rw [← extended_coeIdeal_eq_map_algebraMap (K := L₂) M (differentIdeal (𝓞 K) (𝓞 L₂))]
  rw [← extended_inv _ (by simp [coeIdeal_differentIdeal (𝓞 K) K]),
    coeIdeal_differentIdeal (𝓞 K) K, inv_inv]
  rw [coe_extended_eq_span]
  congr!
  ext x
  exact IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := (𝓞 L₂)) (𝓞 L₂)⁰ (𝓞 M)
    L₂ M x

example : span (𝓞 L₁) (Set.range (b.ofLinearDisjoint h₁ h₂)) =
    (1 : Submodule (𝓞 M) M).restrictScalars (𝓞 L₁) :=  by
  have : IsScalarTower (𝓞 K) L₂ M := sorry
  have h := (1 : FractionalIdeal (𝓞 M)⁰ M).dual_dual (𝓞 L₁) L₁
  rw [← coeToSubmodule_inj, ← restrictScalars_inj (𝓞 L₁), coe_one] at h
  rw [← h, coe_dual _ _ (dual_ne_zero (𝓞 L₁) L₁ (one_ne_zero' (FractionalIdeal (𝓞 M)⁰ M)))]
  rw [← aux₁]

  have := Submodule.traceDual_span_of_basis (𝓞 K) (1 : Submodule (𝓞 L₂) L₂) b hb.symm


  have t₁ : (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ =
      span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K)) := by

    sorry
  rw [t₁]
  have t₂ : ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K : Set L₂) =
      Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L₂) L₂) := sorry
  rw [t₂]
  have := Submodule.traceDual_span_of_basis (𝓞 K) (1 : Submodule (𝓞 L₂) L₂) b hb.symm
  rw [SetLike.ext'_iff] at this
  erw [this]
  have : (algebraMap L₂ M : L₂ → M) = (IsScalarTower.toAlgHom (𝓞 K) L₂ M).toLinearMap := rfl
  rw [this, ← map_coe, map_span, ← Set.range_comp]
  rw [span_span_of_tower]
  let B := b.ofLinearDisjoint h₁ h₂
  have t₄ : Set.range ((IsScalarTower.toAlgHom (𝓞 K) L₂ M).toLinearMap ∘ b.traceDual) =
      Set.range B.traceDual := by
    refine congr_arg (Set.range ·) ?_
    rw [eq_comm, Basis.traceDual_eq_iff]
    intro i j
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe,
      Basis.ofLinearDisjoint_apply, traceForm_apply, B, IsScalarTower.coe_toAlgHom']
    rw [← map_mul, h₁.trace_algebraMap_eq]
    have :=  b.apply_traceDual i j
    rw [this]
    simp
    exact h₂
  rw [t₄]
  -- Here things get wrong...
  have t₅ := Submodule.traceDual_span_of_basis (A := 𝓞 L₁) (B := 𝓞 M) (K := L₁) (L := M)
    (I := span (𝓞 M) (Set.range B.traceDual)) (b := B.traceDual) ?_
  · rw [t₅]
    simp
    rfl
  ext
  simp [B] -- not true!
  sorry

--  have t₃ : Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L₂) L₂) ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K : Set L₂)

example : span (𝓞 L₁) (Set.range (b.ofLinearDisjoint h₁ h₂)) =
    (1 : Submodule (𝓞 M) M).restrictScalars (𝓞 L₁) :=  by
  have h := (1 : FractionalIdeal (𝓞 M)⁰ M).dual_dual (𝓞 L₁) L₁
  rw [← coeToSubmodule_inj, ← restrictScalars_inj (𝓞 L₁), coe_one] at h
  rw [← h, coe_dual _ _ (dual_ne_zero (𝓞 L₁) L₁ (one_ne_zero' (FractionalIdeal (𝓞 M)⁰ M)))]

  have t₁ : (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ =
      span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual ℤ ℚ)) := by
    simp

    sorry
  rw [ t₁]
  have t₂ : ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual ℤ ℚ : Set L₂) =
      Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L₂) L₂) := sorry
  rw [t₂]
  have t₃ : (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L₂) L₂) : Set L₂) =
      span ℤ (Set.range ⇑b.traceDual) := by
    -- have := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 L₂) L₂) b hb.symm
    -- rw [← this]
    -- ext


    sorry
  rw [t₃]
  have : (algebraMap L₂ M : L₂ → M) = (algebraMap L₂ M).toIntAlgHom.toLinearMap := rfl
  rw [this, ← map_coe, map_span, ← Set.range_comp]
  rw [span_span_of_tower]
  let B := b.ofLinearDisjoint h₁ h₂
  have t₄ : Set.range ((algebraMap L₂ M).toIntAlgHom.toLinearMap ∘ b.traceDual) =
      Set.range B.traceDual := by
    refine congr_arg (Set.range ·) ?_
    rw [eq_comm, Basis.traceDual_eq_iff]
    intro i j
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe,
      Basis.ofLinearDisjoint_apply, traceForm_apply, B]
    rw [← map_mul, h₁.trace_algebraMap_eq]
    have :=  b.apply_traceDual i j
    rw [this]
    simp
    exact h₂
  rw [t₄]
  have t₅ := Submodule.traceDual_span_of_basis (A := 𝓞 L₁) (B := 𝓞 M) (K := L₁) (L := M)
    (I := span (𝓞 M) (Set.range B.traceDual)) (b := B.traceDual)
  rw [t₅]
  simp
  rfl
  ext
  simp






#exit

  let I := ((1 : FractionalIdeal (𝓞 E)⁰ E).dual (𝓞 ℚ) ℚ).extended K
    (M := (𝓞 E)⁰) (N := (𝓞 K)⁰) (f := algebraMap (𝓞 E) (𝓞 K)) sorry


  have : (1 : FractionalIdeal (𝓞 K)⁰ K).dual (𝓞 E) E  =
      ((differentIdeal (𝓞 ℚ) (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)))⁻¹ := sorry

  have main := dual_dual (𝓞 E) E (1 : FractionalIdeal (𝓞 K)⁰ K)
  rw [← coeToSubmodule_inj, ← Submodule.restrictScalars_inj (𝓞 ℚ)] at main
  rw [coe_dual, coe_dual] at main

#exit
  have : dual (𝓞 E) E (1 : FractionalIdeal (𝓞 K)⁰ K) =
    (differentIdeal (𝓞 E) (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := sorry
  rw [this] at main
  have h₁ : differentIdeal (𝓞 E) (𝓞 K) =
    ((differentIdeal (𝓞 ℚ) (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K))) := sorry
  rw [← coeIdeal_inj (K := K)] at h₁
  rw [h₁] at main
  rw [← extended_coeIdeal_eq_map (L := K) (M := (𝓞 E)⁰) (K := E)] at main
  erw [← extended_inv, coeIdeal_differentIdeal (𝓞 ℚ) ℚ, inv_inv] at main
  let B := dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  let B' := B.extended K (M := (𝓞 E)⁰) (N := (𝓞 K)⁰) (f := algebraMap (𝓞 E) (𝓞 K)) sorry
  let A := dual (𝓞 F) F B'
  let O := (algebraMap (𝓞 E) K).range
  have : (A : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) ((algebraMap (𝓞 E) K).range ⊔ (algebraMap (𝓞 F) K).range) := by





end compositum



-- theorem FractionalIdeal.dual_one_ne_zero (A K : Type*) {L B : Type*} [CommRing A] [Field K]
--     [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
--     [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
--     [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
--     [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] :
--     dual A K (1 : FractionalIdeal B⁰ L) ≠ 0 := by simp

open FractionalIdeal Algebra in
example (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K]
    [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A]
    [IsDedekindDomain B] :
    1 ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) :=
  one_le_dual_one A K (one_mem_one B⁰)

theorem differentIdeal_ne_zero (A K L B: Type*) [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [IsFractionRing B L] [NoZeroSMulDivisors A B] :
    differentIdeal A B ≠ 0 := by
  rw [← (FractionalIdeal.coeIdeal_injective (R := B) (K := L)).ne_iff]
  simp [coeIdeal_differentIdeal A K]

theorem LinearMap.BilinForm.dualBasis_eq_iff {V : Type*} {K : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] [Finite ι] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V) :
    B.dualBasis hB b = v ↔ ∀ i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ ↦ by rw [← h, apply_dualBasis_left],
    fun h ↦ funext fun _ ↦ (B.dualBasis hB b).ext_elem_iff.mpr fun _ ↦ by
      rw [dualBasis_repr_apply, dualBasis_repr_apply, apply_dualBasis_left, h]⟩

/-- Doc. -/
noncomputable def IntermediateField.LinearDisjoint.basis_of_basis_right {F : Type*} {E : Type*}
    [Field F] [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F A]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι] [Finite ι]
    (b : Basis ι F B) :
    Basis ι A E :=
  have : Fintype ι := Fintype.ofFinite ι
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_right' h₁ b.linearIndependent)
    (mul_left_cancel₀ (Module.finrank_pos.ne' :  Module.finrank F A ≠ 0) (by
      rw [← Module.finrank_eq_card_basis b, ← finrank_sup h₁,
        Module.finrank_mul_finrank, h₂, finrank_top']))

@[simp]
theorem IntermediateField.LinearDisjoint.basis_of_basis_right_apply {F : Type*}
    {E : Type*} [Field F] [Field E] [Algebra F E] {A B : IntermediateField F E}
    [FiniteDimensional F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι]
    [Finite ι] (b : Basis ι F B) (i : ι) :
    h₁.basis_of_basis_right h₂ b i = algebraMap B E (b i) := by
  simp [basis_of_basis_right]

/-- Doc -/
noncomputable def Basis.traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]  [DecidableEq ι]
    (b : Basis ι K L) :
    Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

@[simp]
theorem Basis.traceDual_repr_apply {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (x : L) (i : ι) :
    (b.traceDual).repr x i = (Algebra.traceForm K L x) (b i) :=
  (Algebra.traceForm K L).dualBasis_repr_apply _ b _ i

theorem Basis.apply_traceDual_left {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.traceForm K L (b.traceDual i) (b j) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

theorem Basis.apply_traceDual_right {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.traceForm K L (b i) (b.traceDual j) = if i = j then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_right _ (Algebra.traceForm_isSymm K) _ i j

@[simp]
theorem  Basis.traceDual_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    b.traceDual.traceDual = b :=
  (Algebra.traceForm K L).dualBasis_dualBasis _ (Algebra.traceForm_isSymm K) _

@[simp]
theorem Submodule.traceDual_restrictScalars (A K : Type*) {L B : Type*} [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) :
    (Submodule.traceDual A K I).restrictScalars A =
      (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

theorem Submodule.traceDual_span_of_basis {A K L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [IsScalarTower A B L] {I : Submodule B L} {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
  rw [traceDual_restrictScalars, hb]
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

theorem IsLocalization.map_injective_of_injective' {A : Type*} [CommRing A] {B : Type*}
    [CommRing B] {f : A →+* B} (K : Type*) {M : Submonoid A} [CommRing K] [IsDomain K] [Algebra A K]
    [NoZeroSMulDivisors A K] [IsLocalization M K] (L : Type*) {N : Submonoid B} [CommRing L]
    [IsDomain L] [Algebra B L] [NoZeroSMulDivisors B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N) (hf' : Function.Injective f) :
    Function.Injective (map L f hf : K →+* L) := by
  by_cases hM : 0 ∈ M
  · have hK : Unique K := uniqueOfZeroMem hM
    obtain ⟨x, y, h⟩ : ∃ x y : K, x ≠ y := nontrivial_iff.mp inferInstance
    simp [hK.uniq x, hK.uniq y] at h
  refine (injective_iff_map_eq_zero (map L f hf)).mpr fun x h ↦ ?_
  have h₁ : (sec M x).1 = 0 := by
    simpa [map, lift, Submonoid.LocalizationWithZeroMap.lift_apply,
      _root_.map_eq_zero_iff f hf'] using h
  have h₂ : ((sec M x).2 : A) ≠ 0 := ne_of_mem_of_not_mem (SetLike.coe_mem (sec M x).2) hM
  simpa [h₁, h₂] using sec_spec M x

theorem FractionalIdeal.extended_ne_zero {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {f : A →+* B} {K : Type*}
    {M : Submonoid A} [CommRing K] [IsDomain K] [Algebra A K] [NoZeroSMulDivisors A K]
    [IsLocalization M K] (L : Type*) [CommRing L] [IsDomain L] [Algebra B L]
    [NoZeroSMulDivisors B L] {N : Submonoid B} [IsLocalization N L] (hf : M ≤ Submonoid.comap f N)
    (hf' : Function.Injective f) {I : FractionalIdeal M K} (hI : I ≠ 0) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ hf hf')).mpr hx₂

theorem FractionalIdeal.extended_coeIdeal_eq_map {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {f : A →+* B} {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N) (I : Ideal A) :
    (I : FractionalIdeal M K).extended L hf = (I.map f : FractionalIdeal N L) := by
  rw [Ideal.map, Ideal.span, ← coeToSubmodule_inj, Ideal.submodule_span_eq, coe_coeIdeal,
    IsLocalization.coeSubmodule_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_ , ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

theorem FractionalIdeal.extended_inv {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*}
    [Field K] [Algebra A K] [IsLocalization A⁰ K] {B : Type*} [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [Algebra A B] [NoZeroSMulDivisors A B]
    [h : IsLocalization B⁰ L]
    {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs (f := algebraMap A B) I⁻¹ =
       (extended L hs (f := algebraMap A B) I : FractionalIdeal B⁰ L)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀, ← extended_mul, inv_mul_cancel₀ hI, extended_one]
  exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI

open nonZeroDivisors NumberField Algebra

theorem differentIdeal.mem_iff (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] (x : B) :
    x ∈ differentIdeal A B ↔
    letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
    ∀ (y : FractionRing B), (∀ (b : B),
     trace (FractionRing A) (FractionRing B) (y * algebraMap B (FractionRing B) b) ∈
      (algebraMap A (FractionRing A)).range) →
      algebraMap B (FractionRing B) x * y ∈ (algebraMap B (FractionRing B)).range := by
  simp only [differentIdeal, Submodule.mem_comap, linearMap_apply,
    Submodule.mem_div_iff_smul_subset, Set.smul_set_subset_iff, SetLike.mem_coe,
    Submodule.mem_traceDual, Submodule.mem_one, traceForm_apply, RingHom.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff, smul_eq_mul]

-- theorem FractionalIdeal.extended_ne_zero {A : Type*} [CommRing A] (M : Submonoid A) {K : Type*}
--     [Field K] [Algebra A K] [IsLocalization M K] {B : Type*} [CommRing B] {L : Type*} [Field L]
--     [Algebra B L] [Algebra A B] [h : IsLocalization (Submonoid.map (algebraMap A B) M) L]
--     {I : FractionalIdeal M K} (hI : I ≠ 0) :
--     extended L (M.le_comap_map (f := algebraMap A B)) I ≠ 0 := by
--   simp [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
--     Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
--     map_eq_zero, not_forall, Classical.not_imp] at ⊢
--   simp [ne_eq, ← coeToSubmodule_inj, coe_zero, Submodule.eq_bot_iff, mem_coe, not_forall,
--     Classical.not_imp] at hI
--   exact hI


-- theorem FractionalIdeal.extended_inv {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*}
--     [Field K] [Algebra A K] [IsLocalization A⁰ K] {B : Type*} [CommRing B] [IsDedekindDomain B]
--     {L : Type*} [Field L] [Algebra B L] [Algebra A B]
--     [h : IsLocalization (Submonoid.map (algebraMap A B) A⁰) L] [h' : IsLocalization B⁰ L]
--     {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
--     extended L (A⁰.le_comap_map (f := algebraMap A B)) I⁻¹ =
--       (extended L (A⁰.le_comap_map (f := algebraMap A B)) I)⁻¹ := sorry

-- -- open FractionalIdeal in
-- -- example {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
-- --     {B : Type*} [CommRing B] {L : Type*} [Field L] [Algebra B L]
-- --     [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
-- --     [IsDedekindDomain A] [IsDedekindDomain B] [IsIntegrallyClosed A] [IsIntegrallyClosed B]
-- --     [IsIntegralClosure B A L] [FiniteDimensional K L]
-- --     [IsIntegrallyClosed B] [h : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
-- --     {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : 1 = 0 := by
-- --   have : IsLocalization (Submonoid.map (algebraMap A B) A⁰) L := by
-- --     rwa [Algebra.algebraMapSubmonoid] at h
-- --   have := A⁰.le_comap_map (f := algebraMap A B)
-- --   have : extended L this I ≠ 0 := by
-- --     simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
-- --       Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
-- --       map_eq_zero, not_forall, Classical.not_imp] at ⊢
-- --     simp only [ne_eq, ← coeToSubmodule_inj, coe_zero, Submodule.eq_bot_iff, mem_coe, not_forall,
-- --       Classical.not_imp] at hI
-- --     exact hI

-- -- theorem FractionalIdeal.extended_ne_zero {A : Type*} [CommRing A] {B : Type*} [CommRing B]
-- --     {f : A →+* B} {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
-- --     (L : Type*) [CommRing L] [Algebra B L] [IsLocalization (Submonoid.map f M) L]
-- --     (hf : Function.Injective f) {I : FractionalIdeal M K} (hI : I ≠ 0) :
-- --     extended L (M.le_comap_map (f := f)) I ≠ 0 := by
-- --   simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
-- --     Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
-- --     not_forall, Classical.not_imp] at ⊢
-- --   simp only [ne_eq, ← coeToSubmodule_inj, coe_zero, Submodule.eq_bot_iff, mem_coe, not_forall,
-- --     Classical.not_imp] at hI
-- --   obtain ⟨x, hx, hx'⟩ := hI
-- --   use x
-- --   use hx
-- --   have := IsLocalization.map_injective_of_injective M K L hf
-- --   exact (map_ne_zero_iff (IsLocalization.map L f _) this).mpr hx'

-- theorem FractionalIdeal.extended_inv {A K : Type*} [Field K] [CommRing A] [IsDedekindDomain A]
--     [Algebra A K] [IsFractionRing A K] {B L : Type*} [Field L] [CommRing B] [IsDedekindDomain B]
--     [Algebra B L] [IsFractionRing B L] {f : A →+* B} [IsLocalization (Submonoid.map f A⁰) L]
--     (hf₁ : A⁰ ≤ Submonoid.comap f B⁰) (hf₂ : Function.Injective f) {I : FractionalIdeal A⁰ K}
--     (hI : I ≠ 0) :
--     extended L hf₁ I⁻¹ = (extended L hf₁ I)⁻¹ := by
--   rw [← mul_eq_one_iff_eq_inv₀, ← extended_mul, inv_mul_cancel₀ hI, extended_one]
--   have := FractionalIdeal.extended_ne_zero (A := A) (B := B) (K := K) (L := L) (M := A⁰)
--     (f := f) hf₂ hI




--   sorry



variable {A B C K L M : Type*}
variable [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]

variable [IsDomain B] [IsIntegrallyClosed B] -- [IsNoetherianRing B]

variable [CommRing C] [Field M] [Algebra C M] [IsFractionRing C M]

variable [IsDomain C] [IsIntegrallyClosed C]

variable [Algebra L M]
variable [Algebra K L] [Algebra K M]
variable [Algebra B M] [Algebra B C]
variable [Algebra A B] [Algebra A C] [Algebra A L] [Algebra A M]
variable [IsScalarTower K L M]
variable [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower A B L] [IsScalarTower A C M]
variable [IsScalarTower B L M] [IsScalarTower B C M]

variable [Algebra.IsIntegral B C]

-- variable [IsIntegralClosure C B M]
variable [NoZeroSMulDivisors B C]
variable [FiniteDimensional K M]

-- variable [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
-- variable [Algebra B C] [Algebra B E] [IsScalarTower B C E] [IsScalarTower B F E]
-- variable [Algebra A B] [Algebra A C] [IsScalarTower A B C]
-- variable [Algebra A F] [IsScalarTower A B F] [IsScalarTower A K F]
-- variable [Algebra A E] [IsScalarTower A C E] [IsScalarTower A K E]
-- variable [FiniteDimensional K E] [Algebra.IsSeparable K E]
-- variable [IsIntegralClosure B A F] [IsIntegralClosure C A E] [IsIntegralClosure C B E]
-- variable [NoZeroSMulDivisors B C]

-- example [Algebra.IsSeparable L M] {I : Submodule B L} :
--     Submodule.span C (algebraMap L M '' Submodule.traceDual A K I) ≤
--       Submodule.traceDual A K (Submodule.span C (algebraMap L M '' I)) := by
--   have : Module.Finite K L := Module.Finite.left K L M
--   have : Module.Finite L M := Module.Finite.right K L M
--   have : IsIntegralClosure C B M := IsIntegralClosure.of_isIntegrallyClosed _ _ _
--   have : Module.Finite B C := IsIntegralClosure.finite B L M C
--   rw [Submodule.span_le]
--   rintro _ ⟨x, hx, rfl⟩
--   rw [SetLike.mem_coe, Submodule.mem_traceDual] at hx ⊢
--   intro y hy
--   rw [Submodule.mem_span_image_iff_exists_fun] at hy
--   obtain ⟨s, hs, c, rfl⟩ := hy
--   rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := L), ← Algebra.smul_def, map_smul,
--     smul_eq_mul]
--   apply hx
--   rw [map_sum]
--   refine Submodule.sum_mem I fun i _ ↦ ?_
--   rw [Algebra.smul_def, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
--     ← Algebra.algebraMap_intTrace (A := B) (c i), mul_comm, ← Algebra.smul_def]
--   exact Submodule.smul_mem _ _ (hs i.prop)

variable [IsDedekindDomain A] [IsIntegralClosure C A M] [Algebra.IsSeparable K M]
  [IsIntegralClosure B A L] [IsDedekindDomain B] [IsDedekindDomain C]

-- variable (B C) in
-- theorem zozo : B⁰ = Submonoid.comap (algebraMap B C) C⁰ := by
--     ext x
--     simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap,
--       FaithfulSMul.algebraMap_eq_zero_iff]

variable [IsScalarTower A L M] [FiniteDimensional K M] [Algebra.IsSeparable K L]
  [Algebra.IsSeparable K M]
-- variable [FiniteDimensional K L] [Algebra.IsSeparable K L] -- Infer those

open Algebra FractionalIdeal

-- Use integral ideals !
theorem step₁ (h' : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) M) :
    have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ := by
      refine le_of_eq ?_
      ext
      simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap,
        FaithfulSMul.algebraMap_eq_zero_iff]
    have : Module.Finite L M := Module.Finite.right K L M
    have : Module.Finite K L := Module.Finite.left K L M
    have : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
    FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ M) =
      FractionalIdeal.dual B L (1 : FractionalIdeal C⁰ M) *
        (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h := by
  -- rw [FractionalIdeal.dual_eq_mul_inv _ _ I, FractionalIdeal.extended_mul]
  -- have : FractionalIdeal.extended M (zozo B C).le I⁻¹ =
  --   (FractionalIdeal.extended M (zozo B C).le I)⁻¹ := by sorry
  -- rw [this, eq_comm]
  -- rw [mul_inv_eq_iff_eq_mul₀]
  -- rw [FractionalIdeal.dual_mul_self]
  -- have h := (zozo B C).le
  -- have  : Submonoid.map (algebraMap B C) B⁰ ≤ C⁰ := by
  --   clear h
  --   intro x hx
  --   simp at hx
  -- rw [algebraMapSubmonoid] at h'
  -- rw [← Submonoid.map_le_iff_le_comap] at h
  have : Module.Finite L M := Module.Finite.right K L M
  have : Module.Finite K L := Module.Finite.left K L M
  have : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ := by
      refine le_of_eq ?_
      ext
      simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap,
        FaithfulSMul.algebraMap_eq_zero_iff]
  have hI₁ : FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) ≠ 0 := by
    refine FractionalIdeal.dual_ne_zero A K ?_
    exact one_ne_zero' (FractionalIdeal B⁰ L)
  have hI₂ : (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h ≠ 0 := by
    simp [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
      Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      map_eq_zero, not_forall, Classical.not_imp] at ⊢
    simp [ne_eq, ← coeToSubmodule_inj, coe_zero, Submodule.eq_bot_iff, mem_coe, not_forall,
      Classical.not_imp] at hI₁
    obtain ⟨x, hx₁, hx₂⟩ := hI₁
    refine ⟨x, ?_, hx₂⟩
    rw [← @mem_coe]
    simpa
  -- have : FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ M) =
  --     FractionalIdeal.dual B L (1 : FractionalIdeal C⁰ M) *
  --       (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h := by
  have h_loc {x : L} : IsLocalization.map M (algebraMap B C) h x = algebraMap L M x := by
    have := IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := B) (M := B⁰) (S := C)
      (Rₘ := L) (Sₘ := M) x
    exact this.symm
  apply le_antisymm
  · intro x hx
    dsimp at hx ⊢
    rw [FractionalIdeal.mem_coe] at hx ⊢
    have h₁ (c : C) : trace L M (x * algebraMap C M c) ∈
        FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal B⁰ L))]
      rintro _ ⟨y, _, rfl⟩
      simp
      rw [mul_comm, ← smul_eq_mul, ← map_smul, trace_trace]
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal C⁰ M))] at hx
      simp at hx
      specialize hx (algebraMap B L y • algebraMap C M c) (by
        refine (FractionalIdeal.mem_one_iff C⁰).mpr ?_
        use algebraMap B C y * c
        rw [Algebra.smul_def]
        rw [map_mul]
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
      rwa [mul_smul_comm] at hx
    have h₂ {c : C} {z : L} (hz : z ∈ (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹) :
        trace L M (x * algebraMap L M z * algebraMap C M c) ∈ (algebraMap B L).range := by
      rw [FractionalIdeal.mem_inv_iff] at hz
      have := h₁ c
      rw [mul_comm x, mul_assoc, ← smul_def, map_smul, smul_eq_mul]
      have := hz (trace L M (x * (algebraMap C M c))) (h₁ c)
      obtain ⟨b, hb₁, hb₂⟩ := this
      rw [← hb₂]
      simp
      refine FractionalIdeal.dual_ne_zero A K ?_
      exact one_ne_zero' (FractionalIdeal B⁰ L)
    have h₃ {z : L} (hz : z ∈ (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹) :
        x * algebraMap L M z ∈ FractionalIdeal.dual B L (1 : FractionalIdeal C⁰ M) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal C⁰ M))]
      rintro m ⟨m, _, rfl⟩
      rw [linearMap_apply, traceForm_apply]
      exact h₂ hz
    have h₄ {z : M}
        (hz : z ∈ ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹) :
        x * z ∈ FractionalIdeal.dual B L (1 : FractionalIdeal C⁰ M) := by
      have : ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹.extended M h) =
        ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv₀ hI₂, ← FractionalIdeal.extended_mul, inv_mul_cancel₀ hI₁,
          FractionalIdeal.extended_one]
      rw [← this, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_extended_eq_span,
        Submodule.mem_span_image_iff_exists_fun] at hz
      obtain ⟨s, hs, _, rfl⟩ := hz
      simp_rw [Finset.mul_sum, mul_smul_comm]
      refine Submodule.sum_smul_mem _ _ fun i _ ↦ ?_
      rw [h_loc]
      apply h₃
      exact hs i.prop
    have h₅ : FractionalIdeal.spanSingleton C⁰ x *
        ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹ ≤
          FractionalIdeal.dual B L (1 : FractionalIdeal C⁰ M) := by
      refine FractionalIdeal.spanSingleton_mul_le_iff.mpr fun z hz ↦ h₄ hz
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    have h₆ :=
      FractionalIdeal.mul_right_mono
        ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)).extended M h) h₅
    dsimp at h₆
    rwa [inv_mul_cancel_right₀] at h₆
    exact hI₂
  · intro x hx
    simp at hx ⊢
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
        rw [Submodule.mem_span_image_iff_exists_fun] at hn
        obtain ⟨s, hs, _, rfl⟩ := hn
        simp_rw [Finset.mul_sum, mul_smul_comm]
        refine Submodule.sum_smul_mem _ _ fun i _ ↦ ?_
        rw [Submodule.mem_traceDual] at hm ⊢
        intro c hc
        simp at hc
        obtain ⟨a, rfl⟩ := hc
        simp at hm ⊢
        rw [← Algebra.trace_trace (S := L), h_loc, mul_comm m, mul_assoc,
          ← Algebra.smul_def, map_smul]
        specialize hm a
        obtain ⟨b, hb⟩ := hm
        rw [← hb]
        have hi := hs i.prop
        rw [SetLike.mem_coe, FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal B⁰ L))] at hi
        simp at hi
        apply hi
        exact FractionalIdeal.coe_mem_one B⁰ b
    | add x _ y _ hx hy =>
        exact Submodule.add_mem _ hx hy

variable [NoZeroSMulDivisors A B] [NoZeroSMulDivisors A C] [Algebra.IsSeparable C (FractionRing C)]

-- use FractionRing
example :
    differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) := by
  rw [← FractionalIdeal.coeIdeal_inj (K := FractionRing C), FractionalIdeal.coeIdeal_mul,
    coeIdeal_differentIdeal B C]


  apply FractionalIdeal.coeToSubmodule_injective
  simp
  apply le_antisymm
  ·
    sorry
  · intro x hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem _ h₁ _ h₂ =>
      rw [IsLocalization.mem_coeSubmodule] at h₁ h₂
      obtain ⟨c₁, hc₁, rfl⟩ := h₁
      obtain ⟨c₂, hc₂, rfl⟩ := h₂
      rw [Ideal.map, Ideal.span, Submodule.mem_span_image_iff_exists_fun] at hc₂
      obtain ⟨s, hs, _, rfl⟩ := hc₂
      rw [map_sum, Finset.mul_sum]
      simp_rw [smul_eq_mul, map_mul, ← mul_assoc, mul_comm (algebraMap C M c₁), mul_assoc,
        ← smul_def]
      refine Submodule.sum_smul_mem _ _ fun i _ ↦ ?_
      rw [IsLocalization.mem_coeSubmodule]
      rw [differentIdeal.mem_iff] at hc₁








      sorry
    | add x hx y hy _ _ =>
      sorry

#lint

#exit

  intro x hx
  simp only [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe,
    FractionalIdeal.coe_extended_eq_span] at hx ⊢


  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := Module.Finite.right K L M
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  have hI₁ : I ≠ 0 := sorry
  have hI₂ : (FractionalIdeal.extended M (zozo B C).le I) ≠ 0 := sorry
  have hI₃ : FractionalIdeal.dual A K I ≠ 0 := sorry
  have h₁ : ∀ c : C, Algebra.trace L M (c • x) ∈ FractionalIdeal.dual A K I := by
    intro c
    simp_rw [FractionalIdeal.mem_dual hI₁, FractionalIdeal.mem_dual hI₂,
      Algebra.traceForm_apply] at hx ⊢
    intro i hi
    have := hx (c • algebraMap L M i) ?_
    · rwa [Algebra.smul_def, ← mul_rotate', ← Algebra.smul_def, ← Algebra.trace_trace (S := L),
        map_smul, smul_eq_mul, mul_comm, mul_comm x, ← Algebra.smul_def] at this
    apply Submodule.smul_mem
    apply Submodule.subset_span
    have := IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := B) (M := B⁰) (S := C)
      (Rₘ := L) (Sₘ := M)
    rw [this]
    exact Set.mem_image_of_mem _ hi
  have h₂ : ∀ c : C, (FractionalIdeal.spanSingleton B⁰ (Algebra.trace L M (c • x))) *
      (FractionalIdeal.dual A K I)⁻¹ ≤ 1 := by
    intro c
    rw [← FractionalIdeal.le_div_iff_mul_le, FractionalIdeal.div_eq_mul_inv, inv_inv, one_mul]
    exact FractionalIdeal.spanSingleton_le_iff_mem.mpr (h₁ c)
    exact inv_ne_zero hI₃
  have h₃ : ∀ i ∈ (FractionalIdeal.dual A K I)⁻¹, ∀ c : C,
      Algebra.trace L M (i • c • x) ∈ (algebraMap B L).range := sorry
  have h₄ :  ∀ i ∈ (FractionalIdeal.dual A K I)⁻¹, i • x ∈
      FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ M) := sorry


--   rw [@FractionalIdeal.spanSingleton_mul_le_iff]


#exit

example {I : FractionalIdeal B⁰ F} (h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰) :
    have : FiniteDimensional K F := sorry
    have : Algebra.IsSeparable K F := sorry
    FractionalIdeal.extended E h (FractionalIdeal.dual A K I) =
      FractionalIdeal.dual A K (I.extended E h) := by
  by_cases hI : I = 0
  · simp [hI]
  have hI' :  FractionalIdeal.extended E h I ≠ 0 := sorry
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_extended_eq_span, FractionalIdeal.coe_dual _ _ hI']
  rw [toto, toto]











  have {a} : (IsLocalization.map E (algebraMap B C) h) a = algebraMap F E a := by
    have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := by
      have :  B⁰ = Submonoid.comap (algebraMap B C) C⁰ := sorry
      rw [Algebra.algebraMapSubmonoid, this]
      apply IsLocalization.isLocalization_of_submonoid_le

      have := Algebra.algebraMapSubmonoid_le_comap B⁰ (IsScalarTower.toAlgHom B C E)
      rw [this]
      rw [← @Submonoid.comap_map_comap]
      rw?
    rw [IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := B) (S := C) (M := B⁰)]
    sorry
#exit

    (x : E) : 1 = 0 := by
  have : C⁰ = Algebra.algebraMapSubmonoid C B⁰ := sorry
  have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := sorry
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) E := sorry
  let _ : Algebra F E := localizationAlgebra B⁰ C
  let _ : Algebra K E := localizationAlgebra A⁰ C
  have : IsScalarTower K F E := sorry
  have : Module.Finite K E := sorry

  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite K F E
  have : Algebra.IsSeparable F E := Algebra.isSeparable_tower_top_of_isSeparable K F E
  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ := by
    refine nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap B C) ?_
    refine NoZeroSMulDivisors.iff_algebraMap_injective.mp ?_
    infer_instance
  let J₀ := FractionalIdeal.extended E h (FractionalIdeal.dual A K I)
  let J₁ := FractionalIdeal.dual A K (I.extended E h)
  have : J₀ = J₁ := by
    unfold J₀ J₁
    by_cases hI : I = 0
    · simp [hI]
    ext x
    have : FractionalIdeal.extended E h I ≠ 0 := sorry
    simp_rw [FractionalIdeal.mem_dual this, FractionalIdeal.mem_extended_iff]
    constructor
    intro hx a ha
    induction hx, ha using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        rw [SetLike.mem_coe, FractionalIdeal.mem_dual hI] at ha
        specialize ha b hb
        rw [Algebra.traceForm_apply]
        have : (IsLocalization.map E (algebraMap B C) h) a = algebraMap F E a := by
          have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := by
            sorry
          have : C⁰ = Algebra.algebraMapSubmonoid C B⁰ := sorry
          have := localizationAlgebraMap_def (R := B) (S := C) (Sₘ := E) (Rₘ := F) (M := B⁰)
          have := (RingHom.congr_fun this a).symm
          convert this

          sorry
        rw [this]
        have : (IsLocalization.map E (algebraMap B C) h) b = algebraMap F E b := sorry
        rw [this]
        rw [← map_mul, ← Algebra.trace_trace (S := F), Algebra.trace_algebraMap]
        simp at ha
        obtain ⟨r, hr⟩ := ha
        refine ⟨Module.finrank F E • r, ?_⟩
        rw [map_nsmul, map_nsmul, hr]
    | zero_left y hy => sorry
    | zero_right x hx => sorry
    | add_left x y z hx hy hz _ _ => sorry
    | add_right x y z hx hy hz _ _ => sorry
    | smul_left r x y hx hy _ => sorry
    | smul_right r x y hx hy _ => sorry


#exit

  have : x ∈ FractionalIdeal.extended E h (FractionalIdeal.dual A K I) → x = 1 := by
    rw [FractionalIdeal.mem_extended_iff]
    intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_dual] at hx



      sorry

  sorry

#exit

variable {A K B E C F : Type*}
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
  [CommRing B] [Field E] [Algebra B E] [IsFractionRing B E]
  [CommRing C] [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra K E] [Algebra K F] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional K E]
  [Algebra.IsSeparable K E]
  [Algebra A F] [IsScalarTower A K F] [IsIntegralClosure C A F]
  [Algebra A E] [IsScalarTower A K E] [IsIntegralClosure B A E]
  [Algebra A B] [IsScalarTower A B E]
  [Algebra C B] [Algebra C E] [IsScalarTower C F E] [IsScalarTower C B E]
  [Algebra A C] [IsScalarTower A K F] [IsScalarTower A C F]
  [IsDedekindDomain A]
  [IsIntegrallyClosed C]
  [FiniteDimensional F E]
  [IsIntegralClosure B C E]
  [Algebra.IsSeparable F E]
  [IsDedekindDomain B]
  [IsDedekindDomain C]
  [FiniteDimensional K F]
  [Algebra.IsSeparable K F]
  [NoZeroSMulDivisors C B]

open nonZeroDivisors

set_option maxHeartbeats 1000000 in
example : 1 = 0 := by
  let BEK := FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ E)
--  let BEK := Submodule.traceDual A K (1 : Submodule B E)
  let BEF := FractionalIdeal.dual C F (1 : FractionalIdeal B⁰ E)
--  let BEF := Submodule.traceDual C F (1 : Submodule B E)
  let CFK₀ := FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ F)
  have h₀ : C⁰ ≤ Submonoid.comap (algebraMap C B) B⁰ := by
    refine nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap C B) ?_
    refine NoZeroSMulDivisors.iff_algebraMap_injective.mp ?_
    infer_instance
  let CFK : FractionalIdeal B⁰ E := FractionalIdeal.extended E h₀ CFK₀
  have : BEK = BEF * CFK := by
    unfold BEK BEF CFK CFK₀
    apply le_antisymm
    · intro b hb
      dsimp at hb ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hb
      rw [FractionalIdeal.mem_coe]
      rw [← FractionalIdeal.dual_inv, FractionalIdeal.mem_dual]



      sorry
    refine (FractionalIdeal.le_dual_iff A K ?_).mp ?_
    · sorry
    · intro z hz
      dsimp at hz ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hz ⊢
      · intro x hx
        rw [FractionalIdeal.mem_extended_iff] at hx
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · sorry

        · simp
        · rintro _ _ _ _ ⟨x, hx⟩ ⟨y, hy⟩
          rw [map_add, ← hx, ← hy, ← map_add]
          exact ⟨x + y, rfl⟩
        · rintro b n hn ⟨y, hy⟩
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
          · rintro _ ⟨t, ht, rfl⟩
            have : (IsLocalization.map E (algebraMap C B) h₀) t = algebraMap F E t := sorry
            rw [this]
            simp
            rw [Algebra.smul_def, ← Algebra.trace_trace (S := F)]
            have : (algebraMap B E) b * (z * (algebraMap F E) t) =
              t • ((algebraMap B E b) * z) := sorry
            rw [this, map_smul, mul_comm]
            simp at hz
            specialize hz (algebraMap B E b) sorry
            obtain ⟨l, hl⟩ := hz
            rw [← hl]
            simp at hy


            sorry
          · sorry
          · sorry
          · sorry
      · sorry
      · exact one_ne_zero

#exit
    ext x


--    rw [FractionalIdeal.mul_def]
    simp [FractionalIdeal.mem_dual]
    constructor
    · intro h
      rw [← FractionalIdeal.mem_coe]
      simp

      sorry
    · intro hx
      rw [← FractionalIdeal.mem_coe] at hx
      simp at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro m hm n hn
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
        · rintro _ ⟨x, hx, rfl⟩ a ha
          rw [FractionalIdeal.mem_one_iff] at ha
          obtain ⟨y, rfl⟩ := ha
          rw [Submodule.mem_traceDual] at hm
          simp at hm
          obtain ⟨z, hz⟩ := hm y
          rw [SetLike.mem_coe, FractionalIdeal.mem_dual] at hx
          simp at hx
          specialize hx (algebraMap C F z) sorry
          obtain ⟨t, ht⟩ := hx
          refine ⟨t, ?_⟩
          rw [← Algebra.trace_trace (S := F)]
          have : m * (IsLocalization.map E (algebraMap C B) this) x * (algebraMap B E y) =
              x • ((algebraMap B E y) * m) := by
            have : IsLocalization (Algebra.algebraMapSubmonoid B C⁰) E := by
              exact IsIntegralClosure.isLocalization_of_isSeparable C F E B
            have := localizationAlgebraMap_def (R := C) (S := B) (Sₘ := E) (Rₘ := F) (M := C⁰)

            erw [← localizationAlgebraMap_def]
            rw [Algebra.smul_def]
            rw [mul_comm _ m, ← mul_assoc, mul_comm _ m]
            congr
            sorry
          rw [this, map_smul, mul_comm, ← hz, smul_eq_mul, ht]
          exact Ne.symm (zero_ne_one' (FractionalIdeal C⁰ F))
        · intro _ _
          refine ⟨0, by simp⟩
        · intro x y _ _ hx hy a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          obtain ⟨y₁, hy₁⟩ := hy a ha
          refine ⟨x₁ + y₁, ?_⟩
          simp [hx₁, hy₁, mul_add, add_mul, map_add]
        · intro b x _ hx a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          rw [Algebra.smul_def]

          sorry
      · sorry
