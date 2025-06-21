import Mathlib

open nonZeroDivisors NumberField

theorem differentIdeal_ne_zero (A K L B : Type*) [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [IsFractionRing B L] [NoZeroSMulDivisors A B] :
    differentIdeal A B ≠ 0 := by
  rw [← (FractionalIdeal.coeIdeal_injective (R := B) (K := L)).ne_iff]
  simp [coeIdeal_differentIdeal A K]

theorem IntermediateField.LinearDisjoint.trace_algebraMap_eq {F : Type*} {E : Type*} [Field F]
    [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F E]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) (x : B) :
    Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algebra.trace F B x) := by
  let b := Module.Free.chooseBasis F B
  simp_rw [Algebra.trace_eq_matrix_trace b,
    Algebra.trace_eq_matrix_trace (b.ofLinearDisjoint h₁ h₂),
    Matrix.trace, map_sum, b.ofLinearDisjoint_leftMulMatrix_eq, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply]

theorem IntermediateField.LinearDisjoint.norm_algebraMap_eq {F : Type*} {E : Type*} [Field F]
    [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F E]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) (x : B) :
    Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.norm F x) := by
  let b := Module.Free.chooseBasis F B
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (b.ofLinearDisjoint h₁ h₂),
    b.ofLinearDisjoint_leftMulMatrix_eq, RingHom.map_det]

theorem LinearMap.BilinForm.dualBasis_eq_iff {V : Type*} {K : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] [Finite ι] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V) :
    B.dualBasis hB b = v ↔ ∀ i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ ↦ by rw [← h, apply_dualBasis_left],
    fun h ↦ funext fun _ ↦ (B.dualBasis hB b).ext_elem_iff.mpr fun _ ↦ by
      rw [dualBasis_repr_apply, dualBasis_repr_apply, apply_dualBasis_left, h]⟩

/-- Doc -/
noncomputable def Basis.traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

@[simp]
theorem Basis.traceDual_repr_apply {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (x : L) (i : ι) :
    (b.traceDual).repr x i = (Algebra.traceForm K L x) (b i) :=
  (Algebra.traceForm K L).dualBasis_repr_apply _ b _ i

theorem Basis.apply_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
theorem Basis.traceDual_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    b.traceDual.traceDual = b :=
  (Algebra.traceForm K L).dualBasis_dualBasis _ (Algebra.traceForm_isSymm K) _

@[simp]
theorem Basis.traceDual_involutive (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  fun b ↦ traceDual_traceDual b

theorem Basis.traceDual_injective (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceDual_involutive K L).injective

@[simp]
theorem Basis.traceDual_inj {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b b' : Basis ι K L):
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

theorem Basis.traceDual_eq_iff {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (v : ι → L) :
    b.traceDual = v ↔
      ∀ i j, Algebra.traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

@[simp]
theorem Submodule.traceDual_restrictScalars (A K : Type*) {L B : Type*} [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) :
    (Submodule.traceDual A K I).restrictScalars A =
      (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

theorem Submodule.traceDual_span_of_basis (A : Type*) {K L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
  rw [traceDual_restrictScalars, hb]
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

instance (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F] [Algebra F K] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) (𝓞 F)⁰) K := by
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, by simpa using ne_zero ha, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa using ne_zero hx

open nonZeroDivisors Algebra FractionalIdeal
section numberfield

open NumberField

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal' :
    differentIdeal (𝓞 K) (𝓞 M) =
       differentIdeal (𝓞 L) (𝓞 M) *
        (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (𝓞 M)) :=
  differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) K (𝓞 L) L (𝓞 M) M

end numberfield

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
