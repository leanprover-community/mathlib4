/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Order.Module.Synonym

/-!

# Hahn embedding theorem on ordered modules

This file proves a variation of Hahn embedding theorem:

For a linearly ordered module $M$ over an Archimedean division ring $K$,
there exists a strictly monotune linear map to lexicographically ordered
`HahnSeries (ArchimedeanClass₀ M) R` with an archimedean module $R$ over the same ring
as long as for a family of `ArchimedeanClass.IsGrade` submodule of $M$, there exists a
strictly monotune linear map to $R$ for each grade.

By setting $K = ℚ$ and $R = ℝ$, the condition can be trivially satisfied, leading
to a proof of the classic Hahn embedding theorem. (TODO: implement this)

## Main definition
* `HahnEmbeddingSeed K M R` specifies a family of `ArchimedeanClass.IsGrade` submodule of `M`, and
  strictly monotune linear maps from each grade to module `R`.

## Main theorem
* `exists_linearMap_hahnSeries_strictMono`: there exists a strictly monotune
  `M →ₗ[K] Lex (HahnSeries (ArchimedeanClass₀ M) R)` as long as
  `HahnEmbeddingSeed K M R` is nonempty.

## References

* [M. Hausner, J.G. Wendel, *Ordered vector spaces*][mhausnerjgwendel1952]

-/

namespace HahnSeries
variable {Γ : Type*} {R : Type*} [PartialOrder Γ] [AddCommMonoid R]
variable (K : Type*) [Semiring K]
variable [Module K R]

/-- Move this -/
noncomputable
def truncateLinearMap (c : Γ) : HahnSeries Γ R →ₗ[K] HahnSeries Γ R where
  toFun (x) := ⟨
    fun i ↦ open Classical in if c ≤ i then 0 else x.coeff i,
    Set.IsPWO.mono x.isPWO_support (by simp)
  ⟩
  map_add' x y := by
    ext i
    by_cases h : c ≤ i <;> simp [h]
  map_smul' s x := by
    ext i
    simp

theorem coeff_truncate_eq {c i : Γ} (h : i < c) (x : HahnSeries Γ R) :
    (truncateLinearMap K c x).coeff i = x.coeff i := by
  simp [truncateLinearMap, not_le_of_gt h]

theorem coeff_truncate_eq_zero {c i : Γ} (h : c ≤ i) (x : HahnSeries Γ R) :
    (truncateLinearMap K c x).coeff i = 0 := by
  simp [truncateLinearMap, h]

/-- Move this -/
def ofFinsupp (f : Γ →₀ R) : HahnSeries Γ R where
  coeff := f
  isPWO_support' := f.finite_support.isPWO

variable (Γ R) in
/-- Move this -/
@[simps]
def ofFinsuppLinearMap : (Γ →₀ R) →ₗ[K] HahnSeries Γ R where
  toFun := ofFinsupp
  map_add' _ _ := by
    ext _
    simp [ofFinsupp]
  map_smul' _ _ := by
    ext _
    simp [ofFinsupp]


end HahnSeries

/-! ### Step 1: base embedding

We start constructing the embedding with a "seed" `HahnEmbeddingSeed`,
which specifies how to embed each Archimedean grade of `M` into `R`
(which always exists if `R = ℝ`). From these, we can create partial map from
the direct sum of all grades to `HahnSeries Γ R`. If `ArchimedeanClass M` is finite, then the
direct sum is the entire `M` and we are done (though we don't specifically prove for this case).
Otherwise, we will extend the map to `M` in the following steps.
-/

open ArchimedeanClass

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [PosSMulMono K M]
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R]
variable [Module K R]

variable (K M R) in
/-- specifies a family of `IsGrade` submodule of `M`, and
strictly monotune linear maps from each grade to module `R`. -/
structure HahnEmbeddingSeed where
  /-- For each `ArchimedeanClass`, specify a corresponding grade. -/
  grades : ArchimedeanClass M → Submodule K M
  /-- For each grade, specify a linear map to `R` as the Hahn series coefficient. -/
  gradeMap (A : ArchimedeanClass M) : grades A →ₗ[K] R
  /-- Asserts that `grades` are indeed grades. -/
  isGrade (A : ArchimedeanClass M) : IsGrade A (grades A)
  /-- Asserts that `gradeMap` is strictly monotone. -/
  strictMono (A : ArchimedeanClass M) : StrictMono (gradeMap A)

open DirectSum

/-- The minimal submodule that contains all grades. -/
abbrev HahnEmbeddingSeed.baseDomain (seed : HahnEmbeddingSeed K M R) := ⨆ A, seed.grades A

/-- Grades as a submodule of `HahnEmbeddingSeed.baseDomain`. -/
abbrev HahnEmbeddingSeed.grades' (seed : HahnEmbeddingSeed K M R) (A : ArchimedeanClass M) :
    Submodule K (baseDomain seed) :=
  (seed.grades A).comap seed.baseDomain.subtype

/-- `HahnEmbeddingSeed.gradeMap` with `HahnEmbeddingSeed.grades'` as codomain. -/
abbrev HahnEmbeddingSeed.gradeMap' (seed : HahnEmbeddingSeed K M R) (A : ArchimedeanClass M) :
    grades' seed A →ₗ[K] R := (seed.gradeMap A).comp (LinearMap.submoduleComap _ _)

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem HahnEmbeddingSeed.iSupIndep (seed : HahnEmbeddingSeed K M R) :
    iSupIndep (seed.grades') := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic seed.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert iSupIndep_of_isGrade seed.isGrade
  ext1 A
  simpa using le_iSup _ _

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem HahnEmbeddingSeed.isInternal (seed : HahnEmbeddingSeed K M R) :
    DirectSum.IsInternal (grades' seed) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep seed)
  apply Submodule.map_injective_of_injective (seed.baseDomain.subtype_injective)
  suffices ⨆ i, seed.baseDomain ⊓ seed.grades i = seed.baseDomain by simpa using this
  apply iSup_congr
  intro A
  simpa using le_iSup _ _

noncomputable
instance (seed : HahnEmbeddingSeed K M R) :
    DirectSum.Decomposition (HahnEmbeddingSeed.grades' seed) :=
  DirectSum.IsInternal.chooseDecomposition _ (HahnEmbeddingSeed.isInternal seed)

/-- Coefficients of Hahn series for each `baseDomain` element. -/
noncomputable
def HahnEmbeddingSeed.hahnCoeff (seed : HahnEmbeddingSeed K M R) :
    baseDomain seed →ₗ[K] ⨁ _ : ArchimedeanClass M, R :=
  (DirectSum.lmap seed.gradeMap') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem HahnEmbeddingSeed.hahnCoeff_apply {seed : HahnEmbeddingSeed K M R}
    {x : seed.baseDomain} {f : Π₀ A, seed.grades A}
    (h : x.val = f.sum fun A ↦ (seed.grades A).subtype)
    (A : ArchimedeanClass M) :
    seed.hahnCoeff x A = seed.gradeMap A (f A) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.grades A) (DirectSum.decompose seed.grades' x A) = f A by
    simp [HahnEmbeddingSeed.hahnCoeff, this]

  have hxm {A : ArchimedeanClass M} (x : seed.grades A) : x.val ∈ seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using le_iSup _ _

  let f' : ⨁ A, seed.grades' A :=
    f.mapRange (fun A x ↦ (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.grades' A)) (by simp)
  have hf : f A = (seed.baseDomain.subtype.submoduleComap (seed.grades A)) (f' A) := by
    apply Subtype.eq
    simp [f']
  have hx : x = (decompose seed.grades').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

/-- Move this -/
def Lex.toLexLinearEquiv (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    M ≃ₗ[R] Lex M :=
  Equiv.toLinearEquiv toLex {
    map_add _ _ := by simp
    map_smul _ _ := by simp
  }

/-- Combining all `HahnEmbeddingSeed.gradeMap` as
a partial linear map from `HahnEmbeddingSeed.baseDomain` to `HahnSeries`. -/
noncomputable
def baseHahnEmbedding (seed : HahnEmbeddingSeed K M R) :
    M →ₗ.[K] Lex (HahnSeries (ArchimedeanClass₀ M) R) where
  domain := seed.baseDomain
  toFun := (Lex.toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _ _ _) ∘ₗ
    (Finsupp.lcomapDomain _ Subtype.val_injective) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem domain_baseHahnEmbedding (seed : HahnEmbeddingSeed K M R) :
    (baseHahnEmbedding seed).domain = ⨆ A, seed.grades A := rfl

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem coeff_baseHahnEmbedding {seed : HahnEmbeddingSeed K M R}
    {x : (baseHahnEmbedding seed).domain} {f : Π₀ A, seed.grades A}
    (h : x.val = f.sum fun A ↦ (seed.grades A).subtype)
    (A : ArchimedeanClass₀ M) :
    (ofLex ((baseHahnEmbedding seed) x)).coeff A = seed.gradeMap A (f A) := by
  simpa [baseHahnEmbedding] using seed.hahnCoeff_apply h A.val

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem mem_domain_baseHahnEmbedding_of_mem_grade {seed : HahnEmbeddingSeed K M R}
    {x : M} {A : ArchimedeanClass M} (h : x ∈ seed.grades A) :
    x ∈ (baseHahnEmbedding seed).domain := by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseHahnEmbedding]
  simpa using le_iSup_iff.mpr fun _ h ↦ h A

/-! ### Step 2: characterize partial embedding

We characterize the base embedding as a member of a class of partial linear embedding
`PartialHahnEmbedding`. These embedding share nice properties, including monotonicity
and transferring `ArchimedeanClass` to `HahnEmbedding.orderTop`.
-/

/-- A partial linear map is called "partial Hahn embedding" if it satisfies
certain properties (See below). -/
structure IsPartialHahnEmbedding (seed : HahnEmbeddingSeed K M R)
    (f : M →ₗ.[K] Lex (HahnSeries (ArchimedeanClass₀ M) R)) : Prop where
  /-- A partial Hahn embedding is strictly monotone. -/
  strictMono : StrictMono f
  /-- A partial Hahn embedding always extends `baseHahnEmbedding`. -/
  baseHahnEmbedding_le : baseHahnEmbedding seed ≤ f
  /-- if Hahn series $f$ is in the range, then any truncation of $f$ is also in the range. -/
  truncate_mem_range : ∀ x, ∀ A,
    toLex (HahnSeries.truncateLinearMap K A (ofLex (f x))) ∈ LinearMap.range f.toFun

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem baseHahnEmbedding_pos (seed : HahnEmbeddingSeed K M R) {x : (baseHahnEmbedding seed).domain}
    (hx : 0 < x) : 0 < baseHahnEmbedding seed x := by
  -- decompose x to sum of grades
  have hmem : x.val ∈ (baseHahnEmbedding seed).domain := x.prop
  simp_rw [domain_baseHahnEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x ↦ x.val) := by
    rw [hf]
    simpa using hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro A
    simpa using DFinsupp.notMem_support_iff.mp (forall_not_of_not_exists hempty A)
  have htop : f.support.min' hsupport ≠ ⊤ := by
    by_contra! h
    have h : ⊤ ∈ f.support := h ▸ f.support.min'_mem hsupport
    rw [DFinsupp.mem_support_iff] at h
    contrapose! h
    rw [← Submodule.coe_eq_zero, ← Submodule.mem_bot K]
    convert ← (f ⊤).prop
    simpa using (seed.isGrade ⊤).sup_eq
  -- The dictating term for HahnSeries < is at the lowest archimedean class of f.support
  refine (HahnSeries.lt_iff _ _).mpr ⟨⟨f.support.min' hsupport, htop⟩, ?_, ?_⟩
  · intro j hj
    rw [coeff_baseHahnEmbedding hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    · contrapose! hj
      rw [← Subtype.coe_le_coe, Subtype.coe_mk]
      exact Finset.min'_le f.support _ hj
  · -- Show that f's value at dominating archimedean class is positive
    rw [coeff_baseHahnEmbedding hf.symm]
    suffices (seed.gradeMap (f.support.min' hsupport)) 0 <
        (seed.gradeMap (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
      simpa using this
    suffices 0 < (f (f.support.min' hsupport)).val by
      apply (seed.strictMono (f.support.min' hsupport))
      simpa using this
    -- using the fact that f.sum is positive, we only needs to show that
    -- the remaining terms of f after removing the dominating class is of higher class
    apply pos_of_pos_of_mk_lt hfpos
    rw [mk_sub_comm]
    have hferase : (f.sum fun _ x ↦ x.val) - (f (f.support.min' hsupport)).val =
        ∑ x ∈ f.support.erase (f.support.min' hsupport), (f x).val := by
      apply sub_eq_of_eq_add
      exact (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
    rw [hferase]
    -- Now both sides are mk (∑ ...)
    -- We rewrite them to mk (dominating term)
    have hmono : StrictMonoOn (fun x ↦ mk (f x).val) f.support := by
      intro A hA B hB h
      simp only
      rw [(seed.isGrade A).archimedeanClass_eq (f A).prop (by simpa using hA)]
      rw [(seed.isGrade B).archimedeanClass_eq (f B).prop (by simpa using hB)]
      exact h
    rw [DFinsupp.sum, mk_sum hsupport hmono]
    rw [(seed.isGrade (f.support.min' hsupport)).archimedeanClass_eq (f _).prop
      (by simpa using f.support.min'_mem hsupport)]
    by_cases hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
    · rw [mk_sum hsupport' (hmono.mono (by simp))]
      rw [(seed.isGrade ((f.support.erase _).min' hsupport')).archimedeanClass_eq
        (f _).prop (by
        simpa using (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
      apply Finset.min'_lt_of_mem_erase_min'
      apply Finset.min'_mem
    · -- special case: f has a single term, and becomes 0 after removing it
      have : f.support.erase (f.support.min' hsupport) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hsupport'
      simpa [this] using lt_top_iff_ne_top.mpr htop

omit [Archimedean R] in
theorem baseHahnEmbedding_strictMono (seed : HahnEmbeddingSeed K M R) :
    StrictMono (baseHahnEmbedding seed) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  apply baseHahnEmbedding_pos
  simpa using h

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem truncate_mem_range_baseHahnEmbedding (seed : HahnEmbeddingSeed K M R)
    (x : (baseHahnEmbedding seed).domain) (A : ArchimedeanClass₀ M) :
    toLex (HahnSeries.truncateLinearMap K A (ofLex (baseHahnEmbedding seed x))) ∈
    LinearMap.range (baseHahnEmbedding seed).toFun := by
  -- decompose x to grades
  have hmem : x.val ∈ (baseHahnEmbedding seed).domain := x.prop
  simp_rw [domain_baseHahnEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some grades
  let f' : Π₀ (i : ArchimedeanClass M), seed.grades i :=
    DFinsupp.mk f.support fun B ↦ if A.val ≤ B.val then 0 else f B.val
  refine ⟨⟨f'.sum fun B x ↦ x.val, ?_⟩, ?_⟩
  · rw [domain_baseHahnEmbedding, Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  · apply_fun ofLex
    rw [ofLex_toLex, LinearPMap.toFun_eq_coe]
    ext B
    rw [coeff_baseHahnEmbedding rfl]
    unfold f'
    obtain hBA | hBA := lt_or_ge B A
    · rw [HahnSeries.coeff_truncate_eq K hBA, coeff_baseHahnEmbedding hf.symm]
      apply congrArg
      have hAB : ¬ A.val ≤ B.val := not_le_of_gt hBA
      simp only [DFinsupp.mk_apply, hAB, ↓reduceIte]
      aesop
    · rw [HahnSeries.coeff_truncate_eq_zero K hBA]
      have hAB : A.val ≤ B.val := hBA
      simp only [DFinsupp.mk_apply, hAB, ↓reduceIte]
      convert LinearMap.map_zero _
      simp

omit [Archimedean R] in
/-- `baseHahnEmbedding` itself is a partial Hahn embedding. -/
theorem isPartialHahnEmbedding_baseHahnEmbedding (seed : HahnEmbeddingSeed K M R) :
    IsPartialHahnEmbedding seed (baseHahnEmbedding seed) where
  strictMono := baseHahnEmbedding_strictMono seed
  baseHahnEmbedding_le := le_refl _
  truncate_mem_range := truncate_mem_range_baseHahnEmbedding seed

/-- The type of all partial Hahn embedding. -/
abbrev PartialHahnEmbedding (seed : HahnEmbeddingSeed K M R) :=
    {f : M →ₗ.[K] Lex (HahnSeries (ArchimedeanClass₀ M) R) // IsPartialHahnEmbedding seed f}

namespace PartialHahnEmbedding
variable {seed : HahnEmbeddingSeed K M R}

noncomputable
instance : Inhabited (PartialHahnEmbedding seed) where
  default := ⟨baseHahnEmbedding seed, isPartialHahnEmbedding_baseHahnEmbedding seed⟩

/-- `PartialHahnEmbedding` as an `OrderedAddMonoidHom`. -/
def toOrderAddMonoidHom (f : PartialHahnEmbedding seed) :
    f.val.domain →+o Lex (HahnSeries (ArchimedeanClass₀ M) R) where
  __ := f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem toOrderAddMonoidHom_apply (f : PartialHahnEmbedding seed) (x : f.val.domain) :
    f.toOrderAddMonoidHom x = f.val x := rfl

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem toOrderAddMonoidHom_injective (f : PartialHahnEmbedding seed) :
    Function.Injective f.toOrderAddMonoidHom := f.prop.strictMono.injective

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem grade_mem (f : PartialHahnEmbedding seed) {x : M} {A : ArchimedeanClass M}
    (hx : x ∈ seed.grades A) : x ∈ f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseHahnEmbedding_le.1
  apply mem_domain_baseHahnEmbedding_of_mem_grade hx

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem map_grade (f : PartialHahnEmbedding seed) {x : f.val.domain} {A : ArchimedeanClass₀ M}
    (hx : x.val ∈ seed.grades A.val) :
    f.val x = toLex (HahnSeries.single A (seed.gradeMap A.val ⟨x.val, hx⟩)) := by
  have hx' : x.val ∈ (baseHahnEmbedding seed).domain := mem_domain_baseHahnEmbedding_of_mem_grade hx
  have heq : (⟨x.val, hx'⟩ : (baseHahnEmbedding seed).domain).val = x.val := rfl
  rw [← f.prop.baseHahnEmbedding_le.2 heq]
  let fx : Π₀ A, seed.grades A := DFinsupp.single A ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun A ↦ (seed.grades A).subtype := by
    simp [fx, DFinsupp.sum_single_index]
  apply_fun ofLex
  rw [ofLex_toLex]
  ext B
  rw [coeff_baseHahnEmbedding hfx]
  unfold fx
  obtain rfl | hBA := eq_or_ne B A
  · simp
  · have hAB : A.val ≠ B.val := Subtype.ext_iff.ne.mp hBA.symm
    simp [HahnSeries.coeff_single_of_ne hBA, DFinsupp.single_eq_of_ne hAB]

omit [Archimedean R] in
/-- Archimedean equivalence is preserved by `f`. -/
theorem archimedeanClass_eq_iff (f : PartialHahnEmbedding seed) (x y : f.val.domain) :
    mk (f.val x) = mk (f.val y) ↔ mk x.val = mk y.val := by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans mk x = mk y
  · apply Function.Injective.eq_iff
    apply orderHom_injective
    apply toOrderAddMonoidHom_injective
  · simp_rw [mk_eq_mk]
    aesop

/-- Archimedean equivalence of input is transferred to `HahnSeries.orderTop` equality. -/
theorem orderTop_eq_iff (f : PartialHahnEmbedding seed) (x y : f.val.domain) :
    (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔ mk x.val = mk y.val := by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
  · have : y = x := Subtype.eq <| hsubsingleton.allEq _ _
    simp [this]
  · have hnonempty : Nonempty (ArchimedeanClass₀ M) := inferInstance
    obtain A := hnonempty.some
    have hnontrivial' : Nontrivial (seed.grades A) := (seed.isGrade A).nontrivial A.prop
    have : Nontrivial R := (seed.strictMono A).injective.nontrivial
    rw [← archimedeanClass_eq_iff]
    simp_rw [← HahnSeries.archimedeanClassOrderIso_apply]
    rw [(HahnSeries.archimedeanClassOrderIso (ArchimedeanClass₀ M) R).injective.eq_iff]

/-- Archimedean class of the input is transfered to `HahnSeries.orderTop`. -/
theorem orderTop_eq_archimedeanClass (f : PartialHahnEmbedding seed) (x : f.val.domain) :
    ArchimedeanClass₀.withTopOrderIso M (ofLex (f.val x)).orderTop = mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hx0' : x.val ≠ 0 := by simpa using hx0
    have : Nontrivial (seed.grades (mk x)) := by
      apply (seed.isGrade (mk x)).nontrivial
      simpa using hx0
    -- Pick a representative `x'` from Archimedean grade with the same class as `x`.
    -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
    obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.grades (mk x))
    have heq : mk x' = mk x.val := by
      apply (seed.isGrade (mk x)).archimedeanClass_eq hx'mem
      simpa using hx'0
    let x'' : f.val.domain := ⟨x', grade_mem f hx'mem⟩
    have hx''mem : x''.val ∈ seed.grades (ArchimedeanClass₀.mk hx0').val := hx'mem
    have h0 : (seed.gradeMap (ArchimedeanClass₀.mk hx0').val) ⟨x''.val, hx''mem⟩ ≠ 0 := by
      rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono _).injective).ne]
      unfold x''
      simpa using hx'0
    have heq' : mk x''.val = mk x.val := heq
    rw [← orderTop_eq_iff, map_grade f hx''mem, ofLex_toLex, HahnSeries.orderTop_single h0] at heq'
    simp [← heq']

theorem orderTop_eq_archimedeanClass₀ (f : PartialHahnEmbedding seed) {x : f.val.domain}
    (hx0 : x.val ≠ 0) : (ofLex (f.val x)).orderTop = ArchimedeanClass₀.mk hx0 := by
  apply_fun ArchimedeanClass₀.withTopOrderIso M
  simp [orderTop_eq_archimedeanClass]

/-- `f.val x` has 0 coefficients at position of archimedean class lower than `x`'s. -/
theorem coeff_eq_zero_of_mem (f : PartialHahnEmbedding seed) {A : ArchimedeanClass M}
    {x : f.val.domain} (hx : x.val ∈ ball K A) {C : ArchimedeanClass₀ M} (hC : C.val ≤ A) :
    (ofLex (f.val x)).coeff C = 0 := by
  by_cases hA : A = ⊤
  · rw [hA] at hx
    have hx : x = 0 := by simpa using hx
    simp [hx]
  · apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    apply_fun ArchimedeanClass₀.withTopOrderIso _
    rw [orderTop_eq_archimedeanClass, ArchimedeanClass₀.withTopOrderIso_apply_coe]
    apply lt_of_le_of_lt hC
    rw [mem_ball_iff K hA] at hx
    simpa using hx

/-- `f.val x` has a non-zero coefficient at position of `x`'s archimedean class. -/
theorem coeff_ne_zero (f : PartialHahnEmbedding seed) {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).coeff (ArchimedeanClass₀.mk hx0) ≠ 0 := by
  apply HahnSeries.coeff_orderTop_ne
  exact f.orderTop_eq_archimedeanClass₀ hx0

/-- When `y` and `z` are both near `x` (the difference is in a `ArchimedeanClass`),
then initial coefficients of `f.val y` and `f.val z` agrees. -/
theorem coeff_eq_of_mem (f : PartialHahnEmbedding seed) (x : M)
    {y z : f.val.domain} {A : ArchimedeanClass M}
    (hy : y.val - x ∈ ball K A) (hz : z.val - x ∈ ball K A)
    {C : ArchimedeanClass₀ M} (hC : C ≤ A) :
    (ofLex (f.val y)).coeff C = (ofLex (f.val z)).coeff C := by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hC
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

/-! ### Step 3: extend embedding

We create larger `HahnPartialEmbedding` from an existing one by adding a new element to the domain
and assigning an appropriate output that preserves all `HahnPartialEmbedding`'s properties.
-/

/-- Evaluate coefficients of the `HahnSeries` given an arbitrary input that's not necessarily in
`f`'s domain. The coefficient is picked from `y` that is "close enough" to `x` (their difference
is in a higher `ArchimedeanClass`). If no such `y` exists (in other words, x is "isolated"), set the
coeffienct to 0.

This doesn't immediately extend `f`'s domain to the entire module in a consistent way. Such
extension isn't necessarily linear.
-/
noncomputable
def evalCoeff (f : PartialHahnEmbedding seed) (x : M) (A : ArchimedeanClass₀ M) : R :=
  open Classical in
  if h : ∃ y : f.val.domain, y.val - x ∈ ball K A then
    (ofLex (f.val h.choose)).coeff A
  else
    0

/-- The coefficient is well-defined regardless which `y` we pick in `evalCoeff`. -/
theorem evalCoeff_eq (f : PartialHahnEmbedding seed) {x : M} {A : ArchimedeanClass₀ M}
    {y : f.val.domain} (hy : y.val - x ∈ ball K A) :
    evalCoeff f x A = (ofLex (f.val y)).coeff A := by
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K A := ⟨y, hy⟩
  simpa [evalCoeff, hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy (le_refl _)

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem evalCoeff_eq_zero (f : PartialHahnEmbedding seed) {x : M} {A : ArchimedeanClass₀ M}
    (h : ¬∃ y : f.val.domain, y.val - x ∈ ball K A) :
    f.evalCoeff x A = 0 := by
  simp [evalCoeff, h]

theorem evalCoeff_isWF_support (f : PartialHahnEmbedding seed) (x : M) :
    (evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra!
  obtain ⟨seq, ⟨hanti, hmem⟩⟩ := this
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    unfold evalCoeff
    simp [hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : ℕ) : seq n ∈ (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem using 1
    refine (f.evalCoeff_eq ?_).symm
    refine ball_antitone _ _ ?_ hy
    simpa using hanti.antitone (show 0 ≤ n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

/-- Promote `PartialHahnEmbedding.evalCoeff`'s output to a new `HahnSeries`. -/
noncomputable
def eval (f : PartialHahnEmbedding seed) (x : M) : Lex (HahnSeries (ArchimedeanClass₀ M) R) :=
  toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.evalCoeff_isWF_support x).isPWO }

@[simp]
theorem eval_zero (f : PartialHahnEmbedding seed) : f.eval 0 = 0 := by
  unfold eval
  convert toLex_zero
  ext A
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp

theorem eval_smul (f : PartialHahnEmbedding seed) (c : K) (x : M) :
    f.eval (c • x) = c • f.eval x := by
  by_cases hc : c = 0
  · simp [hc]
  · unfold eval
    rw [← toLex_smul, toLex.injective.eq_iff]
    ext A
    suffices f.evalCoeff (c • x) A = c • f.evalCoeff x A by simpa using this
    by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K A
    · obtain ⟨y, hy⟩ := h
      have heq : (c • y).val - c • x = c • (y.val - x) := by simp [smul_sub]
      have hy' : (c • y).val - c • x ∈ ball K A := by
        rw [heq]
        exact Submodule.smul_mem _ _ hy
      simp [f.evalCoeff_eq hy, f.evalCoeff_eq hy', LinearPMap.map_smul]
    · have h' : ¬∃ y : f.val.domain, y.val - c • x ∈ ball K A := by
        contrapose! h
        obtain ⟨y, hy⟩ := h
        use c⁻¹ • y
        have heq : (c⁻¹ • y).val - x = c⁻¹ • (y.val - c • x) := by
          simp [smul_sub, smul_smul, inv_mul_cancel₀ hc]
        rw [heq]
        exact Submodule.smul_mem _ _ hy
      simp [f.evalCoeff_eq_zero h, f.evalCoeff_eq_zero h']

/-- If `f.eval x = f.val y`, then for any `z` in the domain, `x - z` can't be closer than `x - y`
in terms of Archimedean classes. -/
theorem archimedeanClass_le_of_eval_eq (f : PartialHahnEmbedding seed) {x : M}
    {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) :
    mk (x - z.val) ≤ mk (x - y.val) := by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (A : ArchimedeanClass₀ M) (hA : A.val < mk (x - z.val)) :
      (ofLex (f.eval x)).coeff A = (ofLex (f.val z)).coeff A := by
    rw [mk_sub_comm] at hA
    simp_rw [eval, ofLex_toLex]
    apply evalCoeff_eq
    exact (mem_ball_iff K A.prop).mpr hA
  have h2 : ∀ A : ArchimedeanClass₀ M, A.val < mk (x - z.val) →
      (ofLex (f.val (z - y))).coeff A = 0 := by
    intro A hA
    rw [LinearPMap.map_sub, ofLex_sub, HahnSeries.coeff_sub, sub_eq_zero, ← h]
    exact (h1 A hA).symm
  contrapose! h2
  refine ⟨ArchimedeanClass₀.mk hyz, h2, ?_⟩
  apply coeff_ne_zero

/-- If `x` isn't in `f`'s domain, `f.eval x` produces a brand new value not in `f`'s range. -/
theorem eval_ne (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) :
    f.eval x ≠ f.val y := by
  have hxy0 : mk (x - y.val) ≠ ⊤ := by
    contrapose! hx with hxy
    rw [mk_eq_top_iff, sub_eq_zero] at hxy
    rw [hxy]
    exact y.prop
  -- decompose x - y = u + v, where v ∈ grade (x - y) and u is at higher class than x - y
  have hxy : x - y.val ∈ closedBall K (mk (x - y.val)) := by simp
  rw [← (seed.isGrade (mk (x - y.val))).sup_eq, Submodule.mem_sup] at hxy
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  have huv' : x - y.val - v = u := by simp [← huv]
  rw [mem_ball_iff K hxy0] at hu
  -- z = x - u = y + v is also in the domain.
  -- Assuming f.eval x = f.val y allows us to use archimedeanClass_le_of_eval_eq on z
  have hyv : y.val + v ∈ f.val.domain := Submodule.add_mem _ (by simp) (f.grade_mem hv)
  by_contra! h
  obtain h := f.archimedeanClass_le_of_eval_eq h ⟨y.val + v, hyv⟩
  contrapose! h
  simpa [← sub_sub, huv'] using hu

/-- If there is a `y` in `f`'s domain with `A = ArchimedeanClass (y - x)`, but there
is no closer `z` to `x` where the difference is of a higher `ArchimedeanClass`, then
`f.eval x` is simply `f.val y` truncated at `A`.

This doesn't mean every `x` can be evaluated this way: it is possible that one can keep
finding an infinite chain of `y` that keeps getting closer to `x` in terms of Archimedean classes,
yet `x` is still isolated within a very high Archimedean class. In fact, in the next theorem,
we will show that there is always such chain for `x` not in `f`'s domain. -/
theorem eval_eq_truncate (f : PartialHahnEmbedding seed) {x : M} {A : ArchimedeanClass₀ M}
    {y : f.val.domain} (hy : mk (y.val - x) = A.val)
    (h : ∀ z : f.val.domain, z.val - x ∉ ball K A) :
    f.eval x = toLex (HahnSeries.truncateLinearMap K A (ofLex (f.val y))) := by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext B
  simp only
  obtain hB | hB := lt_or_ge B A
  · rw [HahnSeries.coeff_truncate_eq K hB]
    apply evalCoeff_eq
    rw [mem_ball_iff _ B.prop, hy]
    simpa using hB
  · rw [HahnSeries.coeff_truncate_eq_zero K hB]
    apply evalCoeff_eq_zero
    contrapose! h
    obtain ⟨z, hz⟩ := h
    use z
    refine ball_antitone _ _ ?_ hz
    simpa using hB

/-- For `x` not in `f`'s domain, there is an infinite chain of `y` from `f`'s domain
that keeps getting closer to `x` in terms of Archimedean classes. -/
theorem exists_sub_mem_submodule (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : ∃ z : f.val.domain, z.val - x ∈ ball K (mk (y.val - x)) := by
  have : y.val - x ≠ 0 := by
    contrapose! hx
    obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
    simp
  let A := ArchimedeanClass₀.mk this
  have hA : mk (y.val - x) = A.val := rfl
  contrapose! hx
  obtain h := f.eval_eq_truncate hA hx
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncate_mem_range y A)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

/-- For `x` not in `f`'s domain, `f.eval x` is consistent with `f`'s monotonicity. -/
theorem eval_lt (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y := by
  -- Expand the definition of HahnSeries' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of (y - x)
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x ≠ 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨ArchimedeanClass₀.mk hxy0, ?_, ?_⟩
  · -- All coefficients before the dictating term are the same
    intro j hj
    apply evalCoeff_eq
    rw [mem_ball_iff K j.prop]
    simpa using hj
  · -- Show the dictating coefficient
    have hyxtop : mk (y.val - x) ≠ ⊤ := by simp [hxy0]
    suffices f.evalCoeff x (ArchimedeanClass₀.mk hxy0) <
        (ofLex (f.val y)).coeff (ArchimedeanClass₀.mk hxy0) by simpa [eval] using this
    -- We find z from f's domain to approximate x. Such approximation obeys:
    -- * f.eval x = f.val z
    -- * x < y → z < y
    -- * mk (x - y) = mk (z - y)
    obtain ⟨z, hz⟩ := f.exists_sub_mem_submodule hx y
    have hz' : z.val - x ∈ ball K (ArchimedeanClass₀.mk hxy0).val := hz
    rw [f.evalCoeff_eq hz']
    have hzy : z < y := by
      change z.val < y.val
      apply (sub_lt_sub_iff_right x).mp
      refine lt_of_mk_lt_mk_of_nonneg ?_ (sub_nonneg_of_le h.le)
      rw [mem_ball_iff K hyxtop] at hz
      simpa using hz
    have hzyne : z.val - y.val ≠ 0 := by
      apply sub_ne_zero_of_ne
      simpa using hzy.ne
    have hzyclass : ArchimedeanClass₀.mk hxy0 = ArchimedeanClass₀.mk hzyne := by
      suffices mk (y.val - x) = mk (z.val - y.val) by
        rw [Subtype.eq_iff]
        simpa using this
      have : y.val - z.val = y.val - x + (x - z.val) := by abel
      rw [mk_sub_comm z.val y.val, this]
      symm
      apply mk_add_eq_mk_left
      rw [mk_sub_comm x z.val]
      rw [mem_ball_iff K hyxtop] at hz
      simpa using hz
    -- Since both y and z are in the domain, we can apply f's monotonicity on them
    rw [← f.prop.strictMono.lt_iff_lt, HahnSeries.lt_iff] at hzy
    obtain ⟨i, hj, hi⟩ := hzy
    -- We show that the dictating coefficient of f.val y < f.val z
    -- is at the same position as the dictating coefficient of f.eval x < f.val y
    have hieq : i = ArchimedeanClass₀.mk hxy0 := by
      apply le_antisymm
      · by_contra! hlt
        obtain hj := sub_eq_zero_of_eq (hj (ArchimedeanClass₀.mk hxy0) hlt)
        contrapose! hj
        rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub, hzyclass]
        apply f.coeff_ne_zero
      · contrapose! hi
        rw [hzyclass] at hi
        have hzy : z.val - y.val ∈ ball K i.val := by
          rw [mem_ball_iff K i.prop]
          simpa using hi
        exact (f.coeff_eq_of_mem y.val (by simp) hzy (by simp)).le
    exact hieq ▸ hi

/-- Extend `f` to a larger partial linear map by adding a new `x`. -/
noncomputable
def extendFun (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain) :
    M →ₗ.[K] Lex (HahnSeries (ArchimedeanClass₀ M) R) :=
  LinearPMap.supSpanSingleton f.val x (eval f x) hx

theorem extendFun_strictMono (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain) :
    StrictMono (f.extendFun hx) := by
  have hx' {c : K} (hc : c ≠ 0) : -c • x ∉ f.val.domain := by
    contrapose! hx
    rw [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
    exact hx
  -- only need to prove 0 < f v for 0 < v = z - y
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyzmem := (z - y).prop
  nth_rw 1 [extendFun, LinearPMap.domain_supSpanSingleton] at hyzmem
  -- decompose v = a + c • x, reducing this to eval_lt
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyzmem
  have : z - y = ⟨a + b, hab.symm ▸ (z - y).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hyz
  have habpos : 0 < a + b := by exact hyz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hc] at habpos
  simp_rw [← hc, extendFun]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]
  suffices f.eval (-c • x) < f.val ⟨a, ha⟩ by
    rw [eval_smul, neg_smul] at this
    exact neg_lt_iff_pos_add.mp this
  have hac : -c • x < a := by
    rw [neg_smul]
    exact neg_lt_iff_pos_add.mpr habpos
  by_cases hc : c = 0
  · rw [hc] at ⊢ hac
    suffices f.val 0 < f.val ⟨a, ha⟩ by simpa using this
    exact f.prop.strictMono (by simpa using hac)
  · specialize hx' hc
    exact f.eval_lt hx' ⟨a, ha⟩ hac

theorem baseHahnEmbedding_le_extendFun (f : PartialHahnEmbedding seed) {x : M}
    (hx : x ∉ f.val.domain) : baseHahnEmbedding seed ≤ (f.extendFun hx) := by
  rw [extendFun]
  exact le_trans f.prop.baseHahnEmbedding_le <| LinearPMap.left_le_sup _ _ _

theorem truncate_eval_mem_range_extendFun (f : PartialHahnEmbedding seed) {x : M}
    (hx : x ∉ f.val.domain) (A : ArchimedeanClass₀ M) :
    toLex (HahnSeries.truncateLinearMap K A (ofLex (f.eval x))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  rw [extendFun, LinearMap.mem_range]
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K A
  · -- if x is not isolated within A, the truncation at A equals to truncating
    -- an nearby y in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.prop.truncate_mem_range y A)
    refine ⟨⟨z.val, ?_⟩, ?_⟩
    · simpa using Submodule.mem_sup_left z.prop
    · rw [LinearPMap.toFun_eq_coe] at hz
      rw [LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ _ z.prop]
      rw [hz, toLex_inj]
      ext B
      obtain hBA | hBA := lt_or_ge B A
      · simp_rw [HahnSeries.coeff_truncate_eq _ hBA]
        refine (f.evalCoeff_eq ?_).symm
        apply Set.mem_of_mem_of_subset hy
        simpa using ball_antitone _ _ hBA.le
      · simp_rw [HahnSeries.coeff_truncate_eq_zero _ hBA]
  · -- if x is isolated within A, truncating has no effect because the trailing coefficients
    -- are already 0
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa using Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    · apply_fun ofLex
      rw [ofLex_toLex, LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_self]
      ext B
      obtain hBA | hBA := lt_or_ge B A
      · rw [HahnSeries.coeff_truncate_eq _ hBA]
      · rw [HahnSeries.coeff_truncate_eq_zero _ hBA]
        rw [eval, ofLex_toLex]
        apply f.evalCoeff_eq_zero
        contrapose! h
        obtain ⟨y, hy⟩ := h
        use y
        apply Set.mem_of_mem_of_subset hy
        simpa using ball_antitone _ _ hBA

theorem truncate_mem_range_extendFun (f : PartialHahnEmbedding seed) {x : M}
    (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (A : ArchimedeanClass₀ M) :
    toLex (HahnSeries.truncateLinearMap K A (ofLex (f.extendFun hx y))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun, LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hc]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw [ofLex_add, map_add, toLex_add, ofLex_smul, map_smul, toLex_smul]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · obtain ⟨⟨a', ha'mem⟩, ha'⟩ := LinearMap.mem_range.mp (f.prop.truncate_mem_range ⟨a, ha⟩ A)
    refine LinearMap.mem_range.mpr ⟨⟨a', ?_⟩, ?_⟩
    · simpa using Submodule.mem_sup_left ha'mem
    · rw [← ha']
      exact LinearPMap.supSpanSingleton_apply_mk_of_mem f.val _ hx ha'mem
  · apply truncate_eval_mem_range_extendFun

theorem isPartialHahnEmbedding_extendFun (f : PartialHahnEmbedding seed) {x : M}
    (hx : x ∉ f.val.domain) : IsPartialHahnEmbedding seed (extendFun f hx) where
  strictMono := f.extendFun_strictMono hx
  baseHahnEmbedding_le := f.baseHahnEmbedding_le_extendFun hx
  truncate_mem_range := f.truncate_mem_range_extendFun hx

/-- Promote `extendFun` to a new `PartialHahnEmbedding`. -/
noncomputable
def extend (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain) :
    PartialHahnEmbedding seed := ⟨f.extendFun hx, f.isPartialHahnEmbedding_extendFun hx⟩

theorem lt_extend (f : PartialHahnEmbedding seed) {x : M} (hx : x ∉ f.val.domain) :
    f < f.extend hx := by
  apply lt_of_le_of_ne
  · change f.val ≤ (f.extend hx).val
    simpa [extend, extendFun] using LinearPMap.left_le_sup _ _ _
  · by_contra!
    have : f.val.domain = (f.extend hx).val.domain := by congr
    rw [this] at hx
    contrapose! hx with h
    simpa using Submodule.mem_sup_right (by simp)

/-! ### Step 4: use Zorn's lemma

We show that `sSup` makes sense on `PartialHahnEmbedding`, which allows us to use Zorn's lemma
to asserts the existence of maximal embedding. Since we already show that we can create greater
embedding by adding new elements, the maximal embedding must have the maximal domain.
-/

/-- A partial linear map that contains every element in a directed set of `PartialHahnEmbedding`. -/
noncomputable
def sSupFun {c : Set (PartialHahnEmbedding seed)} (hc : DirectedOn (· ≤ ·) c) :
    M →ₗ.[K] Lex (HahnSeries (ArchimedeanClass₀ M) R) :=
  LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))

omit [Archimedean R] in
theorem sSupFun_strictMono {c : Set (PartialHahnEmbedding seed)} (hnonempty : c.Nonempty)
    (hc : DirectedOn (· ≤ ·) c) : StrictMono (sSupFun hc) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y - x).val, hf⟩ :=
    LinearPMap.sSup_apply _ hmem ⟨(y - x).val, hf⟩
  rw [this]
  obtain ⟨f', _, hf'⟩ := (Set.mem_image _ _ _).mp hmem
  have hmono: StrictMono f := hf'.symm ▸ f'.prop.strictMono
  rw [show 0 = f 0 by simp]
  apply hmono
  change 0 < y - x
  simpa using h

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem le_sSupFun {c : Set (PartialHahnEmbedding seed)} (hc : DirectedOn (· ≤ ·) c)
    {f : PartialHahnEmbedding seed} (hf : f ∈ c) :
    f.val ≤ sSupFun hc :=
  LinearPMap.le_sSup _ <| (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem baseHahnEmbedding_le_sSupFun {c : Set (PartialHahnEmbedding seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : baseHahnEmbedding seed ≤ sSupFun hc := by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseHahnEmbedding_le (le_sSupFun hc hf)

omit [IsOrderedAddMonoid R] [Archimedean R] in
theorem truncate_mem_range_sSupFun {c : Set (PartialHahnEmbedding seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) (x : (sSupFun hc).domain)
    (A : ArchimedeanClass₀ M) :
    toLex ((HahnSeries.truncateLinearMap K A) (ofLex (sSupFun hc x))) ∈
    LinearMap.range (sSupFun hc).toFun := by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncate_mem_range) ⟨x, hf⟩ A
  simp_rw [LinearMap.mem_range, LinearPMap.toFun_eq_coe] at ⊢ h
  obtain ⟨x', hx'⟩ := h
  have hmem' : x'.val ∈ (sSupFun hc).domain := by
    apply Set.mem_of_mem_of_subset x'.prop
    exact hf'.symm ▸ (le_sSupFun hc hmem').1
  refine ⟨⟨x'.val, hmem'⟩, ?_⟩
  have hleft : (sSupFun hc) ⟨x'.val, hmem'⟩ = f x' := LinearPMap.sSup_apply _ hmem _
  have hright : (sSupFun hc) x = f ⟨x, hf⟩ := LinearPMap.sSup_apply _ hmem ⟨x, hf⟩
  rw [hleft, hright]
  exact hx'

omit [Archimedean R] in
theorem isPartialHahnEmbedding_sSupFun {c : Set (PartialHahnEmbedding seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) :
    IsPartialHahnEmbedding seed (sSupFun hc) where
  strictMono := sSupFun_strictMono hnonempty hc
  baseHahnEmbedding_le := baseHahnEmbedding_le_sSupFun hnonempty hc
  truncate_mem_range := truncate_mem_range_sSupFun hnonempty hc

/-- Promote `sSupFun` to a `PartialHahnEmbedding`. -/
noncomputable
def sSup {c : Set (PartialHahnEmbedding seed)} (hnonempty : c.Nonempty)
    (hc : DirectedOn (· ≤ ·) c) : PartialHahnEmbedding seed :=
  ⟨_, isPartialHahnEmbedding_sSupFun hnonempty hc⟩

variable (seed) in
omit [Archimedean R] in
theorem exists_isMax : ∃ f : PartialHahnEmbedding seed, IsMax f := by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf ↦ le_sSupFun hc.directedOn hf⟩

variable (seed) in
/-- There exists a `PartialHahnEmbedding` whose domain is the whole module. -/
theorem exists_domain_eq_top : ∃ f : PartialHahnEmbedding seed, f.val.domain = ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

end PartialHahnEmbedding

theorem exists_linearMap_hahnSeries_strictMono [h : Nonempty (HahnEmbeddingSeed K M R)] :
    ∃ f : M →ₗ[K] Lex (HahnSeries (ArchimedeanClass₀ M) R), StrictMono f := by
  obtain ⟨⟨⟨fdomain, f⟩, hpartial⟩, rfl⟩ := PartialHahnEmbedding.exists_domain_eq_top h.some
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_⟩
  apply hpartial.strictMono.comp
  intro _ _ h
  simpa [← Subtype.coe_lt_coe] using h
