/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patience Ablett, Kevin Buzzard, Harald Carlens, Wayne Ng Kwing King, Michael Schlößer,
  Justus Springer, Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.Sheaves.Init

/-!
# Properness of `Proj A`

We show that `Proj 𝒜` is proper over `Spec 𝒜₀`.

## Notes
This contribution was created as part of the Durham Computational Algebraic Geometry Workshop

-/

@[expose] public section

namespace AlgebraicGeometry.Proj

variable {σ A : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ)
variable [GradedRing 𝒜]

open Scheme CategoryTheory Limits pullback HomogeneousLocalization

section IsSeparated

lemma lift_awayMapₐ_awayMapₐ_surjective {d e : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g) (hd : 0 < d) :
    Function.Surjective
      (Algebra.TensorProduct.lift (awayMapₐ 𝒜 hg hx) (awayMapₐ 𝒜 hf (hx.trans (mul_comm _ _)))
        (fun _ _ ↦ .all _ _)) := by
  intro z
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective z
  by_cases hfg : (f * g) ^ j = 0
  · use 0
    have := HomogeneousLocalization.subsingleton 𝒜 (x := Submonoid.powers x) ⟨j, hx ▸ hfg⟩
    exact this.elim _ _
  have : n = j * (d + e) := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 hb'
    · convert SetLike.pow_mem_graded _ _ using 2
      · infer_instance
      · exact hx ▸ SetLike.mul_mem_graded hf hg
    · exact hx ▸ hfg
  let x0 : NumDenSameDeg 𝒜 (.powers f) :=
  { deg := j * (d * (e + 1))
    num := ⟨a * g ^ (j * (d - 1)), by
      convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded _ hg) using 2
      rw [this]
      cases d
      · contradiction
      · simp; ring⟩
    den := ⟨f ^ (j * (e + 1)), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  let y0 : NumDenSameDeg 𝒜 (.powers g) :=
  { deg := j * (d * e)
    num := ⟨f ^ (j * e), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den := ⟨g ^ (j * d), by convert SetLike.pow_mem_graded _ hg using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  use mk x0 ⊗ₜ mk y0
  ext
  simp only [Algebra.TensorProduct.lift_tmul, awayMapₐ_apply, val_mul,
    val_awayMap_mk, Localization.mk_mul, val_mk, x0, y0]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  cases d
  · contradiction
  · simp only [hx, add_tsub_cancel_right]
    ring

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
instance isSeparated : IsSeparated (toSpecZero 𝒜) := by
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Pullback.openCoverOfLeftRight
    (affineOpenCover 𝒜).openCover (affineOpenCover 𝒜).openCover _ _) ?_⟩
  intro ⟨i, j⟩
  dsimp [Scheme, Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  let e₁ : pullback ((affineOpenCover 𝒜).f i ≫ toSpecZero 𝒜)
        ((affineOpenCover 𝒜).f j ≫ toSpecZero 𝒜) ≅
        Spec (.of <| TensorProduct (𝒜 0) (Away 𝒜 (i.2 : A)) (Away 𝒜 (j.2 : A))) := by
    refine pullback.congrHom ?_ ?_ ≪≫ pullbackSpecIso (𝒜 0) (Away 𝒜 (i.2 : A)) (Away 𝒜 (j.2 : A))
    · simp [affineOpenCover, affineOpenCoverOfIrrelevantLESpan, awayι_toSpecZero]; rfl
    · simp [affineOpenCover, affineOpenCoverOfIrrelevantLESpan, awayι_toSpecZero]; rfl
  let e₂ : pullback ((affineOpenCover 𝒜).f i) ((affineOpenCover 𝒜).f j) ≅
        Spec (.of <| Away 𝒜 (i.2 * j.2 : A)) :=
    pullbackAwayιIso 𝒜 _ _ _ _ rfl
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e₁.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e₂.inv]
  let F : Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1 →+* Away 𝒜 (i.2.1 * j.2.1) :=
    (Algebra.TensorProduct.lift (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _))
      (fun _ _ ↦ .all _ _)).toRingHom
  have : Function.Surjective F := lift_awayMapₐ_awayMapₐ_surjective 𝒜 i.2.2 j.2.2 rfl i.1.2
  convert IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (R := Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1) F) this using 1
  rw [← cancel_mono (pullbackSpecIso ..).inv]
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, e₂, e₁,
      pullbackSpecIso_inv_fst, ← Spec.map_comp]
    erw [pullbackDiagonalMapIdIso_inv_snd_fst]
    erw [pullbackAwayιIso_inv_fst]
    congr 1
    ext x : 2
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, e₂, e₁]
    erw [pullbackDiagonalMapIdIso_inv_snd_snd]
    erw [pullbackAwayιIso_inv_snd]
    congr 1
    ext x : 2
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x

@[stacks 01MC]
instance : Scheme.IsSeparated (Proj 𝒜) :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp (isSeparated 𝒜)

end IsSeparated

section LocallyOfFiniteType

instance [Algebra.FiniteType (𝒜 0) A] : LocallyOfFiniteType (Proj.toSpecZero 𝒜) := by
  obtain ⟨x, hx, hx'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose d hd hxd using hx'
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
    (Proj.iSup_basicOpen_eq_top' 𝒜 (ι := x) (↑) (fun i ↦ ⟨_, hxd _ i.2⟩) (by simpa using hx))]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)
    (Proj.basicOpenIsoSpec 𝒜 (i : A) (hxd _ i.2) (hd _ i.2).bot_lt).inv, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact HomogeneousLocalization.Away.finiteType _ _ (hxd _ i.2)

end LocallyOfFiniteType

section QuasiCompact

instance [Algebra.FiniteType (𝒜 0) A] : QuasiCompact (Proj.toSpecZero 𝒜) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
  obtain ⟨x, hx, hx'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose d hd hxd using hx'
  have H (i : x) : IsCompact (Proj.basicOpen 𝒜 (i : A)).1 := by
    rw [← Proj.opensRange_awayι _ _ (hxd _ i.2) (hd _ i.2).bot_lt]
    exact isCompact_range (Proj.awayι _ _ (hxd _ i.2) (hd _ i.2).bot_lt).continuous
  have := congr($(Proj.iSup_basicOpen_eq_top' 𝒜
    (ι := x) (↑) (fun i ↦ ⟨_, hxd _ i.2⟩) (by simpa using hx)).1)
  simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
    TopologicalSpace.Opens.coe_mk, TopologicalSpace.Opens.coe_top] at this
  rw [← isCompact_univ_iff, ← this]
  exact isCompact_iUnion H

end QuasiCompact

section UniversallyClosed

open ValuationRing in
/--
Let `𝒜` be a graded ring generated over `𝒜₀` by finitely many homogeneous elements.
Suppose we have the following diagram for some homogeneous `x`
with `O` a valuation ring and `K = Frac(O)`.
```
    φ
K ←--- 𝒜_{(x)}
↑       ↑
|       |
|       |
O ←---- 𝒜₀
    φ₀
```
Then there exists a lift `φₗ : 𝒜_{(x₀)} →+* O` for some `x₀`
such that these two diagrams exist and commute.
```
    φ'                      φ'
K ←--- 𝒜_{(x x₀)}       K ←--- 𝒜_{(x x₀)}
↑       ↑                 ↖       ↑
|       |                 φ ⟍     |
|       |                     ⟍   |
O ←---- 𝒜_{(x₀)}                𝒜_{(x)}
    φₗ
```
This is the underlying algebraic statement of the valuative criterion for `Proj 𝒜`.
-/
@[stacks 01MF "algebraic part"]
theorem valuativeCriterion_existence_aux
    {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    (φ₀ : (𝒜 0) →+* O)
    (ι : Type*) [Finite ι] (x : ι → A) (h2 : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤)
    (j : ι) (φ : Away 𝒜 (x j) →+* K)
    (hcomm : (algebraMap O K).comp φ₀ = φ.comp (fromZeroRingHom 𝒜 _))
    (d : ι → ℕ) (hdi : ∀ i, 0 < d i) (hxdi : ∀ i, x i ∈ 𝒜 (d i)) :
    ∃ (j₀ : ι) (φ' : Away 𝒜 (x j * x j₀) →+* K), φ'.comp (awayMap 𝒜 (hxdi j₀) rfl) = φ ∧
      (φ'.comp (awayMap 𝒜 (hxdi j) (mul_comm (x j) (x j₀)))).range ≤ (algebraMap O K).range := by
  classical
  cases nonempty_fintype ι
  let ψ (i : ι) : ValueGroup O K :=
    valuation O K ((φ (Away.isLocalizationElem (hxdi j) (hxdi i))) ^ ∏ k ∈ Finset.univ.erase i, d k)
  have : Nonempty ι := ⟨j⟩
  let Kmax := (Finset.univ.image ψ).max' (by simp)
  have ⟨i₀, hi1⟩ : ∃ a, ψ a = Kmax := by simpa using Finset.max'_mem (Finset.univ.image ψ)
  have hi₀ (j) : ψ j ≤ ψ i₀ := hi1 ▸ (Finset.univ.image ψ).le_max' (ψ j) (by simp)
  have hKmax : 0 < Kmax := by
    refine zero_lt_iff.mpr fun hKmax ↦ ?_
    have (i : _) : ψ i = 0 := le_zero_iff.mp (hKmax ▸ Finset.le_max' _ _ (by simp))
    simp only [ψ, map_pow, pow_eq_zero_iff', map_eq_zero, ne_eq] at this
    have : φ 1 = 0 := by convert (this j).1; ext; simp
    simp only [map_one, one_ne_zero] at this
  letI := (awayMap 𝒜 (f := x j) (hxdi i₀) rfl).toAlgebra
  have := Away.isLocalization_mul (hxdi j) (hxdi i₀) rfl (hdi _).ne'
  have hunit : IsUnit (φ (Away.isLocalizationElem (hxdi j) (hxdi i₀))) := isUnit_iff_ne_zero.mpr
    fun rid ↦ hKmax.ne' (.symm (by simpa [ψ, rid, Finset.prod_eq_zero_iff, (hdi _).ne'] using hi1))
  let φ' := IsLocalization.Away.lift (S := Away 𝒜 (x j * x i₀)) _ hunit
  have hφ'1 (s) : φ' (awayMap 𝒜 (hxdi i₀) rfl s) = φ s := IsLocalization.Away.lift_eq _ hunit s
  use i₀, φ', IsLocalization.Away.lift_comp ..
  rintro _ ⟨sx, rfl⟩
  rw [RingHom.mem_range, ← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff]
  have := (Away.span_mk_prod_pow_eq_top (hxdi i₀) x h2 d hxdi).ge (Submodule.mem_top (x := sx))
  induction this using Submodule.span_induction with
  | zero => simp
  | add x y hx hy hhx hhy =>
    simp only [RingHom.coe_comp, Function.comp_apply, map_add, ge_iff_le]
    exact ((valuation O K).map_add _ _).trans <| sup_le_iff.mpr ⟨hhx, hhy⟩
  | smul a x₀ hx hx1 =>
    simp only [Algebra.smul_def, RingHom.coe_comp, Function.comp_apply, map_mul, ge_iff_le]
    refine mul_le_one' ?_ hx1
    rw [RingHom.algebraMap_toAlgebra, awayMap_fromZeroRingHom 𝒜 (hxdi j) (mul_comm (x j) (x i₀)),
      ← awayMap_fromZeroRingHom 𝒜 (hxdi i₀) rfl a, hφ'1]
    change valuation O K (φ.comp (fromZeroRingHom 𝒜 (.powers (x j))) a) ≤ 1
    simp only [← hcomm, RingHom.coe_comp, Function.comp_apply, ← Valuation.mem_integer_iff,
      IsFractionRing.coe_inj, exists_eq, mem_integer_iff]
  | mem x1 h =>
    obtain ⟨a, ai, hai, rfl⟩ := h
    simp only [smul_eq_mul] at hai
    have H : (∏ i, x i ^ ai i) * x i₀ ^ (a * (d j - 1)) ∈ 𝒜 ((a * d i₀) • d j) := by
      convert SetLike.mul_mem_graded (SetLike.prod_pow_mem_graded 𝒜 d x ai fun _ _ ↦ hxdi _)
        (SetLike.pow_mem_graded (a * (d j - 1)) (hxdi i₀)) using 2
      simp only [smul_eq_mul, hai]
      cases h : d j
      · cases (hdi j).ne' h
      · simp only [add_tsub_cancel_right]; ring
    suffices valuation O K (φ (Away.mk 𝒜 (hxdi j) _ _ H) /
          φ (Away.isLocalizationElem (hxdi j) (hxdi i₀)) ^ a) ≤ 1 by
      convert this
      rw [eq_div_iff (pow_ne_zero _ hunit.ne_zero), ← hφ'1, ← hφ'1, RingHom.comp_apply,
        ← map_pow, ← map_mul]
      congr
      ext
      simp only [awayMap_mk, Away.val_mk, val_pow, Localization.mk_pow, Localization.mk_mul,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists, val_mul]
      use 1
      simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
      cases h : d j
      · cases (hdi j).ne' h
      · rw [Nat.add_sub_cancel]; ring
    rw [map_div₀, div_le_iff₀ ((pow_pos ((Valuation.pos_iff _).mpr hunit.ne_zero) _).trans_eq
      (Valuation.map_pow _ _ _).symm), one_mul, ← pow_le_pow_iff_left₀ zero_le' zero_le'
        (mul_pos (hdi j) (Finset.prod_pos fun i _ => hdi i)).ne.symm]
    calc
      _ = (∏ i, ψ i ^ (d i * ai i)) * ψ i₀ ^ (d i₀ * a * (d j - 1)) := by
          simp only [ψ, ← map_pow, ← map_prod, ← map_mul]
          congr 2
          apply (show Function.Injective (algebraMap (Away 𝒜 (x j)) (Localization.Away (x j)))
            from val_injective _)
          simp only [map_pow, map_prod, map_mul]
          simp only [HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_pow,
            Localization.mk_prod, Localization.mk_mul]
          rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          use 1
          simp only [OneMemClass.coe_one, ← pow_mul, Submonoid.coe_mul,
            SubmonoidClass.coe_finset_prod, one_mul]
          simp_rw [← mul_assoc, Finset.prod_erase_mul _ d (h := Finset.mem_univ _), mul_assoc,
            ← mul_assoc (Finset.prod ..), Finset.prod_erase_mul _ d (h := Finset.mem_univ _),
            SubmonoidClass.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum,
            ← pow_add, mul_pow, ← Finset.prod_pow, ← pow_mul]
          congr 3
          · simp only [mul_comm _ (∏ i, d i), mul_assoc, mul_left_comm _ (∏ i, d i),
              mul_comm (d _) (ai _), ← Finset.mul_sum, hai]
            cases h : d j
            · cases (hdi j).ne' h
            · simp; ring
          · ext i; congr 1; ring
          · ring
      _ ≤ (∏ i : ι, ψ i₀ ^ (d i * ai i)) * ψ i₀ ^ (d i₀ * a * (d j - 1)) := by
          gcongr with i; exacts [fun i _ ↦ zero_le', zero_le', hi₀ i]
      _ = ψ i₀ ^ (d i₀ * a * d j) := by
          rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
          simp_rw [mul_comm (d _) (ai _), hai]
          cases h : d j
          · cases (hdi j).ne' h
          · simp; ring_nf
      _ = valuation O K ((φ _) ^ a) ^ (d j * ∏ i, d i) := by
          · simp only [ψ, ← map_pow]
            congr 2
            rw [← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc,
              Finset.univ.prod_erase_mul d (h := Finset.mem_univ _),
              mul_comm _ a, mul_right_comm]

@[stacks 01MF]
lemma valuativeCriterion_existence [Algebra.FiniteType (𝒜 0) A] :
    ValuativeCriterion.Existence (Proj.toSpecZero 𝒜) := by
  rintro ⟨O, K, i₁, i₂, w⟩
  obtain ⟨x, hx, hx'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose d hd hxd using hx'
  have : i₁ (IsLocalRing.closedPoint K) ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← Proj.iSup_basicOpen_eq_top' 𝒜 (ι := x) (↑) (fun i ↦ ⟨_, hxd _ i.2⟩) (by simpa using hx),
    TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  have : Set.range i₁ ⊆ (Proj.awayι 𝒜 _ (hxd i i.2) (hd i i.2).bot_lt).opensRange := by
    rw [Proj.opensRange_awayι]
    rintro _ ⟨x, rfl⟩
    obtain rfl := Subsingleton.elim x (IsLocalRing.closedPoint K)
    exact hi
  let φ : Spec (.of <| K) ⟶ _ := IsOpenImmersion.lift _ _ this
  have H : Spec.preimage i₂ ≫ CommRingCat.ofHom (algebraMap O K) =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫ Spec.preimage φ := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage, ← w.w]
    rw [← Proj.awayι_toSpecZero _ _ (hxd i i.2), IsOpenImmersion.lift_fac_assoc]
    exact Nat.zero_lt_of_ne_zero (hd i i.2)
  obtain ⟨i₀, φ', hφ, hφ'⟩ :=
    valuativeCriterion_existence_aux 𝒜 (Spec.preimage i₂).hom x (↑) (by simpa using hx) i
      (O := O) (K := K) (Spec.preimage φ).hom congr(($H).hom)
      (fun i ↦ d _ i.2) (fun i ↦ (hd _ i.2).bot_lt) (fun i ↦ hxd _ i.2)
  let e : O ≃+* (algebraMap O K).range :=
    (AlgEquiv.ofInjective (Algebra.ofId O K) (IsFractionRing.injective _ _)).toRingEquiv
  let φ'' := e.symm.toRingHom.comp ((Subring.inclusion hφ').comp (RingHom.rangeRestrict _))
  have hφ'' : (algebraMap O K).comp φ'' = φ'.comp (awayMap 𝒜 (hxd _ i.2) (mul_comm _ _)) := by
    ext x
    exact congr_arg Subtype.val (e.apply_symm_apply _)
  refine ⟨⟨Spec.map (CommRingCat.ofHom φ'') ≫ Proj.awayι 𝒜 _ (hxd _ i₀.2) (hd _ _).bot_lt, ?_, ?_⟩⟩
  · rw [← Spec.map_comp_assoc]
    convert IsOpenImmersion.lift_fac _ _ this using 1
    change _ = φ ≫ _
    rw [← Spec.map_preimage φ, ← CommRingCat.ofHom_hom (Spec.preimage φ), ← hφ,
      ← CommRingCat.ofHom_comp]
    simp [hφ'', SpecMap_awayMap_awayι, add_comm]
  · simp only [Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    conv_rhs => rw [← Spec.map_preimage i₂]
    congr 1
    ext x
    apply IsFractionRing.injective O K
    refine (DFunLike.congr_fun hφ'' (fromZeroRingHom 𝒜 _ _)).trans ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [awayMap_fromZeroRingHom, ← awayMap_fromZeroRingHom 𝒜 (hxd i₀ i₀.2) rfl,
      ← RingHom.comp_apply, hφ]
    exact congr($(H.symm) x)

instance [Algebra.FiniteType (𝒜 0) A] : UniversallyClosed (Proj.toSpecZero 𝒜) := by
  rw [UniversallyClosed.eq_valuativeCriterion]
  exact ⟨valuativeCriterion_existence 𝒜, inferInstance⟩

end UniversallyClosed

instance [Algebra.FiniteType (𝒜 0) A] : IsProper (Proj.toSpecZero 𝒜) where

end AlgebraicGeometry.Proj
