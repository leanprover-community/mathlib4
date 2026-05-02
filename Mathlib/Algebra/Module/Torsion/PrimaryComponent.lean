/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# I-Primary Components of modules

Let `A` be a commutative ring and `I`, an ideal of `A`.
Given an `A`-Module `M` it's `I`-primary component is defined as
  $$M(I) := \bigcup_{i : \mathbb{N}} \text{torsionBySet A  M }  I ^ i.$$

For `P : HeightOneSpectrum A`, the main result of this file is that
  $$M \cong \bigoplus_{P} M(P).$$

## Main definitions

* `Ideal.primaryComponent` : The `I`-primary component of an `A`-module `M`.

-/

@[expose] public section

variable {A M M₁ M₂ : Type*} [CommRing A]

open IsDedekindDomain Submodule Module HeightOneSpectrum Set Function

namespace Ideal

variable (I : Ideal A)

section CommRing

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

open Set Function Submodule Module

variable (M)
/--
The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`. -/
def primaryComponent : Submodule A M := ⨆ i : ℕ, torsionBySet A M ↑(I ^ i)

theorem primaryComponent_mem (x : M) :
    x ∈ primaryComponent M I ↔ ∃ n, x ∈ torsionBySet A M ↑(I ^ n) := by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_iSup_of_mem)

theorem primaryComponent_map_mem (φ : M₁ →ₗ[A] M₂) (c : primaryComponent M₁ I) :
    φ c ∈ primaryComponent M₂ I := by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

/-- Given an A-linear map between M₁ and M₂, `primaryComponent.map` is the
restriction to the I-primaryComponent components of M₁ and M₂. -/
def primaryComponent.map (φ : M₁ →ₗ[A] M₂) : primaryComponent M₁ I →ₗ[A] primaryComponent M₂ I :=
  (φ.domRestrict (primaryComponent M₁ I)).codRestrict (primaryComponent M₂ I) (fun c ↦
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem I φ c)

theorem primaryComponent.map_ker_eq (φ : M₁ →ₗ[A] M₂) :
    (primaryComponent.map I φ).ker.map (primaryComponent M₁ I).subtype =
      (primaryComponent φ.ker I).map φ.ker.subtype := by
  aesop (add norm [map, Subtype.ext_iff, primaryComponent_mem])

theorem primaryComponent_torsionBySet_eq_inf (I : Ideal A) :
    (primaryComponent (torsionBySet A M ↑I) I).map (Submodule.subtype _) =
    primaryComponent M I ⊓ torsionBySet A M ↑I := by
  ext x
  simp [primaryComponent_mem]

theorem primaryComponent_torsionBySet_of_isCoprime (J : Ideal A) (hD : IsCoprime I J) :
    primaryComponent (torsionBySet A M J) I = ⊥ := by
  have (n : ℕ) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.map_bot, Submodule.mem_bot]
  refine ⟨fun ⟨⟨n, _⟩, _⟩ ↦ ?_, by simp_all⟩
  specialize this n
  simp_all [disjoint_def]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module A M]

open Submodule in
theorem primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) :
    (primaryComponent ↥(N₁ ⊔ N₂) I).map (N₁ ⊔ N₂).subtype =
    (primaryComponent N₁ I).map N₁.subtype ⊔ (primaryComponent N₂ I).map N₂.subtype := by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, hy, z, hz, rfl⟩⟩
    refine ⟨y, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hy]⟩, z, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hz]⟩, rfl⟩
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).1
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).2
  · rintro ⟨y, ⟨⟨n₁, hy⟩, hymem⟩, z, ⟨⟨n₂, hz⟩, hzmem⟩, rfl⟩
    constructor
    · use (max n₁ n₂)
      intro a ha
      specialize hy a (Ideal.pow_le_pow_right (by simp : n₁ ≤ max n₁ n₂) ha)
      specialize hz a (Ideal.pow_le_pow_right (by simp : n₂ ≤ max n₁ n₂) ha)
      aesop
    · use y, hymem, z, hzmem

section IsDedekindDomain

variable [IsDedekindDomain A]

open scoped nonZeroDivisors

theorem iSup_primaryComponent_eq_top (h : IsTorsion A M) :
    ⨆ P : HeightOneSpectrum A, primaryComponent M (P : Ideal A) = ⊤ := by
  rw [eq_top_iff']
  intro x
  obtain ⟨⟨a : A, ha : a ∈ A⁰⟩, hmem : a • x = 0⟩ := h (x := x)
  replace hmem : x ∈ torsionBySet A M (span {a}) := by
    simp_all [← torsionBySet_eq_torsionBySet_span {a}]
  have ha0 : span {a} ≠ ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  rw [← iInf_maxPowDividing_eq ha0] at hmem
  let : Fintype (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})) :=
    Finite.fintype (hasFiniteMulSupport ha0)
  let S := (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})).toFinset
  have : (⨅ i : HeightOneSpectrum A, i.maxPowDividing (span {a})) =
      (⨅ i ∈ S, i.maxPowDividing (span {a})) := by
    ext x
    constructor
    · aesop
    · simp only [mem_iInf]
      intro h i
      by_cases htop : i.maxPowDividing (span {a}) = ⊤ <;> simp_all [S]
  have hPairwise : (S : Set (HeightOneSpectrum _)).Pairwise
      fun i j ↦ i.maxPowDividing (span {a}) ⊔ j.maxPowDividing (span {a}) = ⊤ :=
    fun r hr s hs hrs ↦ (isCoprime_pow_of_ne _ _ hrs _ _).sup_eq
  rw [this, ← iSup_torsionBySet_ideal_eq_torsionBySet_iInf hPairwise] at hmem
  revert x
  rw [← SetLike.le_def]
  refine iSup_mono (fun P x hxmem ↦ ?_)
  by_cases hPS : P ∈ S
  · simp_all only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, mem_toFinset, mem_mulSupport,
      one_eq_top, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
      Subtype.forall, iSup_pos, S]
    exact ⟨(Associates.mk P.asIdeal).count (Associates.mk (span {a})).factors, fun _ b ↦ hxmem _ b⟩
  · simp_all

variable (A M) in
theorem iSupIndep_primaryComponent :
    iSupIndep fun P : HeightOneSpectrum A => primaryComponent M (P : Ideal A) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s p hmem hsum
  simp only [primaryComponent_mem] at hmem
  choose! f hmem using hmem
  let m := s.sup f
  have hSupIndep : iSupIndep fun i : HeightOneSpectrum A ↦ torsionBySet A M ↑(i.asIdeal ^ m) := by
    rw [iSupIndep_iff_supIndep]
    exact fun _ ↦ supIndep_torsionBySet_ideal
      fun _ _ _ _ hPQ ↦ (isCoprime_pow_of_ne _ _ hPQ _ _).sup_eq
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hSupIndep
  apply hSupIndep _ _ ?_ hsum
  exact fun P hP ↦ torsionBySet_le_torsionBySet_pow _ _ (Finset.le_sup hP) _ (hmem P hP)

open DFinsupp hiding disjoint_iff
theorem primaryComponent.map_surjective (M₁ M₂ : Type*)
    [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂] (hM₁ : IsTorsion A M₁)
    (P : HeightOneSpectrum A) (φ : M₁ →ₗ[A] M₂) (hf : Surjective φ) :
    Surjective (primaryComponent.map P.asIdeal φ) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : ∃ a, φ a = y := hf y
  obtain ⟨f, hf⟩ : ∃ f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (lsum ℕ fun i : HeightOneSpectrum A ↦ (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    rw [← mem_iSup_iff_exists_dfinsupp]
    have := iSup_primaryComponent_eq_top hM₁
    simp only [eq_top_iff'] at this
    exact this b
  use f P
  ext
  suffices ∑ x ∈ f.support \ {P}, φ ↑(f x) = 0 by
    aesop (add norm [(Finset.sum_eq_add_sum_diff_singleton P (fun x ↦ φ (f x))), map,
      sumAddHom_apply, sum])
  have hboth : ∀ x ∈ primaryComponent M₂ P.asIdeal,
      x ∈ ⨆ Q ≠ P, primaryComponent M₂ Q.asIdeal → x = 0 := by
    simpa [disjoint_iff, Submodule.eq_bot_iff] using iSupIndep_primaryComponent A M₂ P
  apply hboth <;> clear hboth
  · have h_sum_eq : ∑ x ∈ f.support, φ ↑(f x) = φ b := by
      simpa [sumAddHom_apply, sum] using congr(φ $hf)
    rw [← sub_eq_of_eq_add' (Finset.sum_eq_add_sum_diff_singleton P (fun P ↦ φ (f P)) (by aesop)),
      h_sum_eq]
    exact Submodule.sub_mem _ hy (primaryComponent_map_mem _ _ _)
  · rw [Submodule.mem_biSup_iff_exists_dfinsupp]
    use (mapRange (fun Q : HeightOneSpectrum A ↦ map Q.asIdeal φ) (by simp) f)
    simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      DFinsupp.filter_ne_eq_erase, DFinsupp.support_erase, DFinsupp.erase_apply,
      DFinsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe, subtype_apply, Finset.erase_eq]
    apply Finset.sum_congr_of_eq_on_inter
    · simp_all
    · grind only [= Finset.mem_sdiff, map, = mem_support_toFun, mapRange_apply,
      !LinearMap.codRestrict_apply, = map_zero, LinearMap.domRestrict_apply, #f5c8]
    · aesop

end IsDedekindDomain

end AddCommGroup

end CommRing

end Ideal
