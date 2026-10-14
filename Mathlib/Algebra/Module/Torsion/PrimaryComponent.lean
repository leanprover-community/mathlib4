/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.DedekindDomain.Factorization

import Mathlib.RingTheory.Filtration

/-!
# I-Primary Components of modules

Let `A` be a commutative ring and `I`, an ideal of `A`.
Given an `A`-Module `M` it's `I`-primary component is defined as
  $$M(I) := \bigcup_{i : \mathbb{N}} \text{torsionBySet A  M }  I ^ i.$$

For `P : HeightOneSpectrum A`, the main result of this file is that
  $$M \cong \bigoplus_{P} M(P).$$

## Main definitions

* `Ideal.primaryComponent` : The `I`-primary component of an `A`-module `M`.

## Main results

* `Ideal.baer_of_primaryComponent_eq_top` : over a Noetherian ring, a module `M` with
  `M(I) = M` satisfies Baer's criterion as soon as maps into `M` extend along the inclusions
  `N ⊆ A ⧸ I ^ n`.
* `Ideal.primaryComponent.injective` : over a Noetherian ring, the `I`-primary component of
  an injective module is injective.

## References

* [Stacks: Injective modules, Lemma 08XW](https://stacks.math.columbia.edu/tag/08XW)

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
@[simps!]
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
  rw [← IsConcreteLE.le_iff]
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

theorem primaryComponent.map_surjective {M₁ M₂ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂] (hM₁ : IsTorsion A M₁)
    (P : HeightOneSpectrum A) (φ : M₁ →ₗ[A] M₂) (hf : Surjective φ) :
    Surjective (primaryComponent.map P.asIdeal φ) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : ∃ a, φ a = y := hf y
  obtain ⟨f, hf⟩ : ∃ f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (DFinsupp.lsum ℕ fun i : HeightOneSpectrum A ↦
      (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    simp only [← mem_iSup_iff_exists_dfinsupp, iSup_primaryComponent_eq_top hM₁, mem_top]
  refine ⟨f P, Subtype.ext ?_⟩
  simp only [map_apply_coe]
  rw [eq_comm, ← sub_eq_zero]
  refine (Submodule.disjoint_def.mp (iSupIndep_primaryComponent A M₂ P)) _ ?_ ?_
  · exact Submodule.sub_mem _ hy (primaryComponent_map_mem _ _ _)
  · have hdiff : φ b - φ ↑(f P) = ∑ Q ∈ f.support \ {P}, φ ↑(f Q) := by
      rw [sub_eq_iff_eq_add',
        ← Finset.sum_eq_add_sum_sdiff_singleton P (fun P ↦ φ (f P)) (by aesop)]
      simpa [DFinsupp.sumAddHom_apply, DFinsupp.sum] using congr(φ $hf).symm
    rw [hdiff]
    exact Submodule.sum_mem _ fun Q hQ ↦ Submodule.mem_iSup_of_mem Q <|
        Submodule.mem_iSup_of_mem (by grind) (primaryComponent_map_mem _ _ _)

end IsDedekindDomain

end AddCommGroup

section Injective

universe v

variable {Q : Type v} [AddCommGroup Q] [Module A Q] [IsNoetherianRing A]

private lemma exists_pow_smul_eq_zero_of_primaryComponent_eq_top
    (hQ : primaryComponent Q I = ⊤) (J : Ideal A) (g : J →ₗ[A] Q) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : J, a • g x = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := J)
  have h (x : Q) : ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    obtain ⟨n, hn⟩ := (primaryComponent_mem Q I x).1 (hQ ▸ mem_top)
    exact ⟨n, fun a ha ↦ (mem_torsionBySet_iff _ _).1 hn ⟨a, ha⟩⟩
  choose e he using fun i ↦ h (g (s i))
  refine ⟨Finset.univ.sup e, fun a ha x ↦ ?_⟩
  have hx : x ∈ Submodule.span A (Set.range s) := hs ▸ mem_top
  induction hx using span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact he i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, smul_comm, hy, smul_zero]

theorem baer_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Baer A Q := by
  intro J g
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_primaryComponent_eq_top I hQ J g
  -- `g` vanishes on `I ^ n • J`.
  have hgIJ (x : A) (hx : x ∈ I ^ n • J) : g ⟨x, smul_le_right hx⟩ = 0 := by
    induction hx using smul_induction_on' with
    | smul a ha y hy =>
      rw [show (⟨a • y, _⟩ : J) = a • ⟨y, hy⟩ from rfl, map_smul, hn a ha]
    | add x hx y hy hx' hy' =>
      rw [show (⟨x + y, _⟩ : J) = ⟨x, smul_le_right hx⟩ + ⟨y, smul_le_right hy⟩ from rfl,
        map_add, hx', hy', add_zero]
  -- Artin–Rees: `J ⊓ I ^ (n + k) ≤ I ^ n • J`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  have hAR (x : A) (hxJ : x ∈ J) (hxm : x ∈ I ^ (n + k)) : x ∈ I ^ n • J := by
    have h1 : x ∈ I ^ (n + k) • (⊤ : Ideal A) ⊓ J := ⟨by simpa using hxm, hxJ⟩
    rw [hk (n + k) (by lia), Nat.add_sub_cancel] at h1
    exact smul_mono le_rfl inf_le_right h1
  -- `g` factors through the image of `J` in `A ⧸ I ^ (n + k)`.
  let φ : J →ₗ[A] A ⧸ I ^ (n + k) := (I ^ (n + k)).mkQ ∘ₗ J.subtype
  have hker : LinearMap.ker φ ≤ LinearMap.ker g := fun x hx ↦ by
    have hxm : (x : A) ∈ I ^ (n + k) := by
      simpa [φ, Ideal.Quotient.eq_zero_iff_mem] using hx
    simpa using hgIJ x (hAR x x.2 hxm)
  obtain ⟨w, hw⟩ := h (n + k) (LinearMap.range φ)
    ((LinearMap.ker φ).liftQ g hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap)
  refine ⟨w ∘ₗ (I ^ (n + k)).mkQ, fun x hx ↦ ?_⟩
  have := hw ⟨φ ⟨x, hx⟩, LinearMap.mem_range_self φ _⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  exact this

/-- Over a Noetherian ring, a module `Q` with `Q(I) = Q` is injective as soon as linear maps
into `Q` extend along the inclusions of submodules of `A ⧸ I ^ n`, for all `n`. -/
theorem injective_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Injective A Q :=
  (baer_of_primaryComponent_eq_top I hQ h).injective

/-- Over a Noetherian ring, the `I`-primary component `Γ_I(Q)` of an injective module `Q` is
injective. -/
@[stacks 08XW "(2)"]
instance primaryComponent.injective [Small.{v} A] [Module.Injective A Q] :
    Module.Injective A (primaryComponent Q I) := by
  refine injective_of_primaryComponent_eq_top I (eq_top_iff.2 fun x _ ↦ ?_) fun n N f ↦ ?_
  · obtain ⟨n, hn⟩ := (primaryComponent_mem Q I x).1 x.2
    refine (primaryComponent_mem _ I x).2 ⟨n, (mem_torsionBySet_iff _ _).2 fun a ↦ ?_⟩
    exact Subtype.ext ((mem_torsionBySet_iff _ _).1 hn a)
  obtain ⟨v, hv⟩ := Module.Injective.extension_property A Q _ _ N.subtype N.injective_subtype
    ((primaryComponent Q I).subtype ∘ₗ f)
  -- The extension lands in `Γ_I(Q)`, because `A ⧸ I ^ n` is killed by `I ^ n`.
  refine ⟨v.codRestrict _ fun y ↦ (primaryComponent_mem Q I _).2 ⟨n,
    (mem_torsionBySet_iff _ _).2 fun a ↦ ?_⟩, fun x ↦ Subtype.ext congr($hv x)⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right b _ a.2), map_zero]

end Injective

end CommRing

end Ideal
