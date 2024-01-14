/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.GradedAlgebra.Radical

#align_import algebraic_geometry.projective_spectrum.scheme from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

## Implementation

In `AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `toSpec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `ProjIsoSpecTopComponent.IoSpec.carrier`). This ideal is
    prime, the proof is in `ProjIsoSpecTopComponent.ToSpec.toFun`. The fact that this function
    is continuous is found in `ProjIsoSpecTopComponent.toSpec`
  - backward direction `fromSpec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal`;
    * This ideal is also homogeneous, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.prime`.
    Hence we have a well defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `ProjIsoSpecTopComponent.FromSpec.toFun`. But to prove the continuity of this function,
    we need to prove `fromSpec ∘ toSpec` and `toSpec ∘ fromSpec` are both identities (TBC).

## Main Definitions and Statements

* `degreeZeroPart`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `ProjIsoSpecTopComponent.toSpec`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `ProjIsoSpecTopComponent.ToSpec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

set_option linter.uppercaseLean3 false -- Porting note: Proj and Spec

namespace AlgebraicGeometry

open scoped DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero mk

variable {R A : Type*}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- Porting note: currently require lack of hygiene to use in variable declarations
-- maybe all make into notation3?
set_option hygiene false
-- `Proj` as a locally ringed space
local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜

-- the underlying topological space of `Proj`
local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜

-- `Proj` restrict to some open set
macro "Proj| " U:term : term =>
  `((Proj.toLocallyRingedSpace 𝒜).restrict (Opens.openEmbedding (X := Proj.T) ($U : Opens Proj.T)))

-- the underlying topological space of `Proj` restricted to some open set
local notation "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace
    <| (LocallyRingedSpace.restrict Proj (Opens.openEmbedding (X := Proj.T) (U : Opens Proj.T)))

-- basic open sets in `Proj`
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

-- basic open sets in `Spec`
local notation "sbo " f => PrimeSpectrum.basicOpen f

-- `Spec` as a locally ringed space
local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)

-- the underlying topological space of `Spec`
local notation "Spec.T " ring =>
  (Spec.locallyRingedSpaceObj (CommRingCat.of ring)).toSheafedSpace.toPresheafedSpace.1

local notation3 "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f

namespace ProjIsoSpecTopComponent

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/
namespace ToSpec

open Ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.
variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| (pbo f))

/--
For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `TopComponent.Forward.toFun`-/
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (Ideal.span <| algebraMap A (Away f) '' x.val.asHomogeneousIdeal)
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier

theorem mem_carrier_iff (z : A⁰_ f) :
    z ∈ carrier x ↔ z.val ∈ Ideal.span (algebraMap A (Away f) '' x.1.asHomogeneousIdeal) :=
  Iff.rfl
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mem_carrier_iff

lemma num_not_mem_of_not_mem_carrier (z : A⁰_ f) (h : z ∉ carrier x) :
    z.num ∉ x.1.asHomogeneousIdeal := by
  contrapose! h
  rw [mem_carrier_iff, z.eq_num_div_den, show Localization.mk z.num _ = mk z.num 1 * mk 1 _ by
    rw [mk_mul, one_mul, mul_one]]
  exact Ideal.mul_mem_right _ _ <| Ideal.subset_span ⟨_, h, rfl⟩

lemma pow_mul_num_not_mem_of_not_mem_carrier (z : A⁰_ f) (h : z ∉ carrier x) (n : ℕ) :
    f^n * z.num ∉ x.1.asHomogeneousIdeal :=
  fun r ↦ x.1.isPrime.mem_or_mem r |>.elim
    (fun r ↦ x.2 <| x.1.isPrime.pow_mem_iff_mem _ (by
      by_contra h
      simp only [not_lt, nonpos_iff_eq_zero] at h
      erw [h, pow_zero, ← Ideal.eq_top_iff_one] at r
      exact x.1.isPrime.1 r) |>.mp r) (num_not_mem_of_not_mem_carrier x z h)

theorem MemCarrier.clear_denominator' [DecidableEq (Away f)] {z : Localization.Away f}
    (hz : z ∈ span (algebraMap A (Away f) '' x.val.asHomogeneousIdeal)) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f) (N : ℕ) (acd :
      ∀ y ∈ c.support.image c, A),
      f ^ N • z =
        algebraMap A (Away f)
          (∑ i in c.support.attach,
            acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.choose) := by
  rw [← submodule_span_eq, Finsupp.span_eq_range_total, LinearMap.mem_range] at hz
  rcases hz with ⟨c, eq1⟩
  rw [Finsupp.total_apply, Finsupp.sum] at eq1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers f) (c.support.image c)
  choose acd hacd using hN
  refine' ⟨c, N, acd, _⟩
  rw [← eq1, smul_sum, map_sum, ← sum_attach]
  congr 1
  ext i
  rw [_root_.map_mul, hacd, (Classical.choose_spec i.1.2).2, smul_eq_mul, smul_mul_assoc]
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier.clear_denominator' AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.MemCarrier.clear_denominator'

theorem MemCarrier.clear_denominator [DecidableEq (Away f)] {z : A⁰_ f} (hz : z ∈ carrier x) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f) (N : ℕ) (acd :
      ∀ y ∈ c.support.image c, A),
      f ^ N • z.val =
        algebraMap A (Away f)
          (∑ i in c.support.attach,
            acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.choose) :=
  MemCarrier.clear_denominator' x <| (mem_carrier_iff x z).mpr hz
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier.clear_denominator AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.MemCarrier.clear_denominator

/--
For `x : pbo f`
The ideal `A⁰_f ∩ span {g / 1 | g ∈ x}` is equal to `span {a/f^n | a ∈ x and deg(a) = deg(f^n)}`
-/
lemma carrier_eq_span :
    carrier x =
    Ideal.span { z : HomogeneousLocalization.Away 𝒜 f |
      ∃ (s F : A) (_ : s ∈ x.1.asHomogeneousIdeal) (n : ℕ)
        (s_mem : s ∈ 𝒜 n) (F_mem1 : F ∈ 𝒜 n) (F_mem2 : F ∈ Submonoid.powers f),
        z = Quotient.mk'' ⟨n, ⟨s, s_mem⟩, ⟨F, F_mem1⟩,F_mem2⟩ } := by
  classical
  refine le_antisymm ?_ <| Ideal.span_le.mpr ?_
  · intro z hz
    let k : ℕ := z.den_mem.choose
    have hk : f^k = z.den := z.den_mem.choose_spec
    suffices mem1 : z.num ∈ x.1.asHomogeneousIdeal
    · refine Ideal.subset_span ⟨_, _, mem1, _, z.num_mem_deg, z.den_mem_deg, z.den_mem, ?_⟩
      rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
        HomogeneousLocalization.eq_num_div_den]

    obtain ⟨c, N, acd, eq1⟩ := MemCarrier.clear_denominator x hz
    rw [z.eq_num_div_den, smul_mk, smul_eq_mul, ← mk_one_eq_algebraMap,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at eq1
    obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq1⟩ := eq1
    dsimp only [OneMemClass.coe_one] at eq1
    rw [one_mul, ← hk, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at eq1

    suffices : f^(l + k) * ∑ i in c.support.attach, acd (c i) _ * i.1.2.choose ∈
      x.1.asHomogeneousIdeal
    · exact (x.1.isPrime.mem_or_mem (eq1.symm ▸ this)).resolve_left fun r ↦
        (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).mp x.2 <| x.1.isPrime.mem_of_pow_mem _ r
    exact Ideal.mul_mem_left _ _ <| Ideal.sum_mem _ (fun ⟨j, hj⟩ _ ↦
      Ideal.mul_mem_left _ _ j.2.choose_spec.1)

  · rintro _ ⟨s, _, hs, n, s_mem, F_mem, ⟨l, rfl⟩, rfl⟩
    erw [mem_carrier_iff, HomogeneousLocalization.val_mk'']
    erw [show (Localization.mk s ⟨f ^ l, ⟨_, rfl⟩⟩ : Localization.Away f) =
      (Localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : Localization.Away f) * Localization.mk s 1 by
      · rw [Localization.mk_mul, mul_one, one_mul]]
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span ⟨s, hs, rfl⟩

theorem disjoint :
    Disjoint (x.1.asHomogeneousIdeal.toIdeal : Set A) (Submonoid.powers f : Set A) := by
  by_contra rid
  rw [Set.not_disjoint_iff] at rid
  choose g hg using rid
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg
  by_cases k_ineq : 0 < k
  · erw [x.1.isPrime.pow_mem_iff_mem _ k_ineq] at hg1
    exact x.2 hg1
  · dsimp at hg1
    erw [show k = 0 by linarith, pow_zero, ← Ideal.eq_top_iff_one] at hg1
    apply x.1.isPrime.1
    exact hg1
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.disjoint AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.disjoint

theorem carrier_ne_top : carrier x ≠ ⊤ := by
  have eq_top := disjoint x
  classical
  contrapose! eq_top
  obtain ⟨c, N, acd, eq1⟩ := MemCarrier.clear_denominator x ((Ideal.eq_top_iff_one _).mp eq_top)
  rw [Algebra.smul_def, HomogeneousLocalization.one_val, mul_one] at eq1
  change Localization.mk (f ^ N) 1 = Localization.mk _ 1 at eq1
  simp only [mk_eq_mk', IsLocalization.eq] at eq1
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
  dsimp at eq1
  erw [one_mul, one_mul] at eq1
  change f ^ _ * f ^ _ = f ^ _ * _ at eq1
  rw [Set.not_disjoint_iff_nonempty_inter]
  refine'
    ⟨f ^ M * f ^ N, eq1.symm ▸ mul_mem_left _ _ (sum_mem _ fun i _ => mul_mem_left _ _ _),
      ⟨M + N, by dsimp; rw [pow_add]⟩⟩
  generalize_proofs h₁ h₂
  exact (Classical.choose_spec h₂).1
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier_ne_top AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier_ne_top

variable (f)

/-- The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `TopComponent.forward`.
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, carrier_ne_top x, fun {x1 x2} hx12 => by
    classical
    rw [mem_carrier_iff] at hx12
    let J := span ((algebraMap A (Away f) : A → (Away f)) '' x.val.asHomogeneousIdeal)
    suffices h : ∀ x y : Localization.Away f, x * y ∈ J → x ∈ J ∨ y ∈ J
    · rw [HomogeneousLocalization.mul_val] at hx12; exact h x1.val x2.val hx12
    clear x1 x2 hx12
    intro x1 x2 hx12
    induction' x1 using Localization.induction_on with data_x1
    induction' x2 using Localization.induction_on with data_x2
    rcases data_x1, data_x2 with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩
    rcases MemCarrier.clear_denominator' x hx12 with ⟨c, N, acd, eq1⟩
    simp only [Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * (Localization.mk _ _ * Localization.mk _ _)
      = Localization.mk _ _ at eq1
    simp only [Localization.mk_mul, one_mul] at eq1
    simp only [mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, one_mul] at eq1
    change f ^ _ * (_ * _) = f ^ _ * (f ^ _ * f ^ _ * _) at eq1
    have that : a1 * a2 * f ^ N * f ^ M ∈ x.val.asHomogeneousIdeal.toIdeal := ?_
    rcases x.1.isPrime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _ from that) with (h1 | rid2)
    rcases x.1.isPrime.mem_or_mem h1 with (h1 | rid1)
    rcases x.1.isPrime.mem_or_mem h1 with (h1 | h2)
    · left;
      simp only [show (Localization.mk a1 ⟨f ^ n1, _⟩ : Away f) =
        Localization.mk a1 1 * Localization.mk 1 (⟨f ^ n1, ⟨n1, rfl⟩⟩ : Submonoid.powers f) by
          rw [Localization.mk_mul, mul_one, one_mul]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h1, rfl⟩)
    · right;
      simp only [show (mk a2 ⟨f ^ n2, _⟩ : Away f) =
        mk a2 1 * Localization.mk 1 (⟨f ^ n2, ⟨n2, rfl⟩⟩ : Submonoid.powers f) by
          rw [Localization.mk_mul, mul_one, one_mul]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h2, rfl⟩)
    · exact False.elim (x.2 (x.1.isPrime.mem_of_pow_mem N rid1))
    · exact False.elim (x.2 (x.1.isPrime.mem_of_pow_mem M rid2))
    · rw [← mul_comm (f ^ M), ← mul_comm (f ^ N), eq1]
      refine' mul_mem_left _ _ (mul_mem_left _ _ (sum_mem _ fun i _ => mul_mem_left _ _ _))
      generalize_proofs h₁ h₂; exact (Classical.choose_spec h₂).1⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.toFun

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
theorem preimage_eq (a b : A) (k : ℕ) (a_mem : a ∈ 𝒜 k) (b_mem1 : b ∈ 𝒜 k)
    (b_mem2 : b ∈ Submonoid.powers f) :
    toFun f ⁻¹'
        (@PrimeSpectrum.basicOpen (A⁰_ f) _ (Quotient.mk'' ⟨k, ⟨a, a_mem⟩, ⟨b, b_mem1⟩, b_mem2⟩) :
          Set (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f))) =
      {x | x.1 ∈ (pbo f) ⊓ pbo a} := by
  classical
  ext1 y
  constructor <;> intro hy
  · refine' ⟨y.2, _⟩
    rw [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hy
    rw [ProjectiveSpectrum.mem_coe_basicOpen]
    intro a_mem_y
    apply hy
    rw [toFun, mem_carrier_iff, HomogeneousLocalization.val_mk'', Subtype.coe_mk]
    dsimp; rcases b_mem2 with ⟨k, hk⟩
    dsimp at hk
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : Away f) =
      Localization.mk 1 (⟨f ^ k, ⟨_, rfl⟩⟩ : Submonoid.powers f) * mk a 1 by
        rw [mk_mul, one_mul, mul_one]; congr; rw [hk]]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, a_mem_y, rfl⟩)
  · change y.1 ∈ ProjectiveSpectrum.basicOpen 𝒜 f ⊓ ProjectiveSpectrum.basicOpen 𝒜 a at hy
    rcases hy with ⟨hy1, hy2⟩
    rw [ProjectiveSpectrum.mem_coe_basicOpen] at hy1 hy2
    rw [Set.mem_preimage, toFun, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro rid; dsimp at rid
    rcases MemCarrier.clear_denominator _ rid with ⟨c, N, acd, eq1⟩
    rw [Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * Localization.mk _ _ = Localization.mk _ _ at eq1
    rw [mk_mul, one_mul, mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, one_mul] at eq1
    simp only [Subtype.coe_mk] at eq1
    have : a * f ^ N * f ^ M ∈ y.val.asHomogeneousIdeal.toIdeal := by
      rw [mul_comm _ (f ^ N), mul_comm _ (f ^ M), eq1]
      refine' mul_mem_left _ _ (mul_mem_left _ _ (sum_mem _ fun i _ => mul_mem_left _ _ _))
      generalize_proofs h₁ h₂; exact (Classical.choose_spec h₂).1
    rcases y.1.isPrime.mem_or_mem this with (H1 | H3)
    rcases y.1.isPrime.mem_or_mem H1 with (H1 | H2)
    · exact hy2 H1
    · exact y.2 (y.1.isPrime.mem_of_pow_mem N H2)
    · exact y.2 (y.1.isPrime.mem_of_pow_mem M H3)
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.preimage_eq AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_eq

end ToSpec

section

variable {𝒜}

/-- The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def toSpec {f : A} : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f where
  toFun := ToSpec.toFun f
  continuous_toFun := by
    rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
    rintro _ ⟨⟨k, ⟨a, ha⟩, ⟨b, hb1⟩, ⟨k', hb2⟩⟩, rfl⟩; dsimp
    erw [ToSpec.preimage_eq f a b k ha hb1 ⟨k', hb2⟩]
    refine' isOpen_induced_iff.mpr ⟨(pbo f).1 ⊓ (pbo a).1, IsOpen.inter (pbo f).2 (pbo a).2, _⟩
    ext z; constructor
    · intro hz; simpa [Set.mem_preimage]
    · intro hz; simpa only [Set.inf_eq_inter,Set.mem_inter_iff,Set.mem_preimage]
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec

end

namespace FromSpec

open GradedAlgebra SetLike

open Finset hiding mk_zero

-- Porting note: _root_ doesn't work here
open HomogeneousLocalization

variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

open Lean Meta Elab Tactic

macro "mem_tac_aux" : tactic =>
  `(tactic| first | exact pow_mem_graded _ (Submodule.coe_mem _) | exact nat_cast_mem_graded _ _ |
    exact pow_mem_graded _ f_deg)

macro "mem_tac" : tactic =>
  `(tactic| first | mem_tac_aux |
    repeat (all_goals (apply SetLike.GradedMonoid.toGradedMul.mul_mem)); mem_tac_aux)

/-- The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending
`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the
elements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power
of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,
lies in `q`.

The set `{a | aᵢᵐ/fⁱ ∈ q}`
* is an ideal, as proved in `carrier.asIdeal`;
* is homogeneous, as proved in `carrier.asHomogeneousIdeal`;
* is prime, as proved in `carrier.asIdeal.prime`;
* is relevant, as proved in `carrier.relevant`.
-/
def carrier (q : Spec.T A⁰_ f) : Set A :=
  {a | ∀ i, (Quotient.mk'' ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1}
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier

theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔ ∀ i, (Quotient.mk'' ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
      ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1 :=
  Iff.rfl
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_carrier_iff AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff

theorem mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔
      ∀ i, (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) ∈
          algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' { s | s ∈ q.1 } :=
  (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine' ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x ∈ q.asIdeal at h
        convert h
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'']
        dsimp only [Subtype.coe_mk]; rw [← hx]; rfl)
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_carrier_iff' AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff'

theorem carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a ∈ carrier f_deg q)
    (hb : b ∈ carrier f_deg q) : a + b ∈ carrier f_deg q := by
  refine' fun i => (q.2.mem_or_mem _).elim id id
  change (Quotient.mk'' ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : ℕ → A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 : A⁰_ f)
      else
        -- Porting note: inlining `l`, `r` causes a "can't synth HMul A⁰_ f A⁰_ f ?" error
        if h1 : j ≤ m then
          letI l : A⁰_ f := Quotient.mk''
            ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := Quotient.mk''
            ⟨m * i, ⟨proj 𝒜 i b ^ m, by mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          l * r
        else
          letI l : A⁰_ f := Quotient.mk''
            ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := Quotient.mk''
            ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) * proj 𝒜 i b ^ (m + m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          l * r
  rotate_left
  · rw [(_ : m * i = _)]
    -- Porting note: it seems unification with mul_mem is more fiddly reducing value of mem_tac
    apply GradedMonoid.toGradedMul.mul_mem (i := j • i) (j := (m - j) • i) <;> mem_tac_aux
    rw [← add_smul, Nat.add_sub_of_le h1]; rfl
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem (i := (j-m) • i) (j := (m + m - j) • i) <;> mem_tac_aux
    rw [← add_smul]; congr; zify [le_of_not_lt h2, le_of_not_le h1]; abel
  convert_to ∑ i in range (m + m + 1), g i ∈ q.1; swap
  · refine' q.1.sum_mem fun j _ => nsmul_mem _ _; split_ifs
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'']
  change _ = (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) _
  dsimp only [Subtype.coe_mk]; rw [map_sum, mk_sum]
  apply Finset.sum_congr rfl fun j hj => _
  intro j hj
  change _ = HomogeneousLocalization.val _
  rw [HomogeneousLocalization.smul_val]
  split_ifs with h2 h1
  · exact ((Finset.mem_range.1 hj).not_le h2).elim
  all_goals simp only [HomogeneousLocalization.mul_val, HomogeneousLocalization.zero_val,
    HomogeneousLocalization.val_mk'', Subtype.coe_mk, mk_mul, ← smul_mk]; congr 2
  · dsimp; rw [mul_assoc, ← pow_add, add_comm (m - j), Nat.add_sub_assoc h1]
  · simp_rw [pow_add]; rfl
  · dsimp; rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_not_le h1)]
  · simp_rw [pow_add]; rfl
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.add_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.add_mem

variable (hm : 0 < m) (q : Spec.T A⁰_ f)

theorem carrier.zero_mem : (0 : A) ∈ carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1 using 1
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.zero_val]; simp_rw [map_zero, zero_pow hm]
  convert Localization.mk_zero (S := Submonoid.powers f) _ using 1
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.zero_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem

theorem carrier.smul_mem (c x : A) (hx : x ∈ carrier f_deg q) : c • x ∈ carrier f_deg q := by
  revert c
  refine' DirectSum.Decomposition.inductionOn 𝒜 _ _ _
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    -- Porting note: having trouble with Mul instance
    let product : A⁰_ f :=
      Mul.mul (Quotient.mk'' ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, ?_⟩, ⟨n, rfl⟩⟩ : A⁰_ f)
          (Quotient.mk'' ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, ?_⟩, ⟨i - n, rfl⟩⟩ : A⁰_ f)
    split_ifs with h
    · convert_to product ∈ q.1
      · dsimp
        erw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.val_mk'']
        simp_rw [mul_pow]; rw [Localization.mk_mul]
        congr; erw [← pow_add, Nat.add_sub_of_le h]
        · rw [(_ : m • n = _)]; mem_tac; simp only [smul_eq_mul, mul_comm]
        · rw [(_ : m • (i - n) = _)]; mem_tac; simp only [smul_eq_mul, mul_comm]
      · apply Ideal.mul_mem_left (α := A⁰_ f) _ _ (hx _)
    · simp_rw [zero_pow hm]; convert carrier.zero_mem f_deg hm q i; rw [map_zero, zero_pow hm]
  · simp_rw [add_smul]; exact fun _ _ => carrier.add_mem f_deg q
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.smul_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.smul_mem

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
def carrier.asIdeal : Ideal A where
  carrier := carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal


theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 :=
  fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simp only [proj_apply, decompose_of_mem_ne 𝒜 (Submodule.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm]
    convert carrier.zero_mem f_deg hm q j; rw [map_zero, zero_pow hm]
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ideal.
-/
def carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_homogeneous_ideal AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal

theorem carrier.denom_not_mem : f ∉ carrier.asIdeal f_deg hm q := fun rid =>
  q.IsPrime.ne_top <|
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.one_val,
          HomogeneousLocalization.val_mk'']
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp only [mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self])
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.denom_not_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.denom_not_mem

theorem carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ carrier.asHomogeneousIdeal f_deg hm q :=
  fun rid => carrier.denom_not_mem f_deg hm q <| rid <| DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.relevant AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.relevant

theorem carrier.asIdeal.ne_top : carrier.asIdeal f_deg hm q ≠ ⊤ := fun rid =>
  carrier.denom_not_mem f_deg hm q (rid.symm ▸ Submodule.mem_top)
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.ne_top AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.ne_top

theorem carrier.asIdeal.prime : (carrier.asIdeal f_deg hm q).IsPrime :=
  (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (∀ i, _ ∈ _) ∨ ∀ i, _ ∈ _ by
      rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left]
      · apply q.2.mem_or_mem; convert hxy (nx + ny) using 1
        dsimp
        simp_rw [decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (SetLike.GradedMonoid.toGradedMul.mul_mem hnx hny),
          mul_pow, pow_add]
        simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.mul_val, mk_mul]
        simp only [Submonoid.mk_mul_mk, mk_eq_monoidOf_mk']
      all_goals
        intro n hn; convert q.1.zero_mem using 1
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.zero_val]; simp_rw [proj_apply]
        convert mk_zero (S := Submonoid.powers f) _
        rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm]
        · first | exact hnx | exact hny
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.prime AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime

/-- The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp <| carrier.denom_not_mem f_deg hm q⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.toFun

end FromSpec

section toSpecFromSpec

lemma toSpecFromSpec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (x : Spec.T (A⁰_ f)) :
    toSpec (FromSpec.toFun f_deg hm x) = x := show _ = (_ : PrimeSpectrum _) by
  ext (z : A⁰_ f); fconstructor <;> intro hz
  · change z ∈ ToSpec.carrier _ at hz
    erw [ToSpec.carrier_eq_span, mem_span_set] at hz
    obtain ⟨c, support_le, rfl⟩ := hz
    refine Ideal.sum_mem _ fun j hj ↦ Ideal.mul_mem_left _ _ ?_
    obtain ⟨s, _, hs, n, s_mem, F_mem, ⟨k, rfl⟩, rfl⟩ := support_le hj
    refine x.IsPrime.mem_of_pow_mem m <| show Quotient.mk'' ⟨_, ⟨s^m, _⟩, _, _⟩ ∈ x.asIdeal from ?_
    convert hs n using 1
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
      HomogeneousLocalization.val_mk'']
    simp only [smul_eq_mul, SetLike.coe_gnpow, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 s_mem]
    by_cases ineq : f^k = 0
    · have := IsLocalization.uniqueOfZeroMem (M := Submonoid.powers f) (S := Localization.Away f)
        ⟨k, ineq⟩
      exact Subsingleton.elim _ _
    · simp_rw [← pow_mul]; congr
      exact DirectSum.degree_eq_of_mem_mem 𝒜 F_mem (SetLike.pow_mem_graded k f_deg) ineq |>.symm

  · erw [ToSpec.mem_carrier_iff]
    obtain ⟨k, (k_spec : f^k = z.den)⟩ := z.den_mem
    rw [show z.val = (Localization.mk z.num ⟨f^k, ⟨k, rfl⟩⟩ : Away f) by
        · rw [z.eq_num_div_den]; congr; exact k_spec.symm,
      show (mk z.num ⟨f^k, ⟨k, rfl⟩⟩ : Away f) = mk z.num 1 * (mk 1 ⟨f^k, ⟨k, rfl⟩⟩ : Away f) by
        · rw [mk_mul, mul_one, one_mul]]
    refine Ideal.mul_mem_right _ _ <| Ideal.subset_span ⟨z.num, ?_, rfl⟩

    intro j
    by_cases ineq : z.deg = j
    · subst ineq
      simp only [CommRingCat.coe_of, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 z.num_mem_deg]
      convert x.IsPrime.pow_mem_iff_mem m hm |>.mpr hz using 1
      rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
        HomogeneousLocalization.pow_val, z.eq_num_div_den, Localization.mk_pow]
      by_cases ineq : f^k = 0
      · have := IsLocalization.uniqueOfZeroMem (M := Submonoid.powers f) (S := Localization.Away f)
          ⟨k, ineq⟩
        exact Subsingleton.elim _ _
      · dsimp; congr 2
        rw [← k_spec, ← pow_mul, show z.deg = k * m from
          degree_eq_of_mem_mem 𝒜 (k_spec ▸ z.den_mem_deg) (SetLike.pow_mem_graded k f_deg) ineq]
    · simp only [CommRingCat.coe_of, GradedAlgebra.proj_apply, zero_pow hm,
        DirectSum.decompose_of_mem_ne 𝒜 z.num_mem_deg ineq]
      convert x.asIdeal.zero_mem
      rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
        HomogeneousLocalization.zero_val, Localization.mk_zero]

end toSpecFromSpec

section fromSpecToSpec

lemma fromSpecToSpec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (x : Proj.T| pbo f) :
    FromSpec.toFun f_deg hm (toSpec x) = x := by
  classical
  refine Subtype.ext <| ProjectiveSpectrum.ext _ _ <| HomogeneousIdeal.ext <| Ideal.ext fun z ↦ ?_
  fconstructor <;> intro hz
  · rw [← DirectSum.sum_support_decompose 𝒜 z]
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    specialize hz i
    obtain ⟨c, N, acd, eq1⟩ := ToSpec.MemCarrier.clear_denominator x hz
    rw [HomogeneousLocalization.val_mk'', smul_mk, ← mk_one_eq_algebraMap, mk_eq_mk_iff,
      r_iff_exists, OneMemClass.coe_one, one_mul] at eq1
    obtain ⟨⟨_, ⟨k, rfl⟩⟩, eq1⟩ := eq1
    dsimp at eq1
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at eq1
    suffices mem : f^(k + i) * ∑ i in c.support.attach, acd (c i) _ * _ ∈ x.1.asHomogeneousIdeal
    · exact x.1.isPrime.mem_of_pow_mem _ <| x.1.isPrime.mem_or_mem (eq1.symm ▸ mem)
        |>.resolve_left fun r ↦ ProjectiveSpectrum.mem_basicOpen 𝒜 _ _
        |>.mp x.2 <| x.1.isPrime.mem_of_pow_mem _ r
    exact Ideal.mul_mem_left _ _ <| Ideal.sum_mem _ fun i _ ↦
      Ideal.mul_mem_left _ _ i.1.2.choose_spec.1

  · intro i
    erw [ToSpec.mem_carrier_iff, HomogeneousLocalization.val_mk'']
    dsimp only [GradedAlgebra.proj_apply]
    rw [show (mk (decompose 𝒜 z i ^ m) ⟨f^i, ⟨i, rfl⟩⟩: Away f) =
      (decompose 𝒜 z i ^ m : A) • (mk 1 ⟨f^i, ⟨i, rfl⟩⟩ : Away f) by
      · rw [smul_mk, smul_eq_mul, mul_one], Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ <|
      Ideal.subset_span ⟨_, ⟨Ideal.pow_mem_of_mem _ (x.1.asHomogeneousIdeal.2 i hz) _ hm, rfl⟩⟩

lemma toSpec_injective {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
    Function.Injective (toSpec (𝒜 := 𝒜) (f := f)) := by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpecToSpec, fromSpecToSpec] at this

lemma toSpec_surjective {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
    Function.Surjective (toSpec (𝒜 := 𝒜) (f := f)) :=
  Function.surjective_iff_hasRightInverse |>.mpr
    ⟨FromSpec.toFun f_deg hm, toSpecFromSpec 𝒜 hm f_deg⟩

lemma toSpec_bijective {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
    Function.Bijective (toSpec (𝒜 := 𝒜) (f := f)) :=
  ⟨toSpec_injective 𝒜 hm f_deg, toSpec_surjective 𝒜 hm f_deg⟩

end fromSpecToSpec

variable {𝒜} in
def fromSpec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) where
  toFun := FromSpec.toFun f_deg hm
  continuous_toFun :=
    (IsTopologicalBasis.continuous_iff <|
      IsTopologicalBasis.inducing (α := Proj.T| (pbo f)) (β := Proj) (f := Subtype.val)
        (hf := ⟨rfl⟩) (h := ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)).mpr fun s hs ↦ by
    erw [Set.mem_preimage] at hs
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hs
    dsimp only [Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier,
      LocallyRingedSpace.restrict_carrier]

    suffices o1 : IsOpen <| toSpec '' (Subtype.val ⁻¹' (pbo a).1 : Set (Proj.T| (pbo f)))
    · convert o1
      ext s x
      simp only [Set.mem_preimage, LocallyRingedSpace.restrict_carrier,
        Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier, Set.mem_image]
      constructor
      · intro h; exact ⟨_, h, toSpecFromSpec 𝒜 hm f_deg _⟩
      · rintro ⟨x, hx', rfl⟩; erw [fromSpecToSpec 𝒜 hm f_deg x]; exact hx'

    rw [calc
      Subtype.val ⁻¹' (pbo a).1
      = {x  : Proj.T| (pbo f) | x.1 ∈ (pbo f) ⊓ pbo a} := by
        ext ⟨x, (hx : x ∈ ProjectiveSpectrum.basicOpen _ _)⟩
        show _ ↔ _ ∧ _
        simp only [ProjectiveSpectrum.mem_basicOpen] at hx
        simp [hx]
    _ = {x | x.1 ∈ (pbo f) ⊓ (⨆ i : ℕ, pbo (decompose 𝒜 a i))} := by
        simp_rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a]
        rfl
    _ = {x | x.1 ∈ ⨆ i : ℕ, (pbo f) ⊓ pbo (decompose 𝒜 a i)} := by rw [inf_iSup_eq]
    _ = ⋃ i : ℕ, {x | x.1 ∈ (pbo f) ⊓ pbo (decompose 𝒜 a i)} := by
      ext x
      simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Opens.mem_mk, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
      rfl, Set.image_iUnion]
    refine isOpen_iUnion fun i ↦ ?_

    suffices : toSpec (f := f) '' {x | x.1 ∈ (pbo f) ⊓ pbo (decompose 𝒜 a i)} =
      (PrimeSpectrum.basicOpen (R := A⁰_ f) <|
        Quotient.mk'' ⟨m * i, ⟨decompose 𝒜 a i ^ m, SetLike.pow_mem_graded _ (Submodule.coe_mem _)⟩,
          ⟨f^i, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg⟩, ⟨i, rfl⟩⟩).1
    · erw [this]; exact (PrimeSpectrum.basicOpen _).2

    apply_fun _ using Set.preimage_injective.mpr (toSpec_surjective 𝒜 hm f_deg)
    erw [Set.preimage_image_eq _ (toSpec_injective 𝒜 hm f_deg), ToSpec.preimage_eq,
      ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]
    rfl

end ProjIsoSpecTopComponent

variable {𝒜} in
def projIsoSpecTopComponent {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f))  where
  hom := ProjIsoSpecTopComponent.toSpec
  inv := ProjIsoSpecTopComponent.fromSpec hm f_deg
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun x ↦
    ProjIsoSpecTopComponent.fromSpecToSpec 𝒜 hm f_deg x
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun x ↦
    ProjIsoSpecTopComponent.toSpecFromSpec 𝒜 hm f_deg x

namespace ProjIsoSpecSheafComponent

namespace FromSpec

local notation "φ" => (projIsoSpecTopComponent hm.out f_deg.out).hom
local notation "ψ" => (projIsoSpecTopComponent hm.out f_deg.out).inv

-- We use `φ` denote the homeomorphism `Proj | D(f) ≅ Spec A⁰_f`constructed above.
-- Let `V` be an open set in `Spec A⁰_f`, `s ∈ (Spec A⁰_f)(V)` be a section on `V` of prime spectrum
-- of `A⁰_f` and `y ∈ (φ⁻¹ V)` be a point in `Proj | D(f)`.
variable {𝒜}
variable {m : ℕ} {f : A} [hm : Fact <| 0 < m] [f_deg : Fact <| f ∈ 𝒜 m]
variable {V : (Opens <| Spec (A⁰_ f))ᵒᵖ}
variable (s : (Spec (A⁰_ f)).presheaf.obj V)
variable (y : ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
  Opens.map φ |>.op.obj V).unop)

private lemma _mem_pbo : (y : Proj.T) ∈ pbo f := by
  obtain ⟨⟨z, h1⟩, _, h2⟩ := y.2; rwa [← h2]

private lemma _mem_V : φ ⟨y, _mem_pbo y⟩ ∈ V.unop := by
  obtain ⟨y, ⟨_, h1, rfl⟩⟩ := y; exact h1

/--
Evaluating a section `s` of `(Spec A⁰_f)(V)` on `φ y` where `y ∈ φ⁻¹(V)`
-/
def eval : AlgebraicGeometry.StructureSheaf.Localizations (A⁰_ f) (φ ⟨y, _mem_pbo y⟩) :=
  s.1 ⟨φ ⟨y, _mem_pbo y⟩, _mem_V y⟩

abbrev eval_num : A⁰_ f := eval s y |>.exists_rep.choose.1

abbrev eval_den : A⁰_ f := eval s y |>.exists_rep.choose.2.1

lemma eval_den_not_mem : eval_den s y ∉ (φ ⟨y, _mem_pbo y⟩).asIdeal :=
  eval s y |>.exists_rep.choose.2.2

lemma eval_den_num_not_mem : (eval_den s y).num ∉ y.1.asHomogeneousIdeal := by
  intro r
  refine eval_den_not_mem s y ?_
  erw [ProjIsoSpecTopComponent.ToSpec.mem_carrier_iff, (eval_den s y).eq_num_div_den,
    show Localization.mk (eval_den s y).num _ = mk (eval_den s y).num 1 * Localization.mk 1 _ by
      rw [mk_mul, one_mul, mul_one]]
  exact Ideal.mul_mem_right _ _ <| Ideal.subset_span ⟨_, r, rfl⟩

lemma eval_num_den_not_mem : (eval_num s y).den ∉ y.1.asHomogeneousIdeal := by
  let k := (eval_num s y).den_mem.choose
  have hk : (eval_num s y).den = f^k := (eval_num s y).den_mem.choose_spec.symm
  obtain ⟨⟨a, (h1 : f ∉ _)⟩, _, (h2 : a = y.1)⟩ := y.2
  rw [hk, ← h2]
  intro r
  refine h1 <| a.isPrime.pow_mem_iff_mem _ ?_ |>.mp r
  by_contra! r'
  replace r' : k = 0
  · simpa using r'
  erw [r', pow_zero, ← Ideal.eq_top_iff_one] at r
  exact a.isPrime.ne_top r

lemma eval_eq_num_div_den :
    eval s y =
    Localization.mk (eval_num s y)
      ⟨eval_den s y,
        show eval_den s y ∈ (φ ⟨y, _⟩).asIdeal.primeCompl from eval_den_not_mem s y⟩ :=
  eval s y |>.exists_rep.choose_spec.symm

lemma eval_pt_congr (x) (h : (ψ x.1).1 = y) :
    s.1 x = Localization.mk (eval_num s y) ⟨eval_den s y, by
      convert eval_den_not_mem s y
      simp_rw [← h]
      erw [(projIsoSpecTopComponent _ _).inv_hom_id_apply]
      rfl⟩ := by
  have pt_eq : x = ⟨φ ⟨y, _mem_pbo _⟩, _mem_V y⟩
  · simp_rw [← h]
    ext
    dsimp
    erw [(projIsoSpecTopComponent _ _).inv_hom_id_apply]
  cases pt_eq
  exact eval_eq_num_div_den s y

abbrev α : HomogeneousLocalization.AtPrime 𝒜 y.1.asHomogeneousIdeal.toIdeal :=
  Quotient.mk''
  { deg := (eval_num s y).deg + (eval_den s y).deg
    num := Subtype.mk ((eval_num s y).num * (eval_den s y).den) <|
      SetLike.mul_mem_graded (eval_num s y).num_mem_deg (eval_den s y).den_mem_deg
    den := Subtype.mk ((eval_den s y).num * (eval_num s y).den) <| add_comm (eval_num s y).deg _ ▸
      SetLike.mul_mem_graded (eval_den s y).num_mem_deg (eval_num s y).den_mem_deg
    den_mem := fun r ↦ y.1.isPrime.mem_or_mem r |>.elim (eval_den_num_not_mem s y)
      (eval_num_den_not_mem s y) }

lemma val_α :
    (α s y).val =
    Localization.mk ((eval_num s y).num * (eval_den s y).den)
      ⟨(eval_den s y).num * (eval_num s y).den, by
        exact fun r ↦ y.1.isPrime.mem_or_mem r |>.elim
          (eval_den_num_not_mem s y) (eval_num_den_not_mem s y)⟩ :=
  HomogeneousLocalization.val_mk'' _

lemma α_one : α (m := m) (V := V) 1 = 1 := by
  ext1 y
  rw [Pi.one_apply, HomogeneousLocalization.ext_iff_val, val_α, HomogeneousLocalization.one_val,
    show (1 : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) = Localization.mk 1 1 from
    Localization.mk_self 1 |>.symm, mk_eq_mk_iff, r_iff_exists]
  have eq1 : _ = 1 := eval_eq_num_div_den 1 y |>.symm
  rw [show (1 : Localization.AtPrime (φ ⟨y, _⟩).asIdeal) = Localization.mk 1 1 from
    Localization.mk_self 1 |>.symm, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, (hC : C ∉ ProjIsoSpecTopComponent.ToSpec.carrier _)⟩, eq1⟩ := eq1
  simp only [one_mul, mul_one, Submonoid.coe_one] at eq1 ⊢
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, C.eq_num_div_den, (eval_num 1 y).eq_num_div_den,
    (eval_den 1 y).eq_num_div_den, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨n, rfl⟩⟩, eq1⟩ := eq1
  dsimp at eq1
  rw [show ∀ a b c d e: A, a * (b * c * (d * e)) = (a * b * d) * (e * c) by intros; ring,
    show ∀ a b c d e: A, a * (b * c * (d * e)) = (a * b * d) * (e * c) by intros; ring,
    show C.den = f^_ from C.den_mem.choose_spec.symm, ← pow_add] at eq1
  exact ⟨⟨_, ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _⟩, eq1⟩

lemma α_zero : α (m := m) (V := V) 0 = 0 := by
  ext1 y
  rw [Pi.zero_apply, HomogeneousLocalization.ext_iff_val, val_α, HomogeneousLocalization.zero_val,
    show (0 : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) = Localization.mk 0 1 from
    Localization.mk_zero 1 |>.symm, mk_eq_mk_iff, r_iff_exists]
  have eq1 : _ = 0 := eval_eq_num_div_den 0 y |>.symm
  rw [show (0 : Localization.AtPrime (φ ⟨y, _⟩).asIdeal) = Localization.mk 0 1 from
    Localization.mk_zero 1 |>.symm, mk_eq_mk_iff, r_iff_exists] at eq1
  simp only [one_mul, mul_one, Submonoid.coe_one, mul_zero] at eq1 ⊢
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1
  dsimp at eq1
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.zero_val,
    HomogeneousLocalization.mul_val, C.eq_num_div_den, (eval_num 0 y).eq_num_div_den, mk_mul,
    show (0 : Localization.Away f) = Localization.mk 0 1 from Localization.mk_zero 1 |>.symm,
    mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨n, rfl⟩⟩, eq1⟩ := eq1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk, mul_zero] at eq1
  rw [← mul_assoc] at eq1
  exact ⟨⟨f^n * C.num,
    ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _⟩,
    by erw [← mul_assoc, eq1, zero_mul]⟩

lemma α_add (x y : (Spec (A⁰_ f)).presheaf.obj V) : α (m := m) (V := V) (x + y) = α x + α y := by
  ext1 z
  rw [Pi.add_apply, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.add_val, val_α,
    val_α, val_α, add_mk, mk_eq_mk_iff, r_iff_exists]
  have eq1 := eval_eq_num_div_den (m := m) (V := V) (x + y) z
  rw [show eval (m := m) (V := V) (x + y) z = eval x z + eval y z from rfl,
    eval_eq_num_div_den, eval_eq_num_div_den, add_mk, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1
  dsimp only [Submonoid.coe_mul] at eq1 ⊢
  simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.add_val] at eq1
  simp only [HomogeneousLocalization.eq_num_div_den, mk_mul, add_mk, Submonoid.mk_mul_mk] at eq1
  rw [mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨n, rfl⟩⟩, eq1⟩ := eq1
  dsimp only at eq1
  refine ⟨⟨(f^n * C.den * (eval_den x z).den * (eval_den y z).den * C.num), ?_⟩, ?_⟩
  · rw [show C.den = f^_ from C.den_mem.choose_spec.symm,
      show (eval_den x z).den = f^_ from (eval_den x z).den_mem.choose_spec.symm,
      show (eval_den y z).den = f^_ from (eval_den y z).den_mem.choose_spec.symm,
      ← pow_add, ← pow_add, ← pow_add]
    exact ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _
  · dsimp only
    ring_nf at eq1 ⊢
    exact eq1.symm

lemma α_mul (x y : (Spec (A⁰_ f)).presheaf.obj V) : α (m := m) (V := V) (x * y) = α x * α y := by
  ext1 z
  rw [Pi.mul_apply, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val, val_α,
    val_α, val_α, mk_mul, mk_eq_mk_iff, r_iff_exists]
  have eq1 := eval_eq_num_div_den (m := m) (V := V) (x * y) z
  rw [show eval (m := m) (V := V) (x * y) z = eval x z * eval y z from rfl,
    eval_eq_num_div_den, eval_eq_num_div_den, mk_mul, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1
  dsimp only [Submonoid.coe_mul] at eq1 ⊢
  simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val] at eq1
  simp only [HomogeneousLocalization.eq_num_div_den, mk_mul, Submonoid.mk_mul_mk] at eq1
  rw [mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨n, rfl⟩⟩, eq1⟩ := eq1
  dsimp only at eq1
  refine ⟨⟨f^n * C.den * C.num, ?_⟩, ?_⟩
  · rw [show C.den = f^_ from C.den_mem.choose_spec.symm, ← pow_add]
    exact ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _
  · dsimp only
    ring_nf at eq1 ⊢
    exact eq1.symm

namespace isLocallyFraction

abbrev U (V' : Opens (Spec.T (A⁰_ f))) : Opens Proj.T where
  carrier := {x | ∃ x' ∈ φ ⁻¹' V'.1, x = x'.1}
  is_open' := by
    have ho1 := Homeomorph.isOpen_preimage (h := homeoOfIso (projIsoSpecTopComponent hm.out f_deg.out))
      |>.mpr V'.2
    rw [isOpen_induced_iff] at ho1
    obtain ⟨o, ho1, (eq : _ = φ ⁻¹' V'.1)⟩ := ho1
    simp_rw [← eq]
    convert IsOpen.inter ho1 (pbo f).2 using 1
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨z, h2⟩, h1, rfl⟩

def U.LE {V' : Opens (Spec.T (A⁰_ f))} (le : V' ⟶ V.unop) :
    (U (m := m) V') ⟶
    ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
      Opens.map φ |>.op.obj V).unop :=
  homOfLE <| by rintro _ ⟨x, hx, rfl⟩; simpa using leOfHom le hx

end isLocallyFraction

lemma α_isLocallyFraction : isLocallyFraction 𝒜 |>.pred (α (m := m) s) := by
  intro y
  obtain ⟨V', ⟨(mem1 : φ _ ∈ V'), le, a, b, is_local⟩⟩ := s.2 ⟨φ ⟨y.1, _mem_pbo _⟩, _mem_V _⟩

  obtain ⟨la, (hla : f^_ = _)⟩ := a.den_mem
  obtain ⟨lb, (hlb : f^_ = _)⟩ := b.den_mem

  refine ⟨isLocallyFraction.U (m := m) V', ⟨⟨⟨y.1, _mem_pbo _⟩, mem1, rfl⟩,
    isLocallyFraction.U.LE le, a.deg + b.deg, ⟨a.num * f^lb, SetLike.mul_mem_graded a.num_mem_deg
      (hlb ▸ b.den_mem_deg)⟩, ⟨b.num * f^la, add_comm a.deg _ ▸ SetLike.mul_mem_graded b.num_mem_deg
      (hla ▸ a.den_mem_deg)⟩, fun z ↦ ?_⟩⟩

  have z_mem_pbo : z.1 ∈ pbo f
  · obtain ⟨⟨_, h1⟩, _, h2⟩ := z.2; rw [h2]; exact h1
  have z_mem_V' : φ ⟨z.1, z_mem_pbo⟩ ∈ V'
  · obtain ⟨z, ⟨_, h1, rfl⟩⟩ := z; exact h1
  have z_mem_V : φ ⟨z.1, z_mem_pbo⟩ ∈ V.unop
  · exact leOfHom le z_mem_V'
  specialize is_local ⟨φ ⟨z.1, z_mem_pbo⟩, z_mem_V'⟩
  obtain ⟨b_not_mem, (eq1 : s.1 ⟨φ _, _⟩ * _ = Localization.mk a 1)⟩ := is_local
  change _ * Localization.mk b 1 =  _ at eq1
  replace eq1 : s.1 ⟨φ ⟨z.1, z_mem_pbo⟩, z_mem_V⟩ =
    (Localization.mk a ⟨b, b_not_mem⟩ : Localization.AtPrime _)
  · rw [show Localization.mk a _ = Localization.mk a 1 * Localization.mk 1 _ by
      rw [mk_mul, one_mul, mul_one], ← eq1, mul_assoc, mk_mul, one_mul, mul_one,
      show Localization.mk b ⟨b, _⟩ = 1 from Localization.mk_self ⟨b, _⟩, mul_one]

  fconstructor <;> dsimp only
  · rw [mul_comm]
    exact ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ b_not_mem _

  rw [HomogeneousLocalization.ext_iff_val, val_α, HomogeneousLocalization.val_mk'', mk_eq_mk_iff,
    r_iff_exists]
  rw [show s.1 ⟨φ ⟨z.1, z_mem_pbo⟩, z_mem_V⟩ =
    eval (m := m) (V := V) s ⟨z.1, (isLocallyFraction.U.LE le z) |>.2⟩ from rfl,
    eval_eq_num_div_den, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1
  dsimp only at eq1 ⊢
  simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val] at eq1
  simp only [HomogeneousLocalization.eq_num_div_den, mk_mul, Submonoid.mk_mul_mk] at eq1
  rw [mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩ := eq1
  dsimp only at eq1
  rw [← hla, ← hlb] at eq1
  refine ⟨⟨f^M * C.den * C.num, ?_⟩, ?_⟩
  · rw [show C.den = f^_ from C.den_mem.choose_spec.symm, ← pow_add]
    exact ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _
  · dsimp only
    ring_nf at eq1 ⊢
    exact eq1

@[simps]
def ringHom :
    (Spec (A⁰_ f)).presheaf.obj V ⟶ (φ _* (Proj| (pbo f)).presheaf).obj V where
  toFun s := ⟨α s, α_isLocallyFraction s⟩
  map_one' := Subtype.ext α_one
  map_mul' _ _ := Subtype.ext <| α_mul _ _
  map_zero' := Subtype.ext α_zero
  map_add' _ _ := Subtype.ext <| α_add _ _

end FromSpec

@[simps]
def fromSpec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (Spec (A⁰_ f)).presheaf ⟶
    (projIsoSpecTopComponent hm f_deg).hom  _* (Proj| (pbo f)).presheaf where
  app V := FromSpec.ringHom (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩) (V := V)
  naturality U V le := by aesop_cat

namespace ToSpec

variable {𝒜}
variable {m : ℕ} {f : A} [hm : Fact <| 0 < m] [f_deg : Fact <| f ∈ 𝒜 m]
variable {V : (Opens <| Spec (A⁰_ f))ᵒᵖ}

local notation "φ" => (projIsoSpecTopComponent hm.out f_deg.out).hom
local notation "ψ" => (projIsoSpecTopComponent hm.out f_deg.out).inv

variable (s : φ _* (Proj| (pbo f)).presheaf |>.obj V) (y : V.unop)

private lemma _mem_V :
    (ψ y.1).1 ∈ ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
      Opens.map φ |>.op.obj V).unop := by
  refine ⟨(ψ y.1), show _ ∈ φ ⁻¹' _ from ?_, rfl⟩
  rw [Set.mem_preimage, Iso.inv_hom_id_apply]
  exact y.2

variable (m) in
abbrev eval : HomogeneousLocalization.AtPrime 𝒜 (ψ y.1).1.asHomogeneousIdeal.toIdeal :=
  s.1 ⟨ψ y.1 |>.1, _mem_V _⟩

lemma eval_zero : eval m  0 y = 0 := by delta eval; norm_cast
lemma eval_one : eval m 1 y = 1 := by delta eval; norm_cast

lemma eval_add (s s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) :
    eval m (s + s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y =
    eval m s y + eval m s' y := by
  delta eval; norm_cast

lemma eval_mul (s s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) :
    eval m (s * s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y =
    eval m s y * eval m s' y := by
  delta eval; norm_cast

variable (m) in
def β : Localization.AtPrime y.1.asIdeal :=
  .mk
    (Quotient.mk''
      { deg := m * (eval m s y).deg
        num := ⟨(eval m s y).num * (eval m s y).den ^ m.pred, by
          rw [calc
              m * (eval m s y).deg = (m.pred + 1) * (eval m s y).deg := by
                congr; exact Nat.succ_pred_eq_of_pos hm.out |>.symm
            _ = m.pred * (eval m s y).deg + (eval m s y).deg := by rw [add_mul, one_mul]
            _ = (eval m s y).deg + m.pred * (eval m s y).deg := add_comm _ _]
          exact SetLike.mul_mem_graded (eval m s y).num_mem_deg <|
            SetLike.pow_mem_graded m.pred (eval m s y).den_mem_deg⟩
        den := ⟨f ^ (eval m s y).deg, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩
        den_mem := ⟨_, rfl⟩ })
    { val := Quotient.mk''
        { deg := m * (eval m s y).deg
          num := ⟨(eval m s y).den ^ m, SetLike.pow_mem_graded _ (eval m s y).den_mem_deg⟩
          den := ⟨f ^ (eval m s y).deg, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩
          den_mem := ⟨_, rfl⟩ }
      property := show _ ∉ _ by
        have mem : _ ∉ _ := (eval m s y).den_mem
        contrapose! mem
        intro i
        dsimp only [GradedAlgebra.proj_apply]
        by_cases ineq1 : (eval m s y).deg = i
        · subst ineq1
          simp_rw [DirectSum.decompose_of_mem_same 𝒜 (eval m s y).den_mem_deg]
          exact mem
        · simp_rw [DirectSum.decompose_of_mem_ne 𝒜 (eval m s y).den_mem_deg ineq1, zero_pow hm.out]
          convert Ideal.zero_mem _
          rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
            HomogeneousLocalization.zero_val]
          exact Localization.mk_zero _ }

lemma β_zero : β m 0 y = 0 := by
  rw [show (0 : Localization.AtPrime y.1.asIdeal) = Localization.mk 0 1 from
    Localization.mk_zero _ |>.symm, β, mk_eq_mk_iff, r_iff_exists]
  have eq1 := (eval m 0 y).eq_num_div_den.symm
  rw [eval_zero, HomogeneousLocalization.zero_val,
    show (0 : Localization.AtPrime (ψ y.1).1.asHomogeneousIdeal.toIdeal) = .mk 0 1 from
    mk_zero _ |>.symm, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨c, (hc : ¬ ∀ _, _)⟩, eq1⟩ := eq1
  rw [not_forall] at hc
  obtain ⟨j, hc⟩ := hc
  simp only [one_mul, mul_zero, Submonoid.coe_one] at eq1 ⊢
  replace eq1 : GradedAlgebra.proj 𝒜 (j + (eval m 0 y).deg) (c * (eval m 0 y).num) = 0
  · rw [eval_zero, eq1, map_zero]
  rw [GradedAlgebra.proj_apply,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) (eval m 0 y).num_mem_deg,
    eval_zero] at eq1
  refine ⟨⟨Quotient.mk'' ⟨m * j,
    ⟨decompose 𝒜 c j ^ m, SetLike.pow_mem_graded m (Submodule.coe_mem _)⟩,
    ⟨f^j, mul_comm m j ▸ SetLike.pow_mem_graded j f_deg.out⟩, ⟨j, rfl⟩⟩, hc⟩, ?_⟩
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.zero_val, mk_mul]
  simp only [eval_zero, ← mul_assoc]
  rw [show ∀ x : A, decompose 𝒜 c j ^ m * x = (decompose 𝒜 c j * x) * decompose 𝒜 c j ^ m.pred from
    fun x ↦ calc _ = decompose 𝒜 c j ^ (1 + m.pred) * x :=
                      by congr; rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm
                  _ = decompose 𝒜 c j * decompose 𝒜 c j ^ m.pred * x := by rw [pow_add, pow_one]
                  _ = decompose 𝒜 c j * x * decompose 𝒜 c j ^ m.pred := by ring,
    eq1, zero_mul, zero_mul]
  exact Localization.mk_zero _

lemma β_one : β m 1 y = 1 := by
  rw [show (1 : Localization.AtPrime y.1.asIdeal) = Localization.mk 1 1 from
    Localization.mk_self 1 |>.symm, β, mk_eq_mk_iff, r_iff_exists]
  have eq1 := (eval m 1 y).eq_num_div_den.symm
  rw [eval_one, HomogeneousLocalization.one_val,
    show (1 : Localization.AtPrime (ψ y.1).1.asHomogeneousIdeal.toIdeal) = .mk 1 1 from
    mk_self 1 |>.symm, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨c, (hc : ¬ ∀ _, _)⟩, eq1⟩ := eq1
  rw [not_forall] at hc
  obtain ⟨j, hc⟩ := hc
  simp only [one_mul, mul_one, Submonoid.coe_one] at eq1 ⊢
  replace eq1 : GradedAlgebra.proj 𝒜 (j + (eval m 1 y).deg) (c * (eval m 1 y).num) = _
  · rw [eval_one, eq1]
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) (eval m 1 y).num_mem_deg,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) (HomogeneousLocalization.den_mem_deg _),
    eval_one] at eq1
  refine ⟨⟨Quotient.mk'' ⟨m * j,
    ⟨decompose 𝒜 c j ^ m, SetLike.pow_mem_graded m (Submodule.coe_mem _)⟩,
    ⟨f^j, mul_comm m j ▸ SetLike.pow_mem_graded j f_deg.out⟩, ⟨j, rfl⟩⟩, hc⟩, ?_⟩
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'', mk_mul,
    HomogeneousLocalization.val_mk'', mk_mul]
  simp only [eval_one, ← mul_assoc]
  have eq0 (x : A) : x^m = x * x^m.pred
  · conv_lhs =>
    rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
      pow_add, pow_one]
  have reorder (x : A) : decompose 𝒜 c j ^ m * x = (decompose 𝒜 c j * x) * decompose 𝒜 c j ^ m.pred
  · calc _ = decompose 𝒜 c j * decompose 𝒜 c j ^ m.pred * x := by rw [eq0]
         _ = decompose 𝒜 c j * x * decompose 𝒜 c j ^ m.pred := by ring
  rw [reorder, eq1, ← reorder, mul_assoc, ← eq0]

set_option maxHeartbeats 500000 in
lemma β_add (s s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) :
    β m (s + s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y = β m s y + β m s' y := by
  delta β
  rw [add_mk, mk_eq_mk_iff, r_iff_exists]
  have eq1 := (eval m (s + s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y).eq_num_div_den
  rw [eval_add, HomogeneousLocalization.add_val, (eval m s y).eq_num_div_den,
    (eval m s' y).eq_num_div_den, add_mk, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨c, (hc : ¬ ∀ _, _)⟩, eq1⟩ := eq1
  rw [not_forall] at hc
  obtain ⟨j, hc⟩ := hc
  refine ⟨⟨_, hc⟩, ?_⟩
  simp only [one_mul, mul_one, Submonoid.coe_one, Submonoid.coe_mul] at eq1 ⊢
  replace eq1 := congr_arg
    (GradedAlgebra.proj 𝒜
      (j + ((eval m s y).deg + (eval m s' y).deg +
        (eval m (s + s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y).deg)))
    eq1
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply] at eq1
  rw [coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) ?_,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) ?_] at eq1
  pick_goal 2
  · exact SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (eval m s y).den_mem_deg (eval m s' y).den_mem_deg)
      (eval m (s + s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).num_mem_deg
  pick_goal 2
  · rw [add_comm _ (eval m (s + s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).deg]
    refine SetLike.mul_mem_graded
      (eval m (s + s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).den_mem_deg <|
      Submodule.add_mem _
        (SetLike.mul_mem_graded (eval m s y).den_mem_deg (eval m s' y).num_mem_deg) ?_
    rw [add_comm]
    exact (SetLike.mul_mem_graded (eval m s' y).den_mem_deg (eval m s y).num_mem_deg)

  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.add_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'']
  dsimp only
  rw [mk_mul, mk_mul, mk_mul, mk_mul, mk_mul, add_mk, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, one_mul, mul_one, Submonoid.coe_one, GradedAlgebra.proj_apply,
    eval_add]

  have eq0 (x : A) : x^m = x * x^m.pred
  · conv_lhs =>
    rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
      pow_add, pow_one]
  have reorder (x y a b : A) : decompose 𝒜 c j ^ m * (x ^ m * y ^ m * (a * b)) =
    (decompose 𝒜 c j * (x * y * a)) * (x^m.pred * y^m.pred * b * decompose 𝒜 c j ^ m.pred)
  · rw [eq0, eq0, eq0]; ring
  conv_lhs => rw [reorder, ← eq1]
  conv_rhs => rw [eq0, eq0, eq0, eq0]
  ring

set_option maxHeartbeats 500000 in
lemma β_mul (s s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) :
    β m (s * s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y = β m s y * β m s' y := by
  delta β
  rw [mk_mul, mk_eq_mk_iff, r_iff_exists]
  have eq1 := (eval m (s * s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y).eq_num_div_den
  rw [eval_mul, HomogeneousLocalization.mul_val, (eval m s y).eq_num_div_den,
    (eval m s' y).eq_num_div_den, mk_mul, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨c, (hc : ¬ ∀ _, _)⟩, eq1⟩ := eq1
  rw [not_forall] at hc
  obtain ⟨j, hc⟩ := hc
  refine ⟨⟨_, hc⟩, ?_⟩
  simp only [one_mul, mul_one, Submonoid.coe_one, Submonoid.coe_mul] at eq1 ⊢
  replace eq1 := congr_arg
    (GradedAlgebra.proj 𝒜
      (j + ((eval m s y).deg + (eval m s' y).deg +
        (eval m (s * s' : φ _* (Proj| (pbo f)).presheaf |>.obj V) y).deg)))
    eq1
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply] at eq1
  rw [coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) ?_,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := j) ?_] at eq1
  pick_goal 2
  · exact SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (eval m s y).den_mem_deg (eval m s' y).den_mem_deg)
      (eval m (s * s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).num_mem_deg
  pick_goal 2
  · rw [add_comm _ (eval m (s * s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).deg]
    refine SetLike.mul_mem_graded
      (eval m (s * s' :  φ _* (Proj| (pbo f)).presheaf |>.obj V) y).den_mem_deg
      (SetLike.mul_mem_graded (eval m s y).num_mem_deg (eval m s' y).num_mem_deg)

  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'']
  rw [mk_mul, mk_mul, mk_mul, mk_mul, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, one_mul, mul_one, Submonoid.coe_one, GradedAlgebra.proj_apply,
    eval_mul]

  have eq0 (x : A) : x^m = x * x^m.pred
  · conv_lhs =>
    rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
      pow_add, pow_one]
  have reorder (x y a b : A) : decompose 𝒜 c j ^ m * (x ^ m * y ^ m * (a * b)) =
    (decompose 𝒜 c j * (x * y * a)) * (x^m.pred * y^m.pred * b * decompose 𝒜 c j ^ m.pred)
  · rw [eq0, eq0, eq0]; ring
  conv_lhs => rw [reorder, ← eq1]
  conv_rhs => rw [eq0, eq0]
  ring

namespace isLocallyFraction

abbrev U (V' : Opens Proj.T) : Opens (Spec.T (A⁰_ f)) where
  carrier := φ '' {z | z.1 ∈ V'}
  is_open' := by
    erw [Homeomorph.isOpen_image (h := homeoOfIso (projIsoSpecTopComponent hm.out f_deg.out)),
      isOpen_induced_iff]
    exact ⟨_, V'.2, rfl⟩

def U.LE (V' : Opens Proj.T)
    (le : V' ⟶
          ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
            Opens.map φ |>.op.obj V).unop) : U (m := m) V' ⟶ V.unop :=
  homOfLE <| by rintro _ ⟨z, (hz : z.1 ∈ V'), rfl⟩; simpa using leOfHom le hz

lemma _mem_U_of_ψ_mem (V' : Opens Proj.T) (h : (ψ y.1).1 ∈ V') :
    y.1 ∈ U (m := m) V' :=
  ⟨ψ y.1, h, by rw [Iso.inv_hom_id_apply]⟩

lemma quotient_mk''_not_mem
    (b : A) (degree : ℕ) (b_mem : b ∈ 𝒜 degree) (z : Proj.T| (pbo f))
    (b_not_mem : b ∉ z.1.asHomogeneousIdeal) :
    Quotient.mk''
    { deg := m * degree
      num := ⟨b^m, SetLike.pow_mem_graded _ b_mem⟩
      den := ⟨f^degree, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩
      den_mem := ⟨_, rfl⟩ } ∉ (φ z).asIdeal := by
  classical
  intro rid
  erw [ProjIsoSpecTopComponent.ToSpec.mem_carrier_iff, HomogeneousLocalization.val_mk''] at rid
  obtain ⟨c, N, acd, eq1⟩ := ProjIsoSpecTopComponent.ToSpec.MemCarrier.clear_denominator' _ rid
  rw [smul_mk, ← mk_one_eq_algebraMap, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq1⟩ := eq1
  simp only [OneMemClass.coe_one, smul_eq_mul, one_mul, SetLike.mem_coe, ← mul_assoc,
    ← pow_add] at eq1
  suffices mem : f^(l + N) * b^m ∈ z.1.asHomogeneousIdeal
  · exact z.2 <| z.1.isPrime.mem_of_pow_mem _ <| z.1.isPrime.mem_or_mem mem
      |>.resolve_right fun r ↦ b_not_mem <| z.1.isPrime.mem_of_pow_mem _ r
  rw [eq1]
  exact Ideal.mul_mem_left _ _ <| Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ <|
    i.1.2.choose_spec.1

lemma section_eval_num_congr {x y} (h1 : x = y) : (s.1 y).num = (s.1 x).num := by
  induction h1; rfl

lemma section_eval_den_congr {x y} (h1 : x = y) : (s.1 y).den = (s.1 x).den := by
  induction h1; rfl

lemma section_eval_deg_congr {x y} (h1 : x = y) : (s.1 y).deg = (s.1 x).deg := by
  induction h1; rfl

end isLocallyFraction

set_option maxHeartbeats 1000000 in
lemma β_isLocallyFraction : StructureSheaf.isLocallyFraction (A⁰_ f) |>.pred (β m s)  := by
  classical
  intro y
  obtain ⟨V', mem, le, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, is_local⟩ := s.2 ⟨ψ y.1 |>.1, _mem_V _⟩
  refine ⟨isLocallyFraction.U (m := m) V', isLocallyFraction._mem_U_of_ψ_mem _ _ mem,
    isLocallyFraction.U.LE _ le,
    Quotient.mk''
    { deg := m * degree
      num := ⟨a * b^m.pred, ?_⟩
      den := ⟨f^degree, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩
      den_mem := ⟨_, rfl⟩ },
    Quotient.mk''
    { deg := m * degree
      num := ⟨b^m, SetLike.pow_mem_graded _ b_mem⟩
      den := ⟨f^degree, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩
      den_mem := ⟨_, rfl⟩ },
    ?_⟩
  · convert SetLike.mul_mem_graded a_mem (SetLike.pow_mem_graded m.pred b_mem) using 2
    conv_lhs => rw [show m = (m.pred + 1) from Nat.succ_pred_eq_of_pos hm.out |>.symm, add_mul,
      one_mul, add_comm, ← smul_eq_mul]

  rintro ⟨_, ⟨z, (z_mem : z.1 ∈ V'), rfl⟩⟩
  obtain ⟨(b_not_mem : b ∉ z.1.asHomogeneousIdeal), (eq1 : s.1 ⟨z.1, _⟩ = _)⟩ :=
    is_local ⟨z.1, z_mem⟩
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.eq_num_div_den, mk_eq_mk_iff, r_iff_exists] at eq1

  refine ⟨isLocallyFraction.quotient_mk''_not_mem b degree b_mem _ b_not_mem, ?_⟩
  obtain ⟨⟨C, (hC : ¬ C ∈ z.1.asHomogeneousIdeal)⟩, eq1⟩ := eq1
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (decompose 𝒜 C j : A) ∉ z.1.asHomogeneousIdeal
  · by_contra! rid
    apply hC
    rw [← sum_support_decompose 𝒜 C]
    exact Ideal.sum_mem _ fun i _ ↦ rid i
  erw [mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨⟨Quotient.mk'' ⟨m * j,
    ⟨decompose 𝒜 C j ^ m, SetLike.pow_mem_graded _ (Submodule.coe_mem _)⟩,
    ⟨f^j, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg.out⟩, ⟨_, rfl⟩⟩,
    isLocallyFraction.quotient_mk''_not_mem _ _ (Submodule.coe_mem _) _ hj⟩, ?_⟩
  simp only [OneMemClass.coe_one, Algebra.id.map_eq_id, RingHom.id_apply, one_mul,
    mul_one, Submonoid.coe_one] at eq1 ⊢
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'']
  rw [mk_mul, mk_mul, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Set.mem_setOf_eq, Submonoid.mk_mul_mk, one_mul]
  have φz_mem : φ z ∈ V.unop
  · simpa [Set.mem_preimage] using leOfHom le z_mem
  replace eq1 : C * (b * (eval m s ⟨φ z, φz_mem⟩).num) = C * ((eval m s ⟨φ z, φz_mem⟩).den * a)
  · convert eq1 using 3
    · apply isLocallyFraction.section_eval_num_congr
      ext; dsimp
      erw [(projIsoSpecTopComponent _ _).hom_inv_id_apply]
    · apply isLocallyFraction.section_eval_den_congr
      ext; dsimp
      erw [(projIsoSpecTopComponent _ _).hom_inv_id_apply]

  replace eq1 := congr_arg
    (GradedAlgebra.proj 𝒜
      (j + (degree + (eval m s ⟨φ z, φz_mem⟩).deg)))
    eq1
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply] at eq1
  rw [coe_decompose_mul_add_of_right_mem 𝒜 (a := C) (i := j) ?_,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := C) (i := j) ?_] at eq1
  pick_goal 2
  · rw [add_comm]
    exact SetLike.mul_mem_graded (HomogeneousLocalization.den_mem_deg _) a_mem
  pick_goal 2
  · exact SetLike.mul_mem_graded b_mem (HomogeneousLocalization.num_mem_deg _)

  have eq0 (x : A) : x^m = x * x^m.pred
  · conv_lhs =>
    rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
      pow_add, pow_one]
  have reorder (a b c : A) : decompose 𝒜 C j ^ m * (a * b * c^m) =
    (decompose 𝒜 C j * (c * a)) * (decompose 𝒜 C j ^ m.pred * b * c ^ m.pred)
  · rw [eq0, eq0]; ring
  conv_lhs => rw [reorder, eq1]
  conv_rhs => rw [eq0, eq0]
  ring

@[simps]
def ringHom : (φ _* (Proj| (pbo f)).presheaf).obj V ⟶ (Spec (A⁰_ f)).presheaf.obj V where
  toFun s := ⟨β m s, β_isLocallyFraction s⟩
  map_one' := Subtype.ext <| funext <| β_one
  map_mul' _ _ := Subtype.ext <| funext fun x ↦ β_mul x _ _
  map_zero' := Subtype.ext <| funext <| β_zero
  map_add' _ _ := Subtype.ext <| funext fun x ↦ β_add x _ _

end ToSpec

@[simps]
def toSpec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (projIsoSpecTopComponent hm f_deg).hom  _* (Proj| (pbo f)).presheaf ⟶
    (Spec (A⁰_ f)).presheaf where
  app V := ToSpec.ringHom (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩)
  naturality := by aesop_cat

namespace FromSpecToSpec

variable {𝒜}
variable {m : ℕ} {f : A} [hm : Fact <| 0 < m] [f_deg : Fact <| f ∈ 𝒜 m]
-- variable {V : (Opens <| Spec (A⁰_ f))ᵒᵖ}

local notation "φ" => (projIsoSpecTopComponent hm.out f_deg.out).hom
local notation "ψ" => (projIsoSpecTopComponent hm.out f_deg.out).inv

variable (V : (Opens (Spec.T (A⁰_ f)))ᵒᵖ)
variable (s : (φ _* (Proj| (pbo f)).presheaf).obj V)
variable (x : ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
  Opens.map φ |>.op.obj V).unop)

set_option maxHeartbeats 500000 in
lemma α_toSpec_ringHom : FromSpec.α (ToSpec.ringHom s) x = s.1 x := by
  rw [HomogeneousLocalization.ext_iff_val, FromSpec.val_α, HomogeneousLocalization.eq_num_div_den,
    mk_eq_mk_iff, r_iff_exists]
  have eq1 := FromSpec.eval_eq_num_div_den (ToSpec.ringHom s) x
  rw [FromSpec.eval, ToSpec.ringHom_apply_coe, ToSpec.β, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1
  dsimp at eq1 ⊢
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.eq_num_div_den,
    HomogeneousLocalization.eq_num_div_den, HomogeneousLocalization.eq_num_div_den,
    mk_mul, mk_mul, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨_, ⟨L, rfl⟩⟩, eq1⟩ := eq1
  simp only [Submonoid.mk_mul_mk] at eq1
  erw [ToSpec.eval,
    ToSpec.isLocallyFraction.section_eval_num_congr (hm := hm) (f_deg := f_deg) s
      (x := x)
      (y := ⟨ψ (φ ⟨x.1, FromSpec._mem_pbo _⟩) |>.1,
        by rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; exact x.2⟩)
      (h1 := by simp_rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; rfl),
    ToSpec.isLocallyFraction.section_eval_den_congr (hm := hm) (f_deg := f_deg) s
      (x := x)
      (y := ⟨ψ (φ ⟨x.1, FromSpec._mem_pbo _⟩) |>.1,
        by rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; exact x.2⟩)
      (h1 := by simp_rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; rfl),
    ToSpec.isLocallyFraction.section_eval_deg_congr (hm := hm) (f_deg := f_deg) s
      (x := x)
      (y := ⟨ψ (φ ⟨x.1, FromSpec._mem_pbo _⟩) |>.1,
        by rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; exact x.2⟩)
      (h1 := by simp_rw [(projIsoSpecTopComponent hm.out f_deg.out).hom_inv_id_apply]; rfl)] at eq1

  refine ⟨⟨(f ^ L * C.den * f ^ (s.1 x).deg) * C.num * (s.1 x).den ^ m.pred, ?_⟩, ?_⟩
  · intro rid
    refine x.1.isPrime.mem_or_mem rid |>.elim ?_ ?_
    · intro rid
      rw [← C.den_mem.choose_spec, ← pow_add, ← pow_add] at rid
      exact ProjIsoSpecTopComponent.ToSpec.pow_mul_num_not_mem_of_not_mem_carrier _ _ hC _ rid
    · intro rid
      exact (s.1 x).den_mem <| x.1.isPrime.mem_of_pow_mem _ rid
  · have eq0 (x : A) : x^m = x * x^m.pred
    · conv_lhs =>
      rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
        pow_add, pow_one]
    dsimp
    rw [show f ^ L * C.den * f ^ (s.1 x).deg * C.num * (s.1 x).den ^ Nat.pred m *
      ((s.1 x).den *
        ((FromSpec.eval_num (ToSpec.ringHom s) x).num *
        (FromSpec.eval_den (ToSpec.ringHom s) x).den)) =
      f^L * (C.den * ((FromSpec.eval_den (ToSpec.ringHom s) x).den * (f ^ (s.1 x).deg)) *
        (C.num * ((s.1 x).den ^ m * (FromSpec.eval_num (ToSpec.ringHom s) x).num))) by
      · rw [eq0]; ring, ← eq1]
    ring

end FromSpecToSpec

variable {𝒜} in
lemma fromSpecToSpec {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    toSpec 𝒜 hm f_deg ≫ fromSpec 𝒜 hm f_deg = 𝟙 _  := by
  ext V s
  refine Subtype.ext <| funext fun x ↦ ?_
  erw [comp_apply, fromSpec_app, id_apply, toSpec_app,
    FromSpec.ringHom_apply_coe (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩)]
  apply FromSpecToSpec.α_toSpec_ringHom (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩)

namespace ToSpecFromSpec

variable {𝒜}
variable {m : ℕ} {f : A} [hm : Fact <| 0 < m] [f_deg : Fact <| f ∈ 𝒜 m]
variable {V : (Opens ((Spec.T (A⁰_ f))))ᵒᵖ} (s : ((Spec (A⁰_ f)).presheaf.obj V)) (x : V.unop)

local notation "φ" => (projIsoSpecTopComponent hm.out f_deg.out).hom
local notation "ψ" => (projIsoSpecTopComponent hm.out f_deg.out).inv

lemma _ψ_apply_mem :
    (ψ x.1).1 ∈ ((@Opens.openEmbedding Proj.T (pbo f)).isOpenMap.functor.op.obj <|
      Opens.map φ |>.op.obj V).unop := by
  refine ⟨ψ x.1, ?_, rfl⟩
  erw [Set.mem_preimage, Set.mem_preimage,
    (projIsoSpecTopComponent hm.out f_deg.out).inv_hom_id_apply]
  exact x.2

set_option maxHeartbeats 1000000 in
lemma β_fromSpec_ringHom : ToSpec.β m (FromSpec.ringHom s) x = s.1 x := by
  have eq1 := FromSpec.α s ⟨(ψ x.1).1, _ψ_apply_mem _⟩ |>.eq_num_div_den
  rw [FromSpec.val_α, mk_eq_mk_iff, r_iff_exists] at eq1
  obtain ⟨⟨C, (hC : ¬ ∀ _, _)⟩, eq1⟩ := eq1
  rw [not_forall] at hC
  obtain ⟨j, hC⟩ := hC
  dsimp at eq1
  rw [show (s.1 x) = Localization.mk (FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩)
    ⟨FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩, by
      convert FromSpec.eval_den_not_mem s ⟨(ψ x.1).1, _ψ_apply_mem _⟩
      erw [(projIsoSpecTopComponent hm.out f_deg.out).inv_hom_id_apply]
      rfl⟩ from FromSpec.eval_pt_congr (f_deg := f_deg) (h := rfl) s, ToSpec.β, mk_eq_mk_iff,
    r_iff_exists]

  refine ⟨⟨_, hC⟩, ?_⟩
  dsimp
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.mul_val,
    HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.val_mk'', HomogeneousLocalization.val_mk'',
    HomogeneousLocalization.eq_num_div_den, HomogeneousLocalization.eq_num_div_den,
    mk_mul, mk_mul, mk_mul, mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.mk_mul_mk, one_mul]
  rw [show (FromSpec.α (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩) =
    ToSpec.eval m (FromSpec.ringHom s) x from rfl] at eq1
  replace eq1 := congr_arg
    (GradedAlgebra.proj 𝒜
      (j +
        ((FromSpec.α (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          ((FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          (FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg))))
    eq1

  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply] at eq1
  rw [coe_decompose_mul_add_of_right_mem 𝒜 (a := C) (i := j) ?_,
    coe_decompose_mul_add_of_right_mem 𝒜 (a := C) (i := j) ?_] at eq1
  pick_goal 2
  · rw [show (FromSpec.α (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          ((FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          (FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg) =
          (FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          (FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg +
          (FromSpec.α (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).deg by abel]
    exact SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (HomogeneousLocalization.num_mem_deg _)
        (HomogeneousLocalization.den_mem_deg _))
      (HomogeneousLocalization.num_mem_deg _)
  pick_goal 2
  · exact SetLike.mul_mem_graded
      (HomogeneousLocalization.den_mem_deg _)
      (SetLike.mul_mem_graded (HomogeneousLocalization.num_mem_deg _)
        (HomogeneousLocalization.den_mem_deg _))
  have eq0 (x : A) : x^m = x * x^m.pred
  · conv_lhs =>
    rw [show m = (1 + m.pred) by rw [add_comm]; exact Nat.succ_pred_eq_of_pos hm.out |>.symm,
      pow_add, pow_one]
  have reorder :
      f^j *
        ((FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).den *
          f^(ToSpec.eval m (FromSpec.ringHom s) x).deg) *
        (decompose 𝒜 C j ^ m *
          ((ToSpec.eval m (FromSpec.ringHom s) x).den ^ m *
            (FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).num)) =
      f^j * f^(ToSpec.eval m (FromSpec.ringHom s) x).deg *
        (decompose 𝒜 C j * ((ToSpec.eval m (FromSpec.ringHom s) x).den *
          ((FromSpec.eval_num (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).num *
            (FromSpec.eval_den (m := m) s ⟨(ψ x.1).1, _ψ_apply_mem _⟩).den))) *
        (decompose 𝒜 C j ^ m.pred * (ToSpec.eval m (FromSpec.ringHom s) x).den^m.pred)
  · rw [eq0, eq0]; ring
  erw [reorder, eq1, eq0]
  ring_nf
  rfl

end ToSpecFromSpec

variable {𝒜} in
lemma toSpecFromSpec {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    fromSpec 𝒜 hm f_deg ≫ toSpec 𝒜 hm f_deg = 𝟙 _  := by
  ext V s
  refine Subtype.ext <| funext fun x ↦ ?_
  erw [id_apply, comp_apply, fromSpec_app, toSpec_app,
    ToSpec.ringHom_apply_coe (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩)]
  apply ToSpecFromSpec.β_fromSpec_ringHom (hm := ⟨hm⟩) (f_deg := ⟨f_deg⟩)

end ProjIsoSpecSheafComponent

variable {𝒜} in
def projIsoSpecSheafComponent {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (projIsoSpecTopComponent hm f_deg).hom _* (Proj| (pbo f)).presheaf ≅
    (Spec (A⁰_ f)).presheaf where
  hom := ProjIsoSpecSheafComponent.toSpec 𝒜 hm f_deg
  inv := ProjIsoSpecSheafComponent.fromSpec 𝒜 hm f_deg
  hom_inv_id := ProjIsoSpecSheafComponent.fromSpecToSpec hm f_deg
  inv_hom_id := ProjIsoSpecSheafComponent.toSpecFromSpec hm f_deg

variable {𝒜} in
def projIsoSpec {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
    (Proj| (pbo f)) ≅ Spec (A⁰_ f) :=
  let e := PresheafedSpace.isoOfComponents (projIsoSpecTopComponent hm f_deg)
    (projIsoSpecSheafComponent hm f_deg)
  LocallyRingedSpace.isoOfSheafedSpaceIso ⟨e.1, e.2, e.3, e.4⟩

def ProjectiveSpectrum.exists_homogeneous_element_of_pos_degree_and_not_mem (x : Proj) :
    Σ' (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ f ∉ x.asHomogeneousIdeal := by
  classical
  have m := x.3
  erw [Set.not_subset] at m
  choose f h1 h2 using m
  rw [← sum_support_decompose 𝒜 f] at h2
  suffices m : ∃ (n : ℕ), 0 < n ∧ (decompose 𝒜 f n : A) ∉ x.asHomogeneousIdeal
  · choose n hn m using m; exact ⟨n, decompose 𝒜 f n, hn, Submodule.coe_mem _, m⟩
  by_contra! rid
  refine h2 <| Ideal.sum_mem _ fun i hi ↦ rid i ?_
  simp only [DFinsupp.mem_support_toFun, ne_eq] at hi
  erw [HomogeneousIdeal.mem_irrelevant_iff, GradedAlgebra.proj_apply] at h1
  by_contra! rid
  norm_num at rid
  subst rid
  exact hi <| Subtype.ext_iff_val.mpr h1

def Proj.toScheme : AlgebraicGeometry.Scheme where
  __ := Proj
  local_affine x := by
    obtain ⟨n, f, hn, f_deg, hf⟩ :=
      ProjectiveSpectrum.exists_homogeneous_element_of_pos_degree_and_not_mem 𝒜 x
    exact ⟨⟨pbo f, hf⟩, .of (A⁰_ f), ⟨projIsoSpec hn f_deg⟩⟩

end AlgebraicGeometry
