/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebraic_geometry.projective_spectrum.scheme
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.GradedAlgebra.Radical

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

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `to_Spec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `Proj_iso_Spec_Top_component.to_Spec.carrier`). This ideal is
    prime, the proof is in `Proj_iso_Spec_Top_component.to_Spec.to_fun`. The fact that this function
    is continuous is found in `Proj_iso_Spec_Top_component.to_Spec`
  - backward direction `from_Spec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal`;
    * This ideal is also homogeneous, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.prime`.
    Hence we have a well defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `Proj_iso_Spec_Top_component.from_Spec.to_fun`. But to prove the continuity of this function,
    we need to prove `from_Spec ∘ to_Spec` and `to_Spec ∘ from_Spec` are both identities (TBC).

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Proj_iso_Spec_Top_component.to_Spec`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Proj_iso_Spec_Top_component.to_Spec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

set_option linter.uppercaseLean3 false -- Porting note: Proj and Spec

namespace AlgebraicGeometry

open scoped DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {R A : Type _}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- `Proj` as a locally ringed space
set_option hygiene false -- Porting note: currently required to use in variable declarations
local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜

-- the underlying topological space of `Proj`
local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜

-- `Proj` restrict to some open set
macro "Proj| " U:term : term => `((Proj.toLocallyRingedSpace 𝒜).restrict (Opens.openEmbedding (X := Proj.T) ($U : Opens Proj.T)))
-- notation3 "Proj| " U => LocallyRingedSpace.restrict (Proj.toLocallyRingedSpace 𝒜)
--   (Opens.openEmbedding (X := Proj.T) (U : Opens Proj.T))

-- the underlying topological space of `Proj` restricted to some open set
local notation3 "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace
    <| (LocallyRingedSpace.restrict Proj (Opens.openEmbedding (X := Proj.T) (U : Opens Proj.T)))

-- basic open sets in `Proj`
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

-- basic open sets in `Spec`
local notation "sbo " f => PrimeSpectrum.basicOpen f

-- `Spec` as a locally ringed space
local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)

-- the underlying topological space of `Spec`
local notation3 "Spec.T " ring =>
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
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (Ideal.span <| algebraMap A (Away f) '' x.val.asHomogeneousIdeal)
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier

theorem mem_carrier_iff (z : A⁰_ f) :
    z ∈ carrier x ↔ z.val ∈ Ideal.span (algebraMap A (Away f) '' x.1.asHomogeneousIdeal) :=
  Iff.rfl
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mem_carrier_iff

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

theorem disjoint : Disjoint (x.1.asHomogeneousIdeal.toIdeal : Set A) (Submonoid.powers f : Set A) :=
  by
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
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, carrier_ne_top x, fun {x1 x2} hx12 => by
    classical
    rw [mem_carrier_iff] at hx12
    let J := span ((algebraMap A (Away f) : A → (Away f)) '' x.val.asHomogeneousIdeal)
    suffices h : ∀ x y : Localization.Away f, x * y ∈ J → x ∈ J ∨ y ∈ J
    · rw [HomogeneousLocalization.mul_val] at hx12 ; exact h x1.val x2.val hx12
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
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
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
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : Away f) = Localization.mk 1 (⟨f ^ k, ⟨_, rfl⟩⟩ : Submonoid.powers f) * mk a 1 by
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
    apply IsTopologicalBasis.continuous PrimeSpectrum.isTopologicalBasis_basic_opens
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
* is an ideal, as proved in `carrier.as_ideal`;
* is homogeneous, as proved in `carrier.as_homogeneous_ideal`;
* is prime, as proved in `carrier.as_ideal.prime`;
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
      · rw [Set.mem_image] at h ; rcases h with ⟨x, h, hx⟩
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
        if h1 : j ≤ m then
          -- Porting note : cannot use * notation since can't synth HMul A⁰_ f A⁰_ f ?
          Mul.mul (Quotient.mk''
              ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), ?_⟩,
                ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
            (Quotient.mk''
              ⟨m * i, ⟨proj 𝒜 i b ^ m, by mem_tac⟩,
                ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
        else
          Mul.mul (Quotient.mk''
              ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
                ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
            (Quotient.mk''
              ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) * proj 𝒜 i b ^ (m + m - j), ?_⟩,
                ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
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
    simp_rw [Subtype.coe_mk, proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    -- Porting note: having trouble with Mul instance
    let product : A⁰_ f :=
      Mul.mul (Quotient.mk'' ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, ?_⟩, ⟨n, rfl⟩⟩ : A⁰_ f)
          (Quotient.mk'' ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, ?_⟩, ⟨i - n, rfl⟩⟩ : A⁰_ f)
    split_ifs with h
    · convert_to product ∈ q.1
      · dsimp
        erw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.mul_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.val_mk'', Subtype.coe_mk]
        simp_rw [mul_pow, Subtype.coe_mk]; rw [Localization.mk_mul]
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


theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 := fun i a ha j =>
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
        simp_rw [proj_apply, decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (SetLike.GradedMonoid.toGradedMul.mul_mem hnx hny), mul_pow, pow_add]
        simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.mul_val, mk_mul]
        simp only [Submonoid.mk_mul_mk, mk_eq_monoidOf_mk']
      all_goals
        intro n hn; convert q.1.zero_mem using 1
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk'',
          HomogeneousLocalization.zero_val]; simp_rw [proj_apply, Subtype.coe_mk]
        convert mk_zero (S := Submonoid.powers f) _; rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm]
        · first | exact hnx | exact hny
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.prime AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime

-- variable (f_deg)

/-- The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp <| carrier.denom_not_mem f_deg hm q⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.toFun

end FromSpec

end ProjIsoSpecTopComponent

end AlgebraicGeometry

