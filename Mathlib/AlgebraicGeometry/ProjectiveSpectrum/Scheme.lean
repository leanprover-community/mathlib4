/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.Spec
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
    `ProjIsoSpecTopComponent.FromSpec.toFun`. But to prove the continuity of this function, we need
    to prove `fromSpec ∘ toSpec` and `toSpec ∘ fromSpec` are both identities; these are achieved in
    `ProjIsoSpecTopComponent.fromSpec_toSpec` and `ProjIsoSpecTopComponent.toSpec_fromSpec`.

## Main Definitions and Statements

For a homogeneous element `f` of degree `m`
* `ProjIsoSpecTopComponent.toSpec`: the continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
  defined by sending `x : Proj| (pbo f)` to `A⁰_f ∩ span {g / 1 | g ∈ x}`. We also denote this map
  as `ψ`.
* `ProjIsoSpecTopComponent.ToSpec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

If we further assume `m` is positive
* `ProjIsoSpecTopComponent.fromSpec`: the continuous map between `Spec.T A⁰_f` and `Proj.T| pbo f`
  defined by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}` where `aᵢ` is the `i`-th coordinate of `a`.
  We also denote this map as `φ`
* `projIsoSpecTopComponent`: the homeomorphism `Proj.T| pbo f ≅ Spec.T A⁰_f` obtained by `φ` and
  `ψ`.
## Reference
* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

set_option linter.uppercaseLean3 false

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

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
/-- `Proj` as a locally ringed space -/
local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜

/-- The underlying topological space of `Proj` -/
local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜

/-- `Proj` restrict to some open set -/
macro "Proj| " U:term : term =>
  `((Proj.toLocallyRingedSpace 𝒜).restrict (Opens.openEmbedding (X := Proj.T) ($U : Opens Proj.T)))

/-- the underlying topological space of `Proj` restricted to some open set -/
local notation "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace
    <| (LocallyRingedSpace.restrict Proj (Opens.openEmbedding (X := Proj.T) (U : Opens Proj.T)))

/-- basic open sets in `Proj` -/
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

/-- basic open sets in `Spec` -/
local notation "sbo " f => PrimeSpectrum.basicOpen f

/-- `Spec` as a locally ringed space -/
local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)

/-- the underlying topological space of `Spec` -/
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
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier

@[simp]
theorem mk_mem_carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ carrier x ↔ z.num.1 ∈ x.1.asHomogeneousIdeal := by
  rw [carrier, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one,
    mul_comm, Ideal.unit_mul_mem_iff_mem, ← Ideal.mem_comap,
    IsLocalization.comap_map_of_isPrime_disjoint (.powers f)]
  · rfl
  · infer_instance
  · exact (disjoint_powers_iff_not_mem _ (Ideal.IsPrime.isRadical inferInstance)).mpr x.2
  · exact isUnit_of_invertible _

theorem isPrime_carrier : Ideal.IsPrime (carrier x) := by
  refine Ideal.IsPrime.comap _ (hK := ?_)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) _ _ inferInstance
    ((disjoint_powers_iff_not_mem _ (Ideal.IsPrime.isRadical inferInstance)).mpr x.2)

variable (f)

/-- The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `TopComponent.forward`.
-/
@[simps (config := .lemmasOnly)]
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, isPrime_carrier x⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.toFun

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
theorem preimage_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toFun f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  Set.ext fun y ↦ (mk_mem_carrier y z).not
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec.preimage_eq AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen

end ToSpec

section

/-- The continuous function from the basic open set `D(f)` in `Proj`
to the corresponding basic open set in `Spec A⁰_f`. -/
@[simps! (config := .lemmasOnly) apply_asIdeal]
def toSpec (f : A) : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f where
  toFun := ToSpec.toFun f
  continuous_toFun := by
    rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
    rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.surjective_Quotient_mk'' x
    rw [ToSpec.preimage_basicOpen]
    exact (pbo x.num).2.preimage continuous_subtype_val
#align algebraic_geometry.Proj_iso_Spec_Top_component.to_Spec AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec

variable {𝒜} in
lemma toSpec_preimage_basicOpen {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toSpec 𝒜 f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  ToSpec.preimage_basicOpen f z

end

namespace FromSpec

open GradedAlgebra SetLike

open Finset hiding mk_zero

-- Porting note: _root_ doesn't work here
open HomogeneousLocalization

variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

open Lean Meta Elab Tactic

macro "mem_tac_aux" : tactic =>
  `(tactic| first | exact pow_mem_graded _ (Submodule.coe_mem _) | exact natCast_mem_graded _ _ |
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
  {a | ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1}
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier

theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔ ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
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
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x ∈ q.asIdeal at h
        convert h
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
        dsimp only [Subtype.coe_mk]; rw [← hx]; rfl)
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.mem_carrier_iff' AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff'

theorem mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 n) :
    a ∈ carrier f_deg q ↔
      (HomogeneousLocalization.mk ⟨m * n, ⟨a ^ m, pow_mem_graded m hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal
  · refine ⟨fun h ↦ h n, fun h i ↦ if hi : i = n then hi ▸ h else ?_⟩
    convert zero_mem q.asIdeal
    apply HomogeneousLocalization.val_injective
    simp only [proj_apply, decompose_of_mem_ne _ hn (Ne.symm hi), zero_pow hm.ne',
      HomogeneousLocalization.val_mk, Localization.mk_zero, HomogeneousLocalization.val_zero]
  · simp only [proj_apply, decompose_of_mem_same _ hn]

theorem mem_carrier_iff_of_mem_mul (hm : 0 < m)
    (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 (n * m)) :
    a ∈ carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, ⟨a, mul_comm n m ▸ hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn, iff_iff_eq, eq_comm,
    ← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization.mk_pow, pow_mul]
  rfl

theorem num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    z.num.1 ∈ carrier f_deg q ↔ HomogeneousLocalization.mk z ∈ q.asIdeal := by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n ≠ 0 := fun e ↦ by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_ using 2
  · apply HomogeneousLocalization.val_injective; simp only [hn, HomogeneousLocalization.val_mk]
  · have := degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded n f_deg) (hn.symm ▸ z.den.2) this
    rw [← smul_eq_mul, this]; exact z.num.2

theorem carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a ∈ carrier f_deg q)
    (hb : b ∈ carrier f_deg q) : a + b ∈ carrier f_deg q := by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (.mk ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : ℕ → A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 : A⁰_ f)
      else
        -- Porting note: inlining `l`, `r` causes a "can't synth HMul A⁰_ f A⁰_ f ?" error
        if h1 : j ≤ m then
          letI l : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i b ^ m, by mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          l * r
        else
          letI l : A⁰_ f := HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩
          letI r : A⁰_ f := HomogeneousLocalization.mk
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
  convert_to ∑ i ∈ range (m + m + 1), g i ∈ q.1; swap
  · refine q.1.sum_mem fun j _ => nsmul_mem ?_ _; split_ifs
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
  change _ = (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) _
  dsimp only [Subtype.coe_mk]; rw [map_sum, mk_sum]
  apply Finset.sum_congr rfl fun j hj => _
  intro j hj
  change _ = HomogeneousLocalization.val _
  rw [HomogeneousLocalization.val_smul]
  split_ifs with h2 h1
  · exact ((Finset.mem_range.1 hj).not_le h2).elim
  all_goals simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero,
    HomogeneousLocalization.val_mk, Subtype.coe_mk, Localization.mk_mul, ← smul_mk]; congr 2
  · dsimp; rw [mul_assoc, ← pow_add, add_comm (m - j), Nat.add_sub_assoc h1]
  · simp_rw [pow_add]; rfl
  · dsimp; rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_not_le h1)]
  · simp_rw [pow_add]; rfl
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.add_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.add_mem

variable (hm : 0 < m) (q : Spec.T A⁰_ f)

theorem carrier.zero_mem : (0 : A) ∈ carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1 using 1
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  convert Localization.mk_zero (S := Submonoid.powers f) _ using 1
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.zero_mem AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem

theorem carrier.smul_mem (c x : A) (hx : x ∈ carrier f_deg q) : c • x ∈ carrier f_deg q := by
  revert c
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    -- Porting note: having trouble with Mul instance
    let product : A⁰_ f :=
      Mul.mul (HomogeneousLocalization.mk ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, ?_⟩, ⟨n, rfl⟩⟩)
        (HomogeneousLocalization.mk ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, ?_⟩, ⟨i - n, rfl⟩⟩)
    · split_ifs with h
      · convert_to product ∈ q.1
        · dsimp [product]
          erw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mk]
          · simp_rw [mul_pow]; rw [Localization.mk_mul]
            · congr; erw [← pow_add, Nat.add_sub_of_le h]
            · rw [(_ : m • n = _)]
              · mem_tac
              · simp only [smul_eq_mul, mul_comm]
            · rw [(_ : m • (i - n) = _)]
              · mem_tac
              · simp only [smul_eq_mul, mul_comm]
        · apply Ideal.mul_mem_left (α := A⁰_ f) _ _ (hx _)
      · simpa only [map_zero, zero_pow hm.ne'] using zero_mem f_deg hm q i
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
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (Submodule.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j
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
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_one,
          HomogeneousLocalization.val_mk]
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
        simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_mul, Localization.mk_mul]
        simp only [Submonoid.mk_mul_mk, mk_eq_monoidOf_mk']
      all_goals
        intro n hn; convert q.1.zero_mem using 1
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_zero]; simp_rw [proj_apply]
        convert mk_zero (S := Submonoid.powers f) _
        rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm.ne']
        · first | exact hnx | exact hny
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.prime AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime

/-- The function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`. -/
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp <| carrier.denom_not_mem f_deg hm q⟩
#align algebraic_geometry.Proj_iso_Spec_Top_component.from_Spec.to_fun AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.toFun

end FromSpec

section toSpecFromSpec

lemma toSpec_fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f)) :
    toSpec 𝒜 f (FromSpec.toFun f_deg hm x) = x := by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z

@[deprecated (since := "2024-03-02")] alias toSpecFromSpec := toSpec_fromSpec

end toSpecFromSpec

section fromSpecToSpec

lemma fromSpec_toSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f) :
    FromSpec.toFun f_deg hm (toSpec 𝒜 f x) = x := by
  refine Subtype.ext <| ProjectiveSpectrum.ext _ _ <| HomogeneousIdeal.ext' ?_
  intros i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)

lemma toSpec_injective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Injective (toSpec 𝒜 f) := by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this

lemma toSpec_surjective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Surjective (toSpec 𝒜 f) :=
  Function.surjective_iff_hasRightInverse |>.mpr
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩

lemma toSpec_bijective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m):
    Function.Bijective (toSpec (𝒜 := 𝒜) (f := f)) :=
  ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩

end fromSpecToSpec

namespace toSpec

variable {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

variable {𝒜} in
lemma image_basicOpen_eq_basicOpen (a : A) (i : ℕ) :
    toSpec 𝒜 f '' (Subtype.val ⁻¹' (pbo (decompose 𝒜 a i) : Set (ProjectiveSpectrum 𝒜))) =
    (PrimeSpectrum.basicOpen (R := A⁰_ f) <|
      HomogeneousLocalization.mk
        ⟨m * i, ⟨decompose 𝒜 a i ^ m, SetLike.pow_mem_graded _ (Submodule.coe_mem _)⟩,
          ⟨f^i, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg⟩, ⟨i, rfl⟩⟩).1 :=
  Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm) <|
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe, toSpec_preimage_basicOpen, ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]

end toSpec

variable {𝒜} in
/-- The continuous function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}` where
`m` is the degree of `f` -/
def fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) where
  toFun := FromSpec.toFun f_deg hm
  continuous_toFun := by
    rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜) (pbo f).1
      |>.continuous_iff]
    rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
    have h₁ : Subtype.val (p := (pbo f).1) ⁻¹' (pbo a) =
        ⋃ i : ℕ, Subtype.val (p := (pbo f).1) ⁻¹' (pbo (decompose 𝒜 a i)) := by
      simp [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a]
    let e : _ ≃ _ :=
      ⟨FromSpec.toFun f_deg hm, ToSpec.toFun f, toSpec_fromSpec _ _ _, fromSpec_toSpec _ _ _⟩
    change IsOpen <| e ⁻¹' _
    rw [Set.preimage_equiv_eq_image_symm, h₁, Set.image_iUnion]
    exact isOpen_iUnion fun i ↦ toSpec.image_basicOpen_eq_basicOpen f_deg hm a i ▸
      PrimeSpectrum.isOpen_basicOpen

end ProjIsoSpecTopComponent

variable {𝒜} in
/--
The homeomorphism `Proj|D(f) ≅ Spec A⁰_f` defined by
- `φ : Proj|D(f) ⟶ Spec A⁰_f` by sending `x` to `A⁰_f ∩ span {g / 1 | g ∈ x}`
- `ψ : Spec A⁰_f ⟶ Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def projIsoSpecTopComponent {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f))  where
  hom := ProjIsoSpecTopComponent.toSpec 𝒜 f
  inv := ProjIsoSpecTopComponent.fromSpec f_deg hm
  hom_inv_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.fromSpec_toSpec 𝒜 f_deg hm)
  inv_hom_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.toSpec_fromSpec 𝒜 f_deg hm)

end AlgebraicGeometry
