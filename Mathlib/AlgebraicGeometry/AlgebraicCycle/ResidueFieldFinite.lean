/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldModule
import Mathlib.AlgebraicGeometry.AlgebraicCycle.KrullDimLE
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Residue fields at closed points are finite over the base field

For a scheme `X` locally of finite type over a field `k`, the residue field at a closed point
is a finite extension of `k`. This is the geometric form of **Zariski's lemma**: at a closed
point `q` lying in an affine chart `U`, the prime `hU.primeIdealOf q` is maximal, so the
evaluation map `Γ(X, U) → κ(q)` is surjective; hence `κ(q)` is a finite type `k`-algebra which
is a field, and Zariski's lemma (via Jacobson rings,
`finite_of_finite_type_of_isJacobsonRing`) makes it a finite extension. Together with the fact
that codimension-one points of a curve are closed, this discharges the residue-field
hypothesis of `riemann_roch_of_structureSheaf`.

Main statements:

* `evaluation_surjective_of_isClosed`: at a closed point of an affine chart, evaluation of
  sections is surjective onto the residue field;
* `finite_residueField_of_isClosed`: the residue field at a closed point of a scheme locally
  of finite type over `k` is module-finite over `k` (with respect to the `k`-structure of
  `Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldModule`);
* `isClosed_singleton_of_coheight_eq_one`: on a scheme of Krull dimension at most one,
  codimension-one points are closed.
-/

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

open AlgebraicGeometry Scheme Order CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- At a closed point `q` of an affine chart `U`, evaluation of sections is surjective onto
the residue field: the attached prime is maximal, so every element of the residue field of the
localization is the residue of an actual section (clear denominators using maximality). -/
lemma evaluation_surjective_of_isClosed {U : X.Opens} (hU : IsAffineOpen U)
    {q : X} (hqU : q ∈ U) (hq : IsClosed ({q} : Set X)) :
    Function.Surjective (X.evaluation U q hqU).hom := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q, hqU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨q, hqU⟩
  have hmax : (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨q, hqU⟩ hq
  intro ζ
  obtain ⟨z, rfl⟩ := X.residue_surjective q ζ
  obtain ⟨⟨a, s⟩, hz⟩ :=
    IsLocalization.mk'_surjective (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl z
  obtain ⟨t, m, hm, hst⟩ := hmax.exists_inv s.2
  refine ⟨a * t, ?_⟩
  -- Evaluation is the residue of the germ, and the germ is the localization map.
  rw [← X.germ_residue q hqU]
  have halg : ∀ b : Γ(X, U), (X.presheaf.germ U q hqU).hom b =
      algebraMap Γ(X, U) (X.presheaf.stalk q) b := fun _ => rfl
  -- `z * s = a` in the stalk.
  have h1 : z * algebraMap Γ(X, U) (X.presheaf.stalk q) (s : Γ(X, U)) =
      algebraMap Γ(X, U) (X.presheaf.stalk q) a := by
    rw [← hz]
    exact IsLocalization.mk'_spec _ a s
  -- The correction term `m ∈ 𝔪` dies in the residue field.
  have hres_m : (X.residue q).hom (algebraMap Γ(X, U) (X.presheaf.stalk q) m) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ m).mpr hm)
  have hts : t * (s : Γ(X, U)) = 1 - m := eq_sub_of_add_eq hst
  have hcalc : (X.residue q).hom ((X.presheaf.germ U q hqU).hom (a * t)) =
      (X.residue q).hom z *
        (X.residue q).hom (algebraMap Γ(X, U) (X.presheaf.stalk q) (t * (s : Γ(X, U)))) := by
    rw [halg]
    simp only [map_mul]
    rw [← h1]
    simp only [map_mul]
    ring
  rw [ConcreteCategory.comp_apply, hcalc, hts, map_sub, map_one, map_sub, hres_m, sub_zero,
    map_one, mul_one]

/-- The structure ring map `k → Γ(X, U)` into an affine chart of a scheme locally of finite
type over `k` is of finite type. -/
lemma structureRingHom_finiteType [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {U : X.Opens} (hU : IsAffineOpen U) :
    (structureRingHom (X := X) (R := CommRingCat.of k) U).FiniteType := by
  have h1 : RingHom.FiniteType
      (((X ↘ Spec (CommRingCat.of k)).appLE ⊤ U (by simp)).hom) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType)
      (f := X ↘ Spec (CommRingCat.of k)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h2 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv).surjective
  have h3 : structureRingHom (X := X) (R := CommRingCat.of k) U =
      (((X ↘ Spec (CommRingCat.of k)).appLE ⊤ U (by simp)).hom).comp
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := rfl
  rw [h3]
  exact h1.comp (RingHom.FiniteType.of_surjective _ h2)

/-- **Zariski's lemma, geometric form.** The residue field at a closed point of a scheme
locally of finite type over a field `k` is a finite extension of `k` (with respect to the
`k`-module structure through the structure morphism). -/
lemma finite_residueField_of_isClosed [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {q : X} (hq : IsClosed ({q} : Set X)) :
    Module.Finite k ↑(X.residueField q) := by
  obtain ⟨U, hU, hqU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (Opens.mem_top q)
  -- The ring map underlying the `k`-module structure on `κ(q)`, factored through the chart.
  set c : k →+* ↑(X.residueField q) :=
    (X.Γevaluation q).hom.comp (globalSec (X := X) (R := CommRingCat.of k)) with hc
  have hfactor : X.evaluation ⊤ q trivial =
      X.presheaf.map U.leTop.op ≫ X.evaluation U q hqU := by
    rw [← X.germ_residue, ← X.germ_residue, ← Category.assoc, TopCat.Presheaf.germ_res]
  have hcomp : c = ((X.evaluation U q hqU).hom).comp
      (structureRingHom (X := X) (R := CommRingCat.of k) U) := by
    rw [hc, structureRingHom, ← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← hfactor]
  -- `κ(q)` is a finite type `k`-algebra: quotient of the finite type algebra `Γ(X, U)`.
  letI : Algebra k ↑(X.residueField q) := c.toAlgebra
  haveI hft : Algebra.FiniteType k ↑(X.residueField q) := by
    have : c.FiniteType := by
      rw [hcomp]
      exact RingHom.FiniteType.of_surjective _
        (evaluation_surjective_of_isClosed hU hqU hq) |>.comp
        (structureRingHom_finiteType k hU)
    exact this
  -- Zariski's lemma: a finite type algebra over a Jacobson ring which is a field is finite.
  exact finite_of_finite_type_of_isJacobsonRing k ↑(X.residueField q)

/-- On a scheme of Krull dimension at most one, codimension-one points are closed. -/
lemma isClosed_singleton_of_coheight_eq_one [Order.KrullDimLE 1 X]
    {q : X} (hq : coheight q = 1) : IsClosed ({q} : Set X) := by
  have hmin : IsMin q :=
    Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hq.ge)
  refine isClosed_of_closure_subset fun z hz => ?_
  have hspec : q ⤳ z := specializes_iff_mem_closure.mpr hz
  have hle : z ≤ q := Scheme.le_iff_specializes.mpr hspec
  exact ((Scheme.le_iff_specializes.mp (hmin hle)).antisymm hspec).eq

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
