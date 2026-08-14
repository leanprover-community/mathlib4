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

In this file we show the following form of Zariski's lemma: for a scheme `X` locally of finite type
over a field `k`, the residue field at a closed point is a finite extension of `k`. This is used to
provide one of the simplified versions of Riemann-Roch in `RiemannRoch.lean`.

The two ingredients are both in mathlib: `Ideal.algebraMap_residueField_surjective` gives that
sections of an affine chart surject onto the residue field at a closed point of it, and
`finite_of_finite_type_of_isJacobsonRing` is the algebraic form of Zariski's lemma.
-/

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

open AlgebraicGeometry Scheme Order CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- For `x` in an affine open `U`, the residue field of `X` at `x` is the residue field of the
prime of `Γ(X, U)` corresponding to `x`.

This is the analogue for an affine open of `AlgebraicGeometry.Spec.residueFieldIso`, and belongs
next to it in `Mathlib/AlgebraicGeometry/ResidueField.lean`. -/
noncomputable def _root_.AlgebraicGeometry.IsAffineOpen.residueFieldIso {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    X.residueField x.1 ≅ CommRingCat.of (hU.primeIdealOf x).asIdeal.ResidueField :=
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  haveI := hU.isLocalization_stalk x
  (IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl (X.presheaf.stalk x.1)
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal)).toRingEquiv).toCommRingCatIso

/-- Under `IsAffineOpen.residueFieldIso`, evaluation of sections corresponds to the structure map
of `Ideal.ResidueField`. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.IsAffineOpen.evaluation_residueFieldIso_hom {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    X.evaluation U x.1 x.2 ≫ (hU.residueFieldIso x).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (hU.primeIdealOf x).asIdeal.ResidueField) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  haveI := hU.isLocalization_stalk x
  ext a
  show (hU.residueFieldIso x).hom.hom
    (IsLocalRing.residue _ (algebraMap Γ(X, U) (X.presheaf.stalk x.1) a)) = _
  rw [IsAffineOpen.residueFieldIso]
  show IsLocalRing.ResidueField.mapEquiv _ _ = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue _) ((IsLocalization.algEquiv _ _ _).commutes a)

/-- At a closed point `q` of an affine chart `U`, evaluation of sections is surjective onto the
residue field. The prime corresponding to `q` is maximal, so under
`IsAffineOpen.residueFieldIso` this is `Ideal.algebraMap_residueField_surjective`. -/
lemma evaluation_surjective_of_isClosed {U : X.Opens} (hU : IsAffineOpen U)
    {q : X} (hqU : q ∈ U) (hq : IsClosed ({q} : Set X)) :
    Function.Surjective (X.evaluation U q hqU).hom := by
  haveI : (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨q, hqU⟩ hq
  intro y
  obtain ⟨a, ha⟩ := Ideal.algebraMap_residueField_surjective
    (hU.primeIdealOf ⟨q, hqU⟩).asIdeal ((hU.residueFieldIso ⟨q, hqU⟩).hom.hom y)
  refine ⟨a, (hU.residueFieldIso ⟨q, hqU⟩).commRingCatIsoToRingEquiv.injective ?_⟩
  show (hU.residueFieldIso ⟨q, hqU⟩).hom.hom ((X.evaluation U q hqU).hom a)
    = (hU.residueFieldIso ⟨q, hqU⟩).hom.hom y
  rw [← ha]
  exact DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (hU.evaluation_residueFieldIso_hom ⟨q, hqU⟩)) a

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

/-- The residue field at a codimension-one point of a curve locally of finite type over `k`
is a finite extension of `k`: the point is closed, so this is Zariski's lemma. -/
lemma finite_residueField_of_coheight_eq_one [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] {q : X} (hq : coheight q = 1) :
    Module.Finite k (X.residueField q) :=
  finite_residueField_of_isClosed k (isClosed_singleton_of_coheight_eq_one hq)

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
