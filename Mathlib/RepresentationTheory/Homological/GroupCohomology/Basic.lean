/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(\bigoplus_{G^n} k[G], A)$, where
the righthand side is morphisms in `Rep k G`, and $k[G]$ is equipped with the left regular
representation. If we conjugate the $n$th differential in $\mathrm{Hom}(P, A)$ by this isomorphism,
where `P` is the bar resolution of `k` as a trivial `k`-linear `G`-representation, then the
resulting map agrees with the differential $d^n$ defined above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`, which provides API
specialized to `H⁰`, `H¹`, `H²`.

## Main definitions

* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
  $\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above complex and the
  complex $\mathrm{Hom}(P, A),$ where `P` is the bar resolution of `k` as a trivial resolution.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of
  `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
  (where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module (MonoidAlgebra k G) A` so that we do not run into
possible scalar action diamonds.

## TODO

* Upgrading `groupCohomologyIsoExt` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
  spectral sequences in general).
-/


noncomputable section

universe u

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory

namespace groupCohomology

variable [Monoid G]

/-- The complex `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `k`-linear
`G`-representation. -/
@[deprecated "We now use `(Rep.barComplex k G).linearYonedaObj k A instead"
  (since := "2025-06-08")]
abbrev linearYonedaObjResolution (A : Rep k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (Rep.standardComplex k G).linearYonedaObj k A

end groupCohomology

namespace inhomogeneousCochains

open Rep groupCohomology

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps! -isSimp]
def d [Monoid G] (A : Rep k G) (n : ℕ) :
    ModuleCat.of k ((Fin n → G) → A) ⟶ ModuleCat.of k ((Fin (n + 1) → G) → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
    map_add' f g := by
      ext
      simp [Finset.sum_add_distrib, add_add_add_comm]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, ← smul_assoc, mul_comm r] }

variable [Group G] [DecidableEq G] (A : Rep k G) (n : ℕ)

theorem d_eq :
    d A n =
      (freeLiftLEquiv (Fin n → G) A).toModuleIso.inv ≫
        ((barComplex k G).linearYonedaObj k A).d n (n + 1) ≫
          (freeLiftLEquiv (Fin (n + 1) → G) A).toModuleIso.hom := by
  ext
  simp [d_hom_apply, map_add, barComplex.d_single (k := k)]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep k G)

open inhomogeneousCochains Rep

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    classical
    simp only [d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, ((barComplex k G).linearYonedaObj k A).d_comp_d] }
    simp

variable {A n} in
@[ext]
theorem inhomogeneousCochains.ext {x y : (inhomogeneousCochains A).X n} (h : ∀ g, x g = y g) :
    x = y := funext h

theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = d A n := by
  simp

theorem inhomogeneousCochains.d_comp_d :
    d A n ≫ d A (n + 1) = 0 := by
  simpa [CochainComplex.of] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousCochainsIso [DecidableEq G] :
    inhomogeneousCochains A ≅ (barComplex k G).linearYonedaObj k A := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.freeLiftLEquiv (Fin i → G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of inhomogeneous cochains. -/
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n

variable {A} in
/-- Make an `n`-cocycle out of an element of the kernel of the `n`th differential. -/
abbrev cocyclesMk {n : ℕ} (f : (Fin n → G) → A) (h : inhomogeneousCochains.d A n f = 0) :
    cocycles A n :=
  (inhomogeneousCochains A).cyclesMk f (n + 1) (by simp) (by simp [h])

/-- The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G, A).` -/
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ (inhomogeneousCochains A).X n :=
  (inhomogeneousCochains A).iCycles n

/-- This is the map from `i`-cochains to `j`-cocycles induced by the differential in the complex of
inhomogeneous cochains. -/
abbrev toCocycles (i j : ℕ) : (inhomogeneousCochains A).X i ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

variable {A} in
theorem iCocycles_mk {n : ℕ} (f : (Fin n → G) → A) (h : inhomogeneousCochains.d A n f = 0) :
    iCocycles A n (cocyclesMk f h) = f := by
  exact (inhomogeneousCochains A).i_cyclesMk (i := n) f (n + 1) (by simp) (by simp [h])

end groupCohomology

open groupCohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
abbrev groupCohomology.π [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

@[deprecated (since := "2025-06-11")]
noncomputable alias groupCohomologyπ := groupCohomology.π

@[elab_as_elim]
theorem groupCohomology_induction_on [Group G] {A : Rep k G} {n : ℕ}
    {C : groupCohomology A n → Prop} (x : groupCohomology A n)
    (h : ∀ x : cocycles A n, C (π A n x)) : C x := by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupCohomologyIsoExt [Group G] [DecidableEq G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Hⁿ(Hom(P, A))`, where `P` is any projective resolution of `k` as a trivial `k`-linear
`G`-representation. -/
def groupCohomologyIso [Group G] [DecidableEq G] (A : Rep k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  groupCohomologyIsoExt A n ≪≫ P.isoExt _ _

lemma isZero_groupCohomology_succ_of_subsingleton
    [Group G] [Subsingleton G] (A : Rep k G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso <| groupCohomologyIsoExt _ _


#exit
variable [Group G] [DecidableEq G] (A : Rep k G) (n : ℕ)

#check ((linearYoneda k (Rep k G)).obj A).rightOp

/-
ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 (Rep.trivial k G k)) (Rep.barResolution k G)
  (Rep.standardResolution k G) (Rep.barComplex.isoStandardComplex k G).hom
  rfl : ∀ (F : Rep k G ⥤ ModuleCat k) [inst : F.Additive] (n : ℕ),
  (F.leftDerived n).map (𝟙 (Rep.trivial k G k)) ≫ ((Rep.standardResolution k G).isoLeftDerivedObj F n).hom =
    ((Rep.barResolution k G).isoLeftDerivedObj F n).hom ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
            HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map
        (Rep.barComplex.isoStandardComplex k G).hom

this says
Extⁿ(k, A) ⟶ Hⁿ(Hom(P, A)) is equal to

Extⁿ(k, A) ⟶ Hⁿ(Hom(P', A)) ⟶ Hⁿ(Hom(P, A)).

so that

ok so





-/
#check ProjectiveResolution.isoLeftDerivedObj_hom_naturality (C := Rep k G) (D := ModuleCat k)
  (𝟙 (Rep.trivial k G k)) (Rep.barResolution k G) (Rep.standardResolution k G)
  (Rep.barComplex.isoStandardComplex k G).hom rfl
