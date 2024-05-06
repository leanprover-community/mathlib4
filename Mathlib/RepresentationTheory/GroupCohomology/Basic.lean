/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.GroupCohomology.Resolution
import Mathlib.Tactic.CategoryTheory.Slice
#align_import representation_theory.group_cohomology.basic from "leanprover-community/mathlib"@"cc5dd6244981976cc9da7afc4eee5682b037a013"

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism $\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(k[G^{n + 1}], A)$, where
the righthand side is morphisms in `Rep k G`, and the representation on $k[G^{n + 1}]$
is induced by the diagonal action of `G`. If we conjugate the $n$th differential in
$\mathrm{Hom}(P, A)$ by this isomorphism, where `P` is the standard resolution of `k` as a trivial
`k`-linear `G`-representation, then the resulting map agrees with the differential $d^n$ defined
above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`RepresentationTheory.GroupCohomology.LowDegree`, which gives simpler expressions for `H⁰, H¹, H²`
than the definition `groupCohomology` in this file.

## Main definitions

* `groupCohomology.linearYonedaObjResolution A`: a complex whose objects are the representation
morphisms $\mathrm{Hom}(k[G^{n + 1}], A)$ and whose cohomology is the group cohomology
$\mathrm{H}^n(G, A)$.
* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
$\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above two complexes.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of the
second complex, `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
(where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module (MonoidAlgebra k G) A` so that we do not run into
possible scalar action diamonds.

## TODO

* API for cohomology in low degree: $\mathrm{H}^0, \mathrm{H}^1$ and $\mathrm{H}^2.$ For example,
the inflation-restriction exact sequence.
* The long exact sequence in cohomology attached to a short exact sequence of representations.
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

variable [Group G]
/-
@[simps]
def ChainComplex.linearYoneda {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
  [Linear R C] [EnoughProjectives C]
  {α : Type*} [AddRightCancelSemigroup α] [One α]
  {X Y : ChainComplex C α} (A : Type*) [Ring A] [Linear A C] (Z : C)
#check Functor.mapHomologicalComplex
-/

@[simps!] def ChainComplex.linearYoneda (R : Type*) [Ring R] {C : Type*} [Category C] [Abelian C]
  [Linear R C] [EnoughProjectives C]
  {α : Type*} [AddRightCancelSemigroup α] [One α] (Z : C) :
  ChainComplex C α ⥤ (CochainComplex (ModuleCat R) α)ᵒᵖ :=
  ((CategoryTheory.linearYoneda R C).obj Z).rightOp.mapHomologicalComplex _ ⋙
    HomologicalComplex.opInverse (ModuleCat R) (ComplexShape.up α)

def ChainComplex.linearYoneda' (R : Type*) [Ring R] {C : Type*} [Category C] [Abelian C]
  [Linear R C] [EnoughProjectives C]
  {α : Type*} [AddRightCancelSemigroup α] [One α] (Z : C) :
  (ChainComplex C α)ᵒᵖ ⥤ CochainComplex (ModuleCat R) α :=
  HomologicalComplex.opFunctor C (ComplexShape.down α) ⋙
    ((CategoryTheory.linearYoneda R C).obj Z).mapHomologicalComplex _

def ugh {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
  [Linear R C] [EnoughProjectives C]
  {α : Type*} [AddRightCancelSemigroup α] [One α] (Z : C) (X : ChainComplex C α) :
  ((ChainComplex.linearYoneda R Z).obj X).unop ≅ X.linearYonedaObj R Z :=
Iso.refl _
/-- The complex `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `k`-linear
`G`-representation. -/
abbrev linearYonedaObjResolution (A : Rep k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (groupCohomology.resolution k G).linearYonedaObj k A

abbrev linearYonedaObjBarResolution (A : Rep k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (Rep.barResolution k G).linearYonedaObj k A

theorem linearYonedaObjBarResolution_d_apply {A : Rep k G} (i j : ℕ)
    (x : (Rep.barResolution k G).X i ⟶ A) :
    (linearYonedaObjBarResolution A).d i j x = (Rep.barResolution k G).d j i ≫ x :=
  rfl

end groupCohomology

namespace inhomogeneousCochains

open Rep groupCohomology

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps]
def d [Monoid G] (n : ℕ) (A : Rep k G) : ((Fin n → G) → A) →ₗ[k] (Fin (n + 1) → G) → A where
  toFun f g :=
    A.ρ (g 0) (f fun i => g i.succ) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f g := by
    ext x
/- Porting note: changed from `simp only` which needed extra heartbeats -/
    simp_rw [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    ext x
/- Porting note: changed from `simp only` which needed extra heartbeats -/
    simp_rw [Pi.smul_apply, RingHom.id_apply, map_smul, smul_add, Finset.smul_sum, ← smul_assoc,
      smul_eq_mul, mul_comm r]
#align inhomogeneous_cochains.d inhomogeneousCochains.d

set_option profiler true
variable [Group G] (n) (A : Rep k G)

@[nolint checkType] theorem d_eq :
    d n A =
      (freeLiftEquiv (Fin n → G) A).toModuleIso.inv ≫
        (linearYonedaObjBarResolution A).d n (n + 1) ≫
          (freeLiftEquiv (Fin (n + 1) → G) A).toModuleIso.hom := by
  ext f g
  simp only [ChainComplex.of_x, ChainComplex.linearYonedaObj_d, barResolution.d_def,
    Function.comp_apply, freeLiftEquiv_apply]
  show _ = ((freeLiftEquiv _ _).symm f).hom _
  rw [d_single, map_add, map_sum, freeLiftEquiv_symm_apply, one_smul]
  conv =>
    · enter [2, 2, 2, x]
      rw [freeLiftEquiv_symm_apply, map_one]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep k G)

open inhomogeneousCochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d n A) fun n => by
    simp only [d_eq, d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (linearYonedaObjBarResolution A).d_comp_d] }

@[simp]
theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = inhomogeneousCochains.d n A :=
  CochainComplex.of_d _ _ _ _

set_option profiler true

def inhomogeneousCochainsBarIso : inhomogeneousCochains A ≅ linearYonedaObjBarResolution A := by
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · intro i
    apply (Rep.freeLiftEquiv (Fin i → G) A).toModuleIso.symm
  rintro i j (h : i + 1 = j)
  subst h
  simp only [Iso.symm_hom, inhomogeneousCochains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousCochainsIso : inhomogeneousCochains A ≅ linearYonedaObjResolution A :=
  inhomogeneousCochainsBarIso A ≪≫ ((ChainComplex.linearYoneda (R := k) A).mapIso (Rep.barResolutionIso k G).symm).unop

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of inhomogeneous cochains. -/
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n

/-- The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G, A).` -/
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ ModuleCat.of k ((Fin n → G) → A) :=
  (inhomogeneousCochains A).iCycles n

/-- This is the map from `i`-cochains to `j`-cocycles induced by the differential in the complex of
inhomogeneous cochains. -/
abbrev toCocycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) → A) ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

end groupCohomology

open groupCohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n
#align group_cohomology groupCohomology

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
abbrev groupCohomologyπ [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (extIso k G A n).symm
set_option linter.uppercaseLean3 false in
#align group_cohomology_iso_Ext groupCohomologyIsoExt
