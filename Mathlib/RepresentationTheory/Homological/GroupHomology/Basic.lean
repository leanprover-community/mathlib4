/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The group homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group homology of
`A : Rep k G` to be the homology of the complex
$$\dots \to \bigoplus_{G^2} A \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A$$
with differential $d_n$ sending $a\cdot (g_0, \dots, g_n)$ to
$$\rho(g_0^{-1})(a)\cdot (g_1, \dots, g_n)$$
$$+ \sum_{i = 0}^{n - 1}(-1)^{i + 1}a\cdot (g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}a\cdot (g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\bigoplus_{G^n} A \cong (A \otimes_k \left(\bigoplus_{G^n} k[G]\right))_G$ given by
`Rep.coinvariantsTensorFreeLEquiv`. If we conjugate the $n$th differential in $(A \otimes_k P)_G$
by this isomorphism, where `P` is the bar resolution of `k` as a trivial `k`-linear
`G`-representation, then the resulting map agrees with the differential $d_n$ defined
above, a fact we prove.

Hence our $d_n$ squares to zero, and we get
$\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k),$ where $\mathrm{Tor}$ is defined by deriving the
second argument of the functor $(A, B) \mapsto (A \otimes_k B)_G.$

To talk about homology in low degree, please see the file
`Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree`, which gives simpler expressions
for `H₀`, `H₁`, `H₂` than the definition `groupHomology` in this file.

## Main definitions

* `Rep.Tor k G n`: the left-derived functors given by deriving the second argument of
$(A, B) \mapsto (A \otimes_k B)_G$.
* `Rep.coinvariantsTensorBarResolution A`: a complex whose objects are
$(A \otimes_k \left(\bigoplus_{G^n} k[G]\right))_G$ and whose homology is the group
homology $\mathrm{H}_n(G, A)$.
* `groupHomology.inhomogeneousChains A`: a complex whose objects are
$\bigoplus_{G^n} A$ and whose homology is the group homology $\mathrm{H}_n(G, A).$
* `groupHomology.inhomogeneousChainsIso A`: an isomorphism between the above two complexes.
* `groupHomology A n`: this is $\mathrm{H}_n(G, A),$ defined as the $n$th homology of the
second complex, `inhomogeneousChains A`.
* `groupHomologyIsoTor A n`: an isomorphism $\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k)$
induced by `inhomogeneousChainsIso A`.

## Implementation notes

Group homology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module (MonoidAlgebra k G) A` so that we do not run into
possible scalar action diamonds.

Note that the existing definition of `Tor` in `Mathlib.CategoryTheory.Monoidal.Tor` is for monoidal
categories, and the bifunctor we use here does not define a monoidal structure on `Rep k G` in
general. It corresponds to tensoring modules over `k[G]`, but currently mathlib's `TensorProduct`
is only defined for commutative rings.

## TODO

* API for homology in low degree: $\mathrm{H}_0, \mathrm{H}_1$ and $\mathrm{H}_2.$ For example,
the corestriction-coinflation exact sequence.
* The long exact sequence in homology attached to a short exact sequence of representations.
* Upgrading `groupHomologyIsoTor` to an isomorphism of derived functors.

-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable (k G : Type u) [CommRing k] [Group G]

open MonoidalCategory Representation Finsupp

/-- The left-derived functors given by deriving the second argument of `A, B ↦ (A ⊗[k] B)_G`. -/
@[simps]
def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

variable {k G} (A : Rep k G)

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
lemma isZero_Tor_succ_of_projective (X Y : Rep k G) [Projective Y] (n : ℕ) :
    IsZero (((Tor k G (n + 1)).obj X).obj Y) :=
  Functor.isZero_leftDerived_obj_projective_succ ..

/-- Given a `k`-linear `G`-representation `A`, this is the chain complex `(A ⊗[k] P)_G`, where
`P` is the bar resolution of `k` as a trivial representation. -/
def coinvariantsTensorBarResolution :=
  (((coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj (barComplex k G)

end Rep

namespace groupHomology

open Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (n : ℕ)

namespace inhomogeneousChains

/-- The differential in the complex of inhomogeneous chains used to calculate group homology. -/
def d : ((Fin (n + 1) → G) →₀ A) →ₗ[k] (Fin n → G) →₀ A :=
  lsum (R := k) k fun g => lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹ +
    Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • lsingle (Fin.contractNth j (· * ·) g)

@[simp]
theorem d_single (n : ℕ) (g : Fin (n + 1) → G) (a : A) :
    d A n (single g a) = single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • single (Fin.contractNth j (· * ·) g) a := by
  rw [d, lsum_apply, sum_single_index]
  <;> simp

open ModuleCat.MonoidalCategory

theorem d_eq [DecidableEq G] :
    ModuleCat.ofHom (d A n) = (coinvariantsTensorFreeLEquiv A (Fin (n + 1) → G)).toModuleIso.inv ≫
      (coinvariantsTensorBarResolution A).d (n + 1) n ≫
      (coinvariantsTensorFreeLEquiv A (Fin n → G)).toModuleIso.hom := by
  ext g a : 3
  have := finsuppToCoinvariantsTensorFree_single (A := A) g
  have := barComplex.d_single (k := k) _ g
  have := coinvariantsTensorFreeToFinsupp_mk_tmul_single (A := A) (α := Fin n → G)
  simp_all [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    instMonoidalCategoryStruct_whiskerLeft, ModuleCat.MonoidalCategory.whiskerLeft,
    coinvariantsTensorBarResolution, coinvariantsMap, TensorProduct.tmul_add,
    TensorProduct.tmul_sum, ← Submodule.mkQ_apply _ (Finset.sum _ _)]

end inhomogeneousChains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous chains
$$\dots \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A \to 0$$
which calculates the group homology of `A`. -/
noncomputable abbrev inhomogeneousChains [DecidableEq G] :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n → G) →₀ A))
    (fun n => ModuleCat.ofHom (inhomogeneousChains.d A n)) fun n => by
    simp only [inhomogeneousChains.d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (coinvariantsTensorBarResolution A).d_comp_d] }
    simp

open inhomogeneousChains

@[simp]
theorem inhomogeneousChains.d_def [DecidableEq G] (n : ℕ) :
    (inhomogeneousChains A).d (n + 1) n = ModuleCat.ofHom (d A n) := by
  simp [inhomogeneousChains]

theorem inhomogeneousChains.d_comp_d [DecidableEq G] :
    d A n ∘ₗ d A (n + 1) = 0 := by
  simpa [ChainComplex.of] using
    congr(ModuleCat.Hom.hom $((inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n))

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous chains is isomorphic
to `(A ⊗[k] P)_G`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousChainsIso [DecidableEq G] :
    inhomogeneousChains A ≅ coinvariantsTensorBarResolution A := by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i → G)).toModuleIso.symm
  rintro i j rfl
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

variable [DecidableEq G]

/-- The `n`-cycles `Zₙ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
differential `Cₙ(G, A) ⟶ Cₙ₋₁(G, A)` in the complex of inhomogeneous chains. -/
abbrev cycles (n : ℕ) : ModuleCat k := (inhomogeneousChains A).cycles n

open HomologicalComplex

/-- The natural inclusion of the `n`-cycles `Zₙ(G, A)` into the `n`-chains `Cₙ(G, A).` -/
abbrev iCycles (n : ℕ) : cycles A n ⟶ ModuleCat.of k ((inhomogeneousChains A).X n) :=
  (inhomogeneousChains A).iCycles n

/-- This is the map from `i`-chains to `j`-cycles induced by the differential in the complex of
inhomogeneous chains. -/
abbrev toCycles (i j : ℕ) : ModuleCat.of k ((inhomogeneousChains A).X i) ⟶ cycles A j :=
  (inhomogeneousChains A).toCycles i j

end groupHomology

open groupHomology Rep

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G] (A : Rep k G)

/-- The group homology of a `k`-linear `G`-representation `A`, as the homology of its complex
of inhomogeneous chains. -/
def groupHomology (n : ℕ) : ModuleCat k :=
  (inhomogeneousChains A).homology n

/-- The natural map from `n`-cycles to `n`th group homology for a `k`-linear
`G`-representation `A`. -/
abbrev groupHomologyπ (n : ℕ) :
    cycles A n ⟶ groupHomology A n :=
  (inhomogeneousChains A).homologyπ n

/-- The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Torₙ(A, k)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupHomologyIsoTor (n : ℕ) :
    groupHomology A n ≅ ((Tor k G n).obj A).obj (Rep.trivial k G k) :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIso A)).hom n ≪≫
    ((barResolution k G).isoLeftDerivedObj ((coinvariantsTensor k G).obj A) n).symm

lemma isZero_groupHomology_succ_of_subsingleton [Subsingleton G] (n : ℕ) :
    Limits.IsZero (groupHomology A (n + 1)) :=
  (isZero_Tor_succ_of_projective A (Rep.trivial k G k) n).of_iso <| groupHomologyIsoTor _ _

end
