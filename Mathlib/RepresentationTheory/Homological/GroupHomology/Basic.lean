/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Abelian.LeftDerived

noncomputable section

universe u
section
variable (R A B α : Type*) [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B]

theorem Submodule.Quotient.mk_sum {ι : Type*} (S : Submodule R A)
    (s : Finset ι) (f : ι → A) :
    Submodule.Quotient.mk (p := S) (s.sum f) = s.sum (fun i => Submodule.Quotient.mk (f i)) :=
  map_sum (Submodule.mkQ S) _ _

open CategoryTheory CategoryTheory.Limits

namespace Rep
variable (k G : Type u) [CommRing k] [Group G] (A : Rep k G) (α : Type u) [DecidableEq α]

open MonoidalCategory Representation Finsupp

/-- The left-derived functors given by deriving the second argument of `A, B ↦ (A ⊗[k] B)_G`. -/
def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

variable {k G}
variable (A : Rep k G)
/-
/-- `Torₙ(A, B) -/
def torIso (B : Rep k G) (P : ProjectiveResolution B) (n : ℕ) :
    ((Tor k G n).obj A).obj B
      ≅ ((((coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P.complex).homology n :=
  ProjectiveResolution.isoLeftDerivedObj P ((tensor k G).obj A) n
-/

/-- Given a `k`-linear `G`-representation `A`, this is the chain complex `(A ⊗[k] P)`, where
`P` is the bar resolution of `k` as a trivial representation. -/
def coinvariantsTensorBarResolution :=
  (((coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj (Rep.barResolution k G)

end Rep

namespace groupHomology
open Rep
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) {n : ℕ}

namespace inhomogeneousChains

/-- The differential in the complex of inhomogeneous chains used to calculate group homology. -/
def d (n : ℕ) : ((Fin (n + 1) → G) →₀ A) →ₗ[k] (Fin n → G) →₀ A :=
  Finsupp.lsum (R := k) k fun g => Finsupp.lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹
    + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.lsingle (Fin.contractNth j (· * ·) g)

theorem d_apply (n : ℕ) (x : (Fin (n + 1) → G) →₀ A) :
    d A n x = x.sum fun g a => Finsupp.single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a)
      + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  ext
  simp [d, Finsupp.sum]

@[simp]
theorem d_single (n : ℕ) (g : Fin (n + 1) → G) (a : A) :
    d A n (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a)
      + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  rw [d_apply, Finsupp.sum_single_index]
  simp

theorem d_eq [DecidableEq G] :
    d A n = (coinvariantsTensorFreeLEquiv A (Fin (n + 1) → G)).toModuleIso.inv ≫
      (coinvariantsTensorBarResolution A).d (n + 1) n ≫
      (coinvariantsTensorFreeLEquiv A (Fin n → G)).toModuleIso.hom := by
  ext g a : 2
  have := finsuppToCoinvariantsTensorFree_single (A := A) g
  have := barResolution.d_single (k := k) _ g
  have := coinvariantsTensorFreeToFinsupp_mk_tmul_single (A := A) (α := Fin n → G)
  simp_all [moduleCat_simps, coinvariantsTensorBarResolution, coinvariantsMap,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_whiskerLeft, ModuleCat.MonoidalCategory.whiskerLeft,
    TensorProduct.tmul_add, TensorProduct.tmul_sum, Submodule.Quotient.mk_sum]

end inhomogeneousChains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous chains
$$0 \to \mathrm{FinSupp}(G^0, A) \to \mathrm{FinSupp}(G^1, A) \to \dots$$
which calculates the group homology of `A`. -/
noncomputable abbrev inhomogeneousChains [DecidableEq G] :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n → G) →₀ A))
    (fun n => inhomogeneousChains.d A n) fun n => by
    simp only [inhomogeneousChains.d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (coinvariantsTensorBarResolution A).d_comp_d] }
    simp

open inhomogeneousChains

theorem inhomogeneousChains.d_comp_d [DecidableEq G] :
    d A n ∘ₗ d A (n + 1) = 0 := by
  simpa [ChainComplex.of] using (inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n

@[simp]
theorem inhomogeneousChains.d_def [DecidableEq G] (n : ℕ) :
    (inhomogeneousChains A).d (n + 1) n = d A n :=
  ChainComplex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous chains is isomorphic
to `(A ⊗[k] P)_G`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousChainsBarIso [DecidableEq G] :
    inhomogeneousChains A ≅ coinvariantsTensorBarResolution A := by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i → G)).toModuleIso.symm
  rintro i j (h : j + 1 = i)
  subst h
  simp only [Iso.symm_hom, inhomogeneousChains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

variable [DecidableEq G]

/-- The `n`-cycles `Zₙ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
differential `Cₙ(G, A) ⟶ Cₙ₋₁(G, A)` in the complex of inhomogeneous chains. -/
abbrev cycles (n : ℕ) : ModuleCat k := (inhomogeneousChains A).cycles n

open HomologicalComplex

/-- The `n + 1`-cycles `Zₙ₊₁(G, A)` of a `k`-linear `G`-representation are isomorphic to the kernel
of the linear map `inhomogeneousChains.d A n : (Gⁿ⁺¹ →₀ A) →ₗ[k] (Gⁿ →₀ A).` -/
def cyclesSuccIso (n : ℕ) :
    cycles A (n + 1) ≅ ModuleCat.of k (LinearMap.ker (inhomogeneousChains.d A n)) :=
  (inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop)
  ≪≫ ShortComplex.moduleCatCyclesIso _ ≪≫ (LinearEquiv.ofEq _ _ <| by simp).toModuleIso

theorem cyclesSuccIso_inv_eq {n : ℕ} (x : LinearMap.ker (inhomogeneousChains.d A n)) :
    (cyclesSuccIso A n).inv x
    = HomologicalComplex.cyclesMk (inhomogeneousChains A) x.1 n
      (ChainComplex.next_nat_succ _) (by simp) :=
  congr(((inhomogeneousChains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop)).inv
    $(ShortComplex.moduleCatCyclesIso_inv_apply x.1 (by simp))).trans
    ((inhomogeneousChains A).cyclesIsoSc'_inv_cyclesMk x.1 (ChainComplex.prev _ _)
    (ChainComplex.next_nat_succ _) <| by aesop)

/-- The natural inclusion of the `n`-cycles `Zₙ(G, A)` into the `n`-chains `Cₙ(G, A).` -/
abbrev iCycles (n : ℕ) : cycles A n ⟶ ModuleCat.of k ((Fin n → G) →₀ A) :=
  (inhomogeneousChains A).iCycles n

@[reassoc (attr := simp, elementwise)]
theorem cyclesSuccIso_inv_comp_iCycles (n : ℕ) :
    (cyclesSuccIso A n).inv ≫ iCycles A (n + 1) = Submodule.subtype _ := by
  ext
  simp only [cyclesSuccIso, Iso.trans_inv, Category.assoc, cyclesIsoSc'_inv_iCycles,
    ShortComplex.moduleCatCyclesIso_inv_iCycles]
  simp [moduleCat_simps]

@[reassoc (attr := simp, elementwise)]
theorem cyclesSuccIso_hom_comp_subtype :
    (cyclesSuccIso A n).hom ≫ Submodule.subtype _ = iCycles _ _ := by
  simp only [← Iso.eq_inv_comp, cyclesSuccIso_inv_comp_iCycles]

/-- This is the map from `i`-chains to `j`-cycles induced by the differential in the complex of
inhomogeneous chains. -/
abbrev toCycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) →₀ A) ⟶ cycles A j :=
  (inhomogeneousChains A).toCycles i j

/-- The `n`-opcycles of a `k`-linear `G`-representation `A`, i.e. the cokernel of the
differential `Cₙ₊₁(G, A) ⟶ Cₙ(G, A)` in the complex of inhomogeneous chains. -/
abbrev opcycles (n : ℕ) : ModuleCat k := (inhomogeneousChains A).opcycles n

/-- The natural projection of the `n`-chains `Cₙ(G, A)` onto the `n`-opcycles. -/
noncomputable abbrev pOpcycles (n : ℕ) :
    ModuleCat.of k ((Fin n → G) →₀ A) ⟶ opcycles A n := (inhomogeneousChains A).pOpcycles n

/-- The map from the `i` opcycles to the `j`-chains induced by the differential `i, j`th
differential in the complex of inhomogeneous chains. -/
noncomputable abbrev fromOpcycles (i j : ℕ) :
    opcycles A i ⟶ ModuleCat.of k ((Fin j → G) →₀ A) := (inhomogeneousChains A).fromOpcycles i j

end groupHomology
open groupHomology Rep
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G] (A : Rep k G)

/-- The group homology of a `k`-linear `G`-representation `A`, as the homology of its complex
of inhomogeneous chains. -/
abbrev groupHomology (n : ℕ) : ModuleCat k :=
  (inhomogeneousChains A).homology n

/-- The natural map from `n`-cycles to `n`th group homology for a `k`-linear
`G`-representation `A`. -/
abbrev groupHomologyπ (n : ℕ) :
    cycles A n ⟶ groupHomology A n :=
  (inhomogeneousChains A).homologyπ n

/-abbrev groupHomologyι (n : ℕ) :
    groupHomology A n ⟶ opcycles A n :=
  (inhomogeneousChains A).homologyι n-/

/-- The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Torₙ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupHomologyIsoTor [Group G] (A : Rep k G) (n : ℕ) :
    groupHomology A n ≅ ((Tor k G n).obj A).obj (Rep.trivial k G k) :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsBarIso A)).hom n ≪≫
    (ProjectiveResolution.isoLeftDerivedObj (barResolution.projectiveResolution k G)
      ((coinvariantsTensor k G).obj A) n).symm
