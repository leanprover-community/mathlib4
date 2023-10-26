import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

noncomputable instance {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (forget₂ (ModuleCat.{v} R) Ab) :=
  preservesColimitOfPreservesColimitCocone (ModuleCat.cokernelIsColimit f) (by
    let e : parallelPair ((forget₂ (ModuleCat.{v} R) Ab).map f) 0 ≅
        parallelPair f 0 ⋙ forget₂ _ _ :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat)
    refine' IsColimit.precomposeHomEquiv e _ _
    refine' IsColimit.ofIsoColimit
      (AddCommGroupCat.cokernelIsColimit ((forget₂ (ModuleCat.{v} R) Ab).map f)) _
    refine' Cofork.ext (Iso.refl _) (by aesop_cat))

namespace ShortComplex

variable (S : ShortComplex (ModuleCat.{v} R))

noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

@[simp]
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_concrete_category

lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g ≤ LinearMap.range S.f := by
  rw [moduleCat_exact_iff]
  constructor
  · intro h x₂ hx₂
    exact h x₂ hx₂
  · intro h x₂ hx₂
    exact h hx₂

lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f = LinearMap.ker S.g := by
  rw [moduleCat_exact_iff_ker_sub_range]
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      simp only [LinearMap.mem_ker, moduleCat_zero_apply]
    · intro hx
      exact h hx
  · intro h
    rw [h]

variable {S}

lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f = LinearMap.ker S.g := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f

lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

@[simps]
def moduleCat_mk_of_ker_le_range {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f ≤ LinearMap.ker g) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by
    ext
    exact hfg ⟨_, rfl⟩)

lemma Exact.moduleCat_mk_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f = LinearMap.ker g) :
    (moduleCat_mk_of_ker_le_range f g (by rw [hfg])).Exact := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hfg

variable (S)

def moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g where
  toFun x := ⟨S.f x, by
    rw [LinearMap.mem_ker]
    erw [← comp_apply, S.zero]
    rfl⟩
  map_add' x y := by aesop
  map_smul' a x := by aesop

@[simps]
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g)
  H := ModuleCat.of R (LinearMap.ker S.g ⧸ LinearMap.range S.moduleCatToCycles)
  i := (LinearMap.ker S.g).subtype
  π := (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := ModuleCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    dsimp
    erw [Submodule.Quotient.mk_eq_zero]
    rw [LinearMap.mem_range]
    apply exists_apply_eq_apply
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

@[simp]
lemma moduleCatLeftHomologyData_f' :
    S.moduleCatLeftHomologyData.f' = S.moduleCatToCycles := rfl

noncomputable def moduleCatCyclesIso : S.cycles ≅ ModuleCat.of R (LinearMap.ker S.g) :=
  S.moduleCatLeftHomologyData.cyclesIso

noncomputable def moduleCatHomologyIso :
    S.homology ≅
      ModuleCat.of R ((LinearMap.ker S.g) ⧸ LinearMap.range S.moduleCatToCycles) :=
  S.moduleCatLeftHomologyData.homologyIso

end ShortComplex

end CategoryTheory
