/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!

-/

universe u

open CategoryTheory

namespace ModuleCat

section

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

def homEquivOfSelf :
    (of R R ⟶ M) ≃ M :=
  (LinearMap.ringLmapEquivSelf R R M).toEquiv

@[simp] lemma homEquivOfSelf_apply (φ : of R R ⟶ M) : M.homEquivOfSelf φ = φ (1 : R) := rfl
@[simp] lemma homEquivOfSelf_symm_apply (m : M) (r : R) : M.homEquivOfSelf.symm m r = r • m := rfl

end

def exteriorPower {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (⋀[R]^n M)

def AlternatingMap {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (n : ℕ) :=
  M [⋀^Fin n]→ₗ[R] N

instance {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} {n : ℕ} :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^Fin n]→ₗ[R] N) (Fin n → M) N)

@[ext]
lemma AlternatingMap.ext {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} {n : ℕ}
    {φ φ' : M.AlternatingMap N n} (h : ∀ (m : Fin n → M), φ m = φ' m) : φ = φ' :=
  DFunLike.coe_injective (by funext; apply h)

@[ext 1100]
lemma AlternatingMap.ext₀ {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    {φ φ' : M.AlternatingMap N 0} (h : φ 0 = φ' 0) : φ = φ' := by
  ext m
  obtain rfl : m = 0 := by funext x; fin_cases x
  exact h

def AlternatingMap.postcomp {R : Type u} [CommRing R] {M N N' : ModuleCat.{u} R} {n : ℕ}
    (φ : M.AlternatingMap N n) (f : N ⟶ N') :
    M.AlternatingMap N' n :=
  f.compAlternatingMap φ

@[simp]
lemma AlternatingMap.postcomp_apply {R : Type u} [CommRing R] {M N N' : ModuleCat.{u} R} {n : ℕ}
    (φ : M.AlternatingMap N n) (f : N ⟶ N') (m : Fin n → M) :
    φ.postcomp f m = f (φ m) := rfl

@[simps]
def alternatingMapFunctor {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.{u} R ⥤ Type u where
  obj N := M.AlternatingMap N n
  map {N N'} f φ := φ.postcomp f

namespace AlternatingMap

variable {R : Type u} [CommRing R] {M N₀ : ModuleCat.{u} R} {n : ℕ}
  (φ : M.AlternatingMap N₀ n)

structure Universal where
  desc {N : ModuleCat.{u} R} (ψ : M.AlternatingMap N n) : N₀ ⟶ N
  fac {N : ModuleCat.{u} R} (ψ : M.AlternatingMap N n) : φ.postcomp (desc ψ) = ψ
  postcomp_injective {N : ModuleCat.{u} R} {f g : N₀ ⟶ N}
    (h : φ.postcomp f = φ.postcomp g) : f = g

variable {φ}

def Universal.iso (hφ : φ.Universal) : M.exteriorPower n ≅ N₀ := by
  sorry

section

variable (r : (M.alternatingMapFunctor n).CorepresentableBy N₀)

def ofCorepresentableBy : M.AlternatingMap N₀ n := r.homEquiv (𝟙 _)

def universalOfCorepresentableBy : (ofCorepresentableBy r).Universal where
  desc ψ := r.homEquiv.symm ψ
  fac ψ := by
    obtain ⟨φ, rfl⟩ := r.homEquiv.surjective ψ
    dsimp [ofCorepresentableBy]
    simp only [Equiv.symm_apply_apply]
    erw [r.homEquiv_eq φ]
    rfl
  postcomp_injective {N f g} h := by
    apply r.homEquiv.injective
    rw [r.homEquiv_eq f, r.homEquiv_eq g]
    exact h

end

variable (M)

@[simps]
def zero : M.AlternatingMap (ModuleCat.of R R) 0 where
  toFun _ := (1 : R)
  map_add' _ x := by fin_cases x
  map_smul' _ x := by fin_cases x
  map_eq_zero_of_eq' _ x := by fin_cases x

def equiv₀ (N : ModuleCat.{u} R) : M.AlternatingMap N 0 ≃ N :=
  AlternatingMap.constLinearEquivOfIsEmpty.toEquiv.symm

def corepresentableBy₀ :
    (M.alternatingMapFunctor 0).CorepresentableBy (ModuleCat.of R R) where
  homEquiv {N} := N.homEquivOfSelf.trans (equiv₀ M N).symm
  homEquiv_comp := by
    sorry

def one : M.AlternatingMap M 1 where
  toFun f := f 0
  map_add' _ n _ _:= by fin_cases n; simp
  map_smul' _ n _ _ := by fin_cases n; simp
  map_eq_zero_of_eq' _ i j := by fin_cases i; fin_cases j; tauto

def oneUniversal : (one M).Universal := sorry

end AlternatingMap

namespace exteriorPower

section

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R}

def lift {n : ℕ} {N : ModuleCat.{u} R} (φ : M.AlternatingMap N n) :
    M.exteriorPower n ⟶ N := by
  sorry

def mk {n : ℕ} (m : Fin n → M) : M.exteriorPower n := sorry

@[simps]
def mkAlternatingMap (n : ℕ) : M.AlternatingMap (M.exteriorPower n) n where
  toFun := mk
  map_add' := sorry
  map_smul' := sorry
  map_eq_zero_of_eq' := sorry

@[simp]
lemma lift_mk {n : ℕ} {N : ModuleCat.{u} R} (φ : M [⋀^Fin n]→ₗ[R] N)
    (m : Fin n → M) :
    lift φ (mk m) = φ m := by
  sorry

@[ext]
lemma hom_ext {n : ℕ} {N : ModuleCat.{u} R} {f g : M.exteriorPower n ⟶ N}
    (h : ∀ (m : Fin n → M), f (mk m) = g (mk m)) :
    f = g := by
  sorry

def map {N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) : M.exteriorPower n ⟶ N.exteriorPower n :=
  lift (AlternatingMap.compLinearMap (mkAlternatingMap n) f)

@[simp]
lemma map_mk {N : ModuleCat.{u} R} (f : M ⟶ N) {n : ℕ} (m : Fin n → M) :
    map f n (mk m) = mk (Function.comp f m) := by
  simp only [map, lift_mk, AlternatingMap.compLinearMap_apply, mkAlternatingMap_apply]
  rfl

variable (M)

def iso₀ : M.exteriorPower 0 ≅ ModuleCat.of R R :=
  (AlternatingMap.universalOfCorepresentableBy
    (AlternatingMap.corepresentableBy₀ M)).iso

def iso₁ : M.exteriorPower 1 ≅ M := (AlternatingMap.oneUniversal M).iso

variable (R)

@[simps]
def functor (n : ℕ): ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := M.exteriorPower n
  map f := map f n

end

section ChangeOfRings

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

def fromRestrictScalarsObjExteriorPower (M : ModuleCat.{u} S) (n : ℕ) :
    ((restrictScalars f).obj M).exteriorPower n ⟶
      (restrictScalars f).obj (M.exteriorPower n) :=
  lift
    { toFun := fun m ↦ mk m
      map_add' := fun m i x y ↦ by
        dsimp
        sorry
      map_smul' := sorry
      map_eq_zero_of_eq' := sorry }

@[simp]
lemma fromRestrictScalarsObjExteriorPower_mk (M : ModuleCat.{u} S) (n : ℕ)
    (m : Fin n → M) :
    fromRestrictScalarsObjExteriorPower f M n (mk m) = mk m := by
  apply lift_mk

@[simps]
def restrictScalarsCompFunctorNatTrans (n : ℕ) :
    restrictScalars f ⋙ functor R n ⟶ functor S n ⋙ restrictScalars f where
  app M := fromRestrictScalarsObjExteriorPower f M n

end ChangeOfRings

end exteriorPower

end ModuleCat
