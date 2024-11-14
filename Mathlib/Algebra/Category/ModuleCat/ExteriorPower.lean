/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-!
# The exterior power operations on modules

-/

universe w v u

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

lemma linearMap_eq_zero_iff_of_span_eq_top (f : M →ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = 0 ↔ ∀ (s : S), f s = 0 := by
  rw [← LinearMap.ker_eq_top, ← top_le_iff, ← hM, span_le]
  aesop

lemma linearMap_eq_zero_iff_of_eq_span {V : Submodule R M} (f : V →ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = 0 ↔ ∀ (s : S), f ⟨s, by simpa only [hV] using subset_span (by simp)⟩ = 0 := by
  constructor
  · rintro rfl s
    rfl
  · intro hf
    rw [linearMap_eq_zero_iff_of_span_eq_top (S := (V.subtype ⁻¹' S))]
    · subst hV
      rintro ⟨⟨s, _⟩, hs⟩
      exact hf ⟨s, hs⟩
    · subst hV
      simp

end Submodule

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [AddCommGroup M] [Module R M]

def exteriorProduct : AlternatingMap R M (exteriorPower R n M) (Fin n) where
  toFun m := ⟨ιMulti R n m, ιMulti_range _ _ (by simp)⟩
  map_add' m i x y := Subtype.ext (by simp)
  map_smul' m i c x := Subtype.ext (by simp)
  map_eq_zero_of_eq' v i j hij hij' :=
    Subtype.ext ((ιMulti R (M := M) n).map_eq_zero_of_eq v hij hij')

namespace exteriorPower

variable {R n M} {N : Type w} [AddCommGroup N] [Module R N]
  (φ : AlternatingMap R M N (Fin n))

def desc : exteriorPower R n M →ₗ[R] N :=
  LinearMap.comp (liftAlternating
    (Function.update (fun n ↦ (0 : M [⋀^Fin n]→ₗ[R] N)) n φ)) (Submodule.subtype _)

@[simp]
lemma desc_exteriorProduct (m : Fin n → M) :
    desc φ (exteriorProduct R n M m) = φ m := by
  dsimp [desc]
  erw [liftAlternating_apply_ιMulti]
  simp

lemma linearMap_eq_zero_iff (f : exteriorPower R n M →ₗ[R] N) :
    f = 0 ↔ ∀ (m : Fin n → M), f (exteriorProduct R n M m) = 0 := by
  constructor
  · rintro rfl _
    rfl
  · rw [Submodule.linearMap_eq_zero_iff_of_eq_span f
      (ιMulti_span_fixedDegree R (M := M) n).symm]
    rintro hf ⟨_, m, rfl⟩
    exact hf m

@[ext]
lemma linearMap_ext {f g : exteriorPower R n M →ₗ[R] N}
    (h : ∀ (m : Fin n → M), f (exteriorProduct R n M m) = g (exteriorProduct R n M m)) :
    f = g := by
  rw [← sub_eq_zero, linearMap_eq_zero_iff]
  intro m
  rw [LinearMap.sub_apply, sub_eq_zero]
  exact h m

end exteriorPower

end ExteriorAlgebra

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

section

variable {R : Type u} [CommRing R]

def exteriorPower (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (⋀[R]^n M)

def AlternatingMap (M N : ModuleCat.{u} R) (n : ℕ) :=
  M [⋀^Fin n]→ₗ[R] N

instance {M N : ModuleCat.{u} R} {n : ℕ} :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^Fin n]→ₗ[R] N) (Fin n → M) N)

end

namespace AlternatingMap

variable {R : Type u} [CommRing R] {M N N' : ModuleCat.{u} R} {n : ℕ}

@[ext]
lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (m : Fin n → M), φ m = φ' m) : φ = φ' :=
  DFunLike.coe_injective (by funext; apply h)

@[ext 1100]
lemma ext₀ {φ φ' : M.AlternatingMap N 0} (h : φ 0 = φ' 0) : φ = φ' := by
  ext m
  obtain rfl : m = 0 := by funext x; fin_cases x
  exact h

def postcomp (φ : M.AlternatingMap N n) (f : N ⟶ N') :
    M.AlternatingMap N' n :=
  f.compAlternatingMap φ

@[simp]
lemma postcomp_apply (φ : M.AlternatingMap N n) (f : N ⟶ N') (m : Fin n → M) :
    φ.postcomp f m = f (φ m) := rfl

@[simp]
lemma postcomp_id (φ : M.AlternatingMap N n) :
    φ.postcomp (𝟙 _) = φ := rfl

@[simp]
lemma postcomp_comp (φ : M.AlternatingMap N n)
    (f : N ⟶ N') {N'' : ModuleCat.{u} R} (g : N' ⟶ N'') :
    φ.postcomp (f ≫ g) = (φ.postcomp f).postcomp g := rfl

lemma congr_apply {φ φ' : M.AlternatingMap N n} (h : φ = φ') (m : Fin n → M) :
    φ m = φ' m := by
  rw [h]

end AlternatingMap

@[simps]
def alternatingMapFunctor {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.{u} R ⥤ Type u where
  obj N := M.AlternatingMap N n
  map {N N'} f φ := φ.postcomp f

namespace AlternatingMap

variable {R : Type u} [CommRing R] {M N₀ N₁ : ModuleCat.{u} R} {n : ℕ}

structure Universal (φ : M.AlternatingMap N₀ n) where
  desc {N : ModuleCat.{u} R} (ψ : M.AlternatingMap N n) : N₀ ⟶ N
  fac {N : ModuleCat.{u} R} (ψ : M.AlternatingMap N n) : φ.postcomp (desc ψ) = ψ
  postcomp_injective {N : ModuleCat.{u} R} {f g : N₀ ⟶ N}
    (h : φ.postcomp f = φ.postcomp g) : f = g

variable (M n)

def univ (M : ModuleCat.{u} R) (n : ℕ) : M.AlternatingMap (M.exteriorPower n) n :=
  ExteriorAlgebra.exteriorProduct _ _ _

def univUniversal : (univ M n).Universal where
  desc {N} φ := ExteriorAlgebra.exteriorPower.desc φ
  fac {N} φ := by
    ext m
    apply ExteriorAlgebra.exteriorPower.desc_exteriorProduct
  postcomp_injective {N f g} h :=
    ExteriorAlgebra.exteriorPower.linearMap_ext (congr_apply h)

namespace Universal

attribute [simp] fac

variable {M n} {φ : M.AlternatingMap N₀ n}

lemma hom_ext (hφ : φ.Universal) {N : ModuleCat.{u} R} {f g : N₀ ⟶ N}
    (h : ∀ (m : Fin n → M), f (φ m) = g (φ m)) : f = g :=
  hφ.postcomp_injective (by ext; apply h)

variable (hφ : φ.Universal)

@[simp]
lemma desc_apply {N : ModuleCat.{u} R} (ψ : M.AlternatingMap N n) (m : Fin n → M) :
    hφ.desc ψ (φ m) = ψ m := by
  conv_rhs => rw [← hφ.fac ψ]
  rfl

section

variable {ψ : M.AlternatingMap N₁ n} (hψ : ψ.Universal)

def uniq : N₀ ≅ N₁ where
  hom := hφ.desc ψ
  inv := hψ.desc φ
  hom_inv_id := hφ.postcomp_injective (by simp)
  inv_hom_id := hψ.postcomp_injective (by simp)

@[simp] lemma postcomp_uniq_hom : φ.postcomp (uniq hφ hψ).hom = ψ := by simp [uniq]
@[simp] lemma postcomp_uniq_inv : ψ.postcomp (uniq hφ hψ).inv = φ := by simp [uniq]

end

def iso : M.exteriorPower n ≅ N₀ :=
  (univUniversal M n).uniq hφ

@[simp] lemma postcomp_iso_hom : (univ M n).postcomp hφ.iso.hom = φ := by simp [iso]
@[simp] lemma postcomp_iso_inv : φ.postcomp hφ.iso.inv = univ M n := by simp [iso]

end Universal

section

variable {M n} (r : (M.alternatingMapFunctor n).CorepresentableBy N₀)

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

end AlternatingMap

section

variable {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)

def equiv₀ : M.AlternatingMap N 0 ≃ N :=
  AlternatingMap.constLinearEquivOfIsEmpty.toEquiv.symm

def corepresentableBy₀ :
    (M.alternatingMapFunctor 0).CorepresentableBy (ModuleCat.of R R) where
  homEquiv {N} := N.homEquivOfSelf.trans (equiv₀ M N).symm
  homEquiv_comp _ _ := rfl

def exteriorPower₀Iso : M.exteriorPower 0 ≅ of R R :=
  (AlternatingMap.universalOfCorepresentableBy M.corepresentableBy₀).iso

@[simp]
lemma _root_.Function.update_apply_of_subsingleton
    {M : Type*} (φ : Fin 1 → M) (x : Fin 1) (m : M) (i : Fin 1) :
    Function.update φ x m i = m := by
  obtain rfl := Subsingleton.elim x i
  simp

def equiv₁ : M.AlternatingMap N 1 ≃ (M ⟶ N) where
  toFun φ :=
    { toFun := fun x ↦ φ (fun _ ↦ x)
      map_add' := fun x y ↦ by convert φ.map_add 0 0 x y <;> simp
      map_smul' := fun r x ↦ by convert φ.map_smul 0 0 r x <;> simp }
  invFun f :=
    { toFun := fun x ↦ f (x 0)
      map_add' := fun _ i x y ↦ by fin_cases i; convert f.map_add x y <;> simp
      map_smul' := fun _ i r x ↦ by fin_cases i; convert f.map_smul r x <;> simp
      map_eq_zero_of_eq' := fun _ i j ↦ by fin_cases i; fin_cases j; tauto }
  left_inv φ := by
    ext m
    obtain ⟨x, rfl⟩ : ∃ x, m = fun _ ↦ x := ⟨m 0, by ext i; fin_cases i; rfl⟩
    rfl
  right_inv f := rfl

def corepresentableBy₁ :
    (M.alternatingMapFunctor 1).CorepresentableBy M where
  homEquiv {N} := (equiv₁ M N).symm
  homEquiv_comp _ _ := rfl

def exteriorPower₁Iso : M.exteriorPower 1 ≅ M :=
  (AlternatingMap.universalOfCorepresentableBy M.corepresentableBy₁).iso

end

namespace exteriorPower

section

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R}

def desc {n : ℕ} {N : ModuleCat.{u} R} (φ : M.AlternatingMap N n) :
    M.exteriorPower n ⟶ N :=
  (AlternatingMap.univUniversal M n).desc φ

def mk {n : ℕ} (m : Fin n → M) : M.exteriorPower n :=
  AlternatingMap.univ M n m

@[simp]
lemma desc_mk {n : ℕ} {N : ModuleCat.{u} R} (φ : M [⋀^Fin n]→ₗ[R] N)
    (m : Fin n → M) :
    desc φ (mk m) = φ m := by
  simp [desc, mk]

@[ext]
lemma hom_ext {n : ℕ} {N : ModuleCat.{u} R} {f g : M.exteriorPower n ⟶ N}
    (h : ∀ (m : Fin n → M), f (mk m) = g (mk m)) :
    f = g :=
  (AlternatingMap.univUniversal M n).hom_ext h

def map {N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) : M.exteriorPower n ⟶ N.exteriorPower n :=
  desc (AlternatingMap.compLinearMap (AlternatingMap.univ N n) f)

@[simp]
lemma map_mk {N : ModuleCat.{u} R} (f : M ⟶ N) {n : ℕ} (m : Fin n → M) :
    map f n (mk m) = mk (Function.comp f m) := by
  simp only [map, desc_mk, AlternatingMap.compLinearMap_apply]
  rfl

variable (M R)

@[simps]
def functor (n : ℕ): ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := M.exteriorPower n
  map f := map f n

end

section ChangeOfRings

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

noncomputable def fromRestrictScalarsObjExteriorPower (M : ModuleCat.{u} S) (n : ℕ) :
    ((restrictScalars f).obj M).exteriorPower n ⟶
      (restrictScalars f).obj (M.exteriorPower n) :=
  desc
    { toFun := fun m ↦ mk m
      map_add' := fun m i x y ↦ (AlternatingMap.univ M n).map_add m i x y
      map_smul' := fun m i r x ↦ (AlternatingMap.univ M n).map_smul m i (f r) x
      map_eq_zero_of_eq' := fun m _ _ hm hij ↦
        (AlternatingMap.univ M n).map_eq_zero_of_eq m hm hij }

@[simp]
lemma fromRestrictScalarsObjExteriorPower_mk (M : ModuleCat.{u} S) (n : ℕ)
    (m : Fin n → M) :
    fromRestrictScalarsObjExteriorPower f M n (mk m) = mk m := by
  apply desc_mk

@[simps]
noncomputable def restrictScalarsCompFunctorNatTrans (n : ℕ) :
    restrictScalars f ⋙ functor R n ⟶ functor S n ⋙ restrictScalars f where
  app M := fromRestrictScalarsObjExteriorPower f M n

end ChangeOfRings

end exteriorPower

end ModuleCat
