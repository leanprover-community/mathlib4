/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The exterior power of an object in `ModuleCat R`. -/
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

-- this could be an abbrev, but using a def eases automation
/-- The type of `n`-alternating maps on `M : ModuleCat R` to `N : ModuleCat R`. -/
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
  _root_.AlternatingMap R M N (Fin n)

instance (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :
    FunLike (M.AlternatingMap N n) (Fin n → M) N :=
  inferInstanceAs (FunLike (M [⋀^(Fin n)]→ₗ[R] N) (Fin n → M) N)

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

@[ext]
lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x ) :
    φ = φ' :=
  _root_.AlternatingMap.ext h

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

/-- The postcomposition of an alternating map by a linear map. -/
def postcomp : M.AlternatingMap N' n :=
  g.hom.compAlternatingMap φ

@[simp]
lemma postcomp_apply (x : Fin n → M) :
    φ.postcomp g x = g (φ x) := rfl

end AlternatingMap

namespace exteriorPower

/-- Constructor for elements in `M.exteriorPower n` when `M` is an object of `ModuleCat R`
and `n : ℕ`. -/
def mk {M : ModuleCat.{v} R} {n : ℕ} :
    M.AlternatingMap (M.exteriorPower n) n :=
  exteriorPower.ιMulti _ _

@[ext]
lemma hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : mk.postcomp f = mk.postcomp g) : f = g := by
  ext : 1
  exact exteriorPower.linearMap_ext h

/-- The morphism `M.exteriorPower n ⟶ N` induced by an alternating map. -/
noncomputable def desc {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) : M.exteriorPower n ⟶ N :=
  ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[simp]
lemma desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    desc φ (mk x) = φ x := by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

/-- The morphism `M.exteriorPower n ⟶ N.exteriorPower n` induced by a morphism `M ⟶ N`
in `ModuleCat R`. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.exteriorPower n ⟶ N.exteriorPower n :=
  ofHom (_root_.exteriorPower.map n f.hom)

@[simp]
lemma map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    map f n (mk x) = mk (f ∘ x) := by
  apply exteriorPower.map_apply_ιMulti

variable (R)

/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power. -/
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.exteriorPower n
  map f := map f n

end exteriorPower

end ModuleCat
