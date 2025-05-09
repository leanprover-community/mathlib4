/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The differentials of a morphism in the category of commutative rings

In this file, given a morphism `f : A ⟶ B` in the category `CommRingCat`,
and `M : ModuleCat B`, we define the type `M.Derivation f` of
derivations with values in `M` relative to `f`.
We also construct the module of differentials
`CommRingCat.KaehlerDifferential f : ModuleCat B` and the corresponding derivation.

-/

universe v u

open CategoryTheory

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

namespace ModuleCat

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

/-- The type of derivations with values in a `B`-module `M` relative
to a morphism `f : A ⟶ B` in the category `CommRingCat`. -/
nonrec def Derivation : Type _ :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  Derivation A B M

namespace Derivation

variable {M f}

/-- Constructor for `ModuleCat.Derivation`. -/
def mk (d : B → M) (d_add : ∀ (b b' : B), d (b + b') = d b + d b' := by simp)
    (d_mul : ∀ (b b' : B), d (b * b') = b • d b' + b' • d b := by simp)
    (d_map : ∀ (a : A), d (f a) = 0 := by simp) :
    M.Derivation f :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b ↦ by
      dsimp
      rw [RingHom.smul_toAlgebra, d_mul, d_map, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one, d_map]
    leibniz' := d_mul }

variable (D : M.Derivation f)

/-- The underlying map `B → M` of a derivation `M.Derivation f` when `M : ModuleCat B`
and `f : A ⟶ B` is a morphism in `CommRingCat`. -/
def d (b : B) : M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b

@[simp]
lemma d_add (b b' : B) : D.d (b + b') = D.d b + D.d b' := by simp [d]

@[simp]
lemma d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b := by simp [d]

@[simp]
lemma d_map (a : A) : D.d (f a) = 0 :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

end Derivation

end ModuleCat

namespace CommRingCat

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

variable (f) in
/-- The module of differentials of a morphism `f : A ⟶ B` in the category `CommRingCat`. -/
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.hom.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

namespace KaehlerDifferential

variable (f) in
/-- The (universal) derivation in `(KaehlerDifferential f).Derivation f`
when `f : A ⟶ B` is a morphism in the category `CommRingCat`. -/
noncomputable def D : (KaehlerDifferential f).Derivation f :=
  letI := f.hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun b ↦ _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap

/-- When `f : A ⟶ B` is a morphism in the category `CommRingCat`, this is the
differential map `B → KaehlerDifferential f`. -/
noncomputable abbrev d (b : B) : KaehlerDifferential f := (D f).d b

@[ext]
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (d b) = β (d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ ≤ LinearMap.ker (α - β).hom := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ModuleCat.hom_sub, LinearMap.sub_apply, sub_eq_zero]
    apply h
  rw [top_le_iff, LinearMap.ker_eq_top] at this
  ext : 1
  exact this

/-- The map `KaehlerDifferential f ⟶ (ModuleCat.restrictScalars g').obj (KaehlerDifferential f')`
induced by a commutative square (given by an equality `g ≫ f' = f ≫ g'`)
in the category `CommRingCat`. -/
noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f') :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f'))
  { toFun := fun x ↦ _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

end KaehlerDifferential

end CommRingCat

namespace ModuleCat.Derivation

variable {A B : CommRingCat.{u}} {f : A ⟶ B}
  {M : ModuleCat.{u} B} (D : M.Derivation f)

/-- Given `f : A ⟶ B` a morphism in the category `CommRingCat`, `M : ModuleCat B`,
and `D : M.Derivation f`, this is the induced
morphism `CommRingCat.KaehlerDifferential f ⟶ M`. -/
noncomputable def desc : CommRingCat.KaehlerDifferential f ⟶ M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  ofHom D.liftKaehlerDifferential

@[simp]
lemma desc_d (b : B) : D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b := by
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  apply D.liftKaehlerDifferential_comp_D

end ModuleCat.Derivation
