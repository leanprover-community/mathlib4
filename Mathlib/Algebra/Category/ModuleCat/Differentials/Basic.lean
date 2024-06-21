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
we introduce the definition `CommRingCat.KaehlerDifferential f : ModuleCat B`.

-/

universe u

open CategoryTheory

-- should be moved to `Algebra.Algebra.Defs`
section

lemma RingHom.isScalarTower_toAlgebra_comp {A B C : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (fac : g.comp f = h) :
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra h
    IsScalarTower A B C := by
  letI := RingHom.toAlgebra f
  letI := RingHom.toAlgebra g
  letI := RingHom.toAlgebra h
  constructor
  intro a b c
  change g (f a * b) * c = h a * (g b * c)
  simp only [← fac, map_mul, coe_comp, Function.comp_apply, mul_assoc]

lemma RingHom.smulCommClass_toAlgebra
    {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (g : B →+* C) (h : A →+* C)  :
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra h
    SMulCommClass A B C := by
  letI := RingHom.toAlgebra g
  letI := RingHom.toAlgebra h
  constructor
  intro a b c
  change h a * (g b * c) = g b * (h a * c)
  rw [← mul_assoc, mul_comm (h a) (g b), mul_assoc]

end

namespace CommRingCat

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

-- TODO(?): Define `ModuleCat.Derivation M f`

variable (f) in
/-- The module of differentials of a morphism `f : A ⟶ B` in the category `CommRingCat`. -/
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

namespace KaehlerDifferential

/-- When `f : A ⟶ B` is a morphism in the category `CommRingCat, this is the
differential map `B → KaehlerDifferential f`. -/
noncomputable def d (b : B) : KaehlerDifferential f :=
  letI := f.toAlgebra
  KaehlerDifferential.D A B b

@[simp]
lemma d_add (b b' : B) : d (f := f) (b + b') = d b + d b' := by simp [d]

@[simp]
lemma d_mul (b b' : B) : d (f := f) (b * b') = b • d b' + b' • d b := by simp [d]

@[simp]
lemma d_map (a : A) : d (f := f) (f a) = 0 := by
  letI := f.toAlgebra
  exact (KaehlerDifferential.D A B).map_algebraMap a

@[ext]
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (d b) = β (d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ ≤ LinearMap.ker (α - β) := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    apply h
  rw [top_le_iff, LinearMap.ker_eq_top] at this
  exact this

/-- The map `KaehlerDifferential f ⟶ (ModuleCat.restrictScalars g').obj (KaehlerDifferential f')`
induced by a commutative square (given by an equality `g ≫ f' = f ≫ g'`)
in the category `CommRingCat`. -/
noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g').obj (KaehlerDifferential f') :=
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (g ≫ f').toAlgebra
  have := RingHom.isScalarTower_toAlgebra_comp g f' _ rfl
  have := RingHom.isScalarTower_toAlgebra_comp f g' _ fac.symm
  have := RingHom.smulCommClass_toAlgebra g' f'
  { toFun := fun x ↦ _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (f'.comp g).toAlgebra
  have := RingHom.isScalarTower_toAlgebra_comp g f' _ rfl
  have := RingHom.isScalarTower_toAlgebra_comp f g' _ fac.symm
  have := RingHom.smulCommClass_toAlgebra g' f'
  exact _root_.KaehlerDifferential.map_D A A' B B' b

end KaehlerDifferential

end CommRingCat
