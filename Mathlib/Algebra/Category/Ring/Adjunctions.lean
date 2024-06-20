/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

#align_import algebra.category.Ring.adjunctions from "leanprover-community/mathlib"@"79ffb5563b56fefdea3d60b5736dad168a9494ab"

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/


noncomputable section

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingCat
set_option linter.uppercaseLean3 false -- `CommRing`

open scoped Classical

/-- The free functor `Type u ⥤ CommRingCat` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α ℤ)
  map {X Y} f := (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it
  -- generates are too slow.
  map_id _ := RingHom.ext <| rename_id
  map_comp f g := RingHom.ext fun p => (rename_rename f g p).symm
#align CommRing.free CommRingCat.free

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl
#align CommRing.free_obj_coe CommRingCat.free_obj_coe

-- Porting note: `simpNF` should not trigger on `rfl` lemmas.
-- see https://github.com/leanprover/std4/issues/86
@[simp, nolint simpNF]
theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(free.map f) = ⇑(rename f) :=
  rfl
#align CommRing.free_map_coe CommRingCat.free_map_coe

/-- The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X R => homEquiv
      homEquiv_naturality_left_symm := fun {_ _ Y} f g =>
        RingHom.ext fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }
#align CommRing.adj CommRingCat.adj

instance : (forget CommRingCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end CommRingCat
