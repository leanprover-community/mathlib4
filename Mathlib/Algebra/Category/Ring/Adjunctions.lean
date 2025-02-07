/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/


noncomputable section

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingCat

/-- The free functor `Type u ⥤ CommRingCat` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α ℤ)
  map {X Y} f := ofHom (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl

-- The `simpNF` linter complains here, even though it is a `rfl` lemma,
-- because the implicit arguments on the left-hand side simplify via `dsimp`.
-- (That is, the left-hand side really is not in simp normal form.)
@[simp, nolint simpNF]
theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(free.map f) = ⇑(rename f) :=
  rfl

/-- The free-forgetful adjunction for commutative rings. -/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := fun f ↦ homEquiv f.hom
          invFun := fun f ↦ ofHom <| homEquiv.symm f
          left_inv := fun f ↦ congrArg ofHom (homEquiv.left_inv f.hom)
          right_inv := fun f ↦ homEquiv.right_inv f }
      homEquiv_naturality_left_symm := fun {_ _ Y} f g =>
        hom_ext <| RingHom.ext fun x ↦ eval₂_cast_comp f (Int.castRingHom Y) g x }

instance : (forget CommRingCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end CommRingCat
