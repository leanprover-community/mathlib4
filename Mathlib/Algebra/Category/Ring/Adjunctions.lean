/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.CategoryTheory.Adjunction.Over

/-!
# Adjunctions in `CommRingCat`

## Main results
- `CommRingCat.adj`: `σ ↦ ℤ[σ]` is left adjoint to the forgetful functor `CommRingCat ⥤ Type`.
- `CommRingCat.coyonedaAdj`: `Fun(-, R)` is left adjoint to `Hom_{CRing}(R, -)`.
- `CommRingCat.monoidAlgebraAdj`: `G ↦ R[G]` as `CommGrp ⥤ R-Alg` is left adjoint to `S ↦ Sˣ`.
- `CommRingCat.unitsAdj`: `G ↦ ℤ[G]` is left adjoint to `S ↦ Sˣ`.

-/

noncomputable section

universe v u

open MvPolynomial Opposite

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

/-- `Fun(-, -)` as a functor `Type vᵒᵖ ⥤ CommRingCat ⥤ CommRingCat`. -/
@[simps]
def coyoneda : Type vᵒᵖ ⥤ CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj n :=
  { obj R := CommRingCat.of ((unop n) → R)
    map {R S} φ := CommRingCat.ofHom (Pi.ringHom (φ.hom.comp <| Pi.evalRingHom _ ·)) }
  map {m n} f :=
  { app R := CommRingCat.ofHom (Pi.ringHom (Pi.evalRingHom _ <| f.unop ·)) }

/-- The adjunction `Hom_{CRing}(Fun(n, R), S) ≃ Fun(n, Hom_{CRing}(R, S))`. -/
def coyonedaAdj (R : CommRingCat.{u}) :
    (coyoneda.flip.obj R).rightOp ⊣ yoneda.obj R where
  unit := { app n i := CommRingCat.ofHom (Pi.evalRingHom _ i) }
  counit := { app S := (CommRingCat.ofHom (Pi.ringHom fun f ↦ f.hom)).op }

instance (R : CommRingCat.{u}) : (yoneda.obj R).IsRightAdjoint := ⟨_, ⟨coyonedaAdj R⟩⟩

/-- If `n` is a singleton, `Hom(n, -)` is the identity in `CommRingCat`. -/
@[simps!]
def coyonedaUnique {n : Type v} [Unique n] : coyoneda.obj (op n) ≅ 𝟭 CommRingCat.{max u v} :=
  NatIso.ofComponents (fun X ↦ (RingEquiv.piUnique _).toCommRingCatIso) (fun f ↦ by ext; simp)

/-- The units functor `R ↦ Rˣ`. -/
@[simps]
def units : CommRingCat.{u} ⥤ CommGrp.{u} where
  obj R := CommGrp.of Rˣ
  map f := CommGrp.ofHom (Units.map f.hom)

/-- The monoid algebra functor `CommGrp ⥤ R-Alg` given by `G ↦ R[G]`. -/
@[simps]
def monoidAlgebra (R : CommRingCat.{max u v}) : CommGrp.{v} ⥤ Under R where
  obj G := Under.mk (CommRingCat.ofHom (MonoidAlgebra.singleOneRingHom (k := R) (G := G)))
  map f := Under.homMk (CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom R f.hom)
  map_comp f g := by ext : 2; apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

/-- The adjunction `G ↦ R[G]` and `S ↦ Sˣ` between `CommGrp` and `R-Alg`. -/
def monoidAlgebraAdj (R : CommRingCat.{u}) :
    monoidAlgebra R ⊣ Under.forget R ⋙ units where
  unit := { app G := CommGrp.ofHom (MonoidAlgebra.of R G).toHomUnits }
  counit :=
  { app S := Under.homMk (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom S.hom.hom
      (Units.coeHom S.right) (fun _ _ ↦ .all _ _))) (by ext; simp [MonoidAlgebra.liftNCRingHom])
    naturality S T f := by
      ext : 2
      apply MonoidAlgebra.ringHom_ext <;>
        intro <;> simp [MonoidAlgebra.liftNCRingHom, ← Under.w f, - Under.w] }
  left_triangle_components G := by
    ext : 2
    apply MonoidAlgebra.ringHom_ext <;> intro <;> simp [MonoidAlgebra.liftNCRingHom]
  right_triangle_components S := by dsimp [units]; ext; simp [MonoidAlgebra.liftNCRingHom]

/-- The adjunction `G ↦ ℤ[G]` and `R ↦ Rˣ` between `CommGrp` and `CommRing`. -/
def unitsAdj {R : CommRingCat.{u}} (hR : Limits.IsInitial R) :
    monoidAlgebra R ⋙ Under.forget R ⊣ units :=
  (monoidAlgebraAdj R).comp (Under.equivalenceOfIsInitial hR).toAdjunction

instance (R : CommRingCat) : (monoidAlgebra.{u, u} R).IsLeftAdjoint :=
  ⟨_, ⟨CommRingCat.monoidAlgebraAdj R⟩⟩

instance : CommRingCat.units.IsRightAdjoint :=
  ⟨_, ⟨CommRingCat.unitsAdj Limits.initialIsInitial⟩⟩

end CommRingCat
