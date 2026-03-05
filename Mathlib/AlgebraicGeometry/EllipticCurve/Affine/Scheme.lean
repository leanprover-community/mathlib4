/-
Copyright (c) 2024 David Kurniadi Angdinata All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Michael Stoll, Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Affine schemes associated to Weierstrass curves
-/

universe u

namespace WeierstrassCurve.Affine

open AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (W : Affine R) [W.IsElliptic] (A : Type u) [Nontrivial A]
  [CommRing A] [Algebra R A]

/-- The equivalence between the type of `A`-points of an elliptic curve `W` over `R` and the type of
morphisms from `Spec A` to `Spec R[W]` in the category of schemes over `Spec R`. -/
@[simps!]
noncomputable def pointEquivSpec :
    W⟮A⟯ ≃ WithZero {f : Spec (.of A) ⟶ Spec (.of W.CoordinateRing) //
      f ≫ Spec.algebraMap R W.CoordinateRing = Spec.algebraMap R A} :=
  pointEquiv .. |>.trans (Spec.homEquivAlgHom.trans <| AdjoinRoot.equivAevalAeval _ |>.trans <|
    Equiv.setCongr <| by simp_rw [map_polynomial, Polynomial.evalEval_algebraMap]).symm.optionCongr

end WeierstrassCurve.Affine
