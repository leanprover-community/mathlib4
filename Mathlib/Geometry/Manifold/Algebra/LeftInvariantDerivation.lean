/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivations for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `LeftInvariantDerivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

Note that one can also define a Lie algebra on the space of left-invariant vector fields
(see `instLieAlgebraGroupLieAlgebra`). For finite-dimensional `C^∞` real manifolds, the space of
derivations can be canonically identified with the tangent space, and we recover the same Lie
algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. The left-invariant vector fields should
therefore be favored to construct a theory of Lie groups in suitable generality.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open scoped LieGroup Manifold Derivation ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type*)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffMul I ∞ G] (g h : G)

/-- Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    ∀ g, 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 toDerivation) =
      Derivation.evalAt g toDerivation

variable {I G}

namespace LeftInvariantDerivation

instance : Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  ⟨toDerivation⟩

attribute [coe] toDerivation

theorem toDerivation_injective :
    Function.Injective (toDerivation : LeftInvariantDerivation I G → _) :=
  fun X Y h => by cases X; cases Y; congr

instance : FunLike (LeftInvariantDerivation I G) C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  coe f := f.toDerivation
  coe_injective' _ _ h := toDerivation_injective <| DFunLike.ext' h

instance : LinearMapClass (LeftInvariantDerivation I G) 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  map_add f := map_add f.1
  map_smulₛₗ f := map_smul f.1.1

variable {r : 𝕜} {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

theorem toFun_eq_coe : X.toFun = ⇑X :=
  rfl

theorem coe_injective :
    @Function.Injective (LeftInvariantDerivation I G) (_ → C^∞⟮I, G; 𝕜⟯) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
theorem ext (h : ∀ f, X f = Y f) : X = Y := DFunLike.ext _ _ h

variable (X Y f)

theorem coe_derivation :
    ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) :=
  rfl

/-- Premature version of the lemma. Prefer using `left_invariant` instead. -/
theorem left_invariant' :
    𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X :=
  left_invariant'' X g

protected theorem map_add : X (f + f') = X f + X f' := by simp

protected theorem map_zero : X 0 = 0 := by simp

protected theorem map_neg : X (-f) = -X f := by simp

protected theorem map_sub : X (f - f') = X f - X f' := by simp

protected theorem map_smul : X (r • f) = r • X f := by simp

@[simp]
theorem leibniz : X (f * f') = f • X f' + f' • X f :=
  X.leibniz' _ _

instance : Zero (LeftInvariantDerivation I G) :=
  ⟨⟨0, fun g => by simp only [map_zero]⟩⟩

instance : Inhabited (LeftInvariantDerivation I G) :=
  ⟨0⟩

instance : Add (LeftInvariantDerivation I G) where
  add X Y :=
    ⟨X + Y, fun g => by
      simp only [map_add, left_invariant']⟩

instance : Neg (LeftInvariantDerivation I G) where
  neg X := ⟨-X, fun g => by simp [left_invariant']⟩

instance : Sub (LeftInvariantDerivation I G) where
  sub X Y := ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]
theorem coe_add : ⇑(X + Y) = X + Y :=
  rfl

@[simp]
theorem coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0 :=
  rfl

@[simp]
theorem coe_neg : ⇑(-X) = -X :=
  rfl

@[simp]
theorem coe_sub : ⇑(X - Y) = X - Y :=
  rfl

@[simp, norm_cast]
theorem lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y :=
  rfl

@[simp, norm_cast]
theorem lift_zero :
    (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 :=
  rfl

instance hasNatScalar : SMul ℕ (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

instance hasIntScalar : SMul ℤ (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

instance : AddCommGroup (LeftInvariantDerivation I G) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance : SMul 𝕜 (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by
    simp only [LinearMap.map_smul_of_tower, map_smul]; rw [left_invariant']⟩

variable (r)

@[simp]
theorem coe_smul : ⇑(r • X) = r • ⇑X :=
  rfl

@[simp]
theorem lift_smul (k : 𝕜) : (k • X).1 = k • X.1 :=
  rfl

variable (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps]
def coeFnAddMonoidHom : LeftInvariantDerivation I G →+ C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩

variable {I G}

instance : Module 𝕜 (LeftInvariantDerivation I G) :=
  coe_injective.module _ (coeFnAddMonoidHom I G) coe_smul

/-- Evaluation at a point for left invariant derivations. Same thing as for generic global
derivations (`Derivation.evalAt`). -/
def evalAt : LeftInvariantDerivation I G →ₗ[𝕜] PointDerivation I g where
  toFun X := Derivation.evalAt g X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalAt_apply : evalAt g X f = (X f) g :=
  rfl

@[simp]
theorem evalAt_coe : Derivation.evalAt g ↑X = evalAt g X :=
  rfl

theorem left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g

set_option backward.isDefEq.respectTransparency false in
theorem evalAt_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X) := by
  ext f
  rw [← left_invariant, hfdifferential_apply, hfdifferential_apply, L_mul, fdifferential_comp,
    fdifferential_apply]
  simp only [ContMDiffMap.comp_apply, LinearMap.comp_apply]
  rw [fdifferential_apply, ← hfdifferential_apply (smoothLeftMul_one I h), left_invariant]

theorem comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) := by
  ext h
  rw [ContMDiffMap.comp_apply, L_apply, ← evalAt_apply, evalAt_mul, hfdifferential_apply,
    fdifferential_apply, evalAt_apply]

instance : Bracket (LeftInvariantDerivation I G) (LeftInvariantDerivation I G) where
  bracket X Y :=
    ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [hfdifferential_apply, fdifferential_apply, Derivation.evalAt_apply] at hX hY ⊢
      rw [comp_L] at hX hY
      rw [Derivation.commutator_apply, ContMDiffMap.coe_sub, Pi.sub_apply, coe_derivation]
      rw [coe_derivation] at hX hY ⊢
      rw [hX, hY]
      rfl⟩

@[simp]
theorem commutator_coe_derivation :
    ⇑⁅X, Y⁆ =
      (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
        Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  rfl

theorem commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
  rfl

instance : LieRing (LeftInvariantDerivation I G) where
  add_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_add X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, map_sub, Pi.add_apply]
    ring

instance : LieAlgebra 𝕜 (LeftInvariantDerivation I G) where
  lie_smul r Y Z := by
    ext1
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

end LeftInvariantDerivation
