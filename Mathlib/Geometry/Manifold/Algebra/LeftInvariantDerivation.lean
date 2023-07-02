/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.algebra.left_invariant_derivation
! leanprover-community/mathlib commit b608348ffaeb7f557f2fd46876037abafd326ff3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivation for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `left_invariant_derivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

-/


noncomputable section

open scoped LieGroup Manifold Derivation

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type _)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [SmoothMul I G] (g h : G)

-- Generate trivial has_sizeof instance. It prevents weird type class inference timeout problems
@[local nolint instance_priority, local instance 10000]
private def disable_has_sizeof {α} : SizeOf α :=
  ⟨fun _ => 0⟩

/-- Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    ∀ g,
      𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 to_derivation) =
        Derivation.evalAt g to_derivation
#align left_invariant_derivation LeftInvariantDerivation

variable {I G}

namespace LeftInvariantDerivation

instance : Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  ⟨fun X => X.toDerivation⟩

instance : CoeFun (LeftInvariantDerivation I G) fun _ => C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨fun X => X.toDerivation.toFun⟩

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {x : M} {r : 𝕜}
  {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

theorem toFun_eq_coe : X.toFun = ⇑X :=
  rfl
#align left_invariant_derivation.to_fun_eq_coe LeftInvariantDerivation.toFun_eq_coe

theorem coe_to_linearMap : ⇑(X : C^∞⟮I, G; 𝕜⟯ →ₗ[𝕜] C^∞⟮I, G; 𝕜⟯) = X :=
  rfl
#align left_invariant_derivation.coe_to_linear_map LeftInvariantDerivation.coe_to_linearMap

@[simp]
theorem toDerivation_eq_coe : X.toDerivation = X :=
  rfl
#align left_invariant_derivation.to_derivation_eq_coe LeftInvariantDerivation.toDerivation_eq_coe

theorem coe_injective :
    @Function.Injective (LeftInvariantDerivation I G) (_ → C^⊤⟮I, G; 𝕜⟯) coeFn := fun X Y h => by
  cases X; cases Y; congr; exact Derivation.coe_injective h
#align left_invariant_derivation.coe_injective LeftInvariantDerivation.coe_injective

@[ext]
theorem ext (h : ∀ f, X f = Y f) : X = Y :=
  coe_injective <| funext h
#align left_invariant_derivation.ext LeftInvariantDerivation.ext

variable (X Y f)

theorem coe_derivation :
    ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) :=
  rfl
#align left_invariant_derivation.coe_derivation LeftInvariantDerivation.coe_derivation

theorem coe_derivation_injective :
    Function.Injective
      (coe : LeftInvariantDerivation I G → Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  fun X Y h => by cases X; cases Y; congr; exact h
#align left_invariant_derivation.coe_derivation_injective LeftInvariantDerivation.coe_derivation_injective

/-- Premature version of the lemma. Prefer using `left_invariant` instead. -/
theorem left_invariant' :
    𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X :=
  left_invariant'' X g
#align left_invariant_derivation.left_invariant' LeftInvariantDerivation.left_invariant'

@[simp]
theorem map_add : X (f + f') = X f + X f' :=
  Derivation.map_add X f f'
#align left_invariant_derivation.map_add LeftInvariantDerivation.map_add

@[simp]
theorem map_zero : X 0 = 0 :=
  Derivation.map_zero X
#align left_invariant_derivation.map_zero LeftInvariantDerivation.map_zero

@[simp]
theorem map_neg : X (-f) = -X f :=
  Derivation.map_neg X f
#align left_invariant_derivation.map_neg LeftInvariantDerivation.map_neg

@[simp]
theorem map_sub : X (f - f') = X f - X f' :=
  Derivation.map_sub X f f'
#align left_invariant_derivation.map_sub LeftInvariantDerivation.map_sub

@[simp]
theorem map_smul : X (r • f) = r • X f :=
  Derivation.map_smul X r f
#align left_invariant_derivation.map_smul LeftInvariantDerivation.map_smul

@[simp]
theorem leibniz : X (f * f') = f • X f' + f' • X f :=
  X.leibniz' _ _
#align left_invariant_derivation.leibniz LeftInvariantDerivation.leibniz

instance : Zero (LeftInvariantDerivation I G) :=
  ⟨⟨0, fun g => by simp only [LinearMap.map_zero, Derivation.coe_zero]⟩⟩

instance : Inhabited (LeftInvariantDerivation I G) :=
  ⟨0⟩

instance : Add (LeftInvariantDerivation I G)
    where add X Y :=
    ⟨X + Y, fun g => by
      simp only [LinearMap.map_add, Derivation.coe_add, left_invariant', Pi.add_apply]⟩

instance : Neg (LeftInvariantDerivation I G) where neg X := ⟨-X, fun g => by simp [left_invariant']⟩

instance : Sub (LeftInvariantDerivation I G)
    where sub X Y := ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]
theorem coe_add : ⇑(X + Y) = X + Y :=
  rfl
#align left_invariant_derivation.coe_add LeftInvariantDerivation.coe_add

@[simp]
theorem coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0 :=
  rfl
#align left_invariant_derivation.coe_zero LeftInvariantDerivation.coe_zero

@[simp]
theorem coe_neg : ⇑(-X) = -X :=
  rfl
#align left_invariant_derivation.coe_neg LeftInvariantDerivation.coe_neg

@[simp]
theorem coe_sub : ⇑(X - Y) = X - Y :=
  rfl
#align left_invariant_derivation.coe_sub LeftInvariantDerivation.coe_sub

@[simp, norm_cast]
theorem lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y :=
  rfl
#align left_invariant_derivation.lift_add LeftInvariantDerivation.lift_add

@[simp, norm_cast]
theorem lift_zero :
    (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 :=
  rfl
#align left_invariant_derivation.lift_zero LeftInvariantDerivation.lift_zero

instance hasNatScalar : SMul ℕ (LeftInvariantDerivation I G)
    where smul r X := ⟨r • X, fun g => by simp_rw [LinearMap.map_smul_of_tower, left_invariant']⟩
#align left_invariant_derivation.has_nat_scalar LeftInvariantDerivation.hasNatScalar

instance hasIntScalar : SMul ℤ (LeftInvariantDerivation I G)
    where smul r X := ⟨r • X, fun g => by simp_rw [LinearMap.map_smul_of_tower, left_invariant']⟩
#align left_invariant_derivation.has_int_scalar LeftInvariantDerivation.hasIntScalar

instance : AddCommGroup (LeftInvariantDerivation I G) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance : SMul 𝕜 (LeftInvariantDerivation I G)
    where smul r X := ⟨r • X, fun g => by simp_rw [LinearMap.map_smul, left_invariant']⟩

variable (r X)

@[simp]
theorem coe_smul : ⇑(r • X) = r • X :=
  rfl
#align left_invariant_derivation.coe_smul LeftInvariantDerivation.coe_smul

@[simp]
theorem lift_smul (k : 𝕜) : (↑(k • X) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = k • X :=
  rfl
#align left_invariant_derivation.lift_smul LeftInvariantDerivation.lift_smul

variable (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps]
def coeFnAddMonoidHom : LeftInvariantDerivation I G →+ C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨fun X => X.toDerivation.toFun, coe_zero, coe_add⟩
#align left_invariant_derivation.coe_fn_add_monoid_hom LeftInvariantDerivation.coeFnAddMonoidHom

variable {I G}

instance : Module 𝕜 (LeftInvariantDerivation I G) :=
  coe_injective.Module _ (coeFnAddMonoidHom I G) coe_smul

/-- Evaluation at a point for left invariant derivation. Same thing as for generic global
derivations (`derivation.eval_at`). -/
def evalAt : LeftInvariantDerivation I G →ₗ[𝕜] PointDerivation I g where
  toFun X := Derivation.evalAt g ↑X
  map_add' X Y := rfl
  map_smul' k X := rfl
#align left_invariant_derivation.eval_at LeftInvariantDerivation.evalAt

theorem evalAt_apply : evalAt g X f = (X f) g :=
  rfl
#align left_invariant_derivation.eval_at_apply LeftInvariantDerivation.evalAt_apply

@[simp]
theorem evalAt_coe : Derivation.evalAt g ↑X = evalAt g X :=
  rfl
#align left_invariant_derivation.eval_at_coe LeftInvariantDerivation.evalAt_coe

theorem left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g
#align left_invariant_derivation.left_invariant LeftInvariantDerivation.left_invariant

theorem evalAt_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X) := by ext f;
  rw [← left_invariant, apply_hfdifferential, apply_hfdifferential, L_mul, fdifferential_comp,
    apply_fdifferential, LinearMap.comp_apply, apply_fdifferential, ← apply_hfdifferential,
    left_invariant]
#align left_invariant_derivation.eval_at_mul LeftInvariantDerivation.evalAt_mul

theorem comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) := by
  ext h <;>
    rw [ContMDiffMap.comp_apply, L_apply, ← eval_at_apply, eval_at_mul, apply_hfdifferential,
      apply_fdifferential, eval_at_apply]
#align left_invariant_derivation.comp_L LeftInvariantDerivation.comp_L

instance : Bracket (LeftInvariantDerivation I G) (LeftInvariantDerivation I G)
    where bracket X Y :=
    ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [apply_hfdifferential, apply_fdifferential, Derivation.evalAt_apply] at hX hY ⊢
      rw [comp_L] at hX hY 
      rw [Derivation.commutator_apply, SmoothMap.coe_sub, Pi.sub_apply, coe_derivation]
      rw [coe_derivation] at hX hY ⊢
      rw [hX, hY]
      rfl⟩

@[simp]
theorem commutator_coe_derivation :
    ⇑⁅X, Y⁆ =
      (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
        Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  rfl
#align left_invariant_derivation.commutator_coe_derivation LeftInvariantDerivation.commutator_coe_derivation

theorem commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
  rfl
#align left_invariant_derivation.commutator_apply LeftInvariantDerivation.commutator_apply

instance : LieRing (LeftInvariantDerivation I G) where
  add_lie X Y Z := by
    ext1;
    simp only [commutator_apply, coe_add, Pi.add_apply, LinearMap.map_add,
      LeftInvariantDerivation.map_add]
    ring
  lie_add X Y Z := by
    ext1;
    simp only [commutator_apply, coe_add, Pi.add_apply, LinearMap.map_add,
      LeftInvariantDerivation.map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1; simp only [commutator_apply, coe_add, coe_sub, map_sub, Pi.add_apply]
    ring

instance : LieAlgebra 𝕜 (LeftInvariantDerivation I G)
    where lie_smul r Y Z := by ext1;
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

end LeftInvariantDerivation

