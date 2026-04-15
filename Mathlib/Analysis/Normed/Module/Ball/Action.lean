/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/

@[expose] public section


open Metric Set

variable {𝕜 𝕜' E : Type*} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] {r : ℝ}

section ClosedBall

instance : SMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closedBall_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩

instance mulActionClosedBallBall : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  one_smul _c₂ := Subtype.ext <| one_smul 𝕜 _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _

instance continuousSMul_closedBall_ball : ContinuousSMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

instance : SMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_closedBall_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closedBall_zero_iff.1 c.2) (mem_closedBall_zero_iff.1 x.2) (norm_nonneg _)
            zero_le_one⟩

instance mulActionClosedBallClosedBall :
    MulAction (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul 𝕜 _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _

instance continuousSMul_closedBall_closedBall :
    ContinuousSMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end ClosedBall

section Sphere

instance : SMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x

instance mulActionSphereBall : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _

instance continuousSMul_sphere_ball : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

instance : SMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x

instance mulActionSphereClosedBall : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _

instance continuousSMul_sphere_closedBall :
    ContinuousSMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

instance : SMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop,
          one_mul]⟩

instance mulActionSphereSphere : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _

instance continuousSMul_sphere_sphere : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

instance isScalarTower_closedBall_closedBall_closedBall :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_closedBall_closedBall_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_closedBall_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_closedBall_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_sphere_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_sphere_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_sphere_sphere :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance isScalarTower_sphere_ball_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance isScalarTower_closedBall_ball_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

end IsScalarTower

section SMulCommClass

variable [SMulCommClass 𝕜 𝕜' E]

instance instSMulCommClass_closedBall_closedBall_closedBall :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_closedBall_closedBall_ball :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_sphere_closedBall_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_sphere_closedBall_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] :
    SMulCommClass (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance instSMulCommClass_sphere_sphere_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_sphere_sphere_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance instSMulCommClass_sphere_sphere_sphere :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

end SMulCommClass

variable (𝕜)
variable [CharZero 𝕜]

include 𝕜 in
theorem ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : sphere (0 : E) r) : x ≠ -x :=
  have : IsAddTorsionFree E := .of_isTorsionFree 𝕜 E
  fun h => ne_zero_of_mem_sphere hr x (self_eq_neg.mp (by (conv_lhs => rw [h]); rfl))

include 𝕜 in
theorem ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x
