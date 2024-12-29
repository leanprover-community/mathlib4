/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.RingTheory.OreLocalization.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!

# Group instances of Ore Localizations

The Ore localization of a monoid by itself is endowed with a group structure

-/

section Self

class CommonLeftMultipleMonoid (M : Type*) extends Monoid M where
  cl₁ : M → M → M
  cl₂ : M → M → M
  cl_spec : ∀ a b : M, cl₂ a b * a = cl₁ a b * b

class OreMonoid (M : Type*) extends CommonLeftMultipleMonoid M, CancelMonoid M

variable {M : Type*} [OreMonoid M]

instance oreSetSelf : OreLocalization.OreSet (⊤ : Submonoid M) where
  ore_right_cancel  := by
    intro r1 r2 s eq
    use 1
    simp only [OneMemClass.coe_one, one_mul]
    exact mul_right_cancel eq
  oreNum r s := CommonLeftMultipleMonoid.cl₁ r s
  oreDenom r s := ⟨CommonLeftMultipleMonoid.cl₂ r s, trivial⟩
  ore_eq := fun r s => CommonLeftMultipleMonoid.cl_spec _ _

local notation "OreLocalizationSelf" => @OreLocalization M _ (⊤ : Submonoid M) _ M _

/-- when localizing by the entire monoid, the result is a group -/
instance group_of_self : Group (OreLocalizationSelf) where
  inv := OreLocalization.liftExpand (fun a b => b.val /ₒ ⟨a, trivial⟩)
    fun a b c d => by
      apply OreLocalization.oreDiv_eq_iff.mpr
      use 1, b
      simp
  inv_mul_cancel := OreLocalization.ind fun _ _ => OreLocalization.mul_inv _ _

/-- simplified universal property when localizing by the entire monoid -/
def toGroup {G₁ : Type} [Group G₁] (f : M →* G₁) :
    OreLocalizationSelf →* G₁ :=
  OreLocalization.universalMulHom f
  ⟨⟨(fun (x : ↥((⊤ : Submonoid M))) => toUnits (f x.val)),
  by simp only [OneMemClass.coe_one, map_one]⟩, by simp only
  [Submonoid.coe_mul, map_mul, Subtype.forall, implies_true, forall_const]⟩
  (by intro s ; simp)

/-- uniqueness of the simplified universal property when localizing by the entire monoid -/
theorem toGroup_unique {G₁ : Type} [Group G₁] (f : M →* G₁)
    (φ : OreLocalizationSelf →* G₁)
    (h : ∀ (r : M), (φ ∘ OreLocalization.numeratorHom) r = f r)
    : φ = toGroup f :=
  OreLocalization.universalMulHom_unique f _ _ _ h

end Self
