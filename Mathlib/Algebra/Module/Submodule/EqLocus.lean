/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Submodule.Ker

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# The submodule of elements `x : M` such that `f x = g x`

## Main declarations

* `LinearMap.eqLocus`: the submodule of elements `x : M` such that `f x = g x`

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]

open Submodule

variable {τ₁₂ : R →+* R₂}

section

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

/-- A linear map version of `AddMonoidHom.eqLocusM` -/
def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: #8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }
#align linear_map.eq_locus LinearMap.eqLocus

@[simp]
theorem mem_eqLocus {x : M} {f g : F} : x ∈ eqLocus f g ↔ f x = g x :=
  Iff.rfl
#align linear_map.mem_eq_locus LinearMap.mem_eqLocus

theorem eqLocus_toAddSubmonoid (f g : F) :
    (eqLocus f g).toAddSubmonoid = (f : M →+ M₂).eqLocusM g :=
  rfl
#align linear_map.eq_locus_to_add_submonoid LinearMap.eqLocus_toAddSubmonoid

@[simp]
theorem eqLocus_eq_top {f g : F} : eqLocus f g = ⊤ ↔ f = g := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
theorem eqLocus_same (f : F) : eqLocus f f = ⊤ := eqLocus_eq_top.2 rfl
#align linear_map.eq_locus_same LinearMap.eqLocus_same

theorem le_eqLocus {f g : F} {S : Submodule R M} : S ≤ eqLocus f g ↔ Set.EqOn f g S := Iff.rfl

theorem eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g :=
  DFunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}

open Submodule

theorem eqLocus_eq_ker_sub (f g : M →ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g) :=
  SetLike.ext fun _ => sub_eq_zero.symm
#align linear_map.eq_locus_eq_ker_sub LinearMap.eqLocus_eq_ker_sub

end Ring

end LinearMap
