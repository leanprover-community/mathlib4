/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
an `R`-lineara map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.charaterfy_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.exists_character_apply_ne_zero_of_ne_zero` : for nonzero `a ∈ M`, there is a
  character `c` in `M⋆` such that `c a` is nonzero as well.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uM uN uD
variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module R M]
variable (N : Type uN) [AddCommGroup N] [Module R N]
variable (D : Type uD) [AddCommGroup D] [Module R D]
variable [injective_dual : Module.Injective R D]

-- we really want to consider only injective modules
/--
If `M` is an `R`-module, its `D`-character module is defined to be the `Hom_R(M, D)`
-/
def CharacterModule := M →ₗ[R] D

instance : FunLike (CharacterModule R M D) M (fun _ ↦ D) :=
  inferInstanceAs <| FunLike (M →ₗ[R] D) M _

instance : AddCommGroup (CharacterModule R M D) :=
  inferInstanceAs <| AddCommGroup <| M →ₗ[R] D

instance : Module R (CharacterModule R M D) :=
  LinearMap.module

instance : LinearMapClass (CharacterModule R M D) R M D :=
  inferInstanceAs <| LinearMapClass (M →ₗ[R] D) R M D

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule R M D) (r : R) (m : M) :
    (r • f) m = f (r • m) := by
  rw [LinearMap.smul_apply, f.map_smul]

variable {R M N}

/--
For a linear map `L : M → N`, `(· ∘ L)` defines map from `CharacterModule N` to `CharacterModule M`
-/
@[simps]
def LinearMap.characterify
    (L : M →ₗ[R] N)  :
    CharacterModule R N D →ₗ[R] CharacterModule R M D where
  toFun f := f ∘ₗ L
  map_add' _ _ := LinearMap.ext fun m ↦ by aesop
  map_smul' r c := LinearMap.ext fun m ↦ by
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, RingHom.id_apply]
    rw [CharacterModule.smul_apply, CharacterModule.smul_apply, LinearMap.comp_apply, c.map_smul,
      L.map_smul, c.map_smul]

lemma LinearMap.characterify_surjective_of_injective [UnivLE.{uR, uD}]
    {L : M →ₗ[R] N}
    (inj : Function.Injective L) :
    Function.Surjective <| LinearMap.characterify D L :=
  Module.Baer.iff_injective.mpr injective_dual |>.extension_property L inj

variable (R)

/--
If `R` is a commutative ring, `M ↦ CharacterModule M` and `L ↦ (· ∘ L)` defines a contravariant
endofunctor on `R`-modules.
-/
@[simps!]
def CharacterModuleFunctor :
    (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R <| CharacterModule R M.unop D
  map L := LinearMap.characterify D L.unop
  map_id {_} := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop [UnivLE.{uR, uD}]
    {M N : (ModuleCat R)ᵒᵖ} {L : M ⟶ N} (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R D).map L :=
  LinearMap.characterify_surjective_of_injective D hL

end CharacterModuleFunctor

namespace CharacterModule

/--
Equivalent modules have equivalent character modules
-/
@[simps!]
def cong (e : M ≃ₗ[R] N) :
    CharacterModule R M D ≃ₗ[R] CharacterModule R N D := by
  refine LinearEquiv.ofLinear
    (e.symm.toLinearMap.characterify D) (e.toLinearMap.characterify D) ?_ ?_ <;>
  refine LinearMap.ext <| fun _ ↦ LinearMap.ext fun _ ↦ ?_ <;> aesop

end CharacterModule
