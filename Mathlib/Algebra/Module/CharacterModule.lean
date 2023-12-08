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
variable (M : Type (max uR uM)) [AddCommGroup M] [Module R M]
variable (N : Type (max uR uN)) [AddCommGroup N] [Module R N]
variable (D : Type (max uR uD)) [AddCommGroup D] [Module R D]
variable [injective_dual : Injective <| ModuleCat.of R D]

-- we really want to consider only injective modules
/--
If `M` is an `R`-module, its `D`-character module is defined to be the `Hom_R(M, D)`
-/
@[nolint unusedArguments]
def CharacterModule [Injective <| ModuleCat.of R D] : Type (max uR uM uD) := M →ₗ[R] D

instance : FunLike (CharacterModule.{uR, uM, uD} R M D) M (fun _ ↦ D) :=
  inferInstanceAs <| FunLike (M →ₗ[R] D) M _

instance : AddCommGroup (CharacterModule.{uR, uM, uD} R M D) :=
  inferInstanceAs <| AddCommGroup <| M →ₗ[R] D

instance : Module R (CharacterModule.{uR, uM, uD} R M D) :=
  LinearMap.module

instance : LinearMapClass (CharacterModule.{uR, uM, uD} R M D) R M D :=
  inferInstanceAs <| LinearMapClass (M →ₗ[R] D) R M D

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule.{uR, uM, uD} R M D) (r : R) (m : M) :
    (r • f) m = f (r • m) := by
  rw [LinearMap.smul_apply, f.map_smul]

variable {R M N}

/--
For a linear map `L : M → N`, `(· ∘ L)` defines map from `CharacterModule N` to `CharacterModule M`
-/
@[simps]
def LinearMap.characterify
    (L : M →ₗ[R] N)  :
    CharacterModule.{uR, uN, uD} R N D →ₗ[R] CharacterModule.{uR, uM, uD} R M D where
  toFun f := f ∘ₗ L
  map_add' _ _ := LinearMap.ext fun m ↦ by aesop
  map_smul' r c := LinearMap.ext fun m ↦ by
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, RingHom.id_apply]
    rw [CharacterModule.smul_apply, CharacterModule.smul_apply, LinearMap.comp_apply, c.map_smul,
      L.map_smul, c.map_smul]

lemma LinearMap.characterify_surjective_of_injective
    {L : M →ₗ[R] N}
    (inj : Function.Injective L) :
    Function.Surjective <| LinearMap.characterify.{uR, uM, uN, uD} D L := by
  rintro (g : _ →ₗ[_] _)
  let g'' : (ULift.{max uM uN uD uR} M) →ₗ[R] (ULift.{max uM uN uD uR} D) :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap
  let L'' : ULift.{max uM uN uD uR} M →ₗ[R] ULift.{max uM uN uD uR} N :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ L ∘ₗ ULift.moduleEquiv.toLinearMap
  let L' := ModuleCat.ofHom L''
  have m1 : Mono <| L'
  · rw [ModuleCat.mono_iff_injective]
    intro _ _ h
    exact ULift.down_inj |>.mp <| inj <| ULift.ext_iff _ _ |>.mp h

  let g' := ModuleCat.ofHom g''
  have : Injective (ModuleCat.of R <| ULift.{max uM uN uD uR} D)
  · exact ModuleCat.ulift_injective_of_injective.{uR, max uR uD, max uM uN uR uD} R D
  exact ⟨ULift.moduleEquiv.toLinearMap ∘ₗ Injective.factorThru g' L' ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap, FunLike.ext _ _ fun _ ↦ ULift.ext_iff _ _ |>.mp <|
      FunLike.congr_fun (Injective.comp_factorThru g' L') _⟩

variable (R)

/--
If `R` is a commutative ring, `M ↦ CharacterModule M` and `L ↦ (· ∘ L)` defines a contravariant
endofunctor on `R`-modules.
-/
@[simps!]
def CharacterModuleFunctor :
    (ModuleCat.{max uM uR, uR} R)ᵒᵖ ⥤ ModuleCat.{max uM uD uR, uR} R where
  obj M := ModuleCat.of R <| CharacterModule.{uR, uM, uD} R M.unop D
  map L := LinearMap.characterify.{uR, uM, uM, uD} D L.unop
  map_id {_} := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop
    {M N : (ModuleCat.{max uM uR, uR} R)ᵒᵖ}
    {L : M ⟶ N} (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor.{uR, uM, uD} R D).map L :=
  LinearMap.characterify_surjective_of_injective.{uR, uM, uM, uD} D hL

end CharacterModuleFunctor

namespace CharacterModule

/--
Equivalent modules have equivalent character modules
-/
@[simps!]
def cong (e : M ≃ₗ[R] N) :
    CharacterModule.{uR, uM, uD} R M D ≃ₗ[R] CharacterModule.{uR, uN, uD} R N D := by
  refine LinearEquiv.ofLinear
    (e.symm.toLinearMap.characterify D) (e.toLinearMap.characterify D) ?_ ?_ <;>
  refine LinearMap.ext <| fun _ ↦ LinearMap.ext fun _ ↦ ?_ <;>
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.characterify_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
  aesop

end CharacterModule
