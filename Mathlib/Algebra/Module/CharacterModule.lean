/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Algebra.Category.GroupCat.EpiMono

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (B : Type uB) [AddCommGroup B]

/--
the character module of abelian group `A` in unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`
-/
def CharacterModule : Type uA := A →+ (AddCircle (1 : ℚ))

namespace CharacterModule

instance : FunLike (CharacterModule A) A (AddCircle (1 : ℚ)) where
  coe c := c.toFun
  coe_injective' _ _ _ := by aesop

instance : LinearMapClass (CharacterModule A) ℤ A (AddCircle (1 : ℚ)) where
  map_add _ _ _ := by rw [AddMonoidHom.map_add]
  map_smulₛₗ _ _ _ := by rw [AddMonoidHom.map_zsmul, RingHom.id_apply]

instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A →+ _))

section module

variable [Module R A]  [Module R B]

instance : Module R (CharacterModule A) :=
  Module.compHom (A →+ _) (RingEquiv.toOpposite _ |>.toRingHom : R →+* Rᵈᵐᵃ)

variable {R A B}

@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Given an abelian group homomorphism `f : A → B`, then `f⋆(L) := L ∘ f` defines a linear map
between `B⋆` and `A⋆`
-/
@[simps] def dual (f : A →ₗ[R] B) : CharacterModule B →ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ by
    simp only [RingHom.id_apply, smul_apply]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, smul_apply]
    erw [smul_apply, f.map_smul]
    rfl

lemma dual_surjective_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective <| dual f :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

/--
Two isomorphic modules have isomorphic character modules.
-/
def congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B :=
  LinearEquiv.ofLinear
    (dual e.symm) (dual e)
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun a ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, dual_apply, LinearMap.id_coe, id_eq]
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      erw [e.apply_symm_apply])
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun a ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, dual_apply, LinearMap.id_coe, id_eq]
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      erw [e.symm_apply_apply])

open TensorProduct

/--
Any linear map `L : A → B⋆` induces a character in `(A ⊗ B)⋆` by `a ⊗ b ↦ L a b`
-/
@[simps] noncomputable def uncurry :
    (A →ₗ[R] CharacterModule B) →ₗ[R] CharacterModule (A ⊗[R] B) where
  toFun c := TensorProduct.liftAddHom c.toAddMonoidHom fun r a b ↦ by
    show c (r • a) b = c a (r • b)
    rw [c.map_smul, smul_apply]
  map_add' c c' := DFunLike.ext _ _ fun x ↦ by
    induction x using TensorProduct.induction_on
    · simp
    · dsimp
      rw [liftAddHom_tmul, AddMonoidHom.add_apply, liftAddHom_tmul, liftAddHom_tmul]
      rfl
    · aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ by
    induction x using TensorProduct.induction_on
    · simp
    · dsimp
      rw [liftAddHom_tmul]
      erw [smul_apply]
      rw [smul_tmul', smul_tmul, liftAddHom_tmul]
      rfl
    · aesop

/--
Any character `c` in `(A ⊗ B)⋆` induces a linear map `A → B⋆` by `a ↦ b ↦ c (a ⊗ b) `
-/
@[simps] noncomputable def curry :
    CharacterModule (A ⊗[R] B) →ₗ[R] (A →ₗ[R] CharacterModule B) where
  toFun c :=
  { toFun := fun a ↦ c.comp ((TensorProduct.mk R A B) a).toAddMonoidHom
    map_add' := fun a a' ↦ DFunLike.ext _ _ fun b ↦ by
      rw [AddMonoidHom.add_apply]
      repeat rw [AddMonoidHom.comp_apply]
      simp
    map_smul' := fun r a ↦ DFunLike.ext _ _ fun b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_apply]
      repeat rw [AddMonoidHom.comp_apply]
      simp }
  map_add' c c' := DFunLike.ext _ _ fun a ↦ DFunLike.ext _ _ fun b ↦ by
    dsimp
    repeat rw [AddMonoidHom.add_apply]
    repeat rw [AddMonoidHom.comp_apply]
    simp only [LinearMap.toAddMonoidHom_coe, mk_apply]
    rfl
  map_smul' r c := DFunLike.ext _ _ fun a ↦ DFunLike.ext _ _ fun b ↦ by
    dsimp
    repeat rw [AddMonoidHom.comp_apply]
    simp only [LinearMap.toAddMonoidHom_coe, mk_apply, map_smul]
    rw [smul_apply]

/--
Linear maps into a character module are exactly characters of tensor product.
-/
@[simps!] noncomputable def homEquiv :
    (A →ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (A ⊗[R] B) :=
  LinearEquiv.ofLinear uncurry curry
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun z ↦ by
      refine z.induction_on ?_ ?_ ?_ <;> aesop)
    (LinearMap.ext fun l ↦ DFunLike.ext _ _ fun _ ↦ by aesop)

end module

end CharacterModule
