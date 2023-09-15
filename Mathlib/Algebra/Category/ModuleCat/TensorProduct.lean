/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor-Hom adjunction
Consider two commutative rings `R` and `S` and `X` and `(R, S)`-bimodule.
Consider the tensor functor `(X ⊗[R] .)` from the category of `R`-module to the category of
`S`-module and the hom functor `X →ₗ[S] .` from the category of `S`-module to the category of
`R`-module, they form an adjunction. In particular we have that
```
Hom_S(X⊗[R]Y, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```
-/

universe u u' v

open TensorProduct CategoryTheory

variable (R : Type u) (S : Type u') (X : Type v)
variable [CommRing R] [CommRing S]
variable [AddCommGroup X] [Module R X] [Module S X] [SMulCommClass R S X]

namespace ModuleCat

/--
Let `X` be an `(R,S)`-bimodule, then `(X ⊗[R] .)` is a functor from the category of `R`-modules
to category of `S`-modules.
-/
@[simps!]
def tensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj Y := ModuleCat.of S <| X ⊗[R] Y
  map {Y Y'} l := let L := TensorProduct.map LinearMap.id l
  { L with
    map_smul' := fun s x => x.induction_on
      (show L _ = s • L _ by rw [smul_zero, map_zero, smul_zero])
      (fun x y => show L _ = s • L _ by rw [smul_tmul', map_tmul, map_tmul, LinearMap.id_apply,
        smul_tmul', LinearMap.id_apply])
      (fun x y (hx : L _ = s • L _) (hy : L _ = s • L _) => show L _ = s • L _ by
        rw [smul_add, map_add, hx, hy, map_add, smul_add]) }
  map_id Y := LinearMap.ext fun x => FunLike.congr_fun TensorProduct.map_id x
  map_comp {Y₁ Y₂ Y₃} l₁₂ l₂₃ := LinearMap.ext fun x => by
    have eq1 := FunLike.congr_fun (TensorProduct.map_comp LinearMap.id LinearMap.id l₂₃ l₁₂) x
    rw [LinearMap.comp_id] at eq1
    exact eq1

instance (Z : ModuleCat.{v} S) : Module R (X →ₗ[S] Z) where
  smul r l :=
  { toFun := fun x => l <| r • x
    map_add' := fun x y => by dsimp; rw [smul_add, map_add]
    map_smul' := fun s x => by dsimp; rw [smul_comm, map_smul] }
  one_smul l := LinearMap.ext fun x => show l _ = _ by rw [one_smul]
  mul_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ by rw [mul_comm, mul_smul]
  smul_zero r := rfl
  smul_add r l₁ l₂ := LinearMap.ext fun x => show (l₁ + _) _ = _ by
    rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  add_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ + l _ by rw [add_smul, map_add]
  zero_smul l := LinearMap.ext fun x => show l _ = 0 by rw [zero_smul, map_zero]

@[simp] lemma smul_linearMap_apply {Z : ModuleCat.{v} S} (r : R) (l : X →ₗ[S] Z) (x : X) :
  (r • l) x = l (r • x) := rfl

/--
Let `X` be an `(R,S)`-bimodule, then `(X →ₗ[S] .)` is a functor from the category of `S`-modules
to category of `R`-modules.
-/
@[simps]
def homFunctor : ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj Z := ModuleCat.of R <| X →ₗ[S] Z
  map {Z₁ Z₂} l :=
  { toFun := (l ∘ₗ .)
    map_add' := fun x y => LinearMap.ext fun _ => by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [LinearMap.add_apply, map_add, LinearMap.add_apply, LinearMap.coe_comp,
        LinearMap.coe_comp, Function.comp_apply, Function.comp_apply]
    map_smul' := fun r L => by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [smul_linearMap_apply, smul_linearMap_apply, LinearMap.coe_comp, Function.comp_apply] }
  map_id Z := LinearMap.ext fun (L : _ →ₗ[S] Z) => by
    simp only [LinearMap.coe_comp, Function.comp_apply, Eq.ndrec, LinearMap.add_apply, id_eq,
      eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
      smul_linearMap_apply, LinearMap.coe_mk]
    erw [LinearMap.comp_id]
    rw [id_apply]
  map_comp {Z₁ Z₂ Z₃} L₁₂ L₂₃ := LinearMap.ext fun (L : X →ₗ[S] Z₁) => LinearMap.ext fun x => by
    simp only [LinearMap.coe_comp, Function.comp_apply, Eq.ndrec, LinearMap.add_apply, id_eq,
      eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
      smul_linearMap_apply, LinearMap.coe_mk]
    rw [comp_apply, comp_apply]
    rfl

end ModuleCat
