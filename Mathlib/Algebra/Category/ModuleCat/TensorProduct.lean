/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

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

open Bimodule

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
      rw [LinearMap.bimodule_smul_apply, LinearMap.bimodule_smul_apply, LinearMap.coe_comp,
        Function.comp_apply] }
  map_id Z := LinearMap.ext fun (L : _ →ₗ[S] Z) => by
    simp only [LinearMap.coe_comp, Function.comp_apply, Eq.ndrec, LinearMap.add_apply, id_eq,
      eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.bimodule_smul_apply, LinearMap.coe_mk]
    erw [LinearMap.comp_id]
    rw [id_apply]
  map_comp {Z₁ Z₂ Z₃} L₁₂ L₂₃ := LinearMap.ext fun (L : X →ₗ[S] Z₁) => LinearMap.ext fun x => by
    simp only [LinearMap.coe_comp, Function.comp_apply, Eq.ndrec, LinearMap.add_apply, id_eq,
      eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.bimodule_smul_apply, LinearMap.coe_mk]
    rw [comp_apply, comp_apply]
    rfl

variable {R S X}


/-- uncurry a map from a tensor product to a bilinear map-/
@[simps]
def uncurry' {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S} (l : (tensorFunctor R S X).obj X' ⟶ Y) :
    X' ⟶ (homFunctor R S X).obj Y where
  toFun x' :=
    { toFun := (l <| . ⊗ₜ x')
      map_add' := fun _ _ => show l _ = l _ + l _ by rw [add_tmul _ _ x', map_add]
      map_smul' := fun s _ => show l _ = s • l _ by rw [← smul_tmul', map_smul] }
  map_add' := fun _ _ => LinearMap.ext fun _ => show l _ = l _ + l _ by rw [tmul_add, map_add]
  map_smul' := fun r _ => LinearMap.ext fun _ => show l _ = l (r • _ ⊗ₜ _) by
    rw [← smul_tmul, smul_tmul']

/-- curry a bilinear map into a map from tensor product -/
def curry' {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S} (l : X' →ₗ[R] (X →ₗ[S] Y)) :
    (X ⊗[R] X') →ₗ[S] Y :=
  let L : (X ⊗[R] X') →+ Y := (addConGen _).lift (FreeAddMonoid.lift fun p => l p.2 p.1) <| AddCon.addConGen_le
    fun p q H => show _ = _ from match p, q, H with
    | _, _, Eqv.of_zero_left x => by
      simp only [homFunctor_obj, FreeAddMonoid.lift_eval_of, map_zero]
    | _, _, Eqv.of_zero_right _ => by
      simp only [homFunctor_obj, FreeAddMonoid.lift_eval_of, map_zero, LinearMap.zero_apply]
    | _, _, Eqv.of_add_left _ _ _ => by
      simp only [homFunctor_obj, map_add, FreeAddMonoid.lift_eval_of]
    | _, _, Eqv.of_add_right _ _ _ => by
      simp only [homFunctor_obj, map_add, FreeAddMonoid.lift_eval_of, LinearMap.add_apply]
    | _, _, Eqv.of_smul _ _ _ => by
      simp [l.map_smul, LinearMap.bimodule_smul_apply]
    | _, _, Eqv.add_comm p q => by
      simp [map_add, add_comm]
  { L with
    map_smul' := fun r z => by
      refine z.induction_on ?_ ?_ ?_
      · rw [smul_zero]
        convert L.map_zero
        convert smul_zero _
      · intro x x'
        rw [smul_tmul']
        simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
        rw [tmul, AddCon.lift_mk', tmul, AddCon.lift_mk', FreeAddMonoid.lift_eval_of, map_smul,
          FreeAddMonoid.lift_eval_of]
      · rintro _ _ (h : L _ = r • L _) (h' : L _ = r • L _)
        show L _ = r • L _
        rw [smul_add, map_add, map_add, smul_add, h, h'] }

@[simp]
lemma curry'_apply_tmul {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S} (l : X' →ₗ[R] (X →ₗ[S] Y))
  (x : X) (x' : X') : curry' l (x ⊗ₜ x') = l x' x := rfl

variable (R S X)
/-- The tensoring function is left adjoint to the hom functor. -/
def tensorHomAdjunction : tensorFunctor R S X ⊣ homFunctor R S X :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun X' Y =>
    { toFun := uncurry'
      invFun := curry'
      left_inv := fun l => LinearMap.ext fun x => x.induction_on (by simp only [map_zero])
        (fun _ _ => by erw [curry'_apply_tmul, uncurry'_apply_apply])
        (fun _ _ h₁ h₂ => by rw [map_add, h₁, h₂, map_add])
      right_inv := fun l => LinearMap.ext fun x => LinearMap.ext fun z => by
        rw [uncurry'_apply_apply, curry'_apply_tmul]
        rfl }
    homEquiv_naturality_left_symm := fun {X' X''} Y f g => by
      simp only [homFunctor_obj, Equiv.coe_fn_symm_mk]
      refine LinearMap.ext fun x => x.induction_on ?_ ?_ ?_
      · rw [map_zero, map_zero]
      · intro x x'
        rw [curry'_apply_tmul, comp_apply, comp_apply, tensorFunctor_map_apply]
        erw [curry'_apply_tmul]
      · intro _ _ hx hy
        rw [map_add, hx, hy, map_add]
    homEquiv_naturality_right := fun {X' Y Y'} f g => by
      simp only [homFunctor_obj, Equiv.coe_fn_mk]
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      rw [uncurry'_apply_apply, comp_apply, comp_apply, homFunctor_map_apply, LinearMap.comp_apply,
        uncurry'_apply_apply] }

instance : IsLeftAdjoint (tensorFunctor R S X) :=
⟨_, tensorHomAdjunction _ _ _⟩

instance : IsRightAdjoint (homFunctor R S X) :=
⟨_, tensorHomAdjunction _ _ _⟩

instance : Limits.PreservesColimits (tensorFunctor R S X) :=
Adjunction.leftAdjointPreservesColimits <| tensorHomAdjunction _ _ _

instance : Limits.PreservesLimits (homFunctor R S X) :=
Adjunction.rightAdjointPreservesLimits <| tensorHomAdjunction _ _ _

example : Functor.PreservesEpimorphisms (tensorFunctor R S X) :=
inferInstance

end ModuleCat
