/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.LinearAlgebra.Finsupp

/-!
# Tensor-Hom adjunction
Consider two commutative rings `R` and `S` and `X` an `(R, S)`-bimodule.
Consider the tensor functor `(X ⊗[R] .)` from the category of `R`-module to the category of
`S`-module and the hom functor `X →ₗ[S] .` from the category of `S`-module to the category of
`R`-module. They form an adjunction. In particular we have that
```
Hom_S(X⊗[R]Y, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```

## Implementation notes

1. Order of arguments
```
Hom_S(Y⊗[R]X, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```
is perhaps more natural to work with because all the argument have the same order.
But currently mathlib4 does not know `Y⊗[R] X` is an `S`-module as well.

2. Why not use the [`Tower` file](Mathlib/LinearAlgebra/TensorProduct/Tower.lean`)

In our setting `X` is an `(R, S)` bimodule and `Y` an `R`-module and `Z` an `S`-module
so to use the `Tower` file, we need `S` to be an `R`-algebra which is a luxury we do not have.
But note that in `Tower` file, `curry` and `uncurry` are both tri-linear maps. So `Tower` file
allows interplay of 3 rings which is not allowed in this file.

-/

universe u u' v

open TensorProduct CategoryTheory

variable (R : Type u) (S : Type u') (X : Type v)
variable [CommRing R] [Ring S]
variable [AddCommGroup X] [Module R X] [Module S X] [SMulCommClass R S X]

namespace ModuleCat

/--
Let `X` be an `(R,S)`-bimodule. Then `(X ⊗[R] .)` is a functor from the category of `R`-modules
to the category of `S`-modules.
-/
@[simps!]
noncomputable def tensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj Y := ModuleCat.of S <| X ⊗[R] Y
  map {Y Y'} l :=
  { __ := l.lTensor _
    map_smul' := fun s x => x.induction_on (by aesop) (by aesop)
      fun _ _ (h : l.lTensor _ _ = s • l.lTensor _ _) (h' : l.lTensor _ _ = s • l.lTensor _ _) =>
        show l.lTensor _ _ = s • l.lTensor _ _ by rw [smul_add, map_add, h, h', map_add, smul_add] }
  map_id _ := LinearMap.ext fun x => FunLike.congr_fun TensorProduct.map_id x
  map_comp {_ _ _} l l' := LinearMap.ext fun x => by
    have eq1 := FunLike.congr_fun (TensorProduct.map_comp LinearMap.id LinearMap.id l' l) x
    rwa [LinearMap.comp_id] at eq1

open Bimodule

instance bimodule' (Z : ModuleCat.{v} S) : Module R (X →ₗ[S] Z) :=
  Module.fromOppositeModule

@[simp] lemma bimodule'_smul_apply  (Z : ModuleCat.{v} S) (r : R) (l : X →ₗ[S] Z) (x : X) :
  (r • l) x = l (r • x) := rfl

/--
Let `X` be an `(R,S)`-bimodule. Then `(X →ₗ[S] .)` is a functor from the category of `S`-modules
to the category of `R`-modules.
-/
@[simps]
def homFunctor : ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj Z := ModuleCat.of R <| X →ₗ[S] Z
  map {_ _} l :=
  { toFun := (l ∘ₗ .)
    map_add' := fun _ _ => LinearMap.ext fun _ => l.map_add _ _
    map_smul' := fun r L => LinearMap.ext fun x => rfl }
  map_id Z := LinearMap.ext fun (L : _ →ₗ[S] Z) => by aesop
  map_comp {Z _ _} _ _ := LinearMap.ext fun (L : X →ₗ[S] Z) => LinearMap.ext fun x => by aesop

variable {R S X}

/-- uncurry a map from a tensor product to a bilinear map-/
noncomputable def curry' {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S}
    (l : (tensorFunctor R S X).obj X' ⟶ Y) :
    X' ⟶ (homFunctor R S X).obj Y where
  toFun x' :=
    { toFun := (l <| . ⊗ₜ x')
      map_add' := fun _ _ => show l _ = l _ + l _ by rw [add_tmul _ _ x', map_add]
      map_smul' := fun s _ => show l _ = s • l _ by rw [← smul_tmul', map_smul] }
  map_add' := fun _ _ => LinearMap.ext fun _ => show l _ = l _ + l _ by rw [tmul_add, map_add]
  map_smul' := fun r _ => LinearMap.ext fun _ => show l _ = l (r • _ ⊗ₜ _) by
    rw [← smul_tmul, smul_tmul']

/-- curry a bilinear map into a map from tensor product -/
@[simps]
def uncurry' {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S} (l : X' →ₗ[R] (X →ₗ[S] Y)) :
    (X ⊗[R] X') →ₗ[S] Y :=
  let L : (X ⊗[R] X') →+ Y := (addConGen _).lift (FreeAddMonoid.lift fun p => l p.2 p.1) <|
    AddCon.addConGen_le fun
    | _, _, Eqv.of_zero_left _     => by aesop
    | _, _, Eqv.of_zero_right _    => by aesop
    | _, _, Eqv.of_add_left _ _ _  => by aesop
    | _, _, Eqv.of_add_right _ _ _ => by aesop
    | _, _, Eqv.of_smul r x x'     => by aesop
    | _, _, Eqv.add_comm _ _       => by simp [map_add, add_comm]
  { L with
    map_smul' := fun _ z => z.induction_on
      (by aesop) (fun _ _ => LinearMap.map_smul _ _ _) (by aesop) }

@[simp high]
lemma uncurry'_apply_tmul {X' : ModuleCat.{v} R} {Y : ModuleCat.{v} S} (l : X' →ₗ[R] (X →ₗ[S] Y))
    (x : X) (x' : X') : uncurry' l (x ⊗ₜ x') = l x' x := rfl

variable (R S X)
/-- The tensor functor is left adjoint to the hom functor. -/
noncomputable def tensorHomAdjunction : tensorFunctor R S X ⊣ homFunctor R S X :=
    Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
      { toFun := curry'
        invFun := uncurry'
        left_inv := fun _ => LinearMap.ext fun x => x.induction_on (by aesop) (by aesop) (by aesop)
        right_inv := fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl }
      homEquiv_naturality_left_symm := fun {_ _} _ _ _ => by
        refine' LinearMap.ext fun x => x.induction_on _ _ _ <;> aesop
      homEquiv_naturality_right := by aesop }

noncomputable instance : IsLeftAdjoint (tensorFunctor R S X) :=
⟨_, tensorHomAdjunction _ _ _⟩

noncomputable instance : IsRightAdjoint (homFunctor R S X) :=
⟨_, tensorHomAdjunction _ _ _⟩

noncomputable instance : Limits.PreservesColimits (tensorFunctor R S X) :=
Adjunction.leftAdjointPreservesColimits <| tensorHomAdjunction _ _ _

noncomputable instance : Limits.PreservesLimits (homFunctor R S X) :=
Adjunction.rightAdjointPreservesLimits <| tensorHomAdjunction _ _ _

instance : Functor.PreservesEpimorphisms (tensorFunctor R S X) :=
inferInstance

end ModuleCat

namespace TensorProduct

variable (R' : Type u) [CommRing R']
variable {M N : Type v} [AddCommGroup M] [AddCommGroup N]
variable [Module R' M] [Module R' N]

open ModuleCat
/--
Constructing an additive group map from a tensor product by lifting a bi-additive group map that is
compatible with scalar action.
-/
@[simps!]
noncomputable def toAddCommGroup {C : Type v} [AddCommGroup C]
    (b : M →+ (N →+ C)) (compatible_smul : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n)) :
    (M ⊗[R'] N) →+ C :=
  (((tensorHomAdjunction R' ℤ N).homEquiv (of R' M) (of ℤ C)).symm
      { toFun := fun m => (b m).toIntLinearMap
        map_add' := fun _ _ => by dsimp; rw [b.map_add]; rfl
        map_smul' := fun _ _ => LinearMap.ext fun _ => compatible_smul _ _ _ }).toAddMonoidHom.comp
    (TensorProduct.comm R' M N).toLinearMap.toAddMonoidHom

lemma toAddCommGroup_apply_tmul {C : Type v} [AddCommGroup C]
    (b : M →+ (N →+ C)) (compatible_smul : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n))
    (m : M) (n : N) :
    toAddCommGroup R' b compatible_smul (m ⊗ₜ n) = b m n := rfl

/--
Constructing an additive group map `M ⊗[R] N → C` by lifting a function from
`M × N → C` that is zero-preserving, additive in both arguments and compatible with scalar action.
-/
noncomputable def toAddCommGroup' {C : Type v} [AddCommGroup C]
  (b : M × N → C)
  (map_zero_left : ∀ (n : N), b (0, n) = 0)
  (map_zero_right : ∀ (m : M), b (m, 0) = 0)
  (map_add_left : ∀ (n : N) (m m' : M), b (m + m', n) = b (m, n) + b (m', n))
  (map_add_right : ∀ (m : M) (n n' : N), b (m, n + n') = b (m, n) + b (m, n'))
  (compatible_smul : ∀ (r : R') (m : M) (n : N), b ((r • m), n) = b (m, (r • n))) :
  (M ⊗[R'] N) →+ C :=
toAddCommGroup R'
  { toFun := fun m => ⟨⟨fun n => b (m, n), map_zero_right _⟩, map_add_right _⟩
    map_zero' := AddMonoidHom.ext fun _ => map_zero_left _
    map_add' := fun _ _ => AddMonoidHom.ext fun _ => map_add_left _ _ _ } compatible_smul

lemma toAddCommGroup'_apply_tmul {C : Type v} [AddCommGroup C]
    (b : M × N → C)
    (map_zero_left : ∀ (n : N), b (0, n) = 0)
    (map_zero_right : ∀ (m : M), b (m, 0) = 0)
    (map_add_left : ∀ (n : N) (m m' : M), b (m + m', n) = b (m, n) + b (m', n))
    (map_add_right : ∀ (m : M) (n n' : N), b (m, n + n') = b (m, n) + b (m, n'))
    (compatible_smul : ∀ (r : R') (m : M) (n : N), b ((r • m), n) = b (m, (r • n)))
    (m : M) (n : N) :
    toAddCommGroup' R' b map_zero_left map_zero_right map_add_left map_add_right compatible_smul
      (m ⊗ₜ n) = b (m, n) := rfl

end TensorProduct
