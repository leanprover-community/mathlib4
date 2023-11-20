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
Consider two commutative rings `R` and `S` and `X` an `(S, R)`-bimodule.
Consider the tensor functor `(X ⊗[R] ·)` from the category of left `R`-module to the category of
left `S`-module and the hom functor `(X →ₗ[S] ·)` from the category of left `S`-module to the
category of left `R`-module. They form an adjunction. In particular we have that
```
Hom_S(X⊗[R]Y, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```

## Implementation notes

1. Order of arguments
```
Hom_S(Y⊗[R]X, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```
is perhaps more natural to work with because all the argument have the same order.
But currently mathlib4 does not know `Y⊗[R] X` is an right `S`-module as well.

2. Why not use the [`Tower` file](Mathlib/LinearAlgebra/TensorProduct/Tower.lean`)

In our setting `X` is an `(R, S)`-bimodule and `Y` an `R`-module and `Z` an `S`-module
so to use the `Tower` file, we need `S` to be an `R`-algebra which is a luxury we do not have.
But note that in `Tower` file, `curry` and `uncurry` are both tri-linear maps. So `Tower` file
allows interplay of 3 rings which is not allowed in this file.

-/

universe u u' v v' v''

open TensorProduct CategoryTheory

variable (R : Type u) (S : Type u') (X : Type v)
variable [CommRing R] [Ring S]
variable [AddCommGroup X] [Module Rᵐᵒᵖ X] [Module S X] [SMulCommClass S Rᵐᵒᵖ X]

open MulOpposite

instance leftMod_eq_rightMod : Module R X :=
  Module.compHom X ((RingHom.id R).toOpposite fun _ _ => mul_comm _ _)

section

variable {Y : Type v'} [AddCommGroup Y] [Module R Y]

noncomputable local instance tensorModSMul :
    SMul S (X ⊗[R] Y) where
  smul := fun s => map
    { toFun := (s • ·)
      map_add' := smul_add _
      map_smul' := fun r x => by
        show s • (op r) • x = (op r) • s • x
        exact smul_comm _ _ _ } LinearMap.id

@[simp] private lemma tensorModSMul_smul_tmul
  (s : S) (x : X) (y : Y) : s • (x ⊗ₜ[R] y) = (s • x) ⊗ₜ[R] y := rfl

@[simp] private lemma tensorModSMul_one_smul
    (z : X ⊗[R] Y) :
    (1 : S) • z = z :=
  z.induction_on rfl
    (fun x y => by rw [tensorModSMul_smul_tmul, one_smul])
    (fun _ _ h h' => show map _ _ (_ + _) = _ by
      simpa only [map_add] using congr_arg₂ (· + ·) h h')

private lemma tensorModSMul_mul_smul
    (s s' : S)
    (z : X ⊗[R] Y) :
    (s * s') • z = s • s' • z :=
  z.induction_on rfl
    (fun x' x => by simp only [tensorModSMul_smul_tmul, mul_smul])
    (fun _ _ (h : map _ _ _ = _) (h' : map _ _ _ = _) => by
        show map _ _ (_ + _) = map _ _ (map _ _ _)
        rw [map_add, h, h', map_add, map_add]
        rfl)

private lemma tensorModSMul_add_smul
    (s s' : S)
    (z : X ⊗[R] Y) :
    (s + s') • z = s • z + s' • z :=
  z.induction_on rfl
    (fun x' x => by simp only [tensorModSMul_smul_tmul, add_smul, add_tmul])
    (fun z z' (h : map _ _ _ = _) (h' : map _ _ _ = _) => by
        show map _ _ (_ + _) = map _ _ _ + map _ _ _
        rw [map_add, h, h', map_add, map_add]
        change _ = (s • z + s • z') + (s' • z + s' • z')
        abel)

noncomputable local instance tensorMod :
    Module S (X ⊗[R] Y) where
  smul := (· • ·)
  one_smul := tensorModSMul_one_smul _ _ _
  mul_smul := tensorModSMul_mul_smul _ _ _
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => map_add _ _ _
  add_smul := tensorModSMul_add_smul _ _ _
  zero_smul := fun z => z.induction_on rfl
    (fun _ _ => by rw [tensorModSMul_smul_tmul, zero_smul, zero_tmul])
    (fun _ _ (h : map _ _ _ = _) (h' : map _ _ _ = _) => show map _ _ _ = _ by
      rw [map_add, h, h', zero_add])

/--
Let `R` be a commutative ring and `S` a ring.
Given an `(S, R)`-bimodule `X` and a left `S`-module `Y`, the set of
`S`-linear maps from `X` to `Y` has a left `R`-module structure given by:
-```
l : X →ₗ[S] Y
r : R
x : X
-------------
(r • l) x = l (op r • x)
```
-/
local instance hom_bimodule {Y : Type v''} [AddCommGroup Y] [Module S Y] :
    Module R (X →ₗ[S] Y) where
  smul r l :=
  { toFun := fun x => l (op r • x)
    map_add' := fun x y => by dsimp; rw [smul_add, map_add]
    map_smul' := fun s x => by dsimp; rw [← smul_comm, l.map_smul] }
  one_smul l := LinearMap.ext fun x => show l _ = _ by rw [op_one, one_smul]
  mul_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ by rw [op_mul, mul_smul]
  smul_zero r := rfl
  smul_add r l₁ l₂ := LinearMap.ext fun x => show (l₁ + _) _ = _ by
    rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  add_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ + l _ by
    rw [op_add, add_smul, map_add]
  zero_smul l := LinearMap.ext fun x => show l _ = 0 by rw [op_zero, zero_smul, map_zero]

variable {R S X}
variable
  {Y : Type v'} [AddCommGroup Y] [Module R Y]
  {Z : Type v''} [AddCommGroup Z] [Module S Z]
/--
Let `R` be a commutative ring and `S` a ring.
Given an `(S, R)`-bimodule `X`, a left `R`-module `Y` and a left `S`-module `Z`,
any `S`-linear map `X ⊗[R] Y ⟶ Z` can by curried into a bilinear map `Y ⟶ X ⟶ Z` that
is `R`-linear in the first argument and `S`-linear in the second.

"h" stands for "heterogeneous".
-/
noncomputable def TensorProduct.hcurry (l : X ⊗[R] Y →ₗ[S] Z) : Y →ₗ[R] (X →ₗ[S] Z) where
  toFun y :=
    { toFun := (l <| · ⊗ₜ y)
      map_add' := fun _ _ => show l _ = l _ + l _ by rw [add_tmul, map_add]
      map_smul' := fun s _ => show l _ = s • l _ by rw [← l.map_smul, tensorModSMul_smul_tmul] }
  map_add' := fun _ _ => LinearMap.ext fun _ => show l _ = l _ + l _ by rw [tmul_add, map_add]
  map_smul' := fun r _ => LinearMap.ext fun _ => show l _ = l ((op r • _) ⊗ₜ _) by
    rw [tmul_smul]
    rfl

@[simp] lemma TensorProduct.hcurry_apply_apply (l : X ⊗[R] Y →ₗ[S] Z) (x : X) (y : Y) :
    TensorProduct.hcurry l y x = l (x ⊗ₜ y) := rfl

attribute [aesop unsafe] add_comm in
/--
Let `R` be a commutative ring and `S` a ring.
Give `(R, S)`-bimodule `X`, a left `R`-module `X` and a right `S`-module `Y`,
any bilinear map `X' ⟶ X ⟶ Y` whose first argument is `R`-linear and second `S`-linear can by
uncurried into a map `X ⊗[R] X' ⟶ Y`.

"h" stands for "heterogeneous".
-/
def TensorProduct.huncurry (l : Y →ₗ[R] X →ₗ[S] Z) : X ⊗[R] Y →ₗ[S] Z :=
  let L : X ⊗[R] Y →+ Z := (addConGen _).lift (FreeAddMonoid.lift fun p => l p.2 p.1) <|
    AddCon.addConGen_le <| by
      rintro _ _ (_|_|_|_|_|_) <;> try aesop
      exact (AddCon.ker_rel _).2 <| FunLike.congr_fun (l.map_smul _ _).symm _
  { L with
    map_smul' := fun _ z => z.induction_on
      (by aesop) (fun _ _ => LinearMap.map_smul _ _ _) (by aesop) }

@[simp] lemma TensorProduct.huncurry_apply_tmul (l : Y →ₗ[R] X →ₗ[S] Z) (y : Y) (x : X) :
    TensorProduct.huncurry l (x ⊗ₜ y) = l y x := rfl

lemma TensorProduct.hcurry_huncurry (l : Y →ₗ[R] X →ₗ[S] Z) : hcurry (huncurry l) = l :=
  FunLike.ext _ _ fun _ => FunLike.ext _ _ fun _ => rfl

lemma TensorProduct.huncurry_hcurry (l : X ⊗[R] Y →ₗ[S] Z) :
    huncurry (hcurry l) = l :=
  FunLike.ext _ _ fun x => by refine x.induction_on ?_ ?_ ?_ <;> aesop

namespace ModuleCat

variable (R S X)

/--
Let `X` be an `(S,R)`-bimodule. Then `(X ⊗[R] ·)` is a functor from the category of `R`-modules
to the category of `S`-modules.
-/
@[simps!]
noncomputable def tensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj Y := ModuleCat.of S <| X ⊗[R] Y
  map {Y Y'} l :=
  { toFun := l.lTensor _
    map_add' := fun _ _ => map_add _ _ _
    map_smul' := fun s x => x.induction_on (by aesop)
      (fun y x => by simp only [tensorModSMul_smul_tmul]; rfl)
      fun _ _ (h : l.lTensor _ _ = s • l.lTensor _ _) (h' : l.lTensor _ _ = s • l.lTensor _ _) =>
        show l.lTensor _ _ = s • l.lTensor _ _ by rw [smul_add, map_add, h, h', map_add, smul_add] }
  map_id _ := LinearMap.ext fun x => FunLike.congr_fun TensorProduct.map_id x
  map_comp {A B C} l l' := LinearMap.ext fun (x : X ⊗[R] A) => by
    change map _ (l'.comp l) _ = (map _ _).comp (map _ _) _
    rw [← map_comp, LinearMap.id_comp]

/--
Let `X` be an `(S,R)`-bimodule. Then `(X →ₗ[S] ·)` is a functor from the category of
left `S`-modules to the category of left `R`-modules.
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

/-- The tensor functor is left adjoint to the hom functor. -/
noncomputable def tensorHomAdjunction : tensorFunctor R S X ⊣ homFunctor R S X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
      { toFun := hcurry
        invFun := huncurry
        left_inv := huncurry_hcurry
        right_inv := hcurry_huncurry }
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
