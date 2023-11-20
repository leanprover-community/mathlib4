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
Consider the tensor functor `(X ⊗[R] .)` from the category of left `R`-module to the category of
left `S`-module and the hom functor `X →ₗ[S] .` from the category of right `S`-module to the
category of left `R`-module. They form an adjunction. In particular we have that
```
Hom_S(X⊗[R]Y, Z) ≃ Hom_R(Y, Hom_S(X, Z))
```

## Implementation notes

1. Order of arguments
```
Hom_Sᵐᵒᵖ(Y⊗[R]X, Z) ≃ Hom_R(Y, Hom_Sᵐᵒᵖ(X, Z))
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

local instance : SMulCommClass Rᵐᵒᵖ S X := SMulCommClass.symm _ _ _

instance leftMod_eq_rightMod : Module R X :=
  Module.compHom X ((RingHom.id R).toOpposite fun _ _ => mul_comm _ _)

noncomputable local instance tensorModSMul {X' : Type v'} [AddCommGroup X'] [Module R X'] :
    SMul S (X' ⊗[R] X) where
  smul := fun s => map LinearMap.id
    { toFun := (s • ·)
      map_add' := smul_add _
      map_smul' := fun r x => by
        show s • (op r) • x = (op r) • s • x
        exact smul_comm _ _ _  }

@[simp] private lemma tensorModSMul_smul_tmul {X' : Type v'} [AddCommGroup X'] [Module R X']
  (s : S) (x' : X') (x : X) : s • (x' ⊗ₜ[R] x) = x' ⊗ₜ[R] (s • x) := rfl

@[simp] private lemma tensorModSMul_one_smul {X' : Type v'} [AddCommGroup X'] [Module R X']
    (z : X' ⊗[R] X) :
    (1 : S) • z = z :=
  z.induction_on rfl
    (fun x' x => by rw [tensorModSMul_smul_tmul, one_smul])
    (fun _ _ h h' => show map _ _ (_ + _) = _ by
      simpa only [map_add] using congr_arg₂ (· + ·) h h')

private lemma tensorModSMul_mul_smul {X' : Type v'} [AddCommGroup X'] [Module R X']
    (s s' : S)
    (z : X' ⊗[R] X) :
    (s * s') • z = s • s' • z :=
  z.induction_on rfl
    (fun x' x => by simp only [tensorModSMul_smul_tmul, mul_smul])
    (fun _ _ (h : map _ _ _ = _) (h' : map _ _ _ = _) => by
        show map _ _ (_ + _) = map _ _ (map _ _ _)
        rw [map_add, h, h', map_add, map_add]
        rfl)

private lemma tensorModSMul_add_smul {X' : Type v'} [AddCommGroup X'] [Module R X']
    (s s' : S)
    (z : X' ⊗[R] X) :
    (s + s') • z = s • z + s' • z :=
  z.induction_on rfl
    (fun x' x => by simp only [tensorModSMul_smul_tmul, mul_smul, add_smul, tmul_add])
    (fun z z' (h : map _ _ _ = _) (h' : map _ _ _ = _) => by
        show map _ _ (_ + _) = map _ _ _ + map _ _ _
        rw [map_add, h, h', map_add, map_add]
        change _ = (s • z + s • z') + (s' • z + s' • z')
        abel)

noncomputable local instance tensorMod {X' : Type v'} [AddCommGroup X'] [Module R X'] :
    Module S (X' ⊗[R] X) where
  smul := (· • ·)
  one_smul := tensorModSMul_one_smul _ _ _
  mul_smul := tensorModSMul_mul_smul _ _ _
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => map_add _ _ _
  add_smul := tensorModSMul_add_smul _ _ _
  zero_smul := fun z => z.induction_on rfl
    (fun _ _ => by rw [tensorModSMul_smul_tmul, zero_smul, tmul_zero])
    (fun _ _ (h : map _ _ _ = _) (h' : map _ _ _ = _) => show map _ _ _ = _ by
      rw [map_add, h, h', zero_add])

/--
Let `R` be a commutative ring and `S` a ring.
Give `(S, R)`-bimodule `X`, a left `R`-module `X` and a right `S`-module `Y`, then the the set of
`S`-linear maps from `X` to `Y` has a (left) `R`-module structure given by:
```
l : X →ₗ[Sᵐᵒᵖ] Y
r : R
x : X
-------------
(r • l) x = l (r • x)
```
-/
local instance hom_bimodule {Y : Type v''} [AddCommGroup Y] [Module S Y] :
    Module R (X →ₗ[S] Y) where
  smul r l :=
  { toFun := fun x => l (op r • x)
    map_add' := fun x y => by dsimp; rw [smul_add, map_add]
    map_smul' := fun s x => by dsimp; rw [smul_comm, l.map_smul] }
  one_smul l := LinearMap.ext fun x => show l _ = _ by rw [op_one, one_smul]
  mul_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ by rw [op_mul, mul_smul]
  smul_zero r := rfl
  smul_add r l₁ l₂ := LinearMap.ext fun x => show (l₁ + _) _ = _ by
    rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  add_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ + l _ by
    rw [op_add, add_smul, map_add]
  zero_smul l := LinearMap.ext fun x => show l _ = 0 by rw [op_zero, zero_smul, map_zero]

variable {R S X}
/--
Let `R` be a commutative ring and `S` a ring.
Give `(S, R)`-bimodule `X`, a left `R`-module `X` and a right `S`-module `Y`,
any `S`-linear map `X ⊗[R] X' ⟶ Y` can by curried into a bilinear map `X' ⟶ X ⟶ Y` where
the first argument is `R`-linear and second is `S`-linear.

"h" stands for "heterogeneous".
-/
noncomputable def TensorProduct.hcurry
    {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' ⊗[R] X →ₗ[S] Y) :
    X' →ₗ[R] (X →ₗ[S] Y) where
  toFun x' :=
    { toFun := (l <| x' ⊗ₜ ·)
      map_add' := fun _ _ => show l _ = l _ + l _ by rw [tmul_add, map_add]
      map_smul' := fun s _ => show l _ = s • l _ by rw [← l.map_smul, tensorModSMul_smul_tmul] }
  map_add' := fun _ _ => LinearMap.ext fun _ => show l _ = l _ + l _ by rw [add_tmul, map_add]
  map_smul' := fun r _ => LinearMap.ext fun _ => show l _ = l (_ ⊗ₜ (op r • _)) by
    rw [smul_tmul]
    rfl

@[simp] lemma TensorProduct.hcurry_apply_apply {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' ⊗[R] X →ₗ[S] Y) (x : X) (x' : X') :
    TensorProduct.hcurry l x' x = l (x' ⊗ₜ x) := rfl

attribute [aesop unsafe] add_comm in
/--
Let `R` be a commutative ring and `S` a ring.
Give `(R, S)`-bimodule `X`, a left `R`-module `X` and a right `S`-module `Y`,
any bilinear map `X' ⟶ X ⟶ Y` whose first argument is `R`-linear and second `S`-linear can by
uncurried into a map `X ⊗[R] X' ⟶ Y`.

"h" stands for "heterogeneous".
-/
def TensorProduct.huncurry
    {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' →ₗ[R] X →ₗ[S] Y) :
    X' ⊗[R] X →ₗ[S] Y :=
  let L : (X' ⊗[R] X) →+ Y := (addConGen _).lift (FreeAddMonoid.lift fun p => l p.1 p.2) <|
    AddCon.addConGen_le <| by
      rintro _ _ (_|_|_|_|_|_) <;> try aesop
      exact (AddCon.ker_rel _).2 <| FunLike.congr_fun (l.map_smul _ _) _
  { L with
    map_smul' := fun _ z => z.induction_on
      (by aesop) (fun _ _ => LinearMap.map_smul _ _ _) (by aesop) }

@[simp] lemma TensorProduct.huncurry_apply_tmul
    {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' →ₗ[R] (X →ₗ[S] Y)) (x : X) (x' : X') :
    TensorProduct.huncurry l (x' ⊗ₜ x) = l x' x := rfl

lemma TensorProduct.hcurry_huncurry
    {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' →ₗ[R] (X →ₗ[S] Y)) :
    hcurry (huncurry l) = l :=
  FunLike.ext _ _ fun _ => FunLike.ext _ _ fun _ => rfl

lemma TensorProduct.huncurry_hcurry
    {X' : Type v'} [AddCommGroup X'] [Module R X']
    {Y : Type v''} [AddCommGroup Y] [Module S Y]
    (l : X' ⊗[R] X →ₗ[S] Y) :
    huncurry (hcurry l) = l :=
  FunLike.ext _ _ fun x => by refine x.induction_on ?_ ?_ ?_ <;> aesop

namespace ModuleCat

variable (R S X)

/--
Let `X` be an `(R,S)`-bimodule. Then `(X ⊗[R] .)` is a functor from the category of `R`-modules
to the category of `S`-modules.
-/
@[simps!]
noncomputable def tensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj Y := ModuleCat.of S <| Y ⊗[R] X
  map {Y Y'} l :=
  { toFun := l.rTensor _
    map_add' := fun _ _ => map_add _ _ _
    map_smul' := fun s x => x.induction_on (by aesop)
      (fun y x => by simp only [tensorModSMul_smul_tmul]; rfl)
      fun _ _ (h : l.rTensor _ _ = s • l.rTensor _ _) (h' : l.rTensor _ _ = s • l.rTensor _ _) =>
        show l.rTensor _ _ = s • l.rTensor _ _ by rw [smul_add, map_add, h, h', map_add, smul_add] }
  map_id _ := LinearMap.ext fun x => FunLike.congr_fun TensorProduct.map_id x
  map_comp {A B C} l l' := LinearMap.ext fun (x : A ⊗[R] X) => by
    change map (l'.comp l) _ _ = (map _ _).comp (map _ _) _
    rw [← map_comp, LinearMap.id_comp]


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

namespace TensorProduct

variable (R' : Type u) [CommRing R']
variable {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N]
variable [Module R' M] [Module R' N]

open ModuleCat

/--
Constructing an additive group map from a tensor product by lifting a bi-additive group map that is
compatible with scalar action.
-/
@[simps!]
noncomputable def toAddCommGroup {C : Type v''} [AddCommGroup C]
    (b : M →+ (N →+ C)) (compatible_smul : ∀ (r : R') (m : M) (n : N), b (r • m) n = b m (r • n)) :
    (M ⊗[R'] N) →+ C :=
  letI inst1 : Module R'ᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id R').fromOpposite fun _ _ => mul_comm _ _)
  LinearMap.toAddMonoidHom
    (huncurry
      (⟨⟨fun m => (b m).toIntLinearMap,
        fun _ _ => FunLike.ext _ _ fun _ => by aesop⟩,
        fun r m => FunLike.ext _ _ fun n => compatible_smul r m n⟩ : M →ₗ[R'] N →ₗ[ℤ] C) :
      (M ⊗[R'] N) →ₗ[ℤ] C)

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
