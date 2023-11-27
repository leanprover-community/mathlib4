/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/

import Mathlib.LinearAlgebra.TensorProduct

/-!

# Characteristic Predicate of Tensor Product

Given `Semiring R`, right `R`-modules `M`, left `R`-module N, an `AddCommMonoid X`, we say an
`f : M →+ N →+ X` is `R`-balanced biadditive monoid homomorphism if `f (m • r) n = f m (r • n)`
for all `r ∈ R`, `m ∈ M` and `n ∈ N`. A `R`-balanced biadditive monoid hom `flippedTmul : M →+ N →+ X`
defines `R`-tensor product of `M, N` if it is universal: for any `AddCommMonoid P`, balanced
biadditive monoid hom `f : M →+ N →+ P`, there exists a unique homomorphism `f' : X →+ P` such that
`f' (flippedTmul m n) = f m n` for all `m ∈ M` and `n ∈ N`.


## Main results

### Left modules

If `M` is `(A, B)`-bimodule and `N` is left B-module such that balanced `flippedTmul : M →+ N →+ X` is a
`B`-tensor product. Then `X` has an `A`-module structure.

### Right modules

If `M` is right `B`-module, `N` is `(B, C)`-bimodule such that balanced `flippedTmul : M →+ N →+ X` is a
`B`-tensor product. Then `X` has a right `C`-module structure.

-/

set_option autoImplicit false

open TensorProduct MulOpposite

section defs

universe uR uM uN uX uY

variable (R : Type uR) [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {X : Type uX} [AddCommMonoid X]
variable {X' : Type uX} [AddCommMonoid X']

-- this ideal is copied from Junyan's PR #8638

instance smul_addmonoidHom : SMul R (M →+ X) where
  smul r m :=
  { toFun := fun x ↦ m <| op r • x
    map_zero' := by aesop
    map_add' := by aesop }

@[simp] lemma smul_addmonoidHom_apply (r : R) (m : M →+ X) (a : M) : (r • m) a = m (op r • a) := rfl

instance : Module R (M →+ X) where
  __ := smul_addmonoidHom R
  one_smul _ := FunLike.ext _ _ fun _ ↦ by simp
  mul_smul _ _ _ := FunLike.ext _ _ fun _ ↦ by simp [mul_smul]
  smul_zero _ := FunLike.ext _ _ fun _ ↦ by simp
  smul_add _ _ _ := FunLike.ext _ _ fun _ ↦ by simp
  add_smul _ _ _ := FunLike.ext _ _ fun _ ↦ by simp [add_smul]
  zero_smul _ := FunLike.ext _ _ fun _ ↦ by simp

variable {R} in
@[simps!]
def LinearMap.comp₂AddMonoidHom (f : N →ₗ[R] M →+ X) (g : X →+ X') : N →ₗ[R] M →+ X' :=
  { toFun := g.comp
    map_add' := by aesop
    map_smul' := by aesop } ∘ₗ f

-- This prediacte is weaker than the concrete construction because of `P`'s universe level must be
-- small relative to some universe level. I am unsure how to prevent this.
class IsTensorProduct (flippedTmul :  N →ₗ[R] M →+ X) :=
(lift ⦃P : Type uX⦄ [AddCommMonoid P] (_ : N →ₗ[R] M →+ P) : X →+ P)
(lift_comp ⦃P : Type uX⦄ [AddCommMonoid P] (f : N →ₗ[R] M →+ P) :
  flippedTmul.comp₂AddMonoidHom (lift f) = f)
(lift_uniq ⦃P : Type uX⦄ [AddCommMonoid P] (f : N →ₗ[R] M →+ P) (fHat : X →+ P) :
  (flippedTmul.comp₂AddMonoidHom fHat = f) → lift f = fHat)

@[simp] lemma IsTensorProduct.lift_flippedTmul
    (flippedTmul :  N →ₗ[R] M →+ X) [IsTensorProduct R flippedTmul]
    ⦃P : Type uX⦄ [AddCommMonoid P]
    (f : N →ₗ[R] M →+ P) (m : M) (n : N) :
    IsTensorProduct.lift flippedTmul f (flippedTmul n m) = f n m :=
  FunLike.congr_fun (FunLike.congr_fun (IsTensorProduct.lift_comp f) n) m

-- @[simps]
-- def toClosure (flippedTmul :  N →ₗ[R] M →+ X) :
--     N →ₗ[R] M →+ AddSubmonoid.closure { y | ∃ (m : M) (n : N), y = flippedTmul n m } where
--   toFun n :=
--   { toFun := fun m ↦ ⟨flippedTmul n m, AddSubmonoid.subset_closure ⟨m, n, rfl⟩⟩
--     map_zero' := by aesop
--     map_add' := fun _ _ ↦ by simp }
--   map_add' _ _ := FunLike.ext _ _ <| by aesop
--   map_smul' _ _ := FunLike.ext _ _ <| by aesop

-- -- this is weaker than `IsTensorProduct`, I don't think it can characterise `M ⊗ N` upto group
-- -- isomorphism.
-- class IsTensorProduct' (flippedTmul :  N →ₗ[R] M →+ X) :=
-- (retract : X →+ AddSubmonoid.closure { y | ∃ (m : M) (n : N), y = flippedTmul n m })
-- (is_retract : retract.comp (AddSubmonoid.subtype _) = .id _)
-- (retract_comp : ∀ m n, toClosure R flippedTmul n m = retract (flippedTmul n m))

-- noncomputable example (flippedTmul :  N →ₗ[R] M →+ X)
--     [IsTensorProduct R flippedTmul] : IsTensorProduct' R flippedTmul where
--   retract := IsTensorProduct.lift flippedTmul
--     { toFun := fun n ↦
--       { toFun := fun m ↦ ⟨flippedTmul n m, AddSubmonoid.subset_closure ⟨m, ⟨n, rfl⟩⟩⟩
--         map_zero' := by ext; aesop
--         map_add' := by intros; ext; aesop }
--       map_add' := by intros; ext; aesop
--       map_smul' := by intros; ext; aesop }
--   is_retract := FunLike.ext _ _ <| by
--     rintro ⟨x, hx⟩
--     ext
--     dsimp
--     refine AddSubmonoid.closure_induction hx ?_ ?_ ?_
--     · rintro _ ⟨m, ⟨n, rfl⟩⟩
--       simp only [IsTensorProduct.lift_flippedTmul, LinearMap.coe_mk, AddHom.coe_mk,
--         AddMonoidHom.coe_mk, ZeroHom.coe_mk]
--     · simp only [map_zero, ZeroMemClass.coe_zero]
--     · intro x x' h h'
--       simp only [map_add, AddSubmonoid.coe_add] at h h' ⊢
--       rw [h, h']
--   retract_comp m n := by
--     ext
--     simp only [toClosure_apply_apply_coe, IsTensorProduct.lift_flippedTmul, LinearMap.coe_mk,
--       AddHom.coe_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

-- if any `b : N →ₗ[R] M →+ P` can be lifted to `span ⟨tmul m n⟩ →+ P`, then `IsTensorProduct'` implies `IsTensorProduct` as well.

open IsTensorProduct

variable (flippedTmul : N →ₗ[R] M →+ X) [IsTensorProduct R flippedTmul]

lemma IsTensorProduct.mem_closure (x : X) :
    x ∈ AddSubmonoid.closure { y | ∃ (m : M) (n : N), y = flippedTmul n m } := by
  let img : AddSubmonoid X := AddSubmonoid.closure { y | ∃ (m : M) (n : N), y = flippedTmul n m }
  let b : N →ₗ[R] M →+ img :=
  { toFun := fun n ↦
    { toFun := fun m ↦ ⟨flippedTmul n m, AddSubmonoid.subset_closure ⟨_, _, rfl⟩⟩
      map_zero' := by aesop
      map_add' := by aesop }
    map_add' := by aesop
    map_smul' := by aesop }

  let φ := lift flippedTmul b
  let ψ := img.subtype
  have eq1 : ψ.comp φ = AddMonoidHom.id _
  · rw [← show lift flippedTmul flippedTmul = ψ.comp φ from lift_uniq _ _ <| by aesop]
    exact lift_uniq _ _ <| by intros; aesop

  convert (φ x).2
  exact (FunLike.congr_fun eq1 x).symm

@[elab_as_elim]
lemma IsTensorProduct.induction {motive : X → Prop}
    (tensor : ∀ m n, motive (flippedTmul m n))
    (add : ∀ x x', motive x → motive x' → motive (x + x')) :
    ∀ x, motive x :=
  fun x ↦ AddSubmonoid.closure_induction (mem_closure R flippedTmul x)
    (by rintro _ ⟨m, n, rfl⟩; exact tensor _ _)
    (by convert tensor 0 0 using 1; simp only [map_zero]) add

variable (flippedTmul' : N →ₗ[R] M →+ X') [h : IsTensorProduct R flippedTmul']

@[simps]
def IsTensorProduct.cong : X ≃+ X' where
  toFun := lift flippedTmul flippedTmul'
  invFun := lift flippedTmul' flippedTmul
  left_inv := IsTensorProduct.induction _ flippedTmul
    (fun m n ↦ by simp)
    (fun _ _ h₁ h₂ ↦ by rw [map_add, map_add, h₁, h₂])
  right_inv := IsTensorProduct.induction _ flippedTmul'
    (fun m n ↦ by simp)
    (fun _ _ h₁ h₂ ↦ by rw [map_add, map_add, h₁, h₂])
  map_add' _ _ := by simp

end defs

section module_structure

open IsTensorProduct

section left_mod

universe uA uB uC uR

variable (A : Type uA) [Semiring A]
variable (B : Type uB) [Semiring B]
variable (C : Type uC) [Semiring C]
variable (R : Type uR) [Semiring R]

universe uM uN uX

-- M is (A, B)-bimodule
variable (M : Type uM) [AddCommMonoid M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
-- N is left B-module
variable (N : Type uN) [AddCommMonoid N] [Module B N]
variable (X : Type uX) [AddCommMonoid X]
variable (flippedTmul : N →ₗ[B] M →+ X) [IsTensorProduct B flippedTmul]
-- Then X is a left A-module

variable {A B M N X}

def IsTensorProduct.leftSmul (a : A) : X →+ X := IsTensorProduct.lift flippedTmul
{ toFun := fun n ↦
  { toFun := fun m ↦ flippedTmul n (a • m)
    map_zero' := by aesop
    map_add' := by aesop }
  map_add' := by aesop
  map_smul' := fun _ _ ↦ FunLike.ext _ _ fun _ ↦ by simp [smul_comm] }

@[simp] lemma IsTensorProduct.leftSmul_flippedTmul (a : A) (m : M) (n : N) :
    leftSmul flippedTmul a (flippedTmul n m) = flippedTmul n (a • m) := by
  erw [lift_flippedTmul]; rfl

lemma IsTensorProduct.leftSmul.one_smul (x : X) : leftSmul flippedTmul (1 : A) x = x := by
  suffices h : leftSmul flippedTmul (1 : A) = AddMonoidHom.id _
  · rw [h]; rfl
  exact lift_uniq _ _ <| FunLike.ext _ _ <| by aesop

lemma IsTensorProduct.leftSmul.mul_smul (a a' : A) (x : X) :
    leftSmul flippedTmul (a * a') x =
    leftSmul flippedTmul a (leftSmul flippedTmul a' x) := by
  refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
  · intro m n
    simp only [leftSmul_flippedTmul]
    rw [MulAction.mul_smul]
  · intro x x' hx hx'
    simp only [map_add, hx, hx']

def IsTensorProduct.leftSmul.smul : SMul A X where
  smul r := leftSmul flippedTmul r

def IsTensorProduct.leftSmul.mulAction : MulAction A X where
  __ := leftSmul.smul flippedTmul
  one_smul := leftSmul.one_smul flippedTmul
  mul_smul := leftSmul.mul_smul flippedTmul

def IsTensorProduct.leftSmul.distribMulAction : DistribMulAction A X where
  __ := leftSmul.mulAction flippedTmul
  smul_zero _ := show leftSmul flippedTmul _ _ = 0 by simp
  smul_add a x y :=
    show leftSmul flippedTmul _ _ = leftSmul flippedTmul _ _ + leftSmul flippedTmul _ _ by simp

def IsTensorProduct.leftModule : Module A X where
  __ := leftSmul.distribMulAction flippedTmul
  smul_add a x y := by simp
  add_smul a b x :=
    show leftSmul flippedTmul _ _ = leftSmul flippedTmul _ _ + leftSmul flippedTmul _ _ by
    refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
    · intro m n; simp [add_smul]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
  zero_smul x := show leftSmul flippedTmul _ _ = 0 by
    refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
    · intro m n; simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel

end left_mod

section right_mod

universe uA uB uC uR

variable (A : Type uA) [Semiring A]
variable (B : Type uB) [Semiring B]
variable (C : Type uC) [Semiring C]
variable (R : Type uR) [Semiring R]

universe uM uN uX

-- M is right B-module
variable (M : Type uM) [AddCommMonoid M] [Module Bᵐᵒᵖ M]
-- N is (B, C)-bimodule
variable (N : Type uN) [AddCommMonoid N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass Cᵐᵒᵖ B N]
variable (X : Type uX) [AddCommMonoid X]
variable (flippedTmul : N →ₗ[B] M →+ X) [IsTensorProduct B flippedTmul]
-- then X is right C module

variable {A B C M N X}

def IsTensorProduct.rightSmul (r : Cᵐᵒᵖ) : X →+ X := lift flippedTmul
{ toFun := fun n ↦
  { toFun := fun m ↦ flippedTmul (r • n) m
    map_zero' := by aesop
    map_add' := by aesop }
  map_add' := by aesop
  map_smul' := fun _ _ ↦ FunLike.ext _ _ fun _ ↦ by simp [smul_comm] }

@[simp] lemma IsTensorProduct.rightSmul_flippedTmul (a : Cᵐᵒᵖ) (m : M) (n : N) :
    rightSmul flippedTmul a (flippedTmul n m) = flippedTmul (a • n) m := by
  erw [lift_flippedTmul]; rfl

lemma IsTensorProduct.rightSmul.one_smul (x : X) : rightSmul flippedTmul (1 : Cᵐᵒᵖ) x = x := by
  suffices h : rightSmul flippedTmul (1 : Cᵐᵒᵖ) = AddMonoidHom.id _
  · rw [h]; rfl
  exact lift_uniq _ _ <| FunLike.ext _ _ <| by aesop

lemma IsTensorProduct.rightSmul.mul_smul (a a' : Cᵐᵒᵖ) (x : X) :
    rightSmul flippedTmul (a * a') x =
    rightSmul flippedTmul a (rightSmul flippedTmul a' x) := by
  refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
  · intro m n
    simp only [rightSmul_flippedTmul]
    rw [MulAction.mul_smul]
  · intro x x' hx hx'
    simp only [map_add, hx, hx']

def IsTensorProduct.rightSmul.smul : SMul Cᵐᵒᵖ X where
  smul r := rightSmul flippedTmul r

def IsTensorProduct.rightSmul.mulAction : MulAction Cᵐᵒᵖ X where
  __ := rightSmul.smul flippedTmul
  one_smul := rightSmul.one_smul flippedTmul
  mul_smul := rightSmul.mul_smul flippedTmul

def IsTensorProduct.rightSmul.distribMulAction : DistribMulAction Cᵐᵒᵖ X where
  __ := rightSmul.mulAction flippedTmul
  smul_zero _ := show rightSmul flippedTmul _ _ = 0 by simp
  smul_add a x y := show rightSmul flippedTmul _ _ = rightSmul flippedTmul _ _ + rightSmul flippedTmul _ _ by simp

def IsTensorProduct.rightModule : Module Cᵐᵒᵖ X where
  __ := rightSmul.distribMulAction flippedTmul
  smul_add a x y := by simp
  add_smul a b x := show rightSmul flippedTmul _ _ = rightSmul flippedTmul _ _ + rightSmul flippedTmul _ _ by
    refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
    · intro m n; simp [add_smul]
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel
  zero_smul x := show rightSmul flippedTmul _ _ = 0 by
    refine IsTensorProduct.induction B flippedTmul ?_ ?_ x
    · intro m n; simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
      abel

end right_mod

end module_structure

noncomputable section examples

universe uR uS uM uN
variable (R : Type uR) [CommRing R]
variable (S : Type uS) [CommRing S]
variable (M : Type uM) [AddCommGroup M] [Module R M]
variable (N : Type uN) [AddCommGroup N] [Module R N] [Module S N] [SMulCommClass R S N]

local instance : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id _).fromOpposite mul_comm)
local instance : Module Sᵐᵒᵖ N := Module.compHom N ((RingHom.id _).fromOpposite mul_comm)
local instance : SMulCommClass R Sᵐᵒᵖ N where
  smul_comm r s n := smul_comm r s.unop n

@[simps]
noncomputable def TensorProduct.flippedMKAddHom : N →ₗ[R] M →+ M ⊗[R] N where
  toFun n :=
  { toFun := (· ⊗ₜ n)
    map_zero' := by aesop
    map_add' := by simp [add_tmul] }
  map_add' _ _ := FunLike.ext _ _ fun _ ↦ by simp [tmul_add]
  map_smul' _ _ := FunLike.ext _ _ fun _ ↦ by aesop

noncomputable instance isTensorProduct1 : IsTensorProduct R (TensorProduct.flippedMKAddHom R M N) where
  lift P _ f := TensorProduct.liftAddHom (AddMonoidHom.flip f.toAddMonoidHom) fun r m n ↦ by aesop
  lift_comp P _ f := rfl
  lift_uniq P _ f fHat H := FunLike.ext _ _ fun x ↦ x.induction_on (by aesop) (by aesop) (by aesop)

instance : Module S (M ⊗[R] N) :=
  have i0 :  SMulCommClass Sᵐᵒᵖ R N :=
  { smul_comm := fun s r n ↦ show s.unop • r • n = r • s.unop • n by simp [smul_comm] }
  have i1 := IsTensorProduct.rightModule (B := R) (C := S) (M := M) (N := N) (X := M ⊗[R] N)
  @Module.compHom _ _ (M ⊗[R] N) _ _ (@i1 _ (isTensorProduct1 R M N)) _
    ((RingHom.id S).toOpposite mul_comm)

example (s : S) (m : M) (n : N) : s • (m ⊗ₜ[R] n) = m ⊗ₜ (s • n) := rfl

end examples
