import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.LinearPMap.Basic

class PFunLike (F : Type*) (α γ β : outParam Type*) [SetLike γ α] where
domain : F → γ
coe : Π (f : F), (domain f) → β
coe_injective : Π (f g : F), domain f = domain g →
  (∀ (x : domain f) (y : domain g), (x : α) = (y : α) → coe f x = coe g y) → f = g

attribute [coe] PFunLike.coe

namespace PFunLike

instance {F α γ β : Type*} [SetLike γ α] [PFunLike F α γ β] :
  CoeFun F (fun f ↦ domain f → β) := ⟨coe⟩

lemma ext {F α β γ : Type*} [SetLike γ α] [PFunLike F α γ β] {f g : F} (h : domain f = domain g)
    (h' : ∀ ⦃x : domain f⦄ ⦃y : domain g⦄, (x : α) = y → f x = g y) : f = g :=
  coe_injective f g h h'

end PFunLike

class ZeroPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [Zero M] [Zero N]
    [ZeroMemClass γ M] [PFunLike F M γ N] where
  pmap_zero : ∀ (f : F), f 0 = 0

@[to_additive]
class OnePHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [One M] [One N]
    [OneMemClass γ M] [PFunLike F M γ N] where
  pmap_one : ∀ (f : F), f 1 = 1

class AddPHomClass (F : Type*) (M γ N : outParam Type*)
    [SetLike γ M] [Add M] [Add N] [AddMemClass γ M] [PFunLike F M γ N] where
  pmap_add : ∀ (f : F) (x y : PFunLike.domain f), f (x + y) = f x + f y

@[to_additive]
class MulPHomClass (F : Type*) (M γ N : outParam Type*)
    [SetLike γ M] [Mul M] [Mul N] [MulMemClass γ M] [PFunLike F M γ N] where
  pmap_mul : ∀ (f : F) (x y : PFunLike.domain f), f (x * y) = f x * f y

class AddMonoidPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M]
    [AddZeroClass M] [AddZeroClass N] [AddSubmonoidClass γ M] [PFunLike F M γ N]
    extends AddPHomClass F M γ N, ZeroPHomClass F M γ N

@[to_additive]
class MonoidPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M]
    [MulOneClass M] [MulOneClass N] [SubmonoidClass γ M] [PFunLike F M γ N]
    extends MulPHomClass F M γ N, OnePHomClass F M γ N

@[to_additive]
theorem pmap_mul_eq_one {F M γ N : Type*} [MulOneClass M] [MulOneClass N] [SetLike γ M]
    [SubmonoidClass γ M] [PFunLike F M γ N] [MonoidPHomClass F M γ N]
    {f : F} {a b : PFunLike.domain f} (h : a * b = 1) : f a * f b = 1 := by
  rw [← MulPHomClass.pmap_mul, h, OnePHomClass.pmap_one]

@[to_additive]
theorem pmap_inv {F G γ H : Type*} [Group G] [DivisionMonoid H] [SetLike γ G]
    [SubgroupClass γ G] [PFunLike F G γ H] [MonoidPHomClass F G γ H]
    {f : F} (a : PFunLike.domain f) : f (a⁻¹) = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| pmap_mul_eq_one <| inv_mul_cancel _

@[to_additive]
theorem pmap_div {F G γ H : Type*} [Group G] [DivisionMonoid H] [SetLike γ G]
    [SubgroupClass γ G] [PFunLike F G γ H] [MonoidPHomClass F G γ H]
    {f : F} (a b : PFunLike.domain f) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, MulPHomClass.pmap_mul, pmap_inv]

class AddActionPSemiHomClass (F : Type*) {M N : outParam Type*} (φ : outParam (M → N))
    (X γ Y : outParam Type*) [SetLike γ X] [VAdd M X] [VAdd N Y] [PFunLike F X γ Y]
    [VAddMemClass γ M X] where
  pmap_vadd : ∀ (f : F) (c : M) (x : PFunLike.domain f), f (c +ᵥ x) = φ c +ᵥ f x

@[to_additive]
class MulActionPSemiHomClass (F : Type*) {M N : outParam Type*} (φ : outParam (M → N))
    (X γ Y : outParam Type*) [SetLike γ X] [SMul M X] [SMul N Y] [PFunLike F X γ Y]
    [SMulMemClass γ M X] where
  pmap_smul : ∀ (f : F) (c : M) (x : PFunLike.domain f), f (c • x) = φ c • f x

@[to_additive]
abbrev MulActionPHomClass (F : Type*) (M X γ Y : outParam Type*) [SetLike γ X]
    [SMul M X] [SMul M Y] [PFunLike F X γ Y] [SMulMemClass γ M X] :=
  MulActionPSemiHomClass F (@id M) X γ Y

class SemilinearPMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam (R →+* S)) (M γ N : outParam Type*) [SetLike γ M]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [PFunLike F M γ N]
    [AddMemClass γ M] [SMulMemClass γ R M]
    extends AddPHomClass F M γ N, MulActionPSemiHomClass F σ M γ N

abbrev LinearPMapClass (F : Type*) (R M γ N : outParam Type*) [Semiring R] [SetLike γ M]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [PFunLike F M γ N]
    [AddMemClass γ M] [SMulMemClass γ R M] :=
  SemilinearPMapClass F (RingHom.id R) M γ N

instance (priority := 900) SMulMemClass.SMulWithZero (R M α : Type*) [Zero R] [Zero M]
    [SMulWithZero R M] [SetLike α M] [SMulMemClass α R M] [ZeroMemClass α M] (a : α) :
    SMulWithZero R a where
  smul_zero r := by ext1; simp
  zero_smul m := by ext1; simp

instance (priority := 100) SemilinearPMapClass.toAddMonoidPHomClass (F : Type*)
    {R S : outParam Type*} [Semiring R] [Semiring S] (σ : outParam (R →+* S))
    (M γ N : outParam Type*) [SetLike γ M] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module S N] [PFunLike F M γ N] [AddSubmonoidClass γ M] [SMulMemClass γ R M]
    [SemilinearPMapClass F σ M γ N] :
    AddMonoidPHomClass F M γ N where
  pmap_zero f := by
    rw [← zero_smul R 0, MulActionPSemiHomClass.pmap_smul, map_zero, zero_smul]

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

instance LinearPMap.PFunLike : PFunLike (E →ₗ.[R] F) E (Submodule R E) F where
  domain f := f.domain
  coe f := f.toFun
  coe_injective _ _ hd h := LinearPMap.ext hd h

instance LinearPMap.LinearPMapClass : LinearPMapClass (E →ₗ.[R] F) R E (Submodule R E) F where
  pmap_add f x y := f.toFun.map_add x y
  pmap_smul f c x := f.toFun.map_smul c x
