/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Prod

/-!
# Prod instances for additive and multiplicative actions

This file defines instances for binary product of additive and multiplicative actions and provides
scalar multiplication as a homomorphism from `α × β` to `β`.

## Main declarations

* `smulMulHom`/`smulMonoidHom`: Scalar multiplication bundled as a multiplicative/monoid
  homomorphism.

## See also

* `Mathlib.Algebra.Group.Action.Option`
* `Mathlib.Algebra.Group.Action.Pi`
* `Mathlib.Algebra.Group.Action.Sigma`
* `Mathlib.Algebra.Group.Action.Sum`

# Porting notes

The `to_additive` attribute can be used to generate both the `smul` and `vadd` lemmas
from the corresponding `pow` lemmas, as explained on zulip here:
https://leanprover.zulipchat.com/#narrow/near/316087838

This was not done as part of the port in order to stay as close as possible to the mathlib3 code.
-/

assert_not_exists MonoidWithZero

variable {M N P E α β : Type*}

namespace Prod

section
variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (x : α × β)

@[to_additive] instance smul : SMul M (α × β) where smul a p := (a • p.1, a • p.2)

@[to_additive (attr := simp)] lemma smul_fst : (a • x).1 = a • x.1 := rfl

@[to_additive (attr := simp)] lemma smul_snd : (a • x).2 = a • x.2 := rfl

@[to_additive (attr := simp)]
lemma smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) := rfl

@[to_additive]
lemma smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) := rfl

@[to_additive (attr := simp)] lemma smul_swap : (a • x).swap = a • x.swap := rfl

variable [Pow α E] [Pow β E]

@[to_additive existing smul]
instance pow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)

@[to_additive existing (attr := simp) (reorder := 6 7) smul_fst]
lemma pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

@[to_additive existing (attr := simp) (reorder := 6 7) smul_snd]
lemma pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

/- Note that the `c` arguments to this lemmas cannot be in the more natural right-most positions due
to limitations in `to_additive` and `to_additive_reorder`, which will silently fail to reorder more
than two adjacent arguments -/
@[to_additive existing (attr := simp) (reorder := 6 7) smul_mk]
lemma pow_mk (c : E) (a : α) (b : β) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

@[to_additive existing (reorder := 6 7) smul_def]
lemma pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

@[to_additive existing (attr := simp) (reorder := 6 7) smul_swap]
lemma pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c := rfl

@[to_additive vaddAssocClass]
instance isScalarTower [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] :
    IsScalarTower M N (α × β) where
  smul_assoc _ _ _ := mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩

@[to_additive]
instance smulCommClass [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α × β) where
  smul_comm _ _ _ := mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩

@[to_additive]
instance isCentralScalar [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α × β) where
  op_smul_eq_smul _ _ := Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)

@[to_additive]
instance faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)

@[to_additive]
instance faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)

end

@[to_additive]
instance smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
    [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) where
  smul_comm c x y := by simp [smul_def, mul_def, mul_smul_comm]

instance isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
    [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) where
  smul_assoc c x y := by simp [smul_def, mul_def, smul_mul_assoc]

@[to_additive]
instance mulAction [Monoid M] [MulAction M α] [MulAction M β] : MulAction M (α × β) where
  mul_smul _ _ _ := mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩
  one_smul _ := mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section BundledSMul

/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β →ₙ* β where
  toFun a := a.1 • a.2
  map_mul' _ _ := (smul_mul_smul_comm _ _ _ _).symm

/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β →* β :=
  { smulMulHom with map_one' := one_smul _ _ }

end BundledSMul

section Action_by_Prod
variable (M N α) [Monoid M] [Monoid N]

/-- Construct a `MulAction` by a product monoid from `MulAction`s by the factors.
  This is not an instance to avoid diamonds for example when `α := M × N`. -/
@[to_additive AddAction.prodOfVAddCommClass
"Construct an `AddAction` by a product monoid from `AddAction`s by the factors.
This is not an instance to avoid diamonds for example when `α := M × N`."]
abbrev MulAction.prodOfSMulCommClass [MulAction M α] [MulAction N α] [SMulCommClass M N α] :
    MulAction (M × N) α where
  smul mn a := mn.1 • mn.2 • a
  one_smul a := (one_smul M _).trans (one_smul N a)
  mul_smul x y a := by
    change (x.1 * y.1) • (x.2 * y.2) • a = x.1 • x.2 • y.1 • y.2 • a
    rw [mul_smul, mul_smul, smul_comm y.1 x.2]

/-- A `MulAction` by a product monoid is equivalent to commuting `MulAction`s by the factors. -/
@[to_additive AddAction.prodEquiv
"An `AddAction` by a product monoid is equivalent to commuting `AddAction`s by the factors."]
def MulAction.prodEquiv :
    MulAction (M × N) α ≃ Σ' (_ : MulAction M α) (_ : MulAction N α), SMulCommClass M N α where
  toFun _ :=
    letI instM := MulAction.compHom α (.inl M N)
    letI instN := MulAction.compHom α (.inr M N)
    ⟨instM, instN,
    { smul_comm := fun m n a ↦ by
        change (m, (1 : N)) • ((1 : M), n) • a = ((1 : M), n) • (m, (1 : N)) • a
        simp_rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul] }⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    MulAction.prodOfSMulCommClass M N α
  left_inv := by
    rintro ⟨-, hsmul⟩; dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [← hsmul, Prod.mk_mul_mk, mul_one, one_mul]; rfl
  right_inv := by
    rintro ⟨hM, hN, -⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    congr 1
    · funext; congr; ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    · ext n a; (conv_rhs => rw [← hM.one_smul (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

end Action_by_Prod
