/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Tactic.Abel

/-!
# Tensor product of modules over commutative semirings

This file constructs the tensor product of modules over commutative semirings. Given a semiring `R`
and modules over it `M` and `N`, the standard construction of the tensor product is
`TensorProduct R M N`. It is also a module over `R`.

It comes with a canonical bilinear map
`TensorProduct.mk R M N : M →ₗ[R] N →ₗ[R] TensorProduct R M N`.

## Notation

* This file introduces the notation `M ⊗ N` and `M ⊗[R] N` for the tensor product space
  `TensorProduct R M N`.
* It introduces the notation `m ⊗ₜ n` and `m ⊗ₜ[R] n` for the tensor product of two elements,
  otherwise written as `TensorProduct.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section

variable (R)

/-- The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end

end TensorProduct

variable (R) in
/-- The tensor product of two modules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`. -/
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient

set_option quotPrecheck false in
@[inherit_doc TensorProduct] scoped[TensorProduct] infixl:100 " ⊗ " => TensorProduct _

@[inherit_doc] scoped[TensorProduct] notation:100 M:100 " ⊗[" R "] " N:101 => TensorProduct R M N

namespace TensorProduct

section Module

protected instance zero : Zero (M ⊗[R] N) :=
  (addConGen (TensorProduct.Eqv R M N)).zero

protected instance add : Add (M ⊗[R] N) :=
  (addConGen (TensorProduct.Eqv R M N)).hasAdd

instance addZeroClass : AddZeroClass (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    /- The `toAdd` field is given explicitly as `TensorProduct.add` for performance reasons.
    This avoids any need to unfold `Con.addMonoid` when the type checker is checking
    that instance diagrams commute -/
    toAdd := TensorProduct.add _ _
    toZero := TensorProduct.zero _ _ }

instance addSemigroup : AddSemigroup (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    toAdd := TensorProduct.add _ _ }

instance addCommSemigroup : AddCommSemigroup (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    add_comm := fun x y =>
      AddCon.induction_on₂ x y fun _ _ =>
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }

instance : Inhabited (M ⊗[R] N) :=
  ⟨0⟩

variable {M N}

variable (R) in
/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open scoped TensorProduct`. -/
def tmul (m : M) (n : N) : M ⊗[R] N :=
  AddCon.mk' _ <| FreeAddMonoid.of (m, n)

/-- The canonical function `M → N → M ⊗ N`. -/
infixl:100 " ⊗ₜ " => tmul _

/-- The canonical function `M → N → M ⊗ N`. -/
notation:100 x:100 " ⊗ₜ[" R "] " y:101 => tmul R x y

/-- Produces an arbitrary representation of the form `mₒ ⊗ₜ n₀ + ...`. -/
unsafe instance [Repr M] [Repr N] : Repr (M ⊗[R] N) where
  reprPrec mn p :=
    let parts := mn.unquot.toList.map fun (mi, ni) =>
      Std.Format.group f!"{reprPrec mi 100} ⊗ₜ {reprPrec ni 101}"
    match parts with
    | [] => f!"0"
    | [part] => if p > 100 then Std.Format.bracketFill "(" part ")" else .fill part
    | parts =>
      (if p > 65 then (Std.Format.bracketFill "(" · ")") else (.fill ·)) <|
        .joinSep parts f!" +{Std.Format.line}"

@[elab_as_elim, induction_eliminator]
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih

variable (M) in
@[simp]
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _

theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _

variable (N) in
@[simp]
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _

theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _

instance uniqueLeft [Subsingleton M] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim x 0, zero_tmul]) <| by
    rintro _ _ rfl rfl; apply add_zero

instance uniqueRight [Subsingleton N] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim y 0, tmul_zero]) <| by
    rintro _ _ rfl rfl; apply add_zero

section

variable (R R' M N)

/-- A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProduct.tmul_smul` is
used.
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)

end

/-- Note that this provides the default `CompatibleSMul R R M N` instance through
`IsScalarTower.left`. -/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc, ← smul_assoc]
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩

/-- `smul` can be moved from one side of the product to the other . -/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _

set_option backward.privateInPublic true in
@[instance_reducible]
private def addMonoidWithWrongNSMul : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

attribute [local instance] addMonoidWithWrongNSMul in
/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) ⊗ₜ p.2

theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) ⊗ₜ[R] n :=
  rfl

variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

/-- Given two modules over a commutative semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
* Extension of scalars
* A tensor product of a group representation with a module not carrying an action

Note that in the special case that `R = R'`, since `R` is commutative, we just get the usual scalar
action on a tensor product of two modules. This special case is important enough that, for
performance reasons, we define it explicitly below. -/
instance leftHasSMul : SMul R' (M ⊗[R] N) :=
  ⟨fun r =>
    (addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ →+ M ⊗[R] N) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, tmul_zero]
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, tmul_add]
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]⟩

instance : SMul R (M ⊗[R] N) :=
  TensorProduct.leftHasSMul

protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  map_zero _

protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  map_add _ _ _

protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]

protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]

protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx, ihy, add_add_add_comm]

instance addMonoid : AddMonoid (M ⊗[R] N) :=
  { TensorProduct.addZeroClass _ _ with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    toZero := TensorProduct.zero _ _
    nsmul := fun n v => n • v
    nsmul_zero := by simp [TensorProduct.zero_smul]
    nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, add_comm,
      forall_const] }

instance addCommMonoid : AddCommMonoid (M ⊗[R] N) :=
  { TensorProduct.addCommSemigroup _ _ with
    toAddMonoid := TensorProduct.addMonoid }

variable (R)

theorem _root_.IsAddUnit.tmul_left {n : N} (hn : IsAddUnit n) (m : M) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m ⊗ₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩

theorem _root_.IsAddUnit.tmul_right {m : M} (hm : IsAddUnit m) (n : N) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b ⊗ₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

variable {R}

instance leftDistribMulAction : DistribMulAction R' (M ⊗[R] N) :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add]
        rw [ihx, ihy]
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }

instance : DistribMulAction R (M ⊗[R] N) :=
  TensorProduct.leftDistribMulAction

theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl

@[simp]
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x ⊗ₜ (r • y) = r • x ⊗ₜ[R] y :=
  (smul_tmul _ _ _).symm

theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] (s • n) = (r * s) • m ⊗ₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]

theorem tmul_eq_smul_one_tmul {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
    (s : S) (m : M) : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']

instance leftModule : Module R'' (M ⊗[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

instance : Module R (M ⊗[R] N) :=
  TensorProduct.leftModule

instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add, smul_add, hx, hy]

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]

/-- `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)` -/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

variable [SMul R'₂ R']

/-- `IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]

/-- `IsScalarTower R'₂ R' N` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

end

/-- A short-cut instance for the common case, where the requirements for the `compatible_smul`
instances are sufficient. -/
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M ⊗[R] N) :=
  TensorProduct.isScalarTower_left

-- or right
variable (R M N) in
/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  LinearMap.mk₂ R (· ⊗ₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n :=
  rfl

theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x ⊗ₜ[R] Pi.single i m j = (Pi.single i (x ⊗ₜ[R] m) : ∀ i, N ⊗[R] M i) j := by
  by_cases h : i = j <;> aesop

lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j ⊗ₜ[R] x = (Pi.single i (m ⊗ₜ[R] x) : ∀ i, M i ⊗[R] N) j := by
  by_cases h : i = j <;> aesop

section

theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a ∈ s, m a) ⊗ₜ[R] n = ∑ a ∈ s, m a ⊗ₜ[R] n := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]

theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a ∈ s, n a) = ∑ a ∈ s, m ⊗ₜ[R] n a := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

end

variable (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module
end TensorProduct
end Semiring
