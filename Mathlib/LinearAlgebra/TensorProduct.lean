/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathlib.GroupTheory.Congruence
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Tactic.SuppressCompilation

#align_import linear_algebra.tensor_product from "leanprover-community/mathlib"@"88fcdc3da43943f5b01925deddaa5bf0c0e85e4e"

/-!
# Tensor product of modules over possibly noncommutative semirings.

This file constructs the tensor product of modules over semirings. Given a semiring `R`,
a right `R`-module `M` and a left `R`-module `N`, the standard construction of the tensor
product is `TensorProduct R M N`.

It comes with a canonical monoid homomorphism `φ : M →+ N →+ TensorProduct R M N` that is
`R`-balanced, i.e., satisfying `φ (op r • m) n = φ m (r • n)`. We express the balanced
condition via the `R`-linearity of the map `mk : N → M →+ TensorProduct R M N`, where
`M →+ TensorProduct R M N` has the left `R`-action induced from the right `R`-action on `M`
(this action is registered as a local instance).

Given any `R`-balanced map `f : N →ₗ[R] M →+ P`, there is a unique monoid homomorphism
`TensorProduct R M N →+ P` whose composition with the canonical `R`-balanced map `mk` gives `f`.

We start by proving basic lemmas about `R`-balanced maps.

## Notations

This file uses the localized notation `M ⊗ N` and `M ⊗[R] N` for `TensorProduct R M N`, as well
as `m ⊗ₜ n` and `m ⊗ₜ[R] n` for `TensorProduct.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

suppress_compilation

attribute [-instance] AddMonoidHom.module LinearMap.module
attribute [instance] AddMonoidHom.domModule LinearMap.domModule

@[simps] instance (R M) [SMul R M] : SMul Rᵐᵒᵖᵐᵒᵖ M where
  smul r m := r.unop.unop • m

instance (R M) [Monoid R] [AddMonoid M] [DistribMulAction R M] : DistribMulAction Rᵐᵒᵖᵐᵒᵖ M :=
  DistribMulAction.compHom _ (MulEquiv.opOp R).symm.toMonoidHom

instance (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Module Rᵐᵒᵖᵐᵒᵖ M :=
  Module.compHom _ (RingEquiv.opOp R).symm.toRingHom

instance (R S M) [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass Rᵐᵒᵖᵐᵒᵖ S M where
  smul_comm r := smul_comm r.unop.unop

instance (R S M) [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass R Sᵐᵒᵖᵐᵒᵖ M where
  smul_comm _ s := smul_comm _ s.unop.unop

section Semiring

variable (R : Type*) [Semiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable (L M N : Type*) {P Q S : Type*}
variable [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [Module Rᵐᵒᵖ M] [Module R N] [Module R S]
variable [DistribMulAction R' M]
variable [Module R'' M]

open MulOpposite

/-- The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive TensorProduct.Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (op r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)
#align tensor_product.eqv TensorProduct.Eqv

/-- The tensor product of a right module `M` and a left module `N` over the same semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`. -/
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient
#align tensor_product TensorProduct

variable {R}

set_option quotPrecheck false in
scoped[TensorProduct] infixl:100 " ⊗ " => TensorProduct _

scoped[TensorProduct] notation:100 M " ⊗[" R "] " N:100 => TensorProduct R M N

namespace TensorProduct

section Module

-- porting note: This is added as a local instance for `SMul.aux`.
-- For some reason type-class inference in Lean 3 unfolded this definition.
def addMonoid : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

protected instance add : Add (M ⊗[R] N) :=
  (addConGen (TensorProduct.Eqv R M N)).hasAdd

instance addZeroClass : AddZeroClass (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with
    /- The `toAdd` field is given explicitly as `TensorProduct.add` for performance reasons.
    This avoids any need to unfold `Con.addMonoid` when the type checker is checking
    that instance diagrams commute -/
    toAdd := TensorProduct.add _ _ }

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

variable (R) {M N}

/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open scoped TensorProduct`. -/
def tmul (m : M) (n : N) : M ⊗[R] N :=
  AddCon.mk' _ <| FreeAddMonoid.of (m, n)
#align tensor_product.tmul TensorProduct.tmul

variable {R}

infixl:100 " ⊗ₜ " => tmul _

notation:100 x " ⊗ₜ[" R "] " y:100 => tmul R x y

-- porting note: make the arguments of induction_on explicit
@[elab_as_elim]
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih
#align tensor_product.induction_on TensorProduct.induction_on

/-- An unbundled version of `TensorProduct.liftAddHom`, for better performance. -/
abbrev liftFun (f : M → N → P)
    (hf_zero_left : ∀ n, f 0 n = 0) (hf_zero_right : ∀ m, f m 0 = 0)
    (hf_add_left : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (hf_add_right : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, hf_zero_left]
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, hf_zero_right]
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, hf_add_left]
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, hf_add_right]
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

@[simp]
theorem liftFun_tmul (f : M → N → P)
    (hf_zero_left : ∀ n, f 0 n = 0) (hf_zero_right : ∀ m, f m 0 = 0)
    (hf_add_left : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (hf_add_right : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n)) (m : M) (n : N) :
    liftFun f hf_zero_left hf_zero_right hf_add_left hf_add_right hf (m ⊗ₜ n) = f m n :=
  rfl

def lift : (N →ₗ[R] M →+ P) →+ M ⊗[R] N →+ P where
  toFun f := liftFun (fun m n ↦ f n m)
    (fun _ ↦ map_zero _) (fun _ ↦ by simp_rw [map_zero]; rfl)
    (fun m m' n ↦ map_add _ m m') (fun m n n' ↦ by simp_rw [map_add]; rfl)
    fun r m n ↦ by simp_rw [map_smul]; rfl
  map_zero' := AddMonoidHom.ext fun x ↦ x.induction_on (map_zero _)
    (fun _ _ ↦ rfl) (fun x y hx hy ↦ by simp_rw [map_add, hx, hy])
  map_add' f g := AddMonoidHom.ext fun x ↦ x.induction_on (by simp_rw [map_zero])
    (fun _ _ ↦ rfl) (fun x y hx hy ↦ by aesop)

@[simp]
theorem lift_tmul (f : N →ₗ[R] M →+ P) (m : M) (n : N) :
    lift f (m ⊗ₜ n) = f n m :=
  rfl

variable (M)

@[simp]
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _
#align tensor_product.zero_tmul TensorProduct.zero_tmul

variable {M}

theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _
#align tensor_product.add_tmul TensorProduct.add_tmul

variable (N)

@[simp]
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _
#align tensor_product.tmul_zero TensorProduct.tmul_zero

variable {N}

theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _
#align tensor_product.tmul_add TensorProduct.tmul_add

theorem op_smul_tmul (r : R) (m : M) (n : N) : (op r • m) ⊗ₜ[R] n = m ⊗ₜ (r • n) :=
  Quotient.sound <| AddConGen.Rel.of _ _ <| Eqv.of_smul r m n

instance uniqueLeft [Subsingleton M] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim x 0, zero_tmul]; rfl) <| by
    rintro _ _ rfl rfl; apply add_zero

instance uniqueRight [Subsingleton N] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim y 0, tmul_zero]; rfl) <| by
    rintro _ _ rfl rfl; apply add_zero

section

variable (R R' M N)

/-- A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.intModule`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProduct.tmul_smul` is
used.
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)
#align tensor_product.compatible_smul TensorProduct.CompatibleSMul

end

/-- Note that this provides the default `compatible_smul R R M N` instance through
`IsScalarTower.left`. -/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' Rᵐᵒᵖ M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul Rᵐᵒᵖ m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc, ← smul_assoc]
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩
#align tensor_product.compatible_smul.is_scalar_tower TensorProduct.CompatibleSMul.isScalarTower

/-- `smul` can be moved from one side of the product to the other .-/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _
#align tensor_product.smul_tmul TensorProduct.smul_tmul

/-- This has the wrong value for the `nsmul` field, but we need it in order to create the right
value! -/
private def addCommMonoidWithWrongSMul : AddCommMonoid (M ⊗[R] N) where
  __ := (addConGen (TensorProduct.Eqv R M N)).addMonoid
  __ := addCommSemigroup M N
  toZero := (TensorProduct.addZeroClass _ _).toZero
  toAddSemigroup := addSemigroup _ _

variable [SMulCommClass R' Rᵐᵒᵖ M] [SMulCommClass R'' Rᵐᵒᵖ M]

attribute [local instance] addCommMonoidWithWrongSMul in
/-- Given a right `R`-module `M` and a left `R`-module `N`, if `M` also carry a left action by
a second type `R'`, then `M ⊗[R] N` also carries a left action by `R'`. Note that by convention
any left action always commutes with any right action, expressed by the typeclass
`SMulCommClass R' Rᵐᵒᵖ M`. In particular, if `M` is a `(R',R)`-bimodule, then `M ⊗[R] N` is
a left `R'`-module.

Two natural ways in which this situation arises are:
 * Extension of scalars
 * A tensor product of a group representation with a module not carrying an action

Note that if `R` is commutative and `R' = R`, we get that `M ⊗[R] N` is also a `R`-module.
This special case is treated in the file about commutative tensor products. -/
instance leftHasSMul : SMul R' (M ⊗[R] N) where
  smul r := liftFun (fun m n => (r • m) ⊗ₜ n)
    (by simp) (by simp) (by simp [add_tmul]) (by simp [tmul_add])
    (fun r' m n => by dsimp; rw [smul_comm, op_smul_tmul])
#align tensor_product.left_has_smul TensorProduct.leftHasSMul

protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  AddMonoidHom.map_zero _
#align tensor_product.smul_zero TensorProduct.smul_zero

protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  AddMonoidHom.map_add _ _ _
#align tensor_product.smul_add TensorProduct.smul_add

protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]
#align tensor_product.zero_smul TensorProduct.zero_smul

protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]
#align tensor_product.one_smul TensorProduct.one_smul

protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx, ihy, add_add_add_comm]
#align tensor_product.add_smul TensorProduct.add_smul

instance addCommMonoid : AddCommMonoid (M ⊗[R] N) :=
  { TensorProduct.addCommSemigroup _ _,
    TensorProduct.addZeroClass _ _ with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    toZero := (TensorProduct.addZeroClass _ _).toZero
    nsmul := fun n v => n • v
    nsmul_zero := by simp [TensorProduct.zero_smul]
    nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, add_comm,
      forall_const] }

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
#align tensor_product.left_distrib_mul_action TensorProduct.leftDistribMulAction

theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl
#align tensor_product.smul_tmul' TensorProduct.smul_tmul'

theorem op_smul_tmul_smul (r s : R) (m : M) (n : N) :
    (op r • m) ⊗ₜ[R] (s • n) = m ⊗ₜ[R] ((r * s) • n) := by
  simp_rw [op_smul_tmul, smul_smul]

instance leftModule : Module R'' (M ⊗[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }
#align tensor_product.left_module TensorProduct.leftModule

instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul])
      fun x y hx hy => by rw [smul_add, smul_add, hx, hy]

variable {S : Type*} [Monoid S]
variable {S' : Type*} [Semiring S']
variable [DistribMulAction S N] [Module S' N]
variable [SMulCommClass R S N] [SMulCommClass R S' N]

attribute [local instance] addCommMonoidWithWrongSMul in
/-- Given a right `R`-module `M` and a left `R`-module `N`, if `N` also carry a right action by
a second type, then `M ⊗[R] N` also carries a right action by that type.
To avoid conflict with `leftHasSMul`, it's best to ensure there isn't a `S`-action on `M` that
commutes with the `Rᵐᵒᵖ`-action (i.e. `M` is not a `(S,R)`-bimodule), in order to make this
an instance locally. -/
def rightHasSMul : SMul S (M ⊗[R] N) where
  smul s := liftFun (fun m n => m ⊗ₜ (s • n))
    (by simp) (by simp) (by simp [add_tmul]) (by simp [tmul_add])
    (fun r' m n => by dsimp; rw [← smul_comm, op_smul_tmul])

attribute [local instance] rightHasSMul

protected theorem smul_zero' (s : S) : s • (0 : M ⊗[R] N) = 0 :=
  AddMonoidHom.map_zero _

protected theorem smul_add' (s : S) (x y : M ⊗[R] N) : s • (x + y) = s • x + s • y :=
  AddMonoidHom.map_add _ _ _

protected theorem zero_smul' (x : M ⊗[R] N) : (0 : S') • x = 0 :=
  have : ∀ (s : S') (m : M) (n : N), s • m ⊗ₜ[R] n = m ⊗ₜ (s • n) := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero'])
    (fun m n => by rw [this, zero_smul, tmul_zero]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add', ihx, ihy, add_zero]

protected theorem one_smul' (x : M ⊗[R] N) : (1 : S) • x = x :=
  have : ∀ (s : S) (m : M) (n : N), s • m ⊗ₜ[R] n = m ⊗ₜ (s • n) := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero'])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add', ihx, ihy]

protected theorem add_smul' (r s : S') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (s : S') (m : M) (n : N), s • m ⊗ₜ[R] n = m ⊗ₜ (s • n) := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero', add_zero])
    (fun m n => by simp_rw [this, add_smul, tmul_add]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add']
    rw [ihx, ihy, add_add_add_comm]

/-- Promote `rightHasSMul` to a `DistribMulAction`. -/
def rightDistribMulAction : DistribMulAction S (M ⊗[R] N) :=
  have : ∀ (s : S) (m : M) (n : N), s • m ⊗ₜ[R] n = m ⊗ₜ (s • n) := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add' r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero'])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add']
        rw [ihx, ihy]
    one_smul := TensorProduct.one_smul'
    smul_zero := TensorProduct.smul_zero' }

attribute [local instance] rightDistribMulAction

theorem smul_tmul'' (s : S) (m : M) (n : N) : s • m ⊗ₜ[R] n = m ⊗ₜ (s • n) := rfl

/-- Promote `rightHasSMul` to a `Module`. -/
def rightModule : Module S' (M ⊗[R] N) where
  __ := rightDistribMulAction
  add_smul := TensorProduct.add_smul'
  zero_smul := TensorProduct.zero_smul'

attribute [local instance] rightModule

/-- `M ⊗[R] N` is a `(R'', S')`-bimodule if `M` is a `(R'', R)`-bimodule and `N` is a
  `(R, S')`-bimodule. -/
instance smulCommClass : SMulCommClass R'' S' (M ⊗[R] N) where
  smul_comm r s x := x.induction_on (by simp)
    (fun m n ↦ by rw [smul_tmul'', smul_tmul', smul_tmul', smul_tmul''])
    fun x y hx hy ↦ by simp_rw [smul_add, hx, hy]

instance [Module S'ᵐᵒᵖ N] [IsCentralScalar S' N] : IsCentralScalar S' (M ⊗[R] N) where
  op_smul_eq_smul s x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul'', smul_tmul'', op_smul_eq_smul])
      fun x y hx hy => by rw [smul_add, smul_add, hx, hy]

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M] [SMulCommClass R'₂ Rᵐᵒᵖ M]

/-- `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)` -/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm])
      fun x y ihx ihy => by simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]
#align tensor_product.smul_comm_class_left TensorProduct.smulCommClass_left

variable [SMul R'₂ R']

/-- `IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc])
      fun x y ihx ihy => by rw [smul_add, smul_add, smul_add, ihx, ihy]⟩
#align tensor_product.is_scalar_tower_left TensorProduct.isScalarTower_left

variable {S'₂ : Type*} [Monoid S'₂] [DistribMulAction S'₂ N] [SMulCommClass R S'₂ N]

instance smulCommClass_right [SMulCommClass S S'₂ N] : SMulCommClass S S'₂ (M ⊗[R] N) where
  smul_comm s s'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero'])
      (fun m n => by simp_rw [smul_tmul'', smul_comm])
      fun x y ihx ihy => by simp_rw [TensorProduct.smul_add']; rw [ihx, ihy]

variable [SMul S'₂ S]

instance isScalarTower_right [IsScalarTower S'₂ S N] : IsScalarTower S'₂ S (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul'', smul_tmul'', smul_tmul'', smul_assoc])
      fun x y ihx ihy => by rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

end

variable (R M N)

def mk : N →ₗ[R] M →+ M ⊗[R] N where
  toFun n :=
  { toFun := (· ⊗ₜ n)
    map_zero' := zero_tmul M n
    map_add' := fun m m' ↦ add_tmul m m' n }
  map_add' n n' := by ext m; exact tmul_add m n n'
  map_smul' r n := by ext m; exact (op_smul_tmul r m n).symm

variable {R M N}

@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N n m = m ⊗ₜ n :=
  rfl
#align tensor_product.mk_apply TensorProduct.mk_apply

theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
#align tensor_product.ite_tmul TensorProduct.ite_tmul

theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
#align tensor_product.tmul_ite TensorProduct.tmul_ite

section

open BigOperators

theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a in s, m a) ⊗ₜ[R] n = ∑ a in s, m a ⊗ₜ[R] n := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, add_tmul, ih]
#align tensor_product.sum_tmul TensorProduct.sum_tmul

theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a in s, n a) = ∑ a in s, m ⊗ₜ[R] n a := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, tmul_add, ih]
#align tensor_product.tmul_sum TensorProduct.tmul_sum

end

variable (R M N)

theorem closure_tmul_eq_top : AddSubmonoid.closure {t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t} = ⊤ := by
  ext t; simp only [AddSubmonoid.mem_top, iff_true_iff]
  refine t.induction_on ?_ ?_ ?_
  · exact zero_mem _
  · intro m n
    apply AddSubmonoid.subset_closure
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact add_mem ht₁ ht₂

theorem exists_eq_tmul_of_forall (x : M ⊗[R] N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module

attribute [local instance] rightModule

section UMP

variable {M N}
variable {f : N →ₗ[R] M →+ P}

@[simp]
theorem lift.tmul (x y) : lift f (x ⊗ₜ y) = f y x :=
  rfl
#align tensor_product.lift.tmul TensorProduct.lift.tmul

theorem ext' {g h : M ⊗[R] N →+ P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  AddMonoidHom.ext fun z =>
    z.induction_on (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add, h.map_add, ihx, ihy]
#align tensor_product.ext' TensorProduct.ext'

theorem lift.unique {g : M ⊗[R] N →+ P} (H : ∀ x y, g (x ⊗ₜ y) = f y x) : g = lift f :=
  ext' fun m n => by rw [H, lift.tmul]
#align tensor_product.lift.unique TensorProduct.lift.unique

theorem lift_mk : lift (mk R M N) = AddMonoidHom.id _ :=
  Eq.symm <| lift.unique fun _ _ => rfl
#align tensor_product.lift_mk TensorProduct.lift_mk

open AddMonoidHom

@[simps] def _root_.AddMonoidHom.llcomp : (P →+ Q) →+ (M →+ P) →ₗ[R] (M →+ Q) where
  toFun f :=
  { toFun := f.comp
    map_add' := fun g g' ↦ by ext; apply f.map_add
    map_smul' := fun r g ↦ rfl }
  map_zero' := rfl
  map_add' g g' := rfl

variable (f)

abbrev _root_.LinearMap.comprm (g : P →+ Q) : N →ₗ[R] M →+ Q := (llcomp g).comp f

theorem lift_comprm (g : P →+ Q) : lift (f.comprm g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp
#align tensor_product.lift_compr₂ TensorProduct.lift_comprm

theorem lift_mk_comprm (f : M ⊗[R] N →+ P) :
    lift ((mk R M N).comprm f) = f := by
  rw [lift_comprm, lift_mk, AddMonoidHom.comp_id]
#align tensor_product.lift_mk_compr₂ TensorProduct.lift_mk_comprm

theorem ext {g h : M ⊗ N →+ P} (H : (mk R M N).comprm g = (mk R M N).comprm h) :
    g = h := by
  rw [← lift_mk_comprm g, H, lift_mk_comprm]
#align tensor_product.ext TensorProduct.ext

attribute [local ext high] ext

@[simps] def liftEquiv : (N →ₗ[R] M →+ P) ≃+ (M ⊗[R] N →+ P) where
  __ := lift
  invFun := (mk R M N).comprm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable [SMulCommClass R'' Rᵐᵒᵖ M] [Module R'' P] [Module R'' Q]

@[simps] def _root_.LinearMap.domModuleToAddMonoidHom : (M →ₗ[R''] P) →ₗ[R] (M →+ P) where
  toFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R R'' M N) in
@[simps] def lmk : N →ₗ[R] M →ₗ[R''] M ⊗[R] N where
  toFun n :=
  { __ := mk R M N n
    map_smul' := fun r m ↦ (smul_tmul' r m n).symm }
  map_add' _ _ := LinearMap.ext (by simp)
  map_smul' _ _ := LinearMap.ext (by simp)

@[simps] def _root_.LinearMap.hllcomp : (P →ₗ[R''] Q) →+ (M →ₗ[R''] P) →ₗ[R] (M →ₗ[R''] Q) where
  toFun f :=
  { toFun := f.comp
    map_add' := fun _ _ ↦ LinearMap.ext (by simp)
    map_smul' := fun _ _ ↦ LinearMap.ext (by simp) }
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev _root_.LinearMap.hcompr₂ (f : N →ₗ[R] M →ₗ[R''] P) (g : P →ₗ[R''] Q) : N →ₗ[R] M →ₗ[R''] Q :=
  (LinearMap.hllcomp g).comp f

variable (R R'' M N P) in
/-- Linearly constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
@[simps] def uncurry : (N →ₗ[R] M →ₗ[R''] P) →+ M ⊗[R] N →ₗ[R''] P where
  toFun f :=
  { __ := lift (LinearMap.domModuleToAddMonoidHom.comp f)
    map_smul' := fun r x ↦ x.induction_on (by simp)
      (fun _ _ ↦ LinearMap.map_smul _ _ _) (by aesop) }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [LinearMap.comp_add]

#align tensor_product.uncurry TensorProduct.uncurry

theorem uncurry_apply (f : N →ₗ[R] M →ₗ[R''] P) (m : M) (n : N) :
    uncurry R R'' M N P f (m ⊗ₜ n) = f n m := by simp
#align tensor_product.uncurry_apply TensorProduct.uncurry_apply

variable (R R'' M N P)
/-- A linear equivalence constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurryEquiv : (N →ₗ[R] M →ₗ[R''] P) ≃+ (M ⊗[R] N →ₗ[R''] P) where
  __ := uncurry R R'' M N P
  invFun := (lmk R R'' M N).hcompr₂
  left_inv _ := by ext; simp
  right_inv _ := LinearMap.toAddMonoidHom_injective (ext' fun _ _ ↦ lift.tmul _ _)
#align tensor_product.lift.equiv TensorProduct.uncurryEquiv

@[simp]
theorem uncurryEquiv_apply (f : N →ₗ[R] M →ₗ[R''] P) (m : M) (n : N) :
    uncurryEquiv R R'' M N P f (m ⊗ₜ n) = f n m :=
  uncurry_apply f m n
#align tensor_product.lift.equiv_apply TensorProduct.uncurryEquiv_apply

@[simp]
theorem uncurryEquiv_symm_apply (f : M ⊗[R] N →ₗ[R''] P) (m : M) (n : N) :
    (uncurryEquiv R R'' M N P).symm f n m = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.lift.equiv_symm_apply TensorProduct.uncurryEquiv_symm_apply

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def lcurry : (M ⊗[R] N →ₗ[R''] P) →+ (N →ₗ[R] M →ₗ[R''] P) :=
  (uncurryEquiv R R'' M N P).symm
#align tensor_product.lcurry TensorProduct.lcurry

variable {R R'' M N P}

@[simp]
theorem lcurry_apply (f : M ⊗[R] N →ₗ[R''] P) (m : M) (n : N) :
    lcurry R R'' M N P f n m = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.lcurry_apply TensorProduct.lcurry_apply

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def curry (f : M ⊗[R] N →ₗ[R''] P) : N →ₗ[R] M →ₗ[R''] P :=
  lcurry R R'' M N P f
#align tensor_product.curry TensorProduct.curry

@[simp]
theorem curry_apply (f : M ⊗[R] N →ₗ[R''] P) (m : M) (n : N) : curry f n m = f (m ⊗ₜ n) :=
  rfl
#align tensor_product.curry_apply TensorProduct.curry_apply

theorem curry_injective : Function.Injective (curry : (M ⊗[R] N →ₗ[R''] P) → N →ₗ[R] M →ₗ[R''] P) :=
  (uncurryEquiv R R'' M N P).symm.injective
#align tensor_product.curry_injective TensorProduct.curry_injective

end UMP

variable {M N}

section

variable (R N)

/-- In this declaration, `R` acts on the domain of `R →ₗ[R] N`, not the codomain. -/
@[simps] def _root_.LinearMap.smulEquiv : N ≃ₗ[R] (R →ₗ[R] N) where
  toFun n :=
  { __ := AddMonoidHom.smul.flip n
    map_smul' := fun r r' ↦ by simp [mul_smul] }
  map_add' n n' := by ext; simp
  map_smul' r n := by ext; simp
  invFun f := f 1
  left_inv n := by simp
  right_inv f := by ext; simp

/-- The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid : R ⊗[R] N ≃ₗ[R] N :=
  LinearEquiv.ofLinear (uncurry R R R N N <| LinearMap.smulEquiv R N)
    ((LinearMap.smulEquiv R <| R ⊗[R] N).symm.comp <| lmk R R R N)
    (LinearMap.ext fun _ ↦ by simp)
    (LinearMap.toAddMonoidHom_injective <| ext' fun r n ↦ by simp [smul_tmul'])
#align tensor_product.lid TensorProduct.lid

end

@[simp]
theorem lid_tmul (n : N) (r : R) : (TensorProduct.lid R N : R ⊗ N → N) (r ⊗ₜ n) = r • n :=
  rfl
#align tensor_product.lid_tmul TensorProduct.lid_tmul

@[simp]
theorem lid_symm_apply (n : N) : (TensorProduct.lid R N).symm n = 1 ⊗ₜ n :=
  rfl
#align tensor_product.lid_symm_apply TensorProduct.lid_symm_apply

section flip

variable (R M N P)

def _root_.LinearMap.flipMop : (N →ₗ[R] M →+ P) ≃+ (M →ₗ[Rᵐᵒᵖ] N →+ P) where
  toFun f :=
  { __ := f.toAddMonoidHom.flip
    map_smul' := fun r m ↦ by ext; simp }
  invFun f :=
  { __ := f.toAddMonoidHom.flip
    map_smul' := fun r n ↦ by ext; simp }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm : M ⊗[R] N ≃+ N ⊗[Rᵐᵒᵖ] M :=
  (lift <| (LinearMap.flipMop R M N _).symm <| mk Rᵐᵒᵖ N M).toAddEquiv
    (lift <| .flipMop R M N _ <| mk R M N) (ext' fun _ _ ↦ rfl) (ext' fun _ _ ↦ rfl)
#align tensor_product.comm TensorProduct.comm

@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl
#align tensor_product.comm_tmul TensorProduct.comm_tmul

@[simp]
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
#align tensor_product.comm_symm_tmul TensorProduct.comm_symm_tmul

lemma lift_comp_comm_eq  (f : N →ₗ[R] M →+ P) :
    (lift f).comp (TensorProduct.comm R M N).symm = lift (.flipMop R M N P f) :=
  ext rfl

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

attribute [local instance] SMulCommClass.symm in
def rightModuleEquivLeftModule : M ⊗[R] N ≃ₗ[S] N ⊗[Rᵐᵒᵖ] M where
  __ := TensorProduct.comm R M N
  map_smul' r x := x.induction_on (by simp) (fun m n ↦ rfl) fun x y hx hy ↦ by
    rw [AddHom.toFun_eq_coe] at hx hy ⊢
    rw [smul_add, map_add, map_add, smul_add, hx, hy]

end flip

section

open LinearMap

variable {L}
variable [Module R''ᵐᵒᵖ L] [SMulCommClass R'' Rᵐᵒᵖ M]

section

theorem ext₂₁ {g h : (L ⊗[R''] M) ⊗[R] N →+ P}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h :=
  ext' fun xy z ↦ xy.induction_on (by simp_rw [zero_tmul, map_zero]) (fun x y ↦ H x y z)
    fun _ _ e1 e2 ↦ by simp_rw [add_tmul, map_add, e1, e2]

theorem ext₁₂ {g h : L ⊗[R''] (M ⊗[R] N) →+ P}
    (H : ∀ x y z, g (x ⊗ₜ (y ⊗ₜ z)) = h (x ⊗ₜ (y ⊗ₜ z))) : g = h :=
  ext' fun x yz ↦ yz.induction_on (by simp_rw [tmul_zero, map_zero]) (H x)
    fun _ _ e1 e2 ↦ by simp_rw [tmul_add, map_add, e1, e2]

variable (R R'' L M N P)

@[simps] def lliftEquiv : (M →ₗ[R''] L →+ P) ≃ₗ[R] (L ⊗[R''] M →+ P) where
  __ := liftEquiv
  map_smul' r m := ext' fun _ _ ↦ by simp [smul_tmul'']

/-- The associator for tensor product of R-modules, as a linear equivalence.
  The `Rᵐᵒᵖ`-module structure on `P ⊗[R''] M` depends on the local instance `rightModule`.  -/
protected def assoc : (L ⊗[R''] M) ⊗[R] N ≃+ L ⊗[R''] (M ⊗[R] N) :=
  (lift <| (lliftEquiv R R'' L M _).comp <| lcurry R R'' M N _ <| mk R'' L _).toAddEquiv
    (lift <| uncurry _ _ _ _ _ <| (lliftEquiv R R'' L M _).symm.comp <| mk R _ N)
    (ext₂₁ fun _ _ _ ↦ by simp) (ext₁₂ fun _ _ _ ↦ by simp)
#align tensor_product.assoc TensorProduct.assoc

end

@[simp]
theorem assoc_tmul (l : L) (m : M) (n : N) :
    (TensorProduct.assoc R R'' L M N) (l ⊗ₜ m ⊗ₜ n) = l ⊗ₜ (m ⊗ₜ n) :=
  rfl
#align tensor_product.assoc_tmul TensorProduct.assoc_tmul

@[simp]
theorem assoc_symm_tmul (l : L) (m : M) (n : N) :
    (TensorProduct.assoc R R'' L M N).symm (l ⊗ₜ (m ⊗ₜ n)) = l ⊗ₜ m ⊗ₜ n :=
  rfl
#align tensor_product.assoc_symm_tmul TensorProduct.assoc_symm_tmul

end

end TensorProduct

namespace LinearMap

open TensorProduct

variable {L N} [Module Rᵐᵒᵖ P] [Module R Q]

/-- `lTensor M f : M ⊗ N →ₗ M ⊗ Q` is the natural linear map induced by `f : N →ₗ Q`. -/
def lTensor (f : N →ₗ[R] Q) : M ⊗[R] N →+ M ⊗[R] Q := lift ((TensorProduct.mk R M Q).comp f)

variable {M} (N)

/-- `rTensor f N : M ⊗ N →ₗ P ⊗ N` is the natural linear map induced by `f : M →ₗ P`. -/
def rTensor (f : M →ₗ[Rᵐᵒᵖ] P) : M ⊗[R] N →+ P ⊗[R] N :=
  lift <| (flipMop R M N _).symm ((flipMop R P N _ <| TensorProduct.mk R _ _).comp f)
#align linear_map.rtensor LinearMap.rTensor

variable (f : N →ₗ[R] Q) (g : M →ₗ[Rᵐᵒᵖ] P) {N}

@[simp]
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n :=
  rfl
#align linear_map.ltensor_tmul LinearMap.lTensor_tmul

@[simp]
theorem rTensor_tmul (m : M) (n : N) : g.rTensor N (m ⊗ₜ n) = g m ⊗ₜ n :=
  rfl
#align linear_map.rtensor_tmul LinearMap.rTensor_tmul

lemma comm_comp_rTensor_comp_comm_eq :
    AddMonoidHom.comp (TensorProduct.comm R P N)
      ((rTensor N g).comp (TensorProduct.comm R M N).symm) = lTensor N g :=
  TensorProduct.ext rfl

lemma comm_comp_lTensor_comp_comm_eq :
    AddMonoidHom.comp (TensorProduct.comm R P N).symm
      ((lTensor N g).comp <| TensorProduct.comm R M N) = rTensor N g :=
  TensorProduct.ext rfl

open TensorProduct

attribute [local ext high] TensorProduct.ext

variable (M)
/-- `lTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def lTensorHom : (N →ₗ[R] Q) →+ M ⊗[R] N →+ M ⊗[R] Q where
  toFun := lTensor M
  map_zero' := ext' fun _ _ ↦ by simp
  map_add' f g := ext' fun _ _ ↦ by simp [tmul_add]
#align linear_map.ltensor_hom LinearMap.lTensorHom

variable (R'') in
def llTensorHom [SMulCommClass R'' Rᵐᵒᵖ M] : (N →ₗ[R] Q) →+ M ⊗[R] N →ₗ[R''] M ⊗[R] Q where
  toFun f :=
  { __ := lTensor M f
    map_smul' := fun r x ↦ x.induction_on (by simp) (fun _ _ ↦ by simp [smul_tmul'])
      fun x y hx hy ↦ by
        rw [AddHom.toFun_eq_coe] at hx hy ⊢
        rw [smul_add, map_add, map_add, smul_add, hx, hy] }
  map_zero' := LinearMap.toAddMonoidHom_injective (ext' fun _ _ ↦ by simp)
  map_add' _ _ := LinearMap.toAddMonoidHom_injective (ext' fun _ _ ↦ by simp [tmul_add])

variable {M} (N)
/-- `rTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def rTensorHom : (M →ₗ[Rᵐᵒᵖ] P) →+ M ⊗[R] N →+ P ⊗[R] N where
  toFun f := f.rTensor N
  map_zero' := ext' fun _ _ ↦ by simp
  map_add' f g := ext' fun _ _ ↦ by simp [add_tmul]
#align linear_map.rtensor_hom LinearMap.rTensorHom

attribute [local instance] rightModule

def lrTensorHom (S) [Semiring S] [Module S N] [SMulCommClass R S N] :
    (M →ₗ[Rᵐᵒᵖ] P) →+ M ⊗[R] N →ₗ[S] P ⊗[R] N where
  toFun f :=
  { __ := rTensor N f
    map_smul' := fun r x ↦ x.induction_on (by simp) (fun _ _ ↦ by simp [smul_tmul''])
      fun x y hx hy ↦ by
        rw [AddHom.toFun_eq_coe] at hx hy ⊢
        rw [smul_add, map_add, map_add, smul_add, hx, hy] }
  map_zero' := LinearMap.toAddMonoidHom_injective (ext' fun _ _ ↦ by simp)
  map_add' _ _ := LinearMap.toAddMonoidHom_injective (ext' fun _ _ ↦ by simp [add_tmul])

def lrTensor' (S) [Semiring S] [Module S M] [Module S P]
    [SMulCommClass S Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ P] (f : M →ₗ[Rᵐᵒᵖ] P)
    (hf : IsLinearMap S f) : M ⊗[R] N →ₗ[S] P ⊗[R] N where
  __ := rTensor N f
  map_smul' s x := x.induction_on (by simp) (fun m n ↦ by simp [smul_tmul', hf.map_smul])
    fun x y hx hy ↦ by
      rw [AddHom.toFun_eq_coe] at hx hy ⊢
      rw [smul_add, map_add, map_add, smul_add, hx, hy]

variable {N}
theorem lTensor_comp [Module R S] (g : Q →ₗ[R] S) :
    (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := ext' fun _ _ ↦ by simp
#align linear_map.ltensor_comp LinearMap.lTensor_comp

theorem lTensor_comp_apply [Module R S] (g : Q →ₗ[R] S) (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp]; rfl
#align linear_map.ltensor_comp_apply LinearMap.lTensor_comp_apply

theorem rTensor_comp [Module Rᵐᵒᵖ S] (f : S →ₗ[Rᵐᵒᵖ] M) :
    (g.comp f).rTensor N = (g.rTensor N).comp (f.rTensor N) := ext' fun _ _ ↦ by simp
#align linear_map.rtensor_comp LinearMap.rTensor_comp

theorem rTensor_comp_apply [Module Rᵐᵒᵖ S] (f : S →ₗ[Rᵐᵒᵖ] M) (x : S ⊗[R] N) :
    (g.comp f).rTensor N x = (g.rTensor N) ((f.rTensor N) x) := by rw [rTensor_comp]; rfl
#align linear_map.rtensor_comp_apply LinearMap.rTensor_comp_apply

variable (N)

@[simp]
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = AddMonoidHom.id _ := ext' fun _ _ ↦ by simp
#align linear_map.ltensor_id LinearMap.lTensor_id

-- `simp` can prove this.
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id]; rfl
#align linear_map.ltensor_id_apply LinearMap.lTensor_id_apply

@[simp]
theorem rTensor_id : (id : M →ₗ[Rᵐᵒᵖ] M).rTensor N = AddMonoidHom.id _ := ext' fun _ _ ↦ by simp
#align linear_map.rtensor_id LinearMap.rTensor_id

-- `simp` can prove this.
theorem rTensor_id_apply (x : M ⊗[R] N) : (id : M →ₗ[Rᵐᵒᵖ] M).rTensor N x = x := by
  rw [rTensor_id]; rfl
#align linear_map.rtensor_id_apply LinearMap.rTensor_id_apply

variable (R'' M) {N}
nonrec def _root_.LinearEquiv.lTensor (f : N ≃ₗ[R] Q) : M ⊗[R] N ≃+ M ⊗[R] Q :=
  (f.lTensor M).toAddEquiv (f.symm.lTensor M) (by simp [← lTensor_comp]) (by simp [← lTensor_comp])

def _root_.LinearEquiv.llTensor [SMulCommClass R'' Rᵐᵒᵖ M] (f : N ≃ₗ[R] Q) :
    M ⊗[R] N ≃ₗ[R''] M ⊗[R] Q :=
  (f.lTensor M).toLinearEquiv (llTensorHom R'' M f.toLinearMap).map_smul

variable {M} (N)
nonrec def _root_.LinearEquiv.rTensor (f : M ≃ₗ[Rᵐᵒᵖ] P) : M ⊗[R] N ≃+ P ⊗[R] N :=
  (f.rTensor N).toAddEquiv (f.symm.rTensor N) (by simp [← rTensor_comp]) (by simp [← rTensor_comp])

def _root_.LinearEquiv.lrTensor (S) [Semiring S] [Module S N] [SMulCommClass R S N]
    (f : M ≃ₗ[Rᵐᵒᵖ] P) : M ⊗[R] N ≃ₗ[S] P ⊗[R] N :=
  (f.rTensor N).toLinearEquiv (lrTensorHom N S f.toLinearMap).map_smul

nonrec def _root_.LinearEquiv.lrTensor' (S) [Semiring S] [Module S M] [Module S P]
    [SMulCommClass S Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ P] (f : M ≃ₗ[Rᵐᵒᵖ] P)
    (hf : IsLinearMap S f) : M ⊗[R] N ≃ₗ[S] P ⊗[R] N :=
  (f.rTensor N).toLinearEquiv (f.toLinearMap.lrTensor' N S hf).map_smul

variable (R)

/-- The same definition works if `Rᵐᵒᵖᵐᵒᵖ` is replaced by `Rᵐᵒᵖ`
  or `R` (once the `R`-action on `Rᵐᵒᵖ` is defined). -/
protected def _root_.LinearEquiv.opOpOp : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖᵐᵒᵖ] R where
  toFun := MulOpposite.unop
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl

end LinearMap

namespace TensorProduct

section

variable (R)

attribute [local instance] rightModule

/-- The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid : M ⊗[R] R ≃ₗ[Rᵐᵒᵖ] M :=
  (rightModuleEquivLeftModule R M R Rᵐᵒᵖ) ≪≫ₗ
    (LinearEquiv.opOpOp R).symm.lrTensor' M Rᵐᵒᵖ ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ ≪≫ₗ
      TensorProduct.lid Rᵐᵒᵖ M
#align tensor_product.rid TensorProduct.rid

end

@[simp]
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = op r • m :=
  rfl
#align tensor_product.rid_tmul TensorProduct.rid_tmul

@[simp]
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl
#align tensor_product.rid_symm_apply TensorProduct.rid_symm_apply

variable [Module Rᵐᵒᵖ P] [Module R Q] (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) {M N}

/-- The tensor product of a pair of linear maps between modules. -/
def map : M ⊗[R] N →+ P ⊗[R] Q := (g.lTensor P).comp (f.rTensor N)
#align tensor_product.map TensorProduct.map

@[simp]
theorem map_tmul (m : M) (n : N) : map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
#align tensor_product.map_tmul TensorProduct.map_tmul

instance : LinearMap.CompatibleSMul N Q Rᵐᵒᵖᵐᵒᵖ R where
  map_smul f _ _ := f.map_smul _ _

lemma map_comp_comm_eq :
    (map (g.restrictScalars _) f).comp (TensorProduct.comm R M N).toAddMonoidHom =
      (TensorProduct.comm R P Q).toAddMonoidHom.comp (map f g) :=
  ext rfl

open AddMonoidHom in
theorem map_range_eq_span_tmul :
    AddMonoidHom.mrange (map f g) = AddSubmonoid.closure { t | ∃ m n, f m ⊗ₜ g n = t } := by
  rw [mrange_eq_map, ← closure_tmul_eq_top, map_mclosure]
  congr; ext t
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    use m, n
    simp only [map_tmul]
  · rintro ⟨m, n, rfl⟩
    refine ⟨_, ⟨m, n, rfl⟩, ?_⟩
    simp only [map_tmul]
#align tensor_product.map_range_eq_span_tmul TensorProduct.map_range_eq_span_tmul

/-- Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗ q → P ⊗ Q`. -/
@[simp]
def mapIncl (p : Submodule Rᵐᵒᵖ P) (q : Submodule R Q) : p ⊗[R] q →+ P ⊗[R] Q :=
  map p.subtype q.subtype
#align tensor_product.map_incl TensorProduct.mapIncl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module Rᵐᵒᵖ P']
variable [AddCommMonoid Q'] [Module R Q']

theorem map_comp (f₂ : P →ₗ[Rᵐᵒᵖ] P') (f₁ : M →ₗ[Rᵐᵒᵖ] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext' fun _ _ => rfl
#align tensor_product.map_comp TensorProduct.map_comp

def LinearMap.compAddMonoidHom : (M →ₗ[Rᵐᵒᵖ] P) →+ (P →+ Q') →ₗ[R] M →+ Q' where
  toFun f :=
  { __ := f.toAddMonoidHom.compHom'
    map_smul' := fun r g ↦ by ext; simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

theorem lift_comp_map (i : Q →ₗ[R] P →+ Q') (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) :
    (lift i).comp (map f g) = lift ((LinearMap.compAddMonoidHom f).comp <| i.comp g) :=
  ext' fun _ _ => rfl
#align tensor_product.lift_comp_map TensorProduct.lift_comp_map

attribute [local ext high] ext

@[simp]
theorem map_id : map (.id : M →ₗ[Rᵐᵒᵖ] M) (.id : N →ₗ[R] N) = .id _ := by
  ext; rfl
#align tensor_product.map_id TensorProduct.map_id

theorem map_add_left (f₁ f₂ : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext; simp [add_tmul]
#align tensor_product.map_add_left TensorProduct.map_add_left

theorem map_add_right (f : M →ₗ[Rᵐᵒᵖ] P) (g₁ g₂ : N →ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext; simp [tmul_add]
#align tensor_product.map_add_right TensorProduct.map_add_right

variable (R M N P Q)

/-- The tensor product of a pair of linear maps between modules, bilinear in both maps. -/
def mapBilinear : (M →ₗ[Rᵐᵒᵖ] P) →+ (N →ₗ[R] Q) →+ M ⊗[R] N →+ P ⊗[R] Q where
  toFun f :=
  { toFun := map f
    map_zero' := by ext; simp
    map_add' := fun _ _ ↦ by ext; simp [tmul_add] }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_tmul]
#align tensor_product.map_bilinear TensorProduct.mapBilinear

variable {R M N P Q}

@[simp]
theorem mapBilinear_apply (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) : mapBilinear R M N P Q f g = map f g :=
  rfl
#align tensor_product.map_bilinear_apply TensorProduct.mapBilinear_apply

end

end TensorProduct

namespace LinearMap

open TensorProduct

variable [Module Rᵐᵒᵖ P] [Module R Q] (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) {N}

@[simp]
theorem lTensor_comp_rTensor :
    (g.lTensor P).comp (f.rTensor N) = map f g :=
  rfl
#align linear_map.ltensor_comp_rtensor LinearMap.lTensor_comp_rTensor

@[simp]
theorem rTensor_comp_lTensor :
    (f.rTensor Q).comp (g.lTensor M) = map f g :=
  ext' fun _ _ ↦ rfl
#align linear_map.rtensor_comp_ltensor LinearMap.rTensor_comp_lTensor

@[simp]
theorem map_comp_rTensor [Module Rᵐᵒᵖ S] (f' : S →ₗ[Rᵐᵒᵖ] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g :=
  ext' fun _ _ ↦ rfl
#align linear_map.map_comp_rtensor LinearMap.map_comp_rTensor

@[simp]
theorem map_comp_lTensor (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') :=
  ext' fun _ _ ↦ rfl
#align linear_map.map_comp_ltensor LinearMap.map_comp_lTensor

@[simp]
theorem rTensor_comp_map [Module Rᵐᵒᵖ S] (f' : P →ₗ[Rᵐᵒᵖ] S) (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g :=
  ext' fun _ _ ↦ rfl
#align linear_map.rtensor_comp_map LinearMap.rTensor_comp_map

@[simp]
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[Rᵐᵒᵖ] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) :=
  ext' fun _ _ ↦ rfl
#align linear_map.ltensor_comp_map LinearMap.lTensor_comp_map

end LinearMap

namespace TensorProduct

variable {M N} [Module Rᵐᵒᵖ P] [Module R Q]

/-- If `M` and `P` are linearly equivalent and `N` and `Q` are linearly equivalent
then `M ⊗ N` and `P ⊗ Q` are linearly equivalent. -/
def congr (f : M ≃ₗ[Rᵐᵒᵖ] P) (g : N ≃ₗ[R] Q) : M ⊗[R] N ≃+ P ⊗[R] Q :=
  (map f g).toAddEquiv (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)
#align tensor_product.congr TensorProduct.congr

@[simp]
theorem congr_tmul (f : M ≃ₗ[Rᵐᵒᵖ] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
#align tensor_product.congr_tmul TensorProduct.congr_tmul

@[simp]
theorem congr_symm_tmul (f : M ≃ₗ[Rᵐᵒᵖ] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl
#align tensor_product.congr_symm_tmul TensorProduct.congr_symm_tmul

variable (R R'' T M P Q)
variable [Module R''ᵐᵒᵖ L] [SMulCommClass R'' Rᵐᵒᵖ M] [Module R P]
variable [Semiring T] [Module Tᵐᵒᵖ P] [SMulCommClass R Tᵐᵒᵖ P] [Module T Q]

attribute [local instance] rightModule

/- Why is this necessary? -/
instance : SMulCommClass R'' Tᵐᵒᵖ (M ⊗[R] P) := TensorProduct.smulCommClass

/-- This special case is useful for describing the interplay between `dualTensorHomEquiv` and
composition of linear maps.

E.g., composition of linear maps gives a map `(M → N) ⊗ (N → P) → (M → P)`, and applying
`dual_tensor_hom_equiv.symm` to the three hom-modules gives a map
`(M.dual ⊗ N) ⊗ (N.dual ⊗ P) → (M.dual ⊗ P)`, which agrees with the application of `contractRight`
on `N ⊗ N.dual` after the suitable rebracketting.
-/
def tensorTensorTensorAssoc : (L ⊗[R''] M) ⊗[R] P ⊗[T] Q ≃+ (L ⊗[R''] M ⊗[R] P) ⊗[T] Q :=
  (TensorProduct.assoc T R (L ⊗[R''] M) P Q).symm.trans <| congr
    { __ := TensorProduct.assoc R R'' L M P
      map_smul' := fun r x ↦ by
        let f := (TensorProduct.assoc R R'' L M P).toAddMonoidHom
        suffices : f.comp (DistribMulAction.toAddMonoidHom _ r)
          = (DistribMulAction.toAddMonoidHom _ r).comp f
        · exact FunLike.congr_fun this x
        exact ext₂₁ fun _ _ _ ↦ rfl }
    (1 : Q ≃ₗ[T] Q)
#align tensor_product.tensor_tensor_tensor_assoc TensorProduct.tensorTensorTensorAssoc

variable {L M P Q}

@[simp]
theorem tensorTensorTensorAssoc_tmul (l : L) (m : M) (p : P) (q : Q) :
    tensorTensorTensorAssoc R R'' L M P Q T (l ⊗ₜ m ⊗ₜ (p ⊗ₜ q)) = l ⊗ₜ (m ⊗ₜ p) ⊗ₜ q :=
  rfl
#align tensor_product.tensor_tensor_tensor_assoc_tmul TensorProduct.tensorTensorTensorAssoc_tmul

@[simp]
theorem tensorTensorTensorAssoc_symm_tmul (l : L) (m : M) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R R'' L M P Q T).symm (l ⊗ₜ (m ⊗ₜ p) ⊗ₜ q) = l ⊗ₜ m ⊗ₜ (p ⊗ₜ q) :=
  rfl
#align tensor_product.tensor_tensor_tensor_assoc_symm_tmul TensorProduct.tensorTensorTensorAssoc_symm_tmul

end TensorProduct

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
variable [Module Rᵐᵒᵖ M] [Module R N] [Module R P] [Module R Q] [Module R S]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R)

/-- Auxiliary function to defining negation multiplication on tensor product. -/
def Neg.aux : M ⊗[R] N →+ M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)
#noalign tensor_product.neg.aux

variable {R}

#noalign tensor_product.neg.aux_of

instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R

protected theorem add_left_neg (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert (tmul_add (R := R) x (-y) y).symm; rw [add_left_neg, tmul_zero])
    fun x y hx hy => by
    suffices : -x + x + (-y + y) = 0
    · rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]
#align tensor_product.add_left_neg TensorProduct.add_left_neg

instance addCommGroup : AddCommGroup (M ⊗[R] N) :=
  { TensorProduct.addCommMonoid with
    neg := Neg.neg
    sub := _
    sub_eq_add_neg := fun _ _ => rfl
    add_left_neg := fun x => TensorProduct.add_left_neg x
    zsmul := fun n v => n • v
    zsmul_zero' := by simp [TensorProduct.zero_smul]
    zsmul_succ' := by simp [Nat.succ_eq_one_add, TensorProduct.one_smul, TensorProduct.add_smul]
    zsmul_neg' := fun n x => by
      change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
      rw [← zero_add (_ • x), ← TensorProduct.add_left_neg ((n.succ : ℤ) • x), add_assoc,
        ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
      rfl }

theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  (mk R M N _).map_neg _
#align tensor_product.neg_tmul TensorProduct.neg_tmul

theorem tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -m ⊗ₜ[R] n :=
  rfl
#align tensor_product.tmul_neg TensorProduct.tmul_neg

theorem tmul_sub (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ - n₂) = m ⊗ₜ[R] n₁ - m ⊗ₜ[R] n₂ :=
  Eq.trans (by rw [sub_eq_add_neg]) (tmul_add m n₁ (-n₂))
#align tensor_product.tmul_sub TensorProduct.tmul_sub

theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N _).map_sub _ _
#align tensor_product.sub_tmul TensorProduct.sub_tmul

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.intModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M N :=
  ⟨fun r m n =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩
#align tensor_product.compatible_smul.int TensorProduct.CompatibleSMul.int

instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => (CompatibleSMul.smul_tmul (s : S) m n : _)⟩
#align tensor_product.compatible_smul.unit TensorProduct.CompatibleSMul.unit

end TensorProduct

namespace LinearMap

variable [Module Rᵐᵒᵖ P]

@[simp]
theorem lTensor_sub (f g : N →ₗ[R] Q) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  exact (lTensorHom M).map_sub f g
#align linear_map.ltensor_sub LinearMap.lTensor_sub

@[simp]
theorem rTensor_sub (f g : M →ₗ[Rᵐᵒᵖ] P) : (f - g).rTensor N = f.rTensor N - g.rTensor N := by
  exact (rTensorHom N).map_sub f g
#align linear_map.rtensor_sub LinearMap.rTensor_sub

@[simp]
theorem lTensor_neg (f : N →ₗ[R] Q) : (-f).lTensor M = -f.lTensor M := by
  exact (lTensorHom M).map_neg f
#align linear_map.ltensor_neg LinearMap.lTensor_neg

@[simp]
theorem rTensor_neg (f : M →ₗ[Rᵐᵒᵖ] P) : (-f).rTensor N = -f.rTensor N := by
  exact (rTensorHom N).map_neg f
#align linear_map.rtensor_neg LinearMap.rTensor_neg

end LinearMap

end Ring
