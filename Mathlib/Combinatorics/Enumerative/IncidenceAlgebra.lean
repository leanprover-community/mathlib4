/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.

This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.

This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.

The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.

## Main definitions

* `1 : IncidenceAlgebra 𝕜 α` is the delta function, defined analogously to the identity matrix.
* `f * g` is the incidence algebra product, defined analogously to the matrix product.
* `IncidenceAlgebra.zeta` is the zeta function, defined analogously to the upper triangular matrix
  of ones.
* `IncidenceAlgebra.mu` is the inverse of the zeta function.

## Implementation notes

One has to define `mu` as either the left or right inverse of `zeta`. We define it as the left
inverse, and prove it is also a right inverse by defining `mu'` as the right inverse and using that
left and right inverses agree if they exist.

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulas for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.

## References

* [Aigner, *Combinatorial Theory, Chapter IV*][aigner1997]
* [Jacobson, *Basic Algebra I, 8.6*][jacobson1974]
* [Doubilet, Rota, Stanley, *On the foundations of Combinatorial Theory
  VI*][doubilet_rota_stanley_vi]
* [Spiegel, O'Donnell, *Incidence Algebras*][spiegel_odonnel1997]
* [Kung, Rota, Yan, *Combinatorics: The Rota Way, Chapter 3*][kung_rota_yan2009]
-/

open Finset OrderDual

variable {F 𝕜 𝕝 𝕞 α β : Type*}

/-- The `𝕜`-incidence algebra over `α`. -/
structure IncidenceAlgebra (𝕜 α : Type*) [Zero 𝕜] [LE α] where
  /-- The underlying function of an element of the incidence algebra.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → α → 𝕜
  eq_zero_of_not_le' ⦃a b : α⦄ : ¬a ≤ b → toFun a b = 0

namespace IncidenceAlgebra
section Zero
variable [Zero 𝕜] [LE α] {a b : α}

instance instFunLike : FunLike (IncidenceAlgebra 𝕜 α) α (α → 𝕜) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

lemma apply_eq_zero_of_not_le (h : ¬a ≤ b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0 :=
  eq_zero_of_not_le' _ h

lemma le_of_ne_zero {f : IncidenceAlgebra 𝕜 α} : f a b ≠ 0 → a ≤ b :=
  not_imp_comm.1 fun h ↦ apply_eq_zero_of_not_le h _

section Coes

-- this must come after the `FunLike` instance
initialize_simps_projections IncidenceAlgebra (toFun → apply)

@[simp] lemma toFun_eq_coe (f : IncidenceAlgebra 𝕜 α) : f.toFun = f := rfl
@[simp, norm_cast] lemma coe_mk (f : α → α → 𝕜) (h) : (mk f h : α → α → 𝕜) = f := rfl

lemma coe_inj {f g : IncidenceAlgebra 𝕜 α} : (f : α → α → 𝕜) = g ↔ f = g :=
  DFunLike.coe_injective.eq_iff

@[ext]
lemma ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : ∀ a b, a ≤ b → f a b = g a b) : f = g := by
  refine DFunLike.coe_injective' (funext₂ fun a b ↦ ?_)
  by_cases hab : a ≤ b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]

@[simp] lemma mk_coe (f : IncidenceAlgebra 𝕜 α) (h) : mk f h = f := rfl

end Coes

/-! ### Additive and multiplicative structure -/

instance instZero : Zero (IncidenceAlgebra 𝕜 α) := ⟨⟨fun _ _ ↦ 0, fun _ _ _ ↦ rfl⟩⟩
instance instInhabited : Inhabited (IncidenceAlgebra 𝕜 α) := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : IncidenceAlgebra 𝕜 α) = 0 := rfl
lemma zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0 := rfl

end Zero

section Add
variable [AddZeroClass 𝕜] [LE α]

instance instAdd : Add (IncidenceAlgebra 𝕜 α) where
  add f g := ⟨f + g, fun a b h ↦ by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩

@[simp, norm_cast] lemma coe_add (f g : IncidenceAlgebra 𝕜 α) : ⇑(f + g) = f + g := rfl
lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl

end Add

section Smul
variable {M : Type*} [Zero 𝕜] [LE α] [SMulZeroClass M 𝕜]

instance instSmulZeroClassRight : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  smul c f :=
    ⟨c • ⇑f, fun a b hab ↦ by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _

@[simp, norm_cast] lemma coe_constSMul (c : M) (f : IncidenceAlgebra 𝕜 α) : ⇑(c • f) = c • ⇑f := rfl

lemma constSMul_apply (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α) : (c • f) a b = c • f a b := rfl

end Smul

instance instAddMonoid [AddMonoid 𝕜] [LE α] : AddMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ ↦ rfl

instance instAddCommMonoid [AddCommMonoid 𝕜] [LE α] : AddCommMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ ↦ rfl

section AddGroup
variable [AddGroup 𝕜] [LE α]

instance instNeg : Neg (IncidenceAlgebra 𝕜 α) where
  neg f := ⟨-f, fun a b h ↦ by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩

instance instSub : Sub (IncidenceAlgebra 𝕜 α) where
  sub f g := ⟨f - g, fun a b h ↦ by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩

@[simp, norm_cast] lemma coe_neg (f : IncidenceAlgebra 𝕜 α) : ⇑(-f) = -f := rfl
@[simp, norm_cast] lemma coe_sub (f g : IncidenceAlgebra 𝕜 α) : ⇑(f - g) = f - g := rfl
lemma neg_apply (f : IncidenceAlgebra 𝕜 α) (a b : α) : (-f) a b = -f a b := rfl
lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl

instance instAddGroup : AddGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end AddGroup

instance instAddCommGroup [AddCommGroup 𝕜] [LE α] : AddCommGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

section One
variable [Preorder α] [DecidableEq α] [Zero 𝕜] [One 𝕜]

/-- The unit incidence algebra is the delta function, whose entries are `0` except on the diagonal
where they are `1`. -/
instance instOne : One (IncidenceAlgebra 𝕜 α) :=
  ⟨⟨fun a b ↦ if a = b then 1 else 0, fun _a _b h ↦ ite_eq_right_iff.2 fun H ↦ (h H.le).elim⟩⟩

@[simp] lemma one_apply (a b : α) : (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end One

section Mul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Mul 𝕜]

/--
The multiplication operation in incidence algebras is defined on an interval by summing over
all divisions into two subintervals the product of the values of the original pair of functions.
-/
instance instMul : Mul (IncidenceAlgebra 𝕜 α) where
  mul f g :=
    ⟨fun a b ↦ ∑ x ∈ Icc a b, f a x * g x b, fun a b h ↦ by dsimp; rw [Icc_eq_empty h, sum_empty]⟩

@[simp] lemma mul_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) :
    (f * g) a b = ∑ x ∈ Icc a b, f a x * g x b := rfl

end Mul

instance instNonUnitalNonAssocSemiring [Preorder α] [LocallyFiniteOrder α]
    [NonUnitalNonAssocSemiring 𝕜] : NonUnitalNonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instAddCommMonoid
  mul := (· * ·)
  zero := 0
  zero_mul := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ MulZeroClass.zero_mul _
  mul_zero := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ MulZeroClass.mul_zero _
  left_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ left_distrib _ _ _) sum_add_distrib
  right_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ right_distrib _ _ _) sum_add_distrib

instance instNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
    [NonAssocSemiring 𝕜] : NonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonUnitalNonAssocSemiring
  mul := (· * ·)
  zero := 0
  one := 1
  one_mul := fun f ↦ by ext; simp [*]
  mul_one := fun f ↦ by ext; simp [*]

instance instSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] :
    Semiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonAssocSemiring
  mul := (· * ·)
  mul_assoc f g h := by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;>
      aesop (add simp mul_assoc) (add unsafe le_trans)
  one := 1
  zero := 0

instance instRing [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜] :
    Ring (IncidenceAlgebra 𝕜 α) where
  __ := instSemiring
  __ := instAddGroup

/-! ### Scalar multiplication between incidence algebras -/

section SMul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [AddCommMonoid 𝕝] [SMul 𝕜 𝕝]

instance instSMul : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) :=
  ⟨fun f g ↦
    ⟨fun a b ↦ ∑ x ∈ Icc a b, f a x • g x b, fun a b h ↦ by dsimp; rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]
lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
    (f • g) a b = ∑ x ∈ Icc a b, f a x • g x b :=
  rfl

end SMul

instance instIsScalarTower [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
    [Semiring 𝕝] [AddCommMonoid 𝕞] [SMul 𝕜 𝕝] [Module 𝕝 𝕞] [DistribMulAction 𝕜 𝕞]
    [IsScalarTower 𝕜 𝕝 𝕞] :
    IsScalarTower (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) (IncidenceAlgebra 𝕞 α) where
  smul_assoc f g h := by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;> aesop (add unsafe le_trans)

instance [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
    [Module 𝕜 𝕝] : Module (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) where
  smul := (· • ·)
  one_smul f := by ext a b hab; simp [ite_smul, hab]
  mul_smul := smul_assoc
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_eq_zero fun x _ ↦ zero_smul _ _
  smul_zero f := by ext; exact sum_eq_zero fun x _ ↦ smul_zero _

instance smulWithZeroRight [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α] :
    SMulWithZero 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩
    coe_constSMul

instance moduleRight [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝] :
    Module 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩, coe_add⟩
    coe_constSMul

instance algebraRight [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
    [CommSemiring 𝕝] [Algebra 𝕜 𝕝] : Algebra 𝕜 (IncidenceAlgebra 𝕝 α) where
  algebraMap :=
  { toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
    map_one' := by
      ext; simp only [mul_boole, one_apply, Algebra.id.smul_eq_mul, constSMul_apply, map_one]
    map_mul' c d := by
        ext a b
        obtain rfl | h := eq_or_ne a b
        · simp only [one_apply, Algebra.id.smul_eq_mul, mul_apply,
            constSMul_apply, map_mul,
            eq_comm, Icc_self]
          simp
        · simp only [one_apply, mul_one, Algebra.id.smul_eq_mul,
            mul_apply, MulZeroClass.zero_mul, constSMul_apply,
            ← ite_and, ite_mul, mul_ite, map_mul,
            MulZeroClass.mul_zero, if_neg h]
          refine (sum_eq_zero fun x _ ↦ ?_).symm
          exact if_neg fun hx ↦ h <| hx.2.trans hx.1
    map_zero' := by rw [map_zero, zero_smul]
    map_add' c d := by rw [map_add, add_smul] }
  commutes' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, mul_comm]
  smul_def' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, Algebra.smul_def]

/-! ### The Lambda function -/

section Lambda
variable (𝕜) [Zero 𝕜] [One 𝕜] [Preorder α] [DecidableRel (α := α) (· ⩿ ·)]

/-- The lambda function of the incidence algebra is the function that assigns `1` to every nonempty
interval of cardinality one or two. -/
@[simps]
def lambda : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ if a ⩿ b then 1 else 0, fun _a _b h ↦ if_neg fun hh ↦ h hh.le⟩

end Lambda

/-! ### The Zeta and Möbius functions -/

section Zeta
variable (𝕜) [Zero 𝕜] [One 𝕜] [LE α] [DecidableLE α] {a b : α}

/-- The zeta function of the incidence algebra is the function that assigns 1 to every nonempty
interval, convolution with this function sums functions over intervals. -/
def zeta : IncidenceAlgebra 𝕜 α := ⟨fun a b ↦ if a ≤ b then 1 else 0, fun _a _b h ↦ if_neg h⟩

variable {𝕜}

@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 a b = if a ≤ b then 1 else 0 := rfl

lemma zeta_of_le (h : a ≤ b) : zeta 𝕜 a b = 1 := if_pos h

end Zeta

lemma zeta_mul_zeta [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul]

lemma zeta_mul_kappa [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul]

section Mu
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

/-- The Möbius function of the incidence algebra as a bare function defined recursively. -/
private def muFun (a : α) : α → 𝕜
  | b =>
    if a = b then 1
    else
      -∑ x ∈ (Ico a b).attach,
          let h := mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muFun a x
termination_by b => (Icc a b).card

private lemma muFun_apply (a b : α) :
    muFun 𝕜 a b = if a = b then 1 else -∑ x ∈ (Ico a b).attach, muFun 𝕜 a x := by rw [muFun]

/-- The Möbius function which inverts `zeta` as an element of the incidence algebra. -/
def mu : IncidenceAlgebra 𝕜 α :=
  ⟨muFun 𝕜, fun a b ↦ not_imp_comm.1 fun h ↦ by
    rw [muFun_apply] at h
    split_ifs at h with hab
    · exact hab.le
    · rw [neg_eq_zero] at h
      obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
      exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}

lemma mu_apply (a b : α) : mu 𝕜 a b = if a = b then 1 else -∑ x ∈ Ico a b, mu 𝕜 a x := by
  rw [mu, coe_mk, muFun_apply, sum_attach]

@[simp] lemma mu_self (a : α) : mu 𝕜 a a = 1 := by simp [mu_apply]

lemma mu_eq_neg_sum_Ico_of_ne (hab : a ≠ b) :
    mu 𝕜 a b = -∑ x ∈ Ico a b, mu 𝕜 a x := by rw [mu_apply, if_neg hab]

variable (𝕜 α)
/-- The Euler characteristic of a finite bounded order. -/
def eulerChar [BoundedOrder α] : 𝕜 := mu 𝕜 (⊥ : α) ⊤

end Mu

section MuSpec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

lemma sum_Icc_mu_right (a b : α) : ∑ x ∈ Icc a b, mu 𝕜 a x = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a ≤ b
  · simp [Icc_eq_cons_Ico hab, mu_eq_neg_sum_Ico_of_ne ‹_›]
  · exact sum_eq_zero fun x hx ↦ apply_eq_zero_of_not_le
      (fun hax ↦ hab <| hax.trans (mem_Icc.1 hx).2) _

end MuSpec

section Mu'
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

/-- `mu'` as a bare function defined recursively. -/
private def muFun' (b : α) : α → 𝕜
  | a =>
    if a = b then 1
    else
      -∑ x ∈ (Ioc a b).attach,
          let h := mem_Ioc.1 x.2
          have : (Icc ↑x b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          muFun' b x
termination_by a => (Icc a b).card

private lemma muFun'_apply (a b : α) :
    muFun' 𝕜 b a = if a = b then 1 else -∑ x ∈ (Ioc a b).attach, muFun' 𝕜 b x := by
  rw [muFun']

/-- This is the reversed definition of `mu`, which is equal to `mu` but easiest to prove equal by
showing that `zeta * mu = 1` and `mu' * zeta = 1`. -/
private def mu' : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ muFun' 𝕜 b a, fun a b ↦
    not_imp_comm.1 fun h ↦ by
      dsimp only at h
      rw [muFun'_apply] at h
      split_ifs at h with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}

private lemma mu'_apply (a b : α) : mu' 𝕜 a b = if a = b then 1 else -∑ x ∈ Ioc a b, mu' 𝕜 x b := by
  rw [mu', coe_mk, muFun'_apply, sum_attach]

@[simp] private lemma mu'_apply_self (a : α) : mu' 𝕜 a a = 1 := by simp [mu'_apply]

private lemma mu'_eq_sum_Ioc_of_ne (h : a ≠ b) : mu' 𝕜 a b = -∑ x ∈ Ioc a b, mu' 𝕜 x b := by
  rw [mu'_apply, if_neg h]

end Mu'

section Mu'Spec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

private lemma sum_Icc_mu'_left (a b : α) : ∑ x ∈ Icc a b, mu' 𝕜 x b = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a ≤ b
  · simp [Icc_eq_cons_Ioc hab, mu'_eq_sum_Ioc_of_ne ‹_›]
  · exact sum_eq_zero fun x hx ↦ apply_eq_zero_of_not_le
      (fun hxb ↦ hab <| (mem_Icc.1 hx).1.trans hxb) _

end Mu'Spec

section MuZeta
variable (𝕜 α) [AddCommGroup 𝕜] [MulOneClass 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [DecidableEq α] [DecidableLE α]

lemma mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x ∈ Icc a b, mu 𝕜 a x := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).2]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu_right ..

private lemma zeta_mul_mu' : (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x ∈ Icc a b, mu' 𝕜 x b := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).1]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu'_left ..

end MuZeta

section MuEqMu'
variable [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

private lemma mu_eq_mu' : (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜 := by
  classical
  exact left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)

lemma mu_eq_neg_sum_Ioc_of_ne (hab : a ≠ b) : mu 𝕜 a b = -∑ x ∈ Ioc a b, mu 𝕜 x b := by
  rw [mu_eq_mu', mu'_eq_sum_Ioc_of_ne hab]

lemma zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  rw [mu_eq_mu', zeta_mul_mu']

lemma sum_Icc_mu_left (a b : α) : ∑ x ∈ Icc a b, mu 𝕜 x b = if a = b then 1 else 0 := by
  rw [mu_eq_mu', sum_Icc_mu'_left]

end MuEqMu'

section OrderDual
variable (𝕜) [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

@[simp]
lemma mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a := by
  letI : DecidableLE α := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b ↦ mu 𝕜 (ofDual b) (ofDual a)
      eq_zero_of_not_le' := fun a b hab ↦ apply_eq_zero_of_not_le (by exact hab) _ }
  suffices mu 𝕜 = mud by simp_rw [this, mud, coe_mk, ofDual_toDual]
  suffices mud * zeta 𝕜 = 1 by
    rw [← mu_mul_zeta] at this
    apply_fun (· * mu 𝕜) at this
    symm
    simpa [mul_assoc, zeta_mul_mu] using this
  clear a b
  ext a b
  simp only [mul_boole, one_apply, mul_apply, zeta_apply]
  calc
    ∑ x ∈ Icc a b, (if x ≤ b then mud a x else 0) = ∑ x ∈ Icc a b, mud a x := by
      congr! with x hx; exact if_pos (mem_Icc.1 hx).2
    _ = ∑ x ∈ Icc (ofDual b) (ofDual a), mu 𝕜 x (ofDual a) := by simp [Icc_orderDual_def, mud]
    _ = if ofDual b = ofDual a then 1 else 0 := sum_Icc_mu_left ..
    _ = if a = b then 1 else 0 := by simp [eq_comm]

@[simp] lemma mu_ofDual (a b : αᵒᵈ) : mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a := (mu_toDual ..).symm

@[simp]
lemma eulerChar_orderDual [BoundedOrder α] : eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α := by
  simp [eulerChar, ← mu_toDual 𝕜 (α := α)]

end OrderDual

section InversionTop
variable [Ring 𝕜] [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/-- A general form of Möbius inversion. Based on lemma 2.1.2 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_top (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Ici x, f y) (x : α) :
    f x = ∑ y ∈ Ici x, mu 𝕜 x y * g y := by
  letI : DecidableLE α := Classical.decRel _
  symm
  calc
    ∑ y ∈ Ici x, mu 𝕜 x y * g y = ∑ y ∈ Ici x, mu 𝕜 x y * ∑ z ∈ Ici y, f z := by simp_rw [h]
    _ = ∑ y ∈ Ici x, mu 𝕜 x y * ∑ z ∈ Ici y, zeta 𝕜 y z * f z := by
      congr with y
      rw [sum_congr rfl fun z hz ↦ ?_]
      rw [zeta_apply, if_pos (mem_Ici.mp ‹_›), one_mul]
    _ = ∑ y ∈ Ici x, ∑ z ∈ Ici y, mu 𝕜 x y * zeta 𝕜 y z * f z := by simp [mul_sum]
    _ = ∑ z ∈ Ici x, ∑ y ∈ Icc x z, mu 𝕜 x y * zeta 𝕜 y z * f z := by
      rw [sum_sigma' (Ici x) fun y ↦ Ici y]
      rw [sum_sigma' (Ici x) fun z ↦ Icc x z]
      simp only [mul_boole, MulZeroClass.zero_mul, ite_mul, zeta_apply]
      apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;>
        aesop (add simp mul_assoc) (add unsafe le_trans)
    _ = ∑ z ∈ Ici x, (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp_rw [mul_apply, sum_mul]
    _ = ∑ y ∈ Ici x, ∑ z ∈ Ici y, (1 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp only [mu_mul_zeta 𝕜, one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici, le_refl,
        ↓reduceIte, ← add_sum_Ioi_eq_sum_Ici, left_eq_add]
      exact sum_eq_zero fun y hy ↦ if_neg (mem_Ioi.mp hy).not_ge
    _ = f x := by
      simp only [one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici,
        ← add_sum_Ioi_eq_sum_Ici, le_refl, ↓reduceIte, add_eq_left]
      exact sum_eq_zero fun y hy ↦ if_neg (mem_Ioi.mp hy).not_ge

end InversionTop

section InversionBot
variable [Ring 𝕜] [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]

/-- A general form of Möbius inversion. Based on lemma 2.1.3 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_bot (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Iic x, f y) (x : α) :
    f x = ∑ y ∈ Iic x, mu 𝕜 y x * g y := by
  convert moebius_inversion_top (α := αᵒᵈ) f g h x using 3
  rw [← mu_toDual]; rfl

end InversionBot

section Prod

section Preorder

section Ring
variable (𝕜) [Ring 𝕜] [Preorder α] [Preorder β]

section DecidableLe
variable [DecidableLE α] [DecidableLE β]

lemma zeta_prod_apply (a b : α × β) : zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2 := by
  simp [← ite_and, Prod.le_def, and_comm]

lemma zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    zeta 𝕜 (a₁, b₁) (a₂, b₂) = zeta 𝕜 a₁ a₂ * zeta 𝕜 b₁ b₂ := zeta_prod_apply _ _ _

end DecidableLe

variable {𝕜} (f f₁ f₂ : IncidenceAlgebra 𝕜 α) (g g₁ g₂ : IncidenceAlgebra 𝕜 β)

/-- The cartesian product of two incidence algebras. -/
protected def prod : IncidenceAlgebra 𝕜 (α × β) where
  toFun x y := f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def, not_and_or] at hxy
    obtain hxy | hxy := hxy <;> simp [apply_eq_zero_of_not_le hxy]

lemma prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂ := rfl
@[simp] lemma prod_apply (x y : α × β) : f.prod g x y = f x.1 y.1 * g x.2 y.2 := rfl

/-- This is a version of `IncidenceAlgebra.prod_mul_prod` that works over non-commutative rings. -/
lemma prod_mul_prod' [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]
    (h : ∀ a₁ a₂ a₃ b₁ b₂ b₃,
        f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ b₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)) :
    f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) := by
  ext x y; simp [Icc_prod_def, sum_mul_sum, h, sum_product]

@[simp]
lemma one_prod_one [DecidableEq α] [DecidableEq β] :
    (.prod 1 1 : IncidenceAlgebra 𝕜 (α × β)) = 1 := by
  ext x y; simp [Prod.ext_iff, ← ite_and, and_comm]

@[simp]
lemma zeta_prod_zeta [DecidableLE α] [DecidableLE β] :
    (zeta 𝕜).prod (zeta 𝕜) = (zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  ext x y hxy; simp [hxy, hxy.1, hxy.2]

end Ring

section CommRing
variable [CommRing 𝕜] [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (f₁ f₂ : IncidenceAlgebra 𝕜 α) (g₁ g₂ : IncidenceAlgebra 𝕜 β)

@[simp]
lemma prod_mul_prod : f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) :=
  prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ ↦ mul_mul_mul_comm ..

end CommRing
end Preorder

section PartialOrder
variable (𝕜) [Ring 𝕜] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α]
  [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]

/-- The Möbius function on a product order. Based on lemma 2.1.13 of Incidence Algebras by Spiegel
and O'Donnell. -/
@[simp]
lemma mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  refine left_inv_eq_right_inv ?_ zeta_mul_mu
  rw [← zeta_prod_zeta, prod_mul_prod', mu_mul_zeta, mu_mul_zeta, one_prod_one]
  exact fun _ _ _ _ _ _ ↦ Commute.mul_mul_mul_comm (by simp : _ = _) _ _

@[simp]
lemma eulerChar_prod [BoundedOrder α] [BoundedOrder β] :
    eulerChar 𝕜 (α × β) = eulerChar 𝕜 α * eulerChar 𝕜 β := by simp [eulerChar, ← mu_prod_mu]

end PartialOrder
end Prod
end IncidenceAlgebra
