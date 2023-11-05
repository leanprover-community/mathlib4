/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.GroupPower.Lemmas

#align_import algebra.hom.centroid from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Centroid homomorphisms

Let `A` be a (non unital, non associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`CentroidHom`) in keeping
with `AddMonoidHom` etc.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `CentroidHom`: Maps which preserve left and right multiplication.

## Typeclasses

* `CentroidHomClass`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/

open Function

variable {F α : Type*}

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α →+ α where
  /-- Commutativity of centroid homomorphims with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphims with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

/-- `CentroidHomClass F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `CentroidHom`. -/
class CentroidHomClass (F : Type*) (α : outParam <| Type*) [NonUnitalNonAssocSemiring α] extends
  AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphims with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphims with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b


export CentroidHomClass (map_mul_left map_mul_right)

instance [NonUnitalNonAssocSemiring α] [CentroidHomClass F α] : CoeTC F (CentroidHom α) :=
  ⟨fun f ↦
    { (f : α →+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

/-! ### Centroid homomorphisms -/


namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

instance : CentroidHomClass (CentroidHom α) α where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'


/-- Helper instance for when there's too many metavariables to apply `FunLike.CoeFun`
directly. -/
/- Porting note: Lean gave me `unknown constant 'FunLike.CoeFun'` and says `CoeFun` is a type
mismatch, so I used `library_search`. -/
instance : CoeFun (CentroidHom α) fun _ ↦ α → α :=
  inferInstanceAs (CoeFun (CentroidHom α) fun _ ↦ α → α)

-- Porting note: removed @[simp]; not in normal form. (`toAddMonoidHom_eq_coe` below ensures that
-- the LHS simplifies to the RHS anyway.)
theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

@[ext]
theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f :=
  rfl

@[simp]
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl

theorem coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α → α →+ α) :=
  fun _f _g h => ext fun a ↦
    haveI := FunLike.congr_fun h a
    this

/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
def toEnd (f : CentroidHom α) : AddMonoid.End α :=
  (f : α →+ α)

theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) :=
  coe_toAddMonoidHom_injective

/-- Copy of a `CentroidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b ↦ by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b ↦ by simp_rw [h, map_mul_right] }

@[simp]
theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h

variable (α)

/-- `id` as a `CentroidHom`. -/
protected def id : CentroidHom α :=
  { AddMonoidHom.id α with
    map_mul_left' := fun _ _ ↦ rfl
    map_mul_right' := fun _ _ ↦ rfl }

instance : Inhabited (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(CentroidHom.id α) = id :=
  rfl

@[simp, norm_cast]
theorem toAddMonoidHom_id : (CentroidHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : CentroidHom.id α a = a :=
  rfl

/-- Composition of `CentroidHom`s as a `CentroidHom`. -/
def comp (g f : CentroidHom α) : CentroidHom α :=
  { g.toAddMonoidHom.comp f.toAddMonoidHom with
    map_mul_left' := fun _a _b ↦ (congr_arg g <| f.map_mul_left' _ _).trans <| g.map_mul_left' _ _
    map_mul_right' := fun _a _b ↦
      (congr_arg g <| f.map_mul_right' _ _).trans <| g.map_mul_right' _ _ }

@[simp, norm_cast]
theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
  rfl

@[simp, norm_cast]
theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f :=
  rfl

@[simp]
theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f :=
  rfl

@[simp]
theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun a ↦ congrFun (congrArg comp a) f⟩

@[simp]
theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun a ↦ hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance : Zero (CentroidHom α) :=
  ⟨{ (0 : α →+ α) with
      map_mul_left' := fun _a _b ↦ (mul_zero _).symm
      map_mul_right' := fun _a _b ↦ (zero_mul _).symm }⟩

instance : One (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

instance : Add (CentroidHom α) :=
  ⟨fun f g ↦
    { (f + g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        show f (a * b) + g (a * b) = a * (f b + g b)
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b ↦ by
        show f (a * b) + g (a * b) = (f a + g a) * b
        simp [map_mul_right, add_mul] }⟩

instance : Mul (CentroidHom α) :=
  ⟨comp⟩

instance hasNsmul : SMul ℕ (CentroidHom α) :=
  ⟨fun n f ↦
    { ((SMul.smul n f) : α →+ α) with
        map_mul_left' := fun a b ↦ by
          change n • f (a * b) = a * n • f b
          rw [map_mul_left f, ← mul_smul_comm]
        map_mul_right' := fun a b ↦ by
          change n • f (a * b) = n • f a * b
          rw [map_mul_right f, ← smul_mul_assoc] }⟩

instance hasNpowNat : Pow (CentroidHom α) ℕ :=
  ⟨fun f n ↦
    { (f.toEnd ^ n : AddMonoid.End α) with
      map_mul_left' := fun a b ↦ by
        induction' n with n ih
        · exact rfl
        · simp
          rw [pow_succ]
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b ↦ by
        induction' n with n ih
        · exact rfl
        · simp
          rw [pow_succ]
          exact (congr_arg f.toEnd ih).trans (f.map_mul_right' _ _) }⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : CentroidHom α) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ⇑(1 : CentroidHom α) = id :=
  rfl

@[simp, norm_cast]
theorem coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
theorem coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g :=
  rfl

-- Eligible for `dsimp`
@[simp, norm_cast, nolint simpNF]
theorem coe_nsmul (f : CentroidHom α) (n : ℕ) : ⇑(n • f) = n • (⇑f) :=
  rfl

@[simp]
theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
  rfl

@[simp]
theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
  rfl

@[simp]
theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
  rfl

@[simp]
theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
  rfl

-- Eligible for `dsimp`
@[simp, nolint simpNF]
theorem nsmul_apply (f : CentroidHom α) (n : ℕ) (a : α) : (n • f) a = n • f a :=
  rfl

@[simp]
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl

@[simp]
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl

theorem toEnd_nsmul (x : CentroidHom α) (n : ℕ) : (n • x).toEnd = n • x.toEnd :=
  rfl

-- Porting note: I guess the porter has naming issues still
-- cf.`add_monoid_hom.add_comm_monoid`
instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add toEnd_nsmul

instance : NatCast (CentroidHom α) where natCast n := n • (1 : CentroidHom α)

-- Porting note: `nolint simpNF` added because simplify fails on left-hand side
@[simp, norm_cast, nolint simpNF]
theorem coe_nat_cast (n : ℕ) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α) :=
  rfl

theorem nat_cast_apply (n : ℕ) (m : α) : (n : CentroidHom α) m = n • m :=
  rfl

@[simp]
theorem toEnd_one : (1 : CentroidHom α).toEnd = 1 :=
  rfl

@[simp]
theorem toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd :=
  rfl

@[simp]
theorem toEnd_pow (x : CentroidHom α) (n : ℕ) : (x ^ n).toEnd = x.toEnd ^ n :=
  rfl

@[simp, norm_cast]
theorem toEnd_nat_cast (n : ℕ) : (n : CentroidHom α).toEnd = ↑n :=
  rfl

-- cf `add_monoid.End.semiring`
instance : Semiring (CentroidHom α) :=
  toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_nsmul toEnd_pow
    toEnd_nat_cast

theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Negation of `CentroidHom`s as a `CentroidHom`. -/
instance : Neg (CentroidHom α) :=
  ⟨fun f ↦
    { (-f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change -f (a * b) = a * (-f b)
        simp [map_mul_left]
      map_mul_right' := fun a b ↦ by
        change -f (a * b) = (-f a) * b
        simp [map_mul_right] }⟩

instance : Sub (CentroidHom α) :=
  ⟨fun f g ↦
    { (f - g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change (FunLike.coe f - FunLike.coe g) (a * b) = a * (FunLike.coe f - FunLike.coe g) b
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b ↦ by
        change (FunLike.coe f - FunLike.coe g) (a * b) = ((FunLike.coe f - FunLike.coe g) a) * b
        simp [map_mul_right, sub_mul] }⟩

instance hasZsmul : SMul ℤ (CentroidHom α) :=
  ⟨fun n f ↦
    { (SMul.smul n f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f, ← mul_smul_comm]
      map_mul_right' := fun a b ↦ by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f, ← smul_mul_assoc] }⟩

instance : IntCast (CentroidHom α) where intCast z := z • (1 : CentroidHom α)

-- Porting note: `nolint simpNF` added because simplify fails on left-hand side
@[simp, norm_cast, nolint simpNF]
theorem coe_int_cast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) :=
  rfl

theorem int_cast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl

@[simp]
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl

@[simp]
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl

theorem toEnd_zsmul (x : CentroidHom α) (n : ℤ) : (n • x).toEnd = n • x.toEnd :=
  rfl

instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.addCommGroup _ toEnd_zero toEnd_add toEnd_neg toEnd_sub toEnd_nsmul toEnd_zsmul

@[simp, norm_cast]
theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a :=
  rfl

@[simp]
theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
  rfl

@[simp, norm_cast]
theorem toEnd_int_cast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z :=
  rfl

instance instRing : Ring (CentroidHom α) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_nsmul toEnd_zsmul toEnd_pow toEnd_nat_cast toEnd_int_cast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

-- Porting note: Not sure why Lean didn't like `CentroidHom.Ring`
-- See note [reducible non instances]
/-- A prime associative ring has commutative centroid. -/
@[reducible]
def commRing (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.instRing with
    mul_comm := fun f g ↦ by
      ext
      refine' sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r ↦ _)
      rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
        comp_mul_comm] }

end NonUnitalRing

end CentroidHom
