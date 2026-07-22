/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
module

public import Mathlib.Algebra.Algebra.Defs  -- shake: keep (`example` dependency)
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Centroid homomorphisms

Let `A` be a (nonunital, non-associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`CentroidHom`) in keeping
with `AddMonoidHom` etc.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
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

@[expose] public section

assert_not_exists Field

open Function

variable {F M N R α : Type*}

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α →+ α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

/-- `CentroidHomClass F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `CentroidHom`. -/
class CentroidHomClass (F : Type*) (α : outParam Type*)
    [NonUnitalNonAssocSemiring α] [FunLike F α α] : Prop extends AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b


export CentroidHomClass (map_mul_left map_mul_right)

instance [NonUnitalNonAssocSemiring α] [FunLike F α α] [CentroidHomClass F α] :
    CoeTC F (CentroidHom α) :=
  ⟨fun f ↦
    { (f : α →+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

/-! ### Centroid homomorphisms -/

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

instance : FunLike (CentroidHom α) α α where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

instance : CentroidHomClass (CentroidHom α) α where
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'

theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

@[ext]
theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f :=
  rfl

@[simp]
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl

theorem coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α → α →+ α) :=
  fun _f _g h => ext fun a ↦
    haveI := DFunLike.congr_fun h a
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
  DFunLike.ext' h

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
  ⟨fun h ↦ ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun a ↦ congrFun (congrArg comp a) f⟩

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
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, add_mul] }⟩

instance : Mul (CentroidHom α) :=
  ⟨comp⟩

variable [Monoid M] [Monoid N] [Semiring R]
variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]
variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

instance instSMul : SMul M (CentroidHom α) where
  smul n f :=
    { (n • f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f, ← mul_smul_comm]
      map_mul_right' := fun a b ↦ by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f, ← smul_mul_assoc] }

instance [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMulCommClass M N α] : SMulCommClass M N (CentroidHom α) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [DistribMulAction Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance isScalarTowerRight : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  smul_assoc _ _ _ := rfl

instance hasNPowNat : Pow (CentroidHom α) ℕ :=
  ⟨fun f n ↦
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_right' _ _)}⟩

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

@[simp, norm_cast]
theorem coe_smul (n : M) (f : CentroidHom α) : ⇑(n • f) = n • ⇑f :=
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

@[simp]
theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
  rfl

example : SMul ℕ (CentroidHom α) := instSMul

@[simp]
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl

@[simp]
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl

theorem toEnd_smul (m : M) (x : CentroidHom α) : (m • x).toEnd = m • x.toEnd :=
  rfl

instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)

instance : NatCast (CentroidHom α) where natCast n := n • (1 : CentroidHom α)

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α) :=
  rfl

theorem natCast_apply (n : ℕ) (m : α) : (n : CentroidHom α) m = n • m :=
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
theorem toEnd_natCast (n : ℕ) : (n : CentroidHom α).toEnd = ↑n :=
  rfl

-- cf `add_monoid.End.semiring`
instance : Semiring (CentroidHom α) :=
  toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

variable (α) in
/-- `CentroidHom.toEnd` as a `RingHom`. -/
@[simps]
def toEndRingHom : CentroidHom α →+* AddMonoid.End α where
  toFun := toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul

theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]

instance : DistribMulAction M (CentroidHom α) :=
  toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul

instance : Module R (CentroidHom α) :=
  toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

/-!
The following instances show that `α` is a non-unital and non-associative algebra over
`CentroidHom α`.
-/

/-- The tautological action by `CentroidHom α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (CentroidHom α) α where
  smul T a := T a
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := map_zero
  smul_add := map_add

@[simp]
lemma smul_def (T : CentroidHom α) (a : α) : T • a = T a := rfl

instance : SMulCommClass (CentroidHom α) α α where
  smul_comm _ _ _ := map_mul_left _ _ _

instance : SMulCommClass α (CentroidHom α) α := SMulCommClass.symm _ _ _

instance : IsScalarTower (CentroidHom α) α α where
  smul_assoc _ _ _ := (map_mul_right _ _ _).symm

/-!
Let `α` be an algebra over `R`, such that the canonical ring homomorphism of `R` into
`CentroidHom α` lies in the center of `CentroidHom α`. Then `CentroidHom α` is an algebra over `R`
-/

variable {R : Type*}
variable [CommSemiring R]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

/-- The natural ring homomorphism from `R` into `CentroidHom α`.

This is a stronger version of `Module.toAddMonoidEnd`. -/
@[simps! apply_toFun]
def _root_.Module.toCentroidHom : R →+* CentroidHom α := RingHom.smulOneHom

open Module in
/-- `CentroidHom α` as an algebra over `R`. -/
example (h : ∀ (r : R) (T : CentroidHom α), toCentroidHom r * T = T * toCentroidHom r) :
    Algebra R (CentroidHom α) := toCentroidHom.toAlgebra' h

local notation "L" => AddMonoid.End.mulLeft
local notation "R" => AddMonoid.End.mulRight

lemma centroid_eq_centralizer_mulLeftRight :
    RingHom.rangeS (toEndRingHom α) = Subsemiring.centralizer (Set.range L ∪ Set.range R) := by
  ext T
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b ↦ (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a ↦ (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b ↦ ?_, fun a b ↦ ?_⟩, rfl⟩
    · exact congr($(h (L a) (.inl ⟨a, rfl⟩)) b).symm
    · exact congr($(h (R b) (.inr ⟨b, rfl⟩)) a).symm

/-- The canonical homomorphism from the center into the center of the centroid -/
def centerToCentroidCenter :
    NonUnitalSubsemiring.center α →ₙ+* Subsemiring.center (CentroidHom α) where
  toFun z :=
    { L (z : α) with
      val := ⟨L z, z.prop.left_comm, z.prop.left_assoc ⟩
      property := by
        rw [Subsemiring.mem_center_iff]
        intro g
        ext a
        exact map_mul_left g (↑z) a }
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact rfl
  map_add' := fun _ _ => by
    dsimp
    simp only [map_add]
    rfl
  map_mul' z₁ z₂ := by ext a; exact (z₁.prop.left_assoc z₂ a).symm

instance : FunLike (Subsemiring.center (CentroidHom α)) α α where
  coe f := f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

lemma centerToCentroidCenter_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroidCenter z) a = z * a := rfl

/-- The canonical homomorphism from the center into the centroid -/
def centerToCentroid : NonUnitalSubsemiring.center α →ₙ+* CentroidHom α :=
  NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

lemma centerToCentroid_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroid z) a = z * a := rfl

lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) ∈ RingHom.rangeS (toEndRingHom α) := by
  constructor
  · exact fun ha ↦ ⟨AddMonoidHom.ext <| fun _ => (IsMulCentral.comm ha _).symm,
      ⟨centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case comm => exact (congr($hc.symm ·))
    case left_assoc => simpa [e1] using (map_mul_right T · ·)
    case right_assoc => simpa [e2] using (map_mul_left T · ·)

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring

variable [NonUnitalNonAssocCommSemiring α]

/-
Left and right multiplication coincide as α is commutative
-/
local notation "L" => AddMonoid.End.mulLeft

lemma _root_.NonUnitalNonAssocCommSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ ∀ b : α, Commute (L b) (L a) := by
  rw [NonUnitalNonAssocSemiring.mem_center_iff, CentroidHom.centroid_eq_centralizer_mulLeftRight,
    Subsemiring.mem_centralizer_iff, AddMonoid.End.mulRight_eq_mulLeft, Set.union_self]
  aesop

end NonUnitalNonAssocCommSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism from the center of a (non-associative) semiring onto its centroid. -/
def centerIsoCentroid : Subsemiring.center α ≃+* CentroidHom α :=
  { centerToCentroid with
    invFun := fun T ↦
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
    left_inv := fun z ↦ Subtype.ext <| by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
    right_inv := fun T ↦ CentroidHom.ext <| fun _ => by rw [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, ← map_mul_right, one_mul] }

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Negation of `CentroidHom`s as a `CentroidHom`. -/
instance : Neg (CentroidHom α) :=
  ⟨fun f ↦
    { (-f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right] }⟩

instance : Sub (CentroidHom α) :=
  ⟨fun f g ↦
    { (f - g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, sub_mul] }⟩

instance : IntCast (CentroidHom α) where intCast z := z • (1 : CentroidHom α)

@[simp, norm_cast]
theorem coe_intCast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) :=
  rfl

theorem intCast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl

@[simp]
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl

@[simp]
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl

instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

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
theorem toEnd_intCast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z :=
  rfl

instance instRing : Ring (CentroidHom α) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

-- See note [reducible non-instances]
/-- A prime associative ring has commutative centroid. -/
abbrev commRing
    (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.instRing with
    mul_comm := fun f g ↦ by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r ↦ ?_)
      rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
        comp_mul_comm] }

end NonUnitalRing

end CentroidHom
