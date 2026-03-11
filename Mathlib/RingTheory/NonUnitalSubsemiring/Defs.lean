/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Tactic.FastInstance

/-!
# Bundled non-unital subsemirings

We define bundled non-unital subsemirings and some standard constructions:
`subtype` and `inclusion` ring homomorphisms.
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section neg_mul

variable {R S : Type*} [Mul R] [HasDistribNeg R] [SetLike S R] [MulMemClass S R] {s : S}

/-- This lemma exists for `aesop`, as `aesop` simplifies `-x * y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem neg_mul_mem {x y : R} (hx : -x ∈ s) (hy : y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy

/-- This lemma exists for `aesop`, as `aesop` simplifies `x * -y` to `-(x * y)` before applying
unsafe rules like `mul_mem`, leading to a dead end in cases where `neg_mem` does not hold. -/
@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem mul_neg_mem {x y : R} (hx : x ∈ s) (hy : -y ∈ s) : -(x * y) ∈ s := by
  simpa using mul_mem hx hy

-- doesn't work without the above `aesop` lemmas
example {x y z : R} (hx : x ∈ s) (hy : -y ∈ s) (hz : z ∈ s) :
    x * (-y) * z ∈ s := by aesop

end neg_mul

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R]

/-- `NonUnitalSubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both an additive submonoid and also a multiplicative subsemigroup. -/
class NonUnitalSubsemiringClass (S : Type*) (R : outParam (Type u)) [NonUnitalNonAssocSemiring R]
    [SetLike S R] : Prop
  extends AddSubmonoidClass S R where
  mul_mem : ∀ {s : S} {a b : R}, a ∈ s → b ∈ s → a * b ∈ s

-- See note [lower instance priority]
instance (priority := 100) NonUnitalSubsemiringClass.mulMemClass (S : Type*) (R : Type u)
    [NonUnitalNonAssocSemiring R] [SetLike S R] [h : NonUnitalSubsemiringClass S R] :
    MulMemClass S R :=
  { h with }

namespace NonUnitalSubsemiringClass

variable [SetLike S R] [NonUnitalSubsemiringClass S R] (s : S)

open AddSubmonoidClass

/- Prefer subclasses of `NonUnitalNonAssocSemiring` over subclasses of
`NonUnitalSubsemiringClass`. -/
/-- A non-unital subsemiring of a `NonUnitalNonAssocSemiring` inherits a
`NonUnitalNonAssocSemiring` structure -/
instance (priority := 75) toNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalNonAssocSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors Subtype.val rfl fun _ _ => rfl

/-- The natural non-unital ring hom from a non-unital subsemiring of a non-unital semiring `R` to
`R`. -/
def subtype : s →ₙ+* R :=
  { AddSubmonoidClass.subtype s, MulMemClass.subtype s with toFun := (↑) }

variable {s} in
@[simp]
theorem subtype_apply (x : s) : subtype s x = x :=
  rfl

theorem subtype_injective : Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

/-- A non-unital subsemiring of a `NonUnitalSemiring` is a `NonUnitalSemiring`. -/
instance toNonUnitalSemiring {R} [NonUnitalSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalSemiring Subtype.val rfl (by simp) (fun _ _ => rfl) fun _ _ => rfl

/-- A non-unital subsemiring of a `NonUnitalCommSemiring` is a `NonUnitalCommSemiring`. -/
instance toNonUnitalCommSemiring {R} [NonUnitalCommSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] : NonUnitalCommSemiring s := fast_instance%
  Subtype.coe_injective.nonUnitalCommSemiring Subtype.val rfl (by simp) (fun _ _ => rfl)
    fun _ _ => rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/

end NonUnitalSubsemiringClass

/-- A non-unital subsemiring of a non-unital semiring `R` is a subset `s` that is both an additive
submonoid and a semigroup. -/
structure NonUnitalSubsemiring (R : Type u) [NonUnitalNonAssocSemiring R] extends AddSubmonoid R,
  Subsemigroup R

/-- Reinterpret a `NonUnitalSubsemiring` as a `Subsemigroup`. -/
add_decl_doc NonUnitalSubsemiring.toSubsemigroup

/-- Reinterpret a `NonUnitalSubsemiring` as an `AddSubmonoid`. -/
add_decl_doc NonUnitalSubsemiring.toAddSubmonoid

namespace NonUnitalSubsemiring

lemma toAddSubmonoid_injective :
    (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R).Injective :=
  fun ⟨s, hs⟩ t ↦ by congr!

@[simp] lemma toAddSubmonoid_inj {s t : NonUnitalSubsemiring R} :
    s.toAddSubmonoid = t.toAddSubmonoid ↔ s = t := toAddSubmonoid_injective.eq_iff

instance : SetLike (NonUnitalSubsemiring R) R where
  coe s := s.carrier
  coe_injective' := SetLike.coe_injective.comp toAddSubmonoid_injective

lemma toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R)
  | _, _, h => SetLike.ext (SetLike.ext_iff.mp h :)

instance : PartialOrder (NonUnitalSubsemiring R) := .ofSetLike (NonUnitalSubsemiring R) R

/-- The actual `NonUnitalSubsemiring` obtained from an element of a `NonUnitalSubsemiringClass`. -/
@[simps]
def ofClass {S R : Type*} [NonUnitalNonAssocSemiring R] [SetLike S R]
    [NonUnitalSubsemiringClass S R] (s : S) : NonUnitalSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem

instance (priority := 100) : CanLift (Set R) (NonUnitalSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s)
    where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2 },
      rfl ⟩

instance : NonUnitalSubsemiringClass (NonUnitalSubsemiring R) R where
  zero_mem {s} := AddSubmonoid.zero_mem' s.toAddSubmonoid
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  mul_mem {s} := mul_mem' s

theorem mem_carrier {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two non-unital subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : NonUnitalSubsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital subsemiring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalSubsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubsemigroup.copy s hs with carrier := s }

@[simp]
theorem coe_copy (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/-- Construct a `NonUnitalSubsemiring R` from a set `s`, a subsemigroup `sg`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sg ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sg : Subsemigroup R) (hg : ↑sg = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : NonUnitalSubsemiring R where
  carrier := s
  zero_mem' := by subst ha; exact sa.zero_mem
  add_mem' := by subst ha; exact sa.add_mem
  mul_mem' := by subst hg; exact sg.mul_mem

@[simp]
theorem coe_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) {x : R} : x ∈ NonUnitalSubsemiring.mk' s sg hg sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_toSubsemigroup {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toSubsemigroup = sg :=
  SetLike.coe_injective hg.symm

@[simp]
theorem mk'_toAddSubmonoid {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (NonUnitalSubsemiring.mk' s sg hg sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

instance isMulCommutative_toSubsemigroup (S : NonUnitalSubsemiring R) [IsMulCommutative S] :
    IsMulCommutative S.toSubsemigroup := ‹IsMulCommutative S›

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubsemiring R)

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

/-! Note: currently, there are no ordered versions of non-unital rings. -/


@[simp high]
theorem mem_toSubsemigroup {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[simp high]
theorem coe_toSubsemigroup (s : NonUnitalSubsemiring R) : (s.toSubsemigroup : Set R) = s :=
  rfl

@[simp]
theorem mem_toAddSubmonoid {s : NonUnitalSubsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubmonoid (s : NonUnitalSubsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The non-unital subsemiring `R` of the non-unital semiring `R`. -/
instance : Top (NonUnitalSubsemiring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubsemiring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : NonUnitalSubsemiring R) : Set R) = Set.univ :=
  rfl

@[simp] lemma toAddSubmonoid_top : (⊤ : NonUnitalSubsemiring R).toAddSubmonoid = ⊤ := rfl

@[simp]
lemma toAddSubmonoid_eq_top {S : NonUnitalSubsemiring R} : S.toAddSubmonoid = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

-- should we define this as the range of the zero homomorphism?
instance : Bot (NonUnitalSubsemiring R) :=
  ⟨{  carrier := {0}
      add_mem' := fun _ _ => by simp_all
      zero_mem' := Set.mem_singleton 0
      mul_mem' := fun _ _ => by simp_all }⟩

instance : Inhabited (NonUnitalSubsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : NonUnitalSubsemiring R) : Set R) = {0} :=
  rfl

theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubsemiring R) ↔ x = 0 :=
  Set.mem_singleton_iff

/-- The inf of two non-unital subsemirings is their intersection. -/
instance : Min (NonUnitalSubsemiring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubmonoid ⊓ t.toAddSubmonoid with
      carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : NonUnitalSubsemiring R) :
    ((p ⊓ p' : NonUnitalSubsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : NonUnitalSubsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [FunLike F R S]

variable [NonUnitalNonAssocSemiring S]
  [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/-- Restriction of a non-unital ring homomorphism to a non-unital subsemiring of the codomain. -/
def codRestrict (f : F) (s : S') (h : ∀ x, f x ∈ s) : R →ₙ+* s where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
  map_add' x y := Subtype.ext (map_add f x y)
  map_zero' := Subtype.ext (map_zero f)

/-- The non-unital subsemiring of elements `x : R` such that `f x = g x` -/
def eqSlocus (f g : F) : NonUnitalSubsemiring R :=
  { (f : R →ₙ* S).eqLocus (g : R →ₙ* S), (f : R →+ S).eqLocusM g with
    carrier := { x | f x = g x } }

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

/-- The non-unital ring homomorphism associated to an inclusion of
non-unital subsemirings. -/
def inclusion {S T : NonUnitalSubsemiring R} (h : S ≤ T) : S →ₙ+* T :=
  codRestrict (subtype S) _ fun x => h x.2

end NonUnitalSubsemiring
