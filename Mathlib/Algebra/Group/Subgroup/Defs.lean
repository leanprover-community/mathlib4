/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Set.Inclusion
import Mathlib.Tactic.Common
import Mathlib.Tactic.FastInstance

/-!
# Subgroups

This file defines multiplicative and additive subgroups as an extension of submonoids, in a bundled
form (unbundled subgroups are in `Deprecated/Subgroups.lean`).

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup G` : the type of subgroups of a group `G`

* `AddSubgroup A` : the type of subgroups of an additive group `A`

* `Subgroup.subtype` : the natural group homomorphism from a subgroup of group `G` to `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

assert_not_exists RelIso OrderedCommMonoid Multiset MonoidWithZero

open Function
open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

section SubgroupClass

/-- `InvMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under inverses. -/
class InvMemClass (S : Type*) (G : outParam Type*) [Inv G] [SetLike S G] : Prop where
  /-- `s` is closed under inverses -/
  inv_mem : ∀ {s : S} {x}, x ∈ s → x⁻¹ ∈ s

export InvMemClass (inv_mem)

/-- `NegMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under negation. -/
class NegMemClass (S : Type*) (G : outParam Type*) [Neg G] [SetLike S G] : Prop where
  /-- `s` is closed under negation -/
  neg_mem : ∀ {s : S} {x}, x ∈ s → -x ∈ s

export NegMemClass (neg_mem)

/-- Typeclass for substructures `s` such that `s ∪ -s = G`. -/
class HasMemOrNegMem {S G : Type*} [Neg G] [SetLike S G] (s : S) : Prop where
  mem_or_neg_mem (s) (a : G) : a ∈ s ∨ -a ∈ s

/-- Typeclass for substructures `s` such that `s ∪ s⁻¹ = G`. -/
@[to_additive]
class HasMemOrInvMem {S G : Type*} [Inv G] [SetLike S G] (s : S) : Prop where
  mem_or_inv_mem (s) (a : G) : a ∈ s ∨ a⁻¹ ∈ s

export HasMemOrNegMem (mem_or_neg_mem)
export HasMemOrInvMem (mem_or_inv_mem)

/-- `SubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are subgroups of `G`. -/
class SubgroupClass (S : Type*) (G : outParam Type*) [DivInvMonoid G] [SetLike S G] : Prop
    extends SubmonoidClass S G, InvMemClass S G

/-- `AddSubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are
additive subgroups of `G`. -/
class AddSubgroupClass (S : Type*) (G : outParam Type*) [SubNegMonoid G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G, NegMemClass S G

attribute [to_additive] InvMemClass SubgroupClass

attribute [aesop 90% (rule_sets := [SetLike])] inv_mem neg_mem

@[to_additive (attr := simp)]
theorem inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
    {x : G} : x⁻¹ ∈ H ↔ x ∈ H :=
  ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

/-- A subgroup is closed under division. -/
@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))
  /-- An additive subgroup is closed under subtraction. -/]
theorem div_mem {x y : M} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
theorem zpow_mem {x : M} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K
  | (n : ℕ) => by
    rw [zpow_natCast]
    exact pow_mem hx n
  | -[n+1] => by
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx n.succ)

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
theorem exists_inv_mem_iff_exists_mem {P : G → Prop} :
    (∃ x : G, x ∈ H ∧ P x⁻¹) ↔ ∃ x ∈ H, P x := by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

@[to_additive]
theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
  ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

@[to_additive]
theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
  ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

namespace InvMemClass

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an inverse. -/]
instance inv {G S : Type*} [Inv G] [SetLike S G] [InvMemClass S G] {H : S} : Inv H :=
  ⟨fun a => ⟨a⁻¹, inv_mem a.2⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv (x : H) : (x⁻¹).1 = x.1⁻¹ :=
  rfl

end InvMemClass

namespace SubgroupClass

-- Here we assume H, K, and L are subgroups, but in fact any one of them
-- could be allowed to be a subsemigroup.
-- Counterexample where K and L are submonoids: H = ℤ, K = ℕ, L = -ℕ
-- Counterexample where H and K are submonoids: H = {n | n = 0 ∨ 3 ≤ n}, K = 3ℕ + 4ℕ, L = 5ℤ
@[to_additive]
theorem subset_union {H K L : S} : (H : Set G) ⊆ K ∪ L ↔ H ≤ K ∨ H ≤ L := by
  refine ⟨fun h ↦ ?_, fun h x xH ↦ h.imp (· xH) (· xH)⟩
  rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
  exact fun ⟨x, xH, xK⟩ y yH ↦ (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK ↦ xK <| (mul_mem_cancel_right yK).mp ·)
    (mul_mem_cancel_left <| (h xH).resolve_left xK).mp

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits a subtraction. -/]
instance div {G S : Type*} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : S} : Div H :=
  ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩

/-- An additive subgroup of an `AddGroup` inherits an integer scaling. -/
instance _root_.AddSubgroupClass.zsmul {M S} [SubNegMonoid M] [SetLike S M]
    [AddSubgroupClass S M] {H : S} : SMul ℤ H :=
  ⟨fun n a => ⟨n • a.1, zsmul_mem a.2 n⟩⟩

/-- A subgroup of a group inherits an integer power. -/
@[to_additive existing]
instance zpow {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} : Pow H ℤ :=
  ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_div (x y : H) : (x / y).1 = x.1 / y.1 :=
  rfl

variable (H)

-- Prefer subclasses of `Group` over subclasses of `SubgroupClass`.
/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an `AddGroup` structure. -/]
instance (priority := 75) toGroup : Group H := fast_instance%
  Subtype.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `CommGroup` over subclasses of `SubgroupClass`.
/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An additive subgroup of an `AddCommGroup` is an `AddCommGroup`. -/]
instance (priority := 75) toCommGroup {G : Type*} [CommGroup G] [SetLike S G] [SubgroupClass S G] :
    CommGroup H := fast_instance%
  Subtype.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive (attr := coe)
  /-- The natural group hom from an additive subgroup of `AddGroup` `G` to `G`. -/]
protected def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' := fun _ _ => rfl

variable {H} in
@[to_additive (attr := simp)]
lemma subtype_apply (x : H) :
    SubgroupClass.subtype H x = x := rfl

@[to_additive]
lemma subtype_injective :
    Function.Injective (SubgroupClass.subtype H) :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
theorem coe_subtype : (SubgroupClass.subtype H : H → G) = ((↑) : H → G) := by
  rfl

variable {H}

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
def inclusion {H K : S} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.prop⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
theorem inclusion_self (x : H) : inclusion le_rfl x = x := by
  cases x
  rfl

@[to_additive (attr := simp)]
theorem inclusion_mk {h : H ≤ K} (x : G) (hx : x ∈ H) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

@[to_additive]
theorem inclusion_right (h : H ≤ K) (x : K) (hx : (x : G) ∈ H) : inclusion h ⟨x, hx⟩ = x := by
  cases x
  rfl

@[simp]
theorem inclusion_inclusion {L : S} (hHK : H ≤ K) (hKL : K ≤ L) (x : H) :
    inclusion hKL (inclusion hHK x) = inclusion (hHK.trans hKL) x := by
  cases x
  rfl

@[to_additive (attr := simp)]
theorem coe_inclusion {H K : S} (h : H ≤ K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion h a

@[to_additive (attr := simp)]
theorem subtype_comp_inclusion {H K : S} (h : H ≤ K) :
    (SubgroupClass.subtype K).comp (inclusion h) = SubgroupClass.subtype H :=
  rfl

end SubgroupClass

end SubgroupClass

/-- A subgroup of a group `G` is a subset containing 1, closed under multiplication
and closed under multiplicative inverse. -/
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier

/-- An additive subgroup of an additive group `G` is a subset containing 0, closed
under addition and additive inverse. -/
structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x ∈ carrier → -x ∈ carrier

attribute [to_additive] Subgroup

/-- Reinterpret a `Subgroup` as a `Submonoid`. -/
add_decl_doc Subgroup.toSubmonoid

/-- Reinterpret an `AddSubgroup` as an `AddSubmonoid`. -/
add_decl_doc AddSubgroup.toAddSubmonoid

namespace Subgroup

@[to_additive]
instance : SetLike (Subgroup G) G where
  coe s := s.carrier
  coe_injective' p q h := by
    obtain ⟨⟨⟨hp,_⟩,_⟩,_⟩ := p
    obtain ⟨⟨⟨hq,_⟩,_⟩,_⟩ := q
    congr

initialize_simps_projections Subgroup (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubgroup (carrier → coe, as_prefix coe)

/-- The actual `Subgroup` obtained from an element of a `SubgroupClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubgroup` obtained from an element of a
`AddSubgroupClass` -/]
def ofClass {S G : Type*} [Group G] [SetLike S G] [SubgroupClass S G]
    (s : S) : Subgroup G :=
  ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, InvMemClass.inv_mem⟩

@[to_additive]
instance (priority := 100) : CanLift (Set G) (Subgroup G) (↑)
    (fun s ↦ 1 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → x⁻¹ ∈ s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2.1, inv_mem' := h.2.2}, rfl⟩

-- TODO: Below can probably be written more uniformly
@[to_additive]
instance : SubgroupClass (Subgroup G) G where
  inv_mem := Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

-- This is not a simp lemma,
-- because the simp normal form left-hand side is given by `mem_toSubmonoid` below.
@[to_additive]
theorem mem_carrier {s : Subgroup G} {x : G} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mem_mk {s : Submonoid G} {x : G} (h_inv) :
    x ∈ mk s h_inv ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem coe_set_mk {s : Submonoid G} (h_inv) :
    (mk s h_inv : Set G) = s :=
  rfl

@[to_additive (attr := simp)]
theorem mk_le_mk {s t : Submonoid G} (h_inv) (h_inv') :
    mk s h_inv ≤ mk t h_inv' ↔ s ≤ t :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem coe_toSubmonoid (K : Subgroup G) : (K.toSubmonoid : Set G) = K :=
  rfl

@[to_additive (attr := simp)]
theorem mem_toSubmonoid (K : Subgroup G) (x : G) : x ∈ K.toSubmonoid ↔ x ∈ K :=
  Iff.rfl

@[to_additive]
theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subgroup G → Submonoid G) :=
  fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid, coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[to_additive (attr := simp)]
theorem toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q :=
  toSubmonoid_injective.eq_iff

@[to_additive (attr := mono)]
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subgroup G → Submonoid G) := fun _ _ =>
  id

@[to_additive (attr := mono)]
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subgroup G → Submonoid G) :=
  toSubmonoid_strictMono.monotone

@[to_additive (attr := simp)]
theorem toSubmonoid_le {p q : Subgroup G} : p.toSubmonoid ≤ q.toSubmonoid ↔ p ≤ q :=
  Iff.rfl

@[to_additive (attr := simp)]
lemma coe_nonempty (s : Subgroup G) : (s : Set G).Nonempty := ⟨1, one_mem _⟩

end Subgroup

namespace Subgroup

variable (H K : Subgroup G)

/-- Copy of a subgroup with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive (attr := simps)
      /-- Copy of an additive subgroup with a new `carrier` equal to the old one.
      Useful to fix definitional equalities -/]
protected def copy (K : Subgroup G) (s : Set G) (hs : s = K) : Subgroup G where
  carrier := s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx

@[to_additive]
theorem copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K.copy s hs = K :=
  SetLike.coe_injective hs

/-- Two subgroups are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubgroup`s are equal if they have the same elements. -/]
theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
  SetLike.ext h

/-- A subgroup contains the group's 1. -/
@[to_additive /-- An `AddSubgroup` contains the group's 0. -/]
protected theorem one_mem : (1 : G) ∈ H :=
  one_mem _

/-- A subgroup is closed under multiplication. -/
@[to_additive /-- An `AddSubgroup` is closed under addition. -/]
protected theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
  mul_mem

/-- A subgroup is closed under inverse. -/
@[to_additive /-- An `AddSubgroup` is closed under inverse. -/]
protected theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
  inv_mem

/-- A subgroup is closed under division. -/
@[to_additive /-- An `AddSubgroup` is closed under subtraction. -/]
protected theorem div_mem {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H :=
  div_mem hx hy

@[to_additive]
protected theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H :=
  inv_mem_iff

@[to_additive]
protected theorem exists_inv_mem_iff_exists_mem (K : Subgroup G) {P : G → Prop} :
    (∃ x : G, x ∈ K ∧ P x⁻¹) ↔ ∃ x ∈ K, P x :=
  exists_inv_mem_iff_exists_mem

@[to_additive]
protected theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
  mul_mem_cancel_right h

@[to_additive]
protected theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
  mul_mem_cancel_left h

@[to_additive]
protected theorem pow_mem {x : G} (hx : x ∈ K) : ∀ n : ℕ, x ^ n ∈ K :=
  pow_mem hx

@[to_additive]
protected theorem zpow_mem {x : G} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K :=
  zpow_mem hx

/-- Construct a subgroup from a nonempty set that is closed under division. -/
@[to_additive /-- Construct a subgroup from a nonempty set that is closed under subtraction -/]
def ofDiv (s : Set G) (hsn : s.Nonempty) (hs : ∀ᵉ (x ∈ s) (y ∈ s), x * y⁻¹ ∈ s) :
    Subgroup G :=
  have one_mem : (1 : G) ∈ s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : ∀ x, x ∈ s → x⁻¹ ∈ s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _ (inv_mem _ hy) }

/-- A subgroup of a group inherits a multiplication. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an addition. -/]
instance mul : Mul H :=
  H.toSubmonoid.mul

/-- A subgroup of a group inherits a 1. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a zero. -/]
instance one : One H :=
  H.toSubmonoid.one

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an inverse. -/]
instance inv : Inv H :=
  ⟨fun a => ⟨a⁻¹, H.inv_mem a.2⟩⟩

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a subtraction. -/]
instance div : Div H :=
  ⟨fun a b => ⟨a / b, H.div_mem a.2 b.2⟩⟩

/-- An `AddSubgroup` of an `AddGroup` inherits a natural scaling. -/
instance _root_.AddSubgroup.nsmul {G} [AddGroup G] {H : AddSubgroup G} : SMul ℕ H :=
  ⟨fun n a => ⟨n • a, H.nsmul_mem a.2 n⟩⟩

/-- A subgroup of a group inherits a natural power -/
@[to_additive existing]
protected instance npow : Pow H ℕ :=
  ⟨fun a n => ⟨a ^ n, H.pow_mem a.2 n⟩⟩

/-- An `AddSubgroup` of an `AddGroup` inherits an integer scaling. -/
instance _root_.AddSubgroup.zsmul {G} [AddGroup G] {H : AddSubgroup G} : SMul ℤ H :=
  ⟨fun n a => ⟨n • a, H.zsmul_mem a.2 n⟩⟩

/-- A subgroup of a group inherits an integer power -/
@[to_additive existing]
instance zpow : Pow H ℤ :=
  ⟨fun a n => ⟨a ^ n, H.zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : H) : G) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_div (x y : H) : (↑(x / y) : G) = ↑x / ↑y :=
  rfl

@[to_additive (attr := norm_cast)]
theorem coe_mk (x : G) (hx : x ∈ H) : ((⟨x, hx⟩ : H) : G) = x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n := by
  dsimp

@[to_additive (attr := simp)]
theorem mk_eq_one {g : G} {h} : (⟨g, h⟩ : H) = 1 ↔ g = 1 := Submonoid.mk_eq_one ..

/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an `AddGroup` structure. -/]
instance toGroup {G : Type*} [Group G] (H : Subgroup G) : Group H := fast_instance%
  Subtype.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An `AddSubgroup` of an `AddCommGroup` is an `AddCommGroup`. -/]
instance toCommGroup {G : Type*} [CommGroup G] (H : Subgroup G) : CommGroup H := fast_instance%
  Subtype.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive /-- The natural group hom from an `AddSubgroup` of `AddGroup` `G` to `G`. -/]
protected def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
lemma subtype_apply {s : Subgroup G} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
lemma subtype_injective (s : Subgroup G) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
theorem coe_subtype : ⇑H.subtype = ((↑) : H → G) :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
def inclusion {H K : Subgroup G} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
theorem coe_inclusion {H K : Subgroup G} (h : H ≤ K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion h a

@[to_additive]
theorem inclusion_injective {H K : Subgroup G} (h : H ≤ K) : Function.Injective <| inclusion h :=
  Set.inclusion_injective h

@[to_additive (attr := simp)]
lemma inclusion_inj {H K : Subgroup G} (h : H ≤ K) {x y : H} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]
theorem subtype_comp_inclusion {H K : Subgroup G} (hH : H ≤ K) :
    K.subtype.comp (inclusion hH) = H.subtype :=
  rfl

open Set

/-- A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` -/
structure Normal : Prop where
  /-- `H` is closed under conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H

attribute [class] Normal

end Subgroup

namespace AddSubgroup

/-- An AddSubgroup `H` is normal if whenever `n ∈ H`, then `g + n - g ∈ H` for every `g : A` -/
structure Normal (H : AddSubgroup A) : Prop where
  /-- `H` is closed under additive conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : A, g + n + -g ∈ H

attribute [to_additive] Subgroup.Normal

attribute [class] Normal

end AddSubgroup

namespace Subgroup

variable {H : Subgroup G}

@[to_additive]
instance (priority := 100) normal_of_comm {G : Type*} [CommGroup G] (H : Subgroup G) : H.Normal :=
  ⟨by simp [mul_comm]⟩

namespace Normal

@[to_additive]
theorem conj_mem' (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) :
    g⁻¹ * n * g ∈ H := by
  convert nH.conj_mem n hn g⁻¹
  rw [inv_inv]

@[to_additive]
theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ H := nH.conj_mem (a * b) h a⁻¹
  simpa

@[to_additive]
theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H :=
  ⟨nH.mem_comm, nH.mem_comm⟩

end Normal

end Subgroup

namespace Subgroup

variable (H : Subgroup G)

section Normalizer

/-- The `normalizer` of `H` is the largest subgroup of `G` inside which `H` is normal. -/
@[to_additive
/-- The `normalizer` of `H` is the largest subgroup of `G` inside which `H` is normal. -/]
def normalizer : Subgroup G where
  carrier := { g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }
  one_mem' := by simp
  mul_mem' {a b} (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n := by
    rw [hb, ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

-- variant for sets.
-- TODO should this replace `normalizer`?
/-- The `setNormalizer` of `S` is the subgroup of `G` whose elements satisfy `g*S*g⁻¹=S` -/
@[to_additive
      /-- The `setNormalizer` of `S` is the subgroup of `G` whose elements satisfy
      `g+S-g=S`. -/]
def setNormalizer (S : Set G) : Subgroup G where
  carrier := { g : G | ∀ n, n ∈ S ↔ g * n * g⁻¹ ∈ S }
  one_mem' := by simp
  mul_mem' {a b} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) (hb : ∀ n, n ∈ S ↔ b * n * b⁻¹ ∈ S) n := by
    rw [hb, ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

variable {H}

@[to_additive]
theorem mem_normalizer_iff {g : G} : g ∈ H.normalizer ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H :=
  Iff.rfl

@[to_additive]
theorem mem_normalizer_iff'' {g : G} : g ∈ H.normalizer ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H := by
  rw [← inv_mem_iff (x := g), mem_normalizer_iff, inv_inv]

@[to_additive]
theorem mem_normalizer_iff' {g : G} : g ∈ H.normalizer ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H :=
  ⟨fun h n => by rw [h, mul_assoc, mul_inv_cancel_right], fun h n => by
    rw [mul_assoc, ← h, inv_mul_cancel_right]⟩

@[to_additive]
theorem le_normalizer : H ≤ normalizer H := fun x xH n => by
  rw [H.mul_mem_cancel_right (H.inv_mem xH), H.mul_mem_cancel_left xH]

end Normalizer

@[deprecated (since := "2025-04-09")] alias IsCommutative := IsMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.IsCommutative := IsAddCommutative

/-- A subgroup of a commutative group is commutative. -/
@[to_additive /-- A subgroup of a commutative group is commutative. -/]
instance commGroup_isMulCommutative {G : Type*} [CommGroup G] (H : Subgroup G) :
    IsMulCommutative H :=
  ⟨CommMagma.to_isCommutative⟩

@[deprecated (since := "2025-04-09")] alias commGroup_isCommutative := commGroup_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.addCommGroup_isCommutative :=
  commGroup_isMulCommutative

@[to_additive]
lemma mul_comm_of_mem_isMulCommutative [IsMulCommutative H] {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a := by
  simpa only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] using mul_comm (⟨a, ha⟩ : H) (⟨b, hb⟩ : H)

@[deprecated (since := "2025-04-09")] alias mul_comm_of_mem_isCommutative :=
  mul_comm_of_mem_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.add_comm_of_mem_isCommutative :=
  _root_.AddSubgroup.add_comm_of_mem_isAddCommutative

end Subgroup
