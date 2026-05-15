/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Subsemigroup.Center
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Center
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subsemigroup.Membership
import Mathlib.Algebra.Ring.Centralizer
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.FBinop

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring.
We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `NonUnitalSubring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `instance : CompleteLattice (NonUnitalSubring R)` : the complete lattice structure on the
  non-unital subrings.

* `NonUnitalSubring.center` : the center of a non-unital ring `R`.

* `NonUnitalSubring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `NonUnitalSubring.gi` : `closure : Set M → NonUnitalSubring M` and coercion
  `coe : NonUnitalSubring M → Set M`
  form a `GaloisInsertion`.

* `comap f B : NonUnitalSubring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : NonUnitalSubring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings

* `f.range : NonUnitalSubring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : NonUnitalSubring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

@[expose] public section


universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/-- Sum of a list of elements in a non-unital subring is in the non-unital subring. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in a `NonUnitalSubring` of a `NonUnitalRing` is
in the `NonUnitalSubring`. -/
protected theorem multiset_sum_mem {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Sum of elements in a `NonUnitalSubring` of a `NonUnitalRing` indexed by a `Finset`
is in the `NonUnitalSubring`. -/
protected theorem sum_mem {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    {ι : Type*} {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-! ## top -/


/-- The non-unital subring `R` of the ring `R`. -/
instance : Top (NonUnitalSubring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : NonUnitalSubring R) : Set R) = Set.univ :=
  rfl

@[simp]
lemma toNonUnitalSubsemiring_top : (⊤ : NonUnitalSubring R).toNonUnitalSubsemiring = ⊤ := rfl

@[simp] lemma toAddSubgroup_top : (⊤ : NonUnitalSubring R).toAddSubgroup = ⊤ := rfl

@[simp]
lemma toNonUnitalSubsemiring_eq_top {S : NonUnitalSubring R} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ := by simp [← SetLike.coe_set_eq]

@[simp] lemma toAddSubgroup_eq_top {S : NonUnitalSubring R} : S.toAddSubgroup = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/-- The ring equiv between the top element of `NonUnitalSubring R` and `R`. -/
@[simps!]
def topEquiv : (⊤ : NonUnitalSubring R) ≃+* R := NonUnitalSubsemiring.topEquiv

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubring R)

/-! ## comap -/


/-- The preimage of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
def comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring S) :
    NonUnitalSubring R :=
  { s.toSubsemigroup.comap (f : R →ₙ* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
theorem coe_comap (s : NonUnitalSubring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : NonUnitalSubring S} {f : F} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : NonUnitalSubring T) (g : S →ₙ+* T) (f : R →ₙ+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/

/-- The image of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
def map {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring R) :
    NonUnitalSubring S :=
  { s.toSubsemigroup.map (f : R →ₙ* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

@[simp]
theorem coe_map (f : F) (s : NonUnitalSubring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : F} {s : NonUnitalSubring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image _ _ _

@[simp]
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →ₙ+* T) (f : R →ₙ+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubring R → NonUnitalSubring S) (comap f) := fun _S _T =>
  map_le_iff_le_comap

/-- A `NonUnitalSubring` is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R → S)) :
    s ≃+* s.map f :=
  {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## range -/

/-- The range of a ring homomorphism, as a `NonUnitalSubring` of the target.
See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R →ₙ+* S) : NonUnitalSubring S :=
  ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
theorem mem_range {f : R →ₙ+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

theorem range_eq_map (f : R →ₙ+* S) : f.range = NonUnitalSubring.map f ⊤ := by ext; simp

theorem mem_range_self (f : R →ₙ+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩

theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

/-- The range of a ring homomorphism is a fintype if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →ₙ+* S) : Fintype (range f) :=
  Set.fintypeRange f

end NonUnitalRingHom

namespace NonUnitalSubring

section Order

variable {R : Type u} [NonUnitalNonAssocRing R]

/-! ## bot -/


instance : Bot (NonUnitalSubring R) :=
  ⟨(0 : R →ₙ+* R).range⟩

instance : Inhabited (NonUnitalSubring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0} :=
  (NonUnitalRingHom.coe_range (0 : R →ₙ+* R)).trans (@Set.range_const R R _ 0)

theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubring R) ↔ x = 0 :=
  show x ∈ ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

/-! ## inf -/

/-- The inf of two `NonUnitalSubring`s is their intersection. -/
instance : Min (NonUnitalSubring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : NonUnitalSubring R) :
    ((p ⊓ p' : NonUnitalSubring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : NonUnitalSubring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : InfSet (NonUnitalSubring R) :=
  ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (NonUnitalSubring R)) :
    ((sInf S : NonUnitalSubring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
theorem mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} {x : R} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
theorem sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- `NonUnitalSubring`s of a ring form a complete lattice. -/
instance : CompleteLattice (NonUnitalSubring R) :=
  { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : NonUnitalSubring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

end Order

/-! ## Center of a ring -/

section Center
variable {R : Type u}

section NonUnitalNonAssocRing
variable (R) [NonUnitalNonAssocRing R]

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : NonUnitalSubring R :=
  { NonUnitalSubsemiring.center R with
    neg_mem' := Set.neg_mem_center }

theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
theorem center_toNonUnitalSubsemiring :
    (center R).toNonUnitalSubsemiring = NonUnitalSubsemiring.center R :=
  rfl

/-- The center is commutative and associative. -/
instance center.instNonUnitalCommRing : NonUnitalCommRing (center R) where
  __ : NonUnitalCommSemiring (center R) :=
    inferInstanceAs <| NonUnitalCommSemiring (NonUnitalSubsemiring.center R)
  __ := (inferInstance : NonUnitalNonAssocRing (center R))

variable {R}

/-- The center of isomorphic (not necessarily unital or associative) rings are isomorphic. -/
@[simps!] def centerCongr {S} [NonUnitalNonAssocRing S] (e : R ≃+* S) : center R ≃+* center S :=
  NonUnitalSubsemiring.centerCongr e

/-- The center of a (not necessarily unital or associative) ring
is isomorphic to the center of its opposite. -/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ :=
  NonUnitalSubsemiring.centerToMulOpposite

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

-- no instance diamond, unlike the unital version
example : (center.instNonUnitalCommRing _).toNonUnitalRing =
      NonUnitalSubringClass.toNonUnitalRing (center R) := by
  with_reducible_and_instances rfl

theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g := Subsemigroup.mem_center_iff

instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
theorem center_eq_top (R) [NonUnitalCommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end NonUnitalRing

section Centralizer

variable {R : Type*} [NonUnitalRing R]

/-- The centralizer of a set as non-unital subring. -/
def centralizer (s : Set R) : NonUnitalSubring R :=
  { NonUnitalSubsemiring.centralizer s with
    carrier := s.centralizer
    neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
theorem coe_centralizer (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl

theorem centralizer_toNonUnitalSubsemiring (s : Set R) :
    (centralizer s).toNonUnitalSubsemiring = NonUnitalSubsemiring.centralizer s :=
  rfl

theorem mem_centralizer_iff {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl

theorem center_le_centralizer (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer

theorem centralizer_le (s t : Set R) (h : s ⊆ t) :
    centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
theorem centralizer_eq_top_iff_subset {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
theorem centralizer_univ : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

end Center

/-! ## `NonUnitalSubring` closure of a subset -/

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- The `NonUnitalSubring` generated by a set. -/
def closure (s : Set R) : NonUnitalSubring R :=
  sInf {S | s ⊆ S}

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : NonUnitalSubring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The `NonUnitalSubring` generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _x hx => mem_closure.2 fun _S hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ closure s := subset_closure hx

theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A `NonUnitalSubring` `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : NonUnitalSubring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- `NonUnitalSubring` closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : (x : R) → x ∈ closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_closure hx)) (zero : p 0 (zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let K : NonUnitalSubring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ ↦ ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩ }
  closure_le (t := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ closure s → y ∈ closure s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (neg_left : ∀ x y hx hy, p x y hx hy → p (-x) y (neg_mem hx) hy)
    (neg_right : ∀ x y hx hy, p x y hx hy → p x (-y) hx (neg_mem hy))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x ∈ closure s) (hy : y ∈ closure s) :
    p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h

theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Subsemigroup.closure s : Set R) :=
  ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Subsemigroup.subset_closure hx)
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear _hx _hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem _ _ hx hy => exact AddSubgroup.subset_closure (mul_mem hx hy)
      | zero_left => simp
      | zero_right => simp
      | add_left _ _ _ _ _ _ h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂
      | add_right _ _ _ _ _ _ h₁ h₂ => simpa [mul_add] using add_mem h₁ h₂
      | neg_left _ _ _ _ h => simpa [neg_mul] using neg_mem h
      | neg_right _ _ _ _ h => simpa [mul_neg] using neg_mem h,
  fun h => by
    induction h using AddSubgroup.closure_induction with
    | mem _ hx => induction hx using Subsemigroup.closure_induction with
      | mem _ h => exact subset_closure h
      | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | neg _ _ h => exact neg_mem h⟩

lemma closure_le_centralizer_centralizer {R : Type*} [NonUnitalRing R] (s : Set R) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
semiring. -/
theorem isMulCommutative_closure {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
ring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
abbrev closureNonUnitalCommRingOfComm {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : NonUnitalCommRing (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance

instance instIsMulCommutative_closure {S R : Type*} [NonUnitalRing R]
    [SetLike S R] [MulMemClass S R] (s : S) [IsMulCommutative s] :
    IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable (R) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) SetLike.coe where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

/-- Closure of a `NonUnitalSubring` `S` equals `S`. -/
@[simp]
theorem closure_eq (s : NonUnitalSubring R) : closure (s : Set R) = s :=
  (NonUnitalSubring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (NonUnitalSubring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (NonUnitalSubring.gi R).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (NonUnitalSubring.gi R).gc.l_iSup

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (NonUnitalSubring.gi R).gc.l_sSup

theorem map_sup (s t : NonUnitalSubring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : F) (s : ι → NonUnitalSubring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem map_inf (s t : NonUnitalSubring R) (f : F) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι → NonUnitalSubring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

theorem comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_iInf {ι : Sort*} (f : F) (s : ι → NonUnitalSubring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem map_bot (f : R →ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `NonUnitalSubring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×ˢ t`
as a `NonUnitalSubring` of `R × S`. -/
def prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

@[norm_cast]
theorem coe_prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ t :=
  rfl

theorem mem_prod {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[gcongr, mono]
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄
    (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : NonUnitalSubring R) :
    Monotone fun t : NonUnitalSubring S => s.prod t :=
  prod_mono (le_refl s)

theorem prod_mono_left (t : NonUnitalSubring S) : Monotone fun s : NonUnitalSubring R => s.prod t :=
  fun _s₁ _s₂ hs => prod_mono hs (le_refl t)

theorem prod_top (s : NonUnitalSubring R) :
    s.prod (⊤ : NonUnitalSubring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod]

theorem top_prod (s : NonUnitalSubring S) :
    (⊤ : NonUnitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
theorem top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of `NonUnitalSubring`s is isomorphic to their product as rings. -/
def prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The underlying set of a non-empty directed Sup of `NonUnitalSubring`s is just a union of the
`NonUnitalSubring`s. Note that this fails without the directedness assumption (the union of two
`NonUnitalSubring`s is typically not a `NonUnitalSubring`) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩

theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]

theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists,
    exists_prop]

theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι → NonUnitalSubring R}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubring R} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) :=
  isMulCommutative_iSup S.monotone.directed_le

theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubring R} {x : S} :
    x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubring R) :
    K.map (f : R →ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubring S) :
    K.comap (f : R →ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalSubring

/-- Restriction of a ring homomorphism to its range interpreted as a `NonUnitalSubring`.

This is the bundled version of `Set.rangeFactorization`. -/
def rangeRestrict (f : R →ₙ+* S) : R →ₙ+* f.range :=
  NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]
theorem coe_rangeRestrict (f : R →ₙ+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl

theorem rangeRestrict_surjective (f : R →ₙ+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

theorem range_eq_top {f : R →ₙ+* S} :
    f.range = (⊤ : NonUnitalSubring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
theorem range_eq_top_of_surjective (f : R →ₙ+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : NonUnitalSubring S) :=
  range_eq_top.2 hf

/-- The `NonUnitalSubring` of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a `NonUnitalSubring` of R -/
def eqLocus (f g : R →ₙ+* S) : NonUnitalSubring R :=
  { (f : R →ₙ* S).eqLocus g, (f : R →+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]
theorem mem_eqLocus {f g : R →ₙ+* S} {x : R} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

@[simp]
theorem eqLocus_same (f : R →ₙ+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its
`NonUnitalSubring` closure. -/
theorem eqOn_set_closure {f g : R →ₙ+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eqOn_set_top {f g : R →ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubring R)) : f = g :=
  ext fun _x => h trivial

theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →ₙ+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h

theorem closure_preimage_le (f : R →ₙ+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the `NonUnitalSubring` generated by a set equals
the `NonUnitalSubring` generated by the image of the set. -/
theorem map_closure (f : R →ₙ+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubring.gi S).gc
    (NonUnitalSubring.gi R).gc fun _ ↦ rfl

end NonUnitalRingHom

namespace NonUnitalSubring

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalRingHom

@[simp]
theorem range_subtype (s : NonUnitalSubring R) : (NonUnitalSubringClass.subtype s).range = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalSubsemiring.range_fst

theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalSubsemiring.range_snd

end NonUnitalSubring

namespace RingEquiv

variable {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S] {s t : NonUnitalSubring R}

/-- Makes the identity isomorphism from a proof two `NonUnitalSubring`s of a multiplicative
monoid are equal. -/
def nonUnitalSubringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`. -/
def ofLeftInverse' {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
theorem ofLeftInverse'_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse' h x) = f x :=
  rfl

@[simp]
theorem ofLeftInverse'_symm_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse' h).symm x = g x :=
  rfl

end RingEquiv

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

theorem closure_preimage_le (f : F) (s : Set S) :
    closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end NonUnitalSubring

end Hom
