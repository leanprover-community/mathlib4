/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Notation.Prod

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib/GroupTheory/Subsemigroup/Center.lean` for the definition of the center as a
subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib/GroupTheory/Subsemigroup/Centralizer.lean` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

assert_not_exists HeytingAlgebra RelIso Finset MonoidWithZero Subsemigroup

variable {M : Type*} {S T : Set M}

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : AddCommute z a
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : Commute z a
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a c : M} [Mul M]

@[to_additive]
protected theorem mid_assoc {z : M} (h : IsMulCentral z) (a c) : a * z * c = a * (z * c) := by
  rw [h.comm, ← h.right_assoc, ← h.comm, ← h.left_assoc, h.comm]

-- cf. `Commute.left_comm`
@[to_additive]
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [(h.comm _).eq, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, (h.comm _).eq]

end IsMulCentral

namespace Set

/-! ### Center -/

section Mul
variable [Mul M]

variable (M) in
/-- The center of a magma. -/
@[to_additive addCenter /-- The center of an additive magma. -/]
def center : Set M :=
  { z | IsMulCentral z }

variable (S) in
/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer /-- The centralizer of a subset of an additive magma. -/]
def centralizer : Set M := {c | ∀ m ∈ S, m * c = c * m}

@[to_additive mem_addCenter_iff]
theorem mem_center_iff {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl

@[to_additive mem_addCentralizer]
lemma mem_centralizer_iff {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m := Iff.rfl

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by rw [hz₁.comm]
    _ = z₂ * (z₁ * a) := by rw [hz₁.mid_assoc z₂]
    _ = (a * z₁) * z₂ := by rw [hz₁.comm, hz₂.comm]
    _ = a * (z₁ * z₂) := by rw [hz₂.right_assoc a z₁]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]

@[to_additive addCenter_subset_addCentralizer]
lemma center_subset_centralizer (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ ↦ (hx.comm m).symm

@[to_additive addCentralizer_union]
lemma centralizer_union : centralizer (S ∪ T) = centralizer S ∩ centralizer T := by
  simp [centralizer, or_imp, forall_and, setOf_and]

@[to_additive (attr := gcongr) addCentralizer_subset]
lemma centralizer_subset (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun _ ht s hs ↦ ht s (h hs)

@[to_additive subset_addCentralizer_addCentralizer]
lemma subset_centralizer_centralizer : S ⊆ S.centralizer.centralizer := by
  intro x hx
  simp only [Set.mem_centralizer_iff]
  exact fun y hy => (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
lemma centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  intro x hx
  rw [Set.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_centralizer_iff] at hx
  exact hx y <| Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ ↦ decidable_of_iff' _ mem_centralizer_iff

@[to_additive addCentralizer_addCentralizer_comm_of_comm]
lemma centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x :=
  fun _ h₁ _ h₂ ↦ h₂ _ fun _ h₃ ↦ h₁ _ fun _ h₄ ↦ h_comm _ h₄ _ h₃

@[to_additive addCentralizer_empty]
theorem centralizer_empty : (∅ : Set M).centralizer = ⊤ := by
  simp only [centralizer, mem_empty_iff_false, IsEmpty.forall_iff, implies_true, setOf_true,
    top_eq_univ]

/-- The centralizer of the product of non-empty sets is equal to the product of the centralizers. -/
@[to_additive addCentralizer_prod]
theorem centralizer_prod {N : Type*} [Mul N] {S : Set M} {T : Set N}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer := by
  ext
  simp_rw [mem_prod, mem_centralizer_iff, mem_prod, and_imp, Prod.forall,
    Prod.mul_def, Prod.eq_iff_fst_eq_snd_eq]
  obtain ⟨b, hb⟩ := hS
  obtain ⟨c, hc⟩ := hT
  exact ⟨fun h => ⟨fun y hy => (h y c hy hc).1, fun y hy => (h b y hb hy).2⟩,
    fun h y z hy hz => ⟨h.1 _ hy, h.2 _ hz⟩⟩

@[to_additive prod_addCentralizer_subset_addCentralizer_prod]
theorem prod_centralizer_subset_centralizer_prod {N : Type*} [Mul N] (S : Set M) (T : Set N) :
    S.centralizer ×ˢ T.centralizer ⊆ (S ×ˢ T).centralizer := by
  rw [subset_def]
  simp only [mem_prod, and_imp, Prod.forall, mem_centralizer_iff, Prod.mk_mul_mk, Prod.mk.injEq]
  exact fun a b ha hb c d hc hd => ⟨ha c hc, hb d hd⟩

@[to_additive addCenter_prod]
theorem center_prod {N : Type*} [Mul N] :
    center (M × N) = center M ×ˢ center N := by
  ext x
  simp only [mem_prod, mem_center_iff, isMulCentral_iff, commute_iff_eq, Prod.ext_iff]
  exact ⟨
    fun ⟨h1, h2, h3⟩ => ⟨
      ⟨ fun a => (h1 (a, x.2)).1,
        fun b c => (h2 (b, x.2) (c, x.2)).1,
        fun a b => (h3 (a, x.2) (b, x.2)).1⟩,
      ⟨ fun a => (h1 (x.1, a)).2,
        fun a b => (h2 (x.1, a) (x.1, b)).2,
        fun a b => (h3 (x.1, a) (x.1, b)).2⟩⟩,
    fun ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ => ⟨
      fun _ => ⟨h1 _, h4 _⟩,
      fun _ _ => ⟨h2 _ _, h5 _ _⟩,
      fun _ _ => ⟨h3 _ _, h6 _ _⟩⟩⟩

open Function in
@[to_additive addCenter_pi]
theorem center_pi {ι : Type*} {A : ι → Type*} [Π i, Mul (A i)] :
    center (Π i, A i) = univ.pi (fun i => center (A i)) := by
  classical
  ext x
  simp only [mem_pi, mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  exact ⟨
    fun ⟨h1, h2, h3⟩ i => ⟨
      fun a => by simpa using h1 (update x i a) i,
      fun b c => by simpa using h2 (update x i b) (update x i c) i,
      fun a b => by simpa using h3 (update x i a) (update x i b) i⟩,
    fun h => ⟨
      fun a i => (h i).1 (a i),
      fun b c i => (h i).2.1 (b i) (c i),
      fun a b i => (h i).2.2 (a i) (b i)⟩⟩

end Mul

section Semigroup
variable [Semigroup M] {a b : M}

@[to_additive]
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (h _).symm, fun _ _ ↦ (mul_assoc z _ _).symm, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]
lemma mul_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg ↦ by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
theorem centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S ⊆ center M :=
  eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by rw [h trivial _ hx],
    fun h _ _ _ hm ↦ (h hm).comm _⟩

variable (M) in
@[to_additive (attr := simp) addCentralizer_univ]
lemma centralizer_univ : centralizer univ = center M :=
  Subset.antisymm (fun _ ha ↦ Semigroup.mem_center_iff.mpr fun b ↦ ha b (Set.mem_univ b))
  fun _ ha b _ ↦ (ha.comm b).symm

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
@[to_additive decidableMemAddCenter]
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

@[to_additive (attr := simp) addCentralizer_eq_univ]
lemma centralizer_eq_univ : centralizer S = univ :=
  eq_univ_of_forall fun _ _ _ ↦ mul_comm _ _

end CommSemigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

@[to_additive (attr := simp) zero_mem_addCentralizer]
lemma one_mem_centralizer : (1 : M) ∈ centralizer S := by simp [mem_centralizer_iff]

end MulOneClass

section Monoid
variable [Monoid M]

@[to_additive subset_addCenter_add_units]
theorem subset_center_units : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.val_inj, Units.val_mul, Units.val_mul, ha.comm]

@[to_additive (attr := simp)]
theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

end DivisionMonoid

section Group
variable [Group M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCentralizer]
lemma inv_mem_centralizer (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  fun g hg ↦ by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[to_additive (attr := simp) sub_mem_addCentralizer]
lemma div_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

end Group
end Set
