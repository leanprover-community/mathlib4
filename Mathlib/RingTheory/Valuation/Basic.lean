/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Unbundled.Units
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.TFAE

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
* `v 0 = 0`
* `∀ x y, v (x + y) ≤ max (v x) (v y)`

`Valuation R Γ₀` is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `Units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `IsEquiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : Valuation R Γ₁` and `v₂ : Valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

## Main definitions

* `Valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `Valuation.IsNontrivial` is the class of non-trivial valuations, namely those for which there
  is an element in the ring whose valuation is `≠ 0` and `≠ 1`.
* `Valuation.IsEquiv`, the heterogeneous equivalence relation on valuations
* `Valuation.supp`, the support of a valuation

* `AddValuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`AddValuation R Γ₀` is implemented as `Valuation R (Multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `WithZero` locale, `Mᵐ⁰` is a shorthand for `WithZero (Multiplicative M)`.

## TODO

If ever someone extends `Valuation`, we should fully comply to the `DFunLike` by migrating the
boilerplate lemmas to `ValuationClass`.
-/

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

section

variable (F R) (Γ₀ : Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]

/-- The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `ValuationClass`. -/
structure Valuation extends R →*₀ Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)

/-- `ValuationClass F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `Valuation`. -/
class ValuationClass (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
    [FunLike F R Γ₀] : Prop
  extends MonoidWithZeroHomClass F R Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y)

export ValuationClass (map_add_le_max)

instance [FunLike F R Γ₀] [ValuationClass F R Γ₀] : CoeTC F (Valuation R Γ₀) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩

end

namespace Valuation

variable {Γ₀ : Type*}
variable {Γ'₀ : Type*}
variable {Γ''₀ : Type*} [LinearOrderedCommMonoidWithZero Γ''₀]

section Basic

variable [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]

instance : FunLike (Valuation R Γ₀) R Γ₀ where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_,_⟩, _⟩, _⟩ := f
    congr

instance : ValuationClass (Valuation R Γ₀) R Γ₀ where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]
theorem coe_mk (f : R →*₀ Γ₀) (h) : ⇑(Valuation.mk f h) = f := rfl

theorem toFun_eq_coe (v : Valuation R Γ₀) : v.toFun = v := rfl

@[simp]
theorem toMonoidWithZeroHom_coe_eq_coe (v : Valuation R Γ₀) :
    (v.toMonoidWithZeroHom : R → Γ₀) = v := rfl

@[ext]
theorem ext {v₁ v₂ : Valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  DFunLike.ext _ _ h

variable (v : Valuation R Γ₀)

@[simp, norm_cast]
theorem coe_coe : ⇑(v : R →*₀ Γ₀) = v := rfl

protected theorem map_zero : v 0 = 0 :=
  v.map_zero'

protected theorem map_one : v 1 = 1 :=
  v.map_one'

protected theorem map_mul : ∀ x y, v (x * y) = v x * v y :=
  v.map_mul'

-- `simp`-normal form is `map_add'`
protected theorem map_add : ∀ x y, v (x + y) ≤ max (v x) (v y) :=
  v.map_add_le_max'

@[simp]
theorem map_add' : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := by
  intro x y
  rw [← le_max_iff, ← ge_iff_le]
  apply v.map_add

theorem map_add_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x + y) ≤ g :=
  le_trans (v.map_add x y) <| max_le hx hy

theorem map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
  lt_of_le_of_lt (v.map_add x y) <| max_lt hx hy

theorem map_sum_le {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, v (f i) ≤ g) :
    v (∑ i ∈ s, f i) ≤ g := by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ zero_le')
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

theorem map_sum_lt {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g := by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

theorem map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g :=
  v.map_sum_lt (ne_of_gt hg) hf

protected theorem map_pow : ∀ (x) (n : ℕ), v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.toMonoidHom.map_pow

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
theorem zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
  map_eq_zero v

theorem ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero v

lemma pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : 0 < v x ↔ x ≠ 0 := by
  rw [zero_lt_iff, ne_zero_iff]

theorem unit_map_eq (u : Rˣ) : (Units.map (v : R →* Γ₀) u : Γ₀) = v u :=
  rfl

theorem ne_zero_of_unit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ) : v x ≠ (0 : Γ₀) := by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

theorem ne_zero_of_isUnit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUnit x) :
    v x ≠ (0 : Γ₀) := by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

/-- A ring homomorphism `S → R` induces a map `Valuation R Γ₀ → Valuation S Γ₀`. -/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp only [comp_apply, v.map_add, map_add] }

@[simp]
theorem comap_apply {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) (s : S) :
    v.comap f s = v (f s) := rfl

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  ext fun _r => rfl

theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  ext fun _r => rfl

/-- A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `Valuation R Γ₀ → Valuation R Γ'₀`.
-/
def map (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) ≤ f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

@[simp]
lemma map_apply (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) (r : R) :
    v.map f hf r = f (v r) := rfl

/-- Two valuations on `R` are defined to be equivalent if they induce the same preorder on `R`. -/
def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  v.toMonoidWithZeroHom.toMonoidHom.map_neg x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

theorem map_sub (x y : R) : v (x - y) ≤ max (v x) (v y) :=
  calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]

theorem map_sub_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x - y) ≤ g := by
  rw [sub_eq_add_neg]
  exact v.map_add_le hx <| (v.map_neg y).trans_le hy

theorem map_sub_lt {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g) : v (x - y) < g := by
  rw [sub_eq_add_neg]
  exact v.map_add_lt hx <| (v.map_neg y).trans_lt hy

variable {x y : R}

@[simp]
lemma le_one_of_subsingleton [Subsingleton R] (v : Valuation R Γ₀) {x : R} :
    v x ≤ 1 := by
  rw [Subsingleton.elim x 1, Valuation.map_one]

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) := by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_gt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ ≤ max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx

theorem map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y :=
  (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)

theorem map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x := by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h

theorem map_sub_eq_of_lt_right (h : v x < v y) : v (x - y) = v y := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_right, map_neg]
  rwa [map_neg]

open scoped Classical in
theorem map_sum_eq_of_lt {ι : Type*} {s : Finset ι} {f : ι → R} {j : ι}
    (hj : j ∈ s) (h0 : v (f j) ≠ 0) (hf : ∀ i ∈ s \ {j}, v (f i) < v (f j)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  rw [Finset.sum_eq_add_sum_diff_singleton hj]
  exact map_add_eq_of_lt_left _ (map_sum_lt _ h0 hf)

theorem map_sub_eq_of_lt_left (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_left]
  rwa [map_neg]

theorem map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x := by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this

lemma map_sub_of_left_eq_zero (hx : v x = 0) : v (x - y) = v y := by
  by_cases hy : v y = 0
  · simpa [*] using map_sub v x y
  · simp [*, map_sub_eq_of_lt_right, zero_lt_iff]

lemma map_sub_of_right_eq_zero (hy : v y = 0) : v (x - y) = v x := by
  rw [map_sub_swap, map_sub_of_left_eq_zero v hy]

lemma map_add_of_left_eq_zero (hx : v x = 0) : v (x + y) = v y := by
  rw [← sub_neg_eq_add, map_sub_of_left_eq_zero v hx, map_neg]

lemma map_add_of_right_eq_zero (hy : v y = 0) : v (x + y) = v x := by
  rw [add_comm, map_add_of_left_eq_zero v hy]

theorem map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1 := by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h

theorem map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1 := by
  rw [← v.map_one, ← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h

/-- An ordered monoid isomorphism `Γ₀ ≃ Γ'₀` induces an equivalence
`Valuation R Γ₀ ≃ Valuation R Γ'₀`. -/
def congr (f : Γ₀ ≃*o Γ'₀) : Valuation R Γ₀ ≃ Valuation R Γ'₀ where
  toFun := map f f.toOrderIso.monotone
  invFun := map f.symm f.toOrderIso.symm.monotone
  left_inv ν := by ext; simp
  right_inv ν := by ext; simp

section One

variable [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R ↦ x = 0]

variable (R Γ₀) in
/-- The trivial valuation, sending everything to 1 other than 0. -/
protected instance one : One (Valuation R Γ₀) where
  one :=
  { __ : R →*₀ Γ₀ := 1
    map_add_le_max' x y := by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe,
        MonoidWithZeroHom.one_apply_def, le_sup_iff]
      split_ifs <;> simp_all }

lemma one_apply_def (x : R) : (1 : Valuation R Γ₀) x = if x = 0 then 0 else 1 := rfl

@[simp] lemma toMonoidWithZeroHom_one : (1 : Valuation R Γ₀).toMonoidWithZeroHom = 1 := rfl

lemma one_apply_of_ne_zero {x : R} (hx : x ≠ 0) : (1 : Valuation R Γ₀) x = 1 := if_neg hx

@[simp]
lemma one_apply_eq_zero_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 0 ↔ x = 0 :=
  MonoidWithZeroHom.one_apply_eq_zero_iff

lemma one_apply_le_one (x : R) : (1 : Valuation R Γ₀) x ≤ 1 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]
lemma one_apply_lt_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x < 1 ↔ x = 0 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

end One

end Monoid

section Group

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {x y : R}

theorem map_inv {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x, v x⁻¹ = (v x)⁻¹ :=
  map_inv₀ _

theorem map_div {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x y, v (x / y) = v x / v y :=
  map_div₀ _

theorem one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 < v x ↔ v x⁻¹ < 1 := by
  simp [inv_lt_one₀ (v.pos_iff.2 h)]

theorem one_le_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 ≤ v x ↔ v x⁻¹ ≤ 1 := by
  simp [inv_le_one₀ (v.pos_iff.2 h)]

theorem val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x < 1 ↔ 1 < v x⁻¹ := by
  simp [one_lt_inv₀ (v.pos_iff.2 h)]

theorem val_le_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x ≤ 1 ↔ 1 ≤ v x⁻¹ := by
  simp [one_le_inv₀ (v.pos_iff.2 h)]

theorem val_eq_one_iff (v : Valuation K Γ₀) {x : K} : v x = 1 ↔ v x⁻¹ = 1 := by
  simp

theorem val_le_one_or_val_inv_lt_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ < 1 := by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le', inv_zero, zero_lt_one, or_self]
  · simp only [← one_lt_val_iff v h, le_or_gt]

/--
This theorem is a weaker version of `Valuation.val_le_one_or_val_inv_lt_one`, but more symmetric
in `x` and `x⁻¹`.
-/
theorem val_le_one_or_val_inv_le_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ ≤ 1 := by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le', inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

/-- The subgroup of elements whose valuation is less than a certain unit. -/
@[simps] def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  carrier := { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_setOf, map_neg]

@[simp] lemma mem_ltAddSubgroup_iff {v : Valuation R Γ₀} {γ x} :
    x ∈ ltAddSubgroup v γ ↔ v x < γ :=
  Iff.rfl

end Group

end Basic

section IsNontrivial

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- A valuation on a ring is nontrivial if there exists an element with valuation
not equal to `0` or `1`. -/
class IsNontrivial : Prop where
  exists_val_nontrivial : ∃ x : R, v x ≠ 0 ∧ v x ≠ 1

lemma IsNontrivial.nontrivial_codomain [hv : IsNontrivial v] :
    Nontrivial Γ₀ := by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  exact ⟨v x, 1, hx1⟩

lemma not_isNontrivial_one [IsDomain R] [DecidablePred fun x : R ↦ x = 0] :
    ¬(1 : Valuation R Γ₀).IsNontrivial := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  rcases eq_or_ne x 0 with rfl | hx0 <;>
  simp_all [one_apply_of_ne_zero]

section Field

variable {K : Type*} [Field K] {w : Valuation K Γ₀}

/-- For fields, being nontrivial is equivalent to the existence of a unit with valuation
not equal to `1`. -/
lemma isNontrivial_iff_exists_unit :
    w.IsNontrivial ↔ ∃ x : Kˣ, w x ≠ 1 :=
  ⟨fun ⟨x, hx0, hx1⟩ ↦
    have : Nontrivial Γ₀ := ⟨w x, 0, hx0⟩
    ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ ↦
    have : Nontrivial Γ₀ := ⟨w x, 1, hx⟩
    ⟨x, w.ne_zero_iff.mpr (Units.ne_zero x), hx⟩⟩

lemma IsNontrivial.exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    ∃ x : K, v x ≠ 0 ∧ v x < 1 := by
  obtain ⟨x, hx⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [ne_iff_lt_or_gt] at hx
  rcases hx with hx | hx
  · use x
    simp [hx]
  · use x⁻¹
    simp [- map_inv₀, ← one_lt_val_iff, hx]

theorem isNontrivial_iff_exists_lt_one {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    v.IsNontrivial ↔ ∃ x, x ≠ 0 ∧ v x < 1 :=
  ⟨fun h ↦ by simpa using h.exists_lt_one (v := v), fun ⟨x, hx0, hx1⟩ ↦ ⟨x, by simp [hx0, hx1.ne]⟩⟩

lemma IsNontrivial.exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    ∃ x : K, v x ≠ 0 ∧ 1 < v x := by
  obtain ⟨x, h0, h1⟩ := hv.exists_lt_one
  use x⁻¹
  simp [one_lt_inv₀ (zero_lt_iff.mpr h0), h0, h1]

end Field

end IsNontrivial

namespace IsEquiv

section

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  {v : Valuation R Γ₀} {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀} {v₃ : Valuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v := fun _ _ => Iff.refl _

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)

theorem of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v' := by subst h; rfl

theorem map {v' : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (inf : Injective f)
    (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.map f hf) :=
  let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) ≤ f (v s) ↔ v r ≤ v s := by rw [H.le_iff_le]
    _ ↔ v' r ≤ v' s := h r s
    _ ↔ f (v' r) ≤ f (v' s) := by rw [H.le_iff_le]

/-- `comap` preserves equivalence. -/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) := fun r s => h (f r) (f s)

end

section LinearOrderedCommMonoidWithZero

variable [Ring R]
  {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂]
  {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
  (h : v₁.IsEquiv v₂)
  {x x₁ x₂ y y₁ y₂ z w : R}

include h

theorem val_eq : v₁ x = v₁ y ↔ v₂ x = v₂ y := by
  simpa only [le_antisymm_iff] using and_congr (h x y) (h y x)

theorem eq_zero : v₁ x = 0 ↔ v₂ x = 0 := by
  rw [← v₁.map_zero, ← v₂.map_zero, h.val_eq]

theorem ne_zero : v₁ x ≠ 0 ↔ v₂ x ≠ 0 := by
  rw [not_iff_not, h.eq_zero]

lemma lt_iff_lt : v₁ x < v₁ y ↔ v₂ x < v₂ y := by
  rw [← le_iff_le_iff_lt_iff_lt, h]

lemma le_one_iff_le_one : v₁ x ≤ 1 ↔ v₂ x ≤ 1 := by
  rw [← v₁.map_one, h, map_one]

lemma eq_one_iff_eq_one : v₁ x = 1 ↔ v₂ x = 1 := by
  rw [← v₁.map_one, h.val_eq, map_one]

lemma lt_one_iff_lt_one : v₁ x < 1 ↔ v₂ x < 1 := by
  rw [← v₁.map_one, h.lt_iff_lt, map_one]

set_option linter.unusedVariables false in
/-- If `v₁.Equiv v₂`, then the ranges of `v₁` and `v₂` are isomorphic. We can adjoin the inverses
of elements of the ranges that are invertible in both monoids, and the two resulting monoids are
also isomorphic.

This `Prop` is precisely the relation saying that the isomorphism sends `x` to `y`.

This is an auxiliary definition for the tactic `rw_val_equiv`. -/
@[nolint unusedArguments]
def Associated (h : v₁.IsEquiv v₂) (x : Γ₁) (y : Γ₂) : Prop :=
  ∃ r s : R, IsUnit (v₁ s) ∧ IsUnit (v₂ s) ∧ v₁ r = x * v₁ s ∧ v₂ r = y * v₂ s

namespace Associated

variable {h} {x₁ x₂ : Γ₁} {y₁ y₂ : Γ₂} (h₁ : h.Associated x₁ y₁) (h₂ : h.Associated x₂ y₂)

theorem value {r : R} : h.Associated (v₁ r) (v₂ r) :=
  ⟨r, 1, by simp⟩

theorem zero : h.Associated 0 0 := by
  simpa using value (h := h) (r := 0)

theorem one : h.Associated 1 1 := by
  simpa using value (h := h) (r := 1)

include h₁ h₂

theorem mul : h.Associated (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨r₁, s₁, u₁, v₁, e₁, f₁⟩ := h₁
  obtain ⟨r₂, s₂, u₂, v₂, e₂, f₂⟩ := h₂
  exact ⟨r₁ * r₂, s₁ * s₂, by simp [mul_mul_mul_comm, *]⟩

omit h₂ in
theorem pow (n : ℕ) : h.Associated (x₁ ^ n) (y₁ ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => simpa [pow_succ] using ih.mul h₁

theorem le_iff_le : x₁ ≤ x₂ ↔ y₁ ≤ y₂ := by
  obtain ⟨r₁, s₁, i₁, j₁, e₁, f₁⟩ := h₁
  obtain ⟨r₂, s₂, i₂, j₂, e₂, f₂⟩ := h₂
  rw [← i₁.mul_le_mul_right, ← i₂.mul_le_mul_left, ← e₁, mul_left_comm, ← mul_assoc, ← e₂,
    ← j₁.mul_le_mul_right, ← j₂.mul_le_mul_left, ← f₁, mul_left_comm, ← mul_assoc, ← f₂,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, h]

theorem min : h.Associated (min x₁ x₂) (min y₁ y₂) := by
  obtain hx | hx := le_total x₁ x₂
  · have hy := (h₁.le_iff_le h₂).mp hx
    rwa [min_eq_left hx, min_eq_left hy]
  · have hy := (h₂.le_iff_le h₁).mp hx
    rwa [min_eq_right hx, min_eq_right hy]

theorem max : h.Associated (max x₁ x₂) (max y₁ y₂) := by
  obtain hx | hx := le_total x₁ x₂
  · have hy := (h₁.le_iff_le h₂).mp hx
    rwa [max_eq_right hx, max_eq_right hy]
  · have hy := (h₂.le_iff_le h₁).mp hx
    rwa [max_eq_left hx, max_eq_left hy]

theorem lt_iff_lt : x₁ < x₂ ↔ y₁ < y₂ := by
  simp_rw [← not_le, h₂.le_iff_le h₁]

theorem eq_iff_eq : x₁ = x₂ ↔ y₁ = y₂ := by
  simp_rw [le_antisymm_iff, h₁.le_iff_le h₂, h₂.le_iff_le h₁]

theorem ne_iff_ne : x₁ ≠ x₂ ↔ y₁ ≠ y₂ := by
  simp_rw [not_iff_not, h₁.eq_iff_eq h₂]

end Associated

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero

variable [Ring R]
  {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
  {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
  (h : v₁.IsEquiv v₂)

include h

theorem associated_iff_exists {x : Γ₁} {y : Γ₂} :
    h.Associated x y ↔ ∃ r s, v₁ r / v₁ s = x ∧ v₂ r / v₂ s = y := by
  refine ⟨fun ⟨r, s, i, j, e, f⟩ ↦ ⟨r, s, by simp [e, f, i.ne_zero, j.ne_zero]⟩, ?_⟩
  rintro ⟨r, s, rfl, rfl⟩
  have : v₁ s = 0 ↔ v₂ s = 0 :=
    Associated.eq_iff_eq (h := h) .value .zero
  by_cases hs : v₁ s = 0
  · rw [hs, this.mp hs, div_zero, div_zero]
    exact .zero
  · have := this.not.mp hs
    exact ⟨r, s, .mk0 _ hs, .mk0 _ this, by simp [hs, this]⟩
alias ⟨Associated.exists_eq, Associated.intro⟩ := associated_iff_exists

namespace Associated

variable {h} {x₁ x₂ : Γ₁} {y₁ y₂ : Γ₂} (h₁ : h.Associated x₁ y₁) (h₂ : h.Associated x₂ y₂)

include h₁

theorem inv : h.Associated x₁⁻¹ y₁⁻¹ := by
  rw [associated_iff_exists] at h₁ ⊢
  obtain ⟨r, s, rfl, rfl⟩ := h₁
  exact ⟨s, r, by simp⟩

theorem zpow (n : ℤ) : h.Associated (x₁ ^ n) (y₁ ^ n) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert h₁.pow n <;> rw [zpow_natCast]
  · convert (h₁.pow n).inv <;> rw [zpow_neg, zpow_natCast]

include h₂

theorem div : h.Associated (x₁ / x₂) (y₁ / y₂) := by
  convert h₁.mul h₂.inv using 1 <;> rw [div_eq_mul_inv]

omit h₁ h₂

@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem rec {motive : ∀ x y, h.Associated x y → Prop}
    (ih : ∀ r s, 0 < v₁ s → 0 < v₂ s → motive (v₁ r / v₁ s) (v₂ r / v₂ s) (div value value))
    {x : Γ₁} {y : Γ₂} (hxy : h.Associated x y) : motive x y hxy := by
  obtain ⟨r, s, i, j, e, f⟩ := hxy
  convert ih r s (zero_lt_iff.mpr i.ne_zero) (zero_lt_iff.mpr j.ne_zero)
  · rw [e, i.mul_div_cancel_right]
  · rw [f, j.mul_div_cancel_right]

end Associated

namespace EquivTac

open Lean Elab Meta Tactic Qq

initialize registerTraceClass `rw_val_equiv

variable {u₁ u₂ u₃ : Level}
  {R : Q(Type u₁)} {Γ₁ : Q(Type u₂)} {Γ₂ : Q(Type u₃)} {hR : Q(Ring $R)}
  {mΓ₁ : Q(LinearOrderedCommMonoidWithZero $Γ₁)}
  (gΓ₁? : Option Q(LinearOrderedCommGroupWithZero $Γ₁))
  {mΓ₂ : Q(LinearOrderedCommMonoidWithZero $Γ₂)}
  (gΓ₂? : Option Q(LinearOrderedCommGroupWithZero $Γ₂))
  (v₁ : Q(Valuation $R $Γ₁)) (v₂ : Q(Valuation $R $Γ₂))
  (h : Q(Valuation.IsEquiv $v₁ $v₂))

set_option linter.unusedVariables false in
include gΓ₁? gΓ₂? in
/-- The main loop: given an expression like `min (v₁ x) (v₁ y) / v₁ z`,
form the associated expression `min (v₂ x) (v₂ y) / v₂ z` and a proof that they are associated.

Allowed operations are: `0`, `1`, `v₁ r`, `⁻¹`, `^` (both `ℕ` and `ℤ`), `*`, `/`, `min`, `max`.

Out of these, `⁻¹`, `^` (for `ℤ`), and `/` are only allowed for groups. -/
partial def mkAssociated (h : Q(Valuation.IsEquiv $v₁ $v₂)) (x : Q($Γ₁)) :
    MetaM (Option ((y : Q($Γ₂)) × Q(Associated $h $x $y))) := do
  match x with
  | ~q(0) => return .some ⟨q(0), q(Associated.zero (h := $h))⟩
  | ~q(1) => return .some ⟨q(1), q(Associated.one (h := $h))⟩
  | ~q(«$v₁» $r) => return .some ⟨q($v₂ $r), q(Associated.value (h := $h) (r := $r))⟩
  | ~q($x ^ $n) =>
    let .some ⟨y, hxy⟩ ← mkAssociated h x | return .none
    return .some ⟨q($y ^ $n), q(Associated.pow $hxy $n)⟩
  | ~q($x₁ * $x₂) =>
    let .some ⟨y₁, hy₁⟩ ← mkAssociated h x₁ | return .none
    let .some ⟨y₂, hy₂⟩ ← mkAssociated h x₂ | return .none
    return .some ⟨q($y₁ * $y₂), q(Associated.mul $hy₁ $hy₂)⟩
  | ~q(min $x₁ $x₂) =>
    let .some ⟨y₁, hy₁⟩ ← mkAssociated h x₁ | return .none
    let .some ⟨y₂, hy₂⟩ ← mkAssociated h x₂ | return .none
    return .some ⟨q(min $y₁ $y₂), q(Associated.min $hy₁ $hy₂)⟩
  | ~q(max $x₁ $x₂) =>
    let .some ⟨y₁, hy₁⟩ ← mkAssociated h x₁ | return .none
    let .some ⟨y₂, hy₂⟩ ← mkAssociated h x₂ | return .none
    return .some ⟨q(max $y₁ $y₂), q(Associated.max $hy₁ $hy₂)⟩
  | _ => -- TODO: Optimise this part so it doesn't run every time we use inverse
    let .some gΓ₁ := gΓ₁? | return .none
    let .some gΓ₂ := gΓ₂? | return .none
    let mΓ₁' : Q(LinearOrderedCommMonoidWithZero $Γ₁) :=
      q(@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero $Γ₁ $gΓ₁)
    let mΓ₂' : Q(LinearOrderedCommMonoidWithZero $Γ₂) :=
      q(@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero $Γ₂ $gΓ₂)
    let @MaybeDefEq.defEq u₂ _ _ _ d₁ ← isDefEqQ mΓ₁' mΓ₁ | return .none
    let @MaybeDefEq.defEq u₃ _ _ _ d₂ ← isDefEqQ mΓ₂' mΓ₂ | return .none
    match x with
    | ~q($x⁻¹) =>
      let .some ⟨y, hxy⟩ ← mkAssociated h x | return .none
      return .some ⟨q($y⁻¹), q(Associated.inv $hxy)⟩
    | ~q($x ^ ($n : ℤ)) =>
      let .some ⟨y, hxy⟩ ← mkAssociated h x | return .none
      return .some ⟨q($y ^ $n), q(Associated.zpow $hxy $n)⟩
    | ~q($x₁ / $x₂) =>
      let .some ⟨y₁, hy₁⟩ ← mkAssociated h x₁ | return .none
      let .some ⟨y₂, hy₂⟩ ← mkAssociated h x₂ | return .none
      return .some ⟨q($y₁ / $y₂), q(Associated.div $hy₁ $hy₂)⟩
    | _ => return .none

/-- The type of relations: `≤`, `<`, `=`, `≠`. -/
inductive RelType : Type
  | le | lt | eq | ne
deriving Repr

/-- Convert a `RelType` to an `Expr` for debugging. -/
def RelType.toExpr : RelType → Expr
  | .le => .const ``RelType.le []
  | .lt => .const ``RelType.lt []
  | .eq => .const ``RelType.eq []
  | .ne => .const ``RelType.ne []

/-- Convert a `RelType` to the `Prop` on `Γ₁` that it represents. -/
def RelType.toProp {α : Q(Type u₁)} (oα : Q(Preorder $α)) : RelType → (x y : Q($α)) → Q(Prop)
  | .le, x, y => q($x ≤ $y)
  | .lt, x, y => q($x < $y)
  | .eq, x, y => q($x = $y)
  | .ne, x, y => q($x ≠ $y)

/-- Match the Prop in the form of `termL₁ ≤ termR₁` (where the `≤` can also be `<`, `=`, or `≠`),
where `termL₁` and `termR₁` are terms of `Γ₁`, and then form the associated terms `termL₂` and
`termR₂` in `Γ₂`, and then a proof of `termL₁ ≤ termR₁ ↔ termL₂ ≤ termR₂`. -/
def mkProof (h : Q(Valuation.IsEquiv $v₁ $v₂)) (rel : RelType) (x y : Q($Γ₁)) :
    MetaM (Option ((e₂ : Q(Prop)) × Q($(rel.toProp q(inferInstance) x y) ↔ $e₂))) := do
  let gΓ₁? ← trySynthInstanceQ q(LinearOrderedCommGroupWithZero $Γ₁)
  let gΓ₂? ← trySynthInstanceQ q(LinearOrderedCommGroupWithZero $Γ₂)
  let .some ⟨z, hxz⟩ ← mkAssociated gΓ₁?.toOption gΓ₂?.toOption v₁ v₂ h x | return .none
  let .some ⟨w, hyw⟩ ← mkAssociated gΓ₁?.toOption gΓ₂?.toOption v₁ v₂ h y | return .none
  trace[rw_val_equiv] m!"Transformed:\n({rel.toProp (α := Γ₁) q(inferInstance) x y})
to:\n({rel.toProp (α := Γ₂) q(inferInstance) z w})"
  match rel with
  | .le => return .some ⟨q($z ≤ $w), q(Associated.le_iff_le (h := $h) $hxz $hyw)⟩
  | .lt => return .some ⟨q($z < $w), q(Associated.lt_iff_lt (h := $h) $hxz $hyw)⟩
  | .eq => return .some ⟨q($z = $w), q(Associated.eq_iff_eq (h := $h) $hxz $hyw)⟩
  | .ne => return .some ⟨q($z ≠ $w), q(Associated.ne_iff_ne (h := $h) $hxz $hyw)⟩

/-- Match the relation to be one of `≤`, `<`, `=`, or `≠`, and then use `mkProof` to build the
proof wanted. -/
def matchAndMkProof (h : Q(Valuation.IsEquiv $v₁ $v₂)) (e₁ : Q(Prop)) :
    MetaM (Option ((e₂ : Q(Prop)) × Q($e₁ ↔ $e₂))) := do
  match e₁ with
  | ~q(($a : «$Γ₁») ≤ $b) => mkProof v₁ v₂ h .le a b
  | ~q(($a : «$Γ₁») < $b) => mkProof v₁ v₂ h .lt a b
  | ~q(($a : «$Γ₁») = $b) => mkProof v₁ v₂ h .eq a b
  | ~q(($a : «$Γ₁») ≠ $b) => mkProof v₁ v₂ h .ne a b
  | _ => return .none

/-- The core simproc of `rw_val_equiv`. Given `h : IsEquiv v₁ v₂`, find relations in `Γ₁` and
transport them to `Γ₂`. -/
def equivCore (h : Q(Valuation.IsEquiv $v₁ $v₂)) : Simp.Simproc := fun e : Expr ↦ do
  let ⟨1, ~q(Prop), e⟩ ← inferTypeQ e | return .continue
  let .some ⟨e₂, pf⟩ ← matchAndMkProof v₁ v₂ h e | return .continue
  return .visit { expr := e₂, proof? := q(propext $pf) }

set_option linter.unusedVariables false in
/-- Process the given local hypothesis. -/
def atLocal (s : Simp.Simproc) (f : FVarId) : TacticM Unit := do
  let hyp ← instantiateMVars (← f.getType)
  let ctx ← Simp.mkContext (simpTheorems := #[])
  let (r, _) ← Simp.mainCore hyp ctx (methods := {post := s})
  liftMetaTactic1 fun m ↦ do
    let .some (f, m) ← applySimpResultToLocalDecl m f r false | return m
    return m

/-- Process the goal. -/
def atTarget (s : Simp.Simproc) : TacticM Unit := do
  liftMetaTactic1 fun m ↦ do
    -- `Simproc` usually does not allow arguments, so we hijacked `Simp.mainCore` to provide a
    -- `Simproc` that accepts arguments (which is `equivCore` here).
    let target ← instantiateMVars (← m.getType)
    let ctx ← Simp.mkContext (simpTheorems := #[])
    let (r, _) ← Simp.mainCore target ctx (methods := {post := s})
    let i ← applySimpResultToTarget m target r
    return i
  evalTactic (← `(tactic| try rfl))

/-- Given the direction (`← ` or nothing) and `equiv : v₁.IsEquiv v₂`, make the simproc that
transforms relations according to the equivalence. -/
def mkSimproc (symm? : Option Syntax) (equiv : Term) : TacticM Simp.Simproc := do
  let h : Expr ← elabTerm equiv none
  match symm? with
  | .none =>
    let ⟨0, h', h⟩ ← inferTypeQ h
      | throwError "given term is not a proof"
    let ~q(@Valuation.IsEquiv $R $Γ₁ $Γ₂ $hR $hΓ₁ $hΓ₂ $v₁ $v₂) := h'
      | throwError "given term is not Valuation.isEquiv"
    return equivCore v₁ v₂ h
  | .some _ =>
    let ⟨0, h', h⟩ ← inferTypeQ h
      | throwError "given term is not a proof"
    let ~q(@Valuation.IsEquiv $R $Γ₁ $Γ₂ $hR $hΓ₁ $hΓ₂ $v₁ $v₂) := h'
      | throwError "given term is not Valuation.isEquiv"
    return equivCore v₂ v₁ q(($h).symm)

open Parser.Tactic Parser.Term

/-- A tactic to rewrite expressions in a goal (e.g. `v₁ x ≤ 1`) with an equivalent one in the other
value group or monoid (e.g. `v₂ x ≤ 1`), given `h : v₁.IsEquiv v₂`.

One can use `← ` to rewrite in the opposite direction, and to use `at` to specify which hypotheses
and/or goal to rewrite at, similar to the syntax of `rw`.

One can also use `rwa_val_equiv` to automatically use `assumption` afterwards, similar to `rwa`.

Usage:
```lean
example {R Γ₁ Γ₂ : Type*} [Ring R]
    [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂]
    {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
    (h : v₁.IsEquiv v₂) :
    {x | v₁ x ≤ 1} = {x | v₂ x ≤ 1} := by
  rw_val_equiv h
```
-/
elab "rw_val_equiv " symm?:(leftArrow)? e:(ppSpace colGt term:max) loc:(location)? : tactic => do
  let s ← mkSimproc symm? e
  match loc with
  | .none => atTarget s
  | .some loc => withLocation (expandLocation loc) (atLocal s) (atTarget s) default

open Lean.Parser.Tactic

/-- An alternate version of `rw_val_equiv` that calls `assumption` afterwards. -/
macro "rwa_val_equiv " s:(leftArrow)? e:(ppSpace colGt term:max) loc:(location)? : tactic =>
  match s with
  | .none => `(tactic| (rw_val_equiv $e $[$loc]?; assumption))
  | .some _ => `(tactic| (rw_val_equiv ← $e $[$loc]?; assumption))

end EquivTac

variable {x y z w : R}

theorem div_le_div_iff_div_le_div : v₁ x / v₁ y ≤ v₁ z / v₁ w ↔ v₂ x / v₂ y ≤ v₂ z / v₂ w := by
  rw_val_equiv h

theorem le_div_iff_le_div : v₁ x ≤ v₁ y / v₁ z ↔ v₂ x ≤ v₂ y / v₂ z := by
  rw_val_equiv h

theorem lt_div_iff_lt_div : v₁ x < v₁ y / v₁ z ↔ v₂ x < v₂ y / v₂ z := by
  rw_val_equiv h

theorem eq_div_iff_eq_div : v₁ x = v₁ y / v₁ z ↔ v₂ x = v₂ y / v₂ z := by
  rw_val_equiv h

theorem ne_div_iff_ne_div : v₁ x ≠ v₁ y / v₁ z ↔ v₂ x ≠ v₂ y / v₂ z := by
  rw_val_equiv h

end LinearOrderedCommGroupWithZero

end IsEquiv

-- end of namespace
section

theorem isEquiv_of_map_strictMono [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ'₀] [Ring R] {v : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀)
    (H : StrictMono f) : IsEquiv (v.map f H.monotone) v := fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩

theorem isEquiv_iff_val_lt_val [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀} :
    v.IsEquiv v' ↔ ∀ {x y : K}, v x < v y ↔ v' x < v' y := by
  simp only [IsEquiv, le_iff_le_iff_lt_iff_lt]
  exact forall_comm

theorem isEquiv_of_val_le_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀}
    (h : ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1) : v.IsEquiv v' := by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]

theorem isEquiv_iff_val_le_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀} :
    v.IsEquiv v' ↔ ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1 :=
  ⟨IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one⟩

theorem isEquiv_iff_val_eq_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀} :
    v.IsEquiv v' ↔ ∀ {x : K}, v x = 1 ↔ v' x = 1 := by
  constructor
  · intro h x
    rw [h.eq_one_iff_eq_one]
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'

theorem isEquiv_iff_val_lt_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀} :
    v.IsEquiv v' ↔ ∀ {x : K}, v x < 1 ↔ v' x < 1 := by
  constructor
  · intro h x
    rw [h.lt_one_iff_lt_one]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))

theorem isEquiv_iff_val_sub_one_lt_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] {v : Valuation K Γ₀} {v' : Valuation K Γ'₀} :
    v.IsEquiv v' ↔ ∀ {x : K}, v (x - 1) < 1 ↔ v' (x - 1) < 1 := by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

alias ⟨IsEquiv.val_sub_one_lt_one_iff, _⟩ := isEquiv_iff_val_sub_one_lt_one

theorem isEquiv_tfae [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    [ v.IsEquiv v',
      ∀ {x y}, v x < v y ↔ v' x < v' y,
      ∀ {x}, v x ≤ 1 ↔ v' x ≤ 1,
      ∀ {x}, v x = 1 ↔ v' x = 1,
      ∀ {x}, v x < 1 ↔ v' x < 1,
      ∀ {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 ].TFAE := by
  tfae_have 1 ↔ 2 := isEquiv_iff_val_lt_val
  tfae_have 1 ↔ 3 := isEquiv_iff_val_le_one
  tfae_have 1 ↔ 4 := isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 5 := isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 6 := isEquiv_iff_val_sub_one_lt_one
  tfae_finish

end

section Supp

variable [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def supp : Ideal R where
  carrier := { x | v x = 0 }
  zero_mem' := map_zero v
  add_mem' {x y} hx hy := le_zero_iff.mp <|
    calc
      v (x + y) ≤ max (v x) (v y) := v.map_add x y
      _ ≤ 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 :=
  Iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance [Nontrivial Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v) :=
  ⟨fun h =>
    one_ne_zero (α := Γ₀) <|
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a := by
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ ≤ v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)

theorem comap_supp {S : Type*} [CommRing S] (f : S →+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

end Supp

-- end of section
end Valuation

section AddMonoid

variable (R) [Ring R] (Γ₀ : Type*) [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- The type of `Γ₀`-valued additive valuations on `R`. -/
def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)

end AddMonoid

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

section Basic

section Monoid

/-- A valuation is coerced to the underlying function `R → Γ₀`. -/
instance (R) (Γ₀) [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] :
    FunLike (AddValuation R Γ₀) R Γ₀ where
  coe v := v.toMonoidWithZeroHom.toFun
  coe_injective' f g := by cases f; cases g; simp +contextual

variable [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  (v : AddValuation R Γ₀)

section

variable (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
variable (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

/-- An alternate constructor of `AddValuation`, that doesn't reference `Multiplicative Γ₀ᵒᵈ` -/
def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
theorem of_apply : (of f h0 h1 hadd hmul) r = f r := rfl

/-- The `Valuation` associated to an `AddValuation` (useful if the latter is constructed using
`AddValuation.of`). -/
def toValuation : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  Equiv.refl _

/-- The `AddValuation` associated to a `Valuation`.
-/
def ofValuation : Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀ :=
  Equiv.refl _

@[simp]
lemma ofValuation_symm_eq : ofValuation.symm = toValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
lemma toValuation_symm_eq : toValuation.symm = ofValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
lemma ofValuation_toValuation : ofValuation (toValuation v) = v := rfl

@[simp]
lemma toValuation_ofValuation (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) :
    toValuation (ofValuation v) = v := rfl

@[simp]
theorem toValuation_apply (r : R) :
    toValuation v r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

@[simp]
theorem ofValuation_apply (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) (r : R) :
    ofValuation v r = OrderDual.ofDual (Multiplicative.toAdd (v r)) :=
  rfl

end

@[simp]
theorem map_zero : v 0 = (⊤ : Γ₀) :=
  Valuation.map_zero v

@[simp]
theorem map_one : v 1 = (0 : Γ₀) :=
  Valuation.map_one v

/-- A helper function for Lean to inferring types correctly.

Deprecated since it is unused.
-/
@[deprecated "Use `⇑v` instead" (since := "2025-09-04")] def asFun : R → Γ₀ := v

@[simp]
theorem map_mul : ∀ (x y : R), v (x * y) = v x + v y :=
  Valuation.map_mul v

-- `simp`-normal form is `map_add'`
theorem map_add : ∀ (x y : R), min (v x) (v y) ≤ v (x + y) :=
  Valuation.map_add v

@[simp]
theorem map_add' : ∀ (x y : R), v x ≤ v (x + y) ∨ v y ≤ v (x + y) := by
  intro x y
  rw [← @min_le_iff _ _ (v x) (v y) (v (x+y)), ← ge_iff_le]
  apply map_add

theorem map_le_add {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x + y) :=
  Valuation.map_add_le v hx hy

theorem map_lt_add {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y) : g < v (x + y) :=
  Valuation.map_add_lt v hx hy

theorem map_le_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) :=
  v.map_sum_le hf

theorem map_lt_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt hg hf

theorem map_lt_sum' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g < ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt' hg hf

@[simp]
theorem map_pow : ∀ (x : R) (n : ℕ), v (x ^ n) = n • (v x) :=
  Valuation.map_pow v

@[ext]
theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  Valuation.ext h

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp]
theorem top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x = (⊤ : Γ₀) ↔ x = 0 :=
  v.zero_iff

theorem ne_top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x ≠ (⊤ : Γ₀) ↔ x ≠ 0 :=
  v.ne_zero_iff

/-- A ring homomorphism `S → R` induces a map `AddValuation R Γ₀ → AddValuation S Γ₀`. -/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  Valuation.comap f v

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  Valuation.comap_id v

theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  Valuation.comap_comp v f g

/-- A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `AddValuation R Γ₀ → AddValuation R Γ'₀`.
-/
def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) :
    AddValuation R Γ'₀ :=
  @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

@[simp]
lemma map_apply (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) (r : R) :
    v.map f ht hf r = f (v r) := rfl

/-- Two additive valuations on `R` are defined to be equivalent if they induce the same
  preorder on `R`. -/
def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  Valuation.IsEquiv v₁ v₂

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  Valuation.map_neg v x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  Valuation.map_sub_swap v x y

theorem map_sub (x y : R) : min (v x) (v y) ≤ v (x - y) :=
  Valuation.map_sub v x y

theorem map_le_sub {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x - y) :=
  Valuation.map_sub_le v hx hy

variable {x y : R}

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = @Min.min Γ₀ _ (v x) (v y) :=
  Valuation.map_add_of_distinct_val v h

theorem map_add_eq_of_lt_left {x y : R} (h : v x < v y) :
    v (x + y) = v x := by
  rw [map_add_of_distinct_val _ h.ne, min_eq_left h.le]

theorem map_add_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x + y) = v y := add_comm y x ▸ map_add_eq_of_lt_left v hx

theorem map_sub_eq_of_lt_left {x y : R} (hx : v x < v y) :
    v (x - y) = v x := by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]

theorem map_sub_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x - y) = v y := map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx

theorem map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
  Valuation.map_eq_of_sub_lt v h

end Monoid

section Group

variable [LinearOrderedAddCommGroupWithTop Γ₀] [Ring R] (v : AddValuation R Γ₀) {x y : R}

@[simp]
theorem map_inv (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = - (v x) :=
  map_inv₀ (toValuation v) x

@[simp]
theorem map_div (v : AddValuation K Γ₀) {x y : K} : v (x / y) = v x - v y :=
  map_div₀ (toValuation v) x y

end Group

end Basic

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  [Ring R]
  {Γ''₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ''₀]
  {v : AddValuation R Γ₀} {v₁ : AddValuation R Γ₀}
  {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v :=
  Valuation.IsEquiv.refl

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
  Valuation.IsEquiv.symm h

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
  Valuation.IsEquiv.trans h₁₂ h₂₃

theorem of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v' :=
  Valuation.IsEquiv.of_eq h

theorem map {v' : AddValuation R Γ₀} (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f)
    (inf : Injective f) (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f ht hf) :=
  @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

/-- `comap` preserves equivalence. -/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) :=
  Valuation.IsEquiv.comap f h

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  Valuation.IsEquiv.val_eq h

theorem ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ (⊤ : Γ₀) ↔ v₂ r ≠ (⊤ : Γ'₀) :=
  Valuation.IsEquiv.ne_zero h

end IsEquiv

section Supp

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [CommRing R] (v : AddValuation R Γ₀)

/-- The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x = ⊤` -/
def supp : Ideal R :=
  Valuation.supp v

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = (⊤ : Γ₀) :=
  Valuation.mem_supp_iff v x

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
  Valuation.map_add_supp v a h

end Supp

-- end of section
end AddValuation

namespace Valuation

variable {K Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- The `AddValuation` associated to a `Valuation`. -/
def toAddValuation : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ :=
  .trans (congr
    { toFun := fun x ↦ .ofAdd <| .toDual <| .toDual <| .ofMul x
      invFun := fun x ↦ x.toAdd.ofDual.ofDual.toMul
      map_mul' := fun _x _y ↦ rfl
      map_le_map_iff' := .rfl }) (AddValuation.ofValuation (R := R) (Γ₀ := (Additive Γ₀)ᵒᵈ))

/-- The `Valuation` associated to a `AddValuation`.
-/
def ofAddValuation : AddValuation R (Additive Γ₀)ᵒᵈ ≃ Valuation R Γ₀ :=
  AddValuation.toValuation.trans <| congr <|
    { toFun := fun x ↦ x.toAdd.ofDual.ofDual.toMul
      invFun := fun x ↦ .ofAdd <| .toDual <| .toDual <| .ofMul x
      map_mul' := fun _x _y ↦ rfl
      map_le_map_iff' := .rfl }

@[simp]
lemma ofAddValuation_symm_eq : ofAddValuation.symm = toAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
lemma toAddValuation_symm_eq : toAddValuation.symm = ofAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
lemma ofAddValuation_toAddValuation (v : Valuation R Γ₀) : ofAddValuation (toAddValuation v) = v :=
  rfl

@[simp]
lemma toValuation_ofValuation (v : AddValuation R (Additive Γ₀)ᵒᵈ) :
    toAddValuation (ofAddValuation v) = v := rfl

@[simp]
theorem toAddValuation_apply (v : Valuation R Γ₀) (r : R) :
    toAddValuation v r = OrderDual.toDual (Additive.ofMul (v r)) :=
  rfl

@[simp]
theorem ofAddValuation_apply (v : AddValuation R (Additive Γ₀)ᵒᵈ) (r : R) :
    ofAddValuation v r = Additive.toMul (OrderDual.ofDual (v r)) :=
  rfl

instance (v : Valuation R Γ₀) : CommMonoidWithZero (MonoidHom.mrange v) where
  zero := ⟨0, 0, by simp⟩
  zero_mul := by
    intro a
    exact Subtype.ext (zero_mul a.val)
  mul_zero := by
    intro a
    exact Subtype.ext (mul_zero a.val)

@[simp]
lemma val_mrange_zero (v : Valuation R Γ₀) : ((0 : MonoidHom.mrange v) : Γ₀) = 0 := rfl

instance {Γ₀} [LinearOrderedCommGroupWithZero Γ₀] [DivisionRing K] (v : Valuation K Γ₀) :
    CommGroupWithZero (MonoidHom.mrange v) where
  inv := fun x ↦ ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    simp_rw [← hy, ← v.map_inv]
    exact MonoidHom.mem_mrange.mpr ⟨_, rfl⟩⟩
  exists_pair_ne := ⟨⟨v 0, by simp⟩, ⟨v 1, by simp [- map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cancel₀ h

end Valuation
