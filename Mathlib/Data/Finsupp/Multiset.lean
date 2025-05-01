/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Sym.Basic

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `Finsupp.toMultiset` the equivalence between `α →₀ ℕ` and `Multiset α`, along
with `Multiset.toFinsupp` the reverse equivalence and `Finsupp.orderIsoMultiset` (the equivalence
promoted to an order isomorphism).

-/

open Finset

variable {α β ι : Type*}

namespace Finsupp

/-- Given `f : α →₀ ℕ`, `f.toMultiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `AddMonoidHom`.

Under the additional assumption of `[DecidableEq α]`, this is available as
`Multiset.toFinsupp : Multiset α ≃+ (α →₀ ℕ)`; the two declarations are separate as this assumption
is only needed for one direction. -/
def toMultiset : (α →₀ ℕ) →+ Multiset α where
  toFun f := Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ ↦ zero_nsmul _) (fun _ ↦ add_nsmul _)
  map_zero' := sum_zero_index

theorem toMultiset_zero : toMultiset (0 : α →₀ ℕ) = 0 :=
  rfl

theorem toMultiset_add (m n : α →₀ ℕ) : toMultiset (m + n) = toMultiset m + toMultiset n :=
  toMultiset.map_add m n

theorem toMultiset_apply (f : α →₀ ℕ) : toMultiset f = f.sum fun a n => n • {a} :=
  rfl

@[simp]
theorem toMultiset_single (a : α) (n : ℕ) : toMultiset (single a n) = n • {a} := by
  rw [toMultiset_apply, sum_single_index]; apply zero_nsmul

theorem toMultiset_sum {f : ι → α →₀ ℕ} (s : Finset ι) :
    Finsupp.toMultiset (∑ i ∈ s, f i) = ∑ i ∈ s, Finsupp.toMultiset (f i) :=
  map_sum Finsupp.toMultiset _ _

theorem toMultiset_sum_single (s : Finset ι) (n : ℕ) :
    Finsupp.toMultiset (∑ i ∈ s, single i n) = n • s.val := by
  simp_rw [toMultiset_sum, Finsupp.toMultiset_single, Finset.sum_nsmul, sum_multiset_singleton]

@[simp]
theorem card_toMultiset (f : α →₀ ℕ) : Multiset.card (toMultiset f) = f.sum fun _ => id := by
  simp [toMultiset_apply, map_finsuppSum, Function.id_def]

theorem toMultiset_map (f : α →₀ ℕ) (g : α → β) :
    f.toMultiset.map g = toMultiset (f.mapDomain g) := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.map_zero, mapDomain_zero, toMultiset_zero]
  · intro a n f _ _ ih
    rw [toMultiset_add, Multiset.map_add, ih, mapDomain_add, mapDomain_single,
      toMultiset_single, toMultiset_add, toMultiset_single, ← Multiset.coe_mapAddMonoidHom,
      (Multiset.mapAddMonoidHom g).map_nsmul]
    rfl

@[to_additive (attr := simp)]
theorem prod_toMultiset [CommMonoid α] (f : α →₀ ℕ) :
    f.toMultiset.prod = f.prod fun a n => a ^ n := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [toMultiset_add, Multiset.prod_add, ih, toMultiset_single, Multiset.prod_nsmul,
      Finsupp.prod_add_index' pow_zero pow_add, Finsupp.prod_single_index, Multiset.prod_singleton]
    exact pow_zero a

@[simp]
theorem toFinset_toMultiset [DecidableEq α] (f : α →₀ ℕ) : f.toMultiset.toFinset = f.support := by
  refine f.induction ?_ ?_
  · rw [toMultiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [toMultiset_add, Multiset.toFinset_add, ih, toMultiset_single, support_add_eq,
      support_single_ne_zero _ hn, Multiset.toFinset_nsmul _ _ hn, Multiset.toFinset_singleton]
    refine Disjoint.mono_left support_single_subset ?_
    rwa [Finset.disjoint_singleton_left]

@[simp]
theorem count_toMultiset [DecidableEq α] (f : α →₀ ℕ) (a : α) : (toMultiset f).count a = f a :=
  calc
    (toMultiset f).count a = Finsupp.sum f (fun x n => (n • {x} : Multiset α).count a) := by
      rw [toMultiset_apply]; exact map_sum (Multiset.countAddMonoidHom a) _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : Multiset α).count a :=
      sum_eq_single _
        (fun a' _ H => by simp only [Multiset.count_singleton, if_false, H.symm, mul_zero])
        (fun _ => zero_mul _)
    _ = f a := by rw [Multiset.count_singleton_self, mul_one]

theorem toMultiset_sup [DecidableEq α] (f g : α →₀ ℕ) :
    toMultiset (f ⊔ g) = toMultiset f ∪ toMultiset g := by
  ext
  simp_rw [Multiset.count_union, Finsupp.count_toMultiset, Finsupp.sup_apply]

theorem toMultiset_inf [DecidableEq α] (f g : α →₀ ℕ) :
    toMultiset (f ⊓ g) = toMultiset f ∩ toMultiset g := by
  ext
  simp_rw [Multiset.count_inter, Finsupp.count_toMultiset, Finsupp.inf_apply]

@[simp]
theorem mem_toMultiset (f : α →₀ ℕ) (i : α) : i ∈ toMultiset f ↔ i ∈ f.support := by
  classical
  rw [← Multiset.count_ne_zero, Finsupp.count_toMultiset, Finsupp.mem_support_iff]

end Finsupp

namespace Multiset

variable [DecidableEq α]

/-- Given a multiset `s`, `s.toFinsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
@[simps symm_apply]
def toFinsupp : Multiset α ≃+ (α →₀ ℕ) where
  toFun s := ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  invFun f := Finsupp.toMultiset f
  map_add' _ _ := Finsupp.ext fun _ => count_add _ _ _
  right_inv f :=
    Finsupp.ext fun a => by
      simp only [Finsupp.toMultiset_apply, Finsupp.sum, Multiset.count_sum',
        Multiset.count_singleton, mul_boole, Finsupp.coe_mk, Finsupp.mem_support_iff,
        Multiset.count_nsmul, Finset.sum_ite_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
  left_inv s := by simp only [Finsupp.toMultiset_apply, Finsupp.sum, Finsupp.coe_mk,
    Multiset.toFinset_sum_count_nsmul_eq]

@[simp]
theorem toFinsupp_support (s : Multiset α) : s.toFinsupp.support = s.toFinset := rfl

@[simp]
theorem toFinsupp_apply (s : Multiset α) (a : α) : toFinsupp s a = s.count a := rfl

theorem toFinsupp_zero : toFinsupp (0 : Multiset α) = 0 := _root_.map_zero _

theorem toFinsupp_add (s t : Multiset α) : toFinsupp (s + t) = toFinsupp s + toFinsupp t :=
  _root_.map_add toFinsupp s t

@[simp]
theorem toFinsupp_singleton (a : α) : toFinsupp ({a} : Multiset α) = Finsupp.single a 1 := by
  ext; rw [toFinsupp_apply, count_singleton, Finsupp.single_eq_pi_single, Pi.single_apply]

@[simp]
theorem toFinsupp_toMultiset (s : Multiset α) : Finsupp.toMultiset (toFinsupp s) = s :=
  Multiset.toFinsupp.symm_apply_apply s

theorem toFinsupp_eq_iff {s : Multiset α} {f : α →₀ ℕ} :
    toFinsupp s = f ↔ s = Finsupp.toMultiset f :=
  Multiset.toFinsupp.apply_eq_iff_symm_apply

theorem toFinsupp_union (s t : Multiset α) : toFinsupp (s ∪ t) = toFinsupp s ⊔ toFinsupp t := by
  ext
  simp

theorem toFinsupp_inter (s t : Multiset α) : toFinsupp (s ∩ t) = toFinsupp s ⊓ toFinsupp t := by
  ext
  simp

@[simp]
theorem toFinsupp_sum_eq (s : Multiset α) : s.toFinsupp.sum (fun _ ↦ id) = Multiset.card s := by
  rw [← Finsupp.card_toMultiset, toFinsupp_toMultiset]

end Multiset

@[simp]
theorem Finsupp.toMultiset_toFinsupp [DecidableEq α] (f : α →₀ ℕ) :
    Multiset.toFinsupp (Finsupp.toMultiset f) = f :=
  Multiset.toFinsupp.apply_symm_apply _

theorem Finsupp.toMultiset_eq_iff [DecidableEq α] {f : α →₀ ℕ} {s : Multiset α} :
    Finsupp.toMultiset f = s ↔ f = Multiset.toFinsupp s :=
  Multiset.toFinsupp.symm_apply_eq

/-! ### As an order isomorphism -/

namespace Finsupp
/-- `Finsupp.toMultiset` as an order isomorphism. -/
def orderIsoMultiset [DecidableEq ι] : (ι →₀ ℕ) ≃o Multiset ι where
  toEquiv := Multiset.toFinsupp.symm.toEquiv
  map_rel_iff' {f g} := by simp [le_def, Multiset.le_iff_count]

@[simp]
theorem coe_orderIsoMultiset [DecidableEq ι] : ⇑(@orderIsoMultiset ι _) = toMultiset :=
  rfl

@[simp]
theorem coe_orderIsoMultiset_symm [DecidableEq ι] :
    ⇑(@orderIsoMultiset ι).symm = Multiset.toFinsupp :=
  rfl

theorem toMultiset_strictMono : StrictMono (@toMultiset ι) := by
  classical exact (@orderIsoMultiset ι _).strictMono

theorem sum_id_lt_of_lt (m n : ι →₀ ℕ) (h : m < n) : (m.sum fun _ => id) < n.sum fun _ => id := by
  rw [← card_toMultiset, ← card_toMultiset]
  apply Multiset.card_lt_card
  exact toMultiset_strictMono h

variable (ι)

/-- The order on `ι →₀ ℕ` is well-founded. -/
theorem lt_wf : WellFounded (@LT.lt (ι →₀ ℕ) _) :=
  Subrelation.wf (sum_id_lt_of_lt _ _) <| InvImage.wf _ Nat.lt_wfRel.2

-- TODO: generalize to `[WellFoundedRelation α] → WellFoundedRelation (ι →₀ α)`
instance : WellFoundedRelation (ι →₀ ℕ) where
  rel := (· < ·)
  wf := lt_wf _

end Finsupp

theorem Multiset.toFinsupp_strictMono [DecidableEq ι] : StrictMono (@Multiset.toFinsupp ι _) :=
  (@Finsupp.orderIsoMultiset ι).symm.strictMono

namespace Sym

variable (α)
variable [DecidableEq α] (n : ℕ)

/-- The `n`th symmetric power of a type `α` is naturally equivalent to the subtype of
finitely-supported maps `α →₀ ℕ` with total mass `n`.

See also `Sym.equivNatSumOfFintype` when `α` is finite. -/
def equivNatSum :
    Sym α n ≃ {P : α →₀ ℕ // P.sum (fun _ ↦ id) = n} :=
  Multiset.toFinsupp.toEquiv.subtypeEquiv <| by simp

@[simp] lemma coe_equivNatSum_apply_apply (s : Sym α n) (a : α) :
    (equivNatSum α n s : α →₀ ℕ) a = (s : Multiset α).count a :=
  rfl

@[simp] lemma coe_equivNatSum_symm_apply (P : {P : α →₀ ℕ // P.sum (fun _ ↦ id) = n}) :
    ((equivNatSum α n).symm P : Multiset α) = Finsupp.toMultiset P :=
  rfl

/-- The `n`th symmetric power of a finite type `α` is naturally equivalent to the subtype of maps
`α → ℕ` with total mass `n`.

See also `Sym.equivNatSum` when `α` is not necessarily finite. -/
noncomputable def equivNatSumOfFintype [Fintype α] :
    Sym α n ≃ {P : α → ℕ // ∑ i, P i = n} :=
  (equivNatSum α n).trans <| Finsupp.equivFunOnFinite.subtypeEquiv <| by simp [Finsupp.sum_fintype]

@[simp] lemma coe_equivNatSumOfFintype_apply_apply [Fintype α] (s : Sym α n) (a : α) :
    (equivNatSumOfFintype α n s : α → ℕ) a = (s : Multiset α).count a :=
  rfl

@[simp] lemma coe_equivNatSumOfFintype_symm_apply [Fintype α] (P : {P : α → ℕ // ∑ i, P i = n}) :
    ((equivNatSumOfFintype α n).symm P : Multiset α) = ∑ a, ((P : α → ℕ) a) • {a} := by
  obtain ⟨P, hP⟩ := P
  change Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm P) = Multiset.sum _
  ext a
  rw [Multiset.count_sum]
  simp [Multiset.count_singleton]

end Sym
