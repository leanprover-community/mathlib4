/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.OfMap

/-!
# Subsets of finite types

In a `Fintype`, all `Set`s are automatically `Finset`s, and there are only finitely many of them.

## Main results

* `Set.toFinset`: convert a subset of a finite type to a `Finset`
* `Finset.fintypeCoeSort`: `((s : Finset α) : Type*)` is a finite type
* `Fintype.finsetEquivSet`: `Finset α` and `Set α` are equivalent if `α` is a `Fintype`
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/-- Construct a finset enumerating a set `s`, given a `Fintype` instance. -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _

@[congr]
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by subst h; congr!

@[simp, grind =]
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by
  simp [toFinset]

set_option backward.isDefEq.respectTransparency false in
/-- Many `Fintype` instances for sets are defined using an extensionally equal `Finset`.
Rewriting `s.toFinset` with `Set.toFinset_ofFinset` replaces the term with such a `Finset`. -/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

/-- Membership of a set with a `Fintype` instance is decidable.

Using this as an instance leads to potential loops with `Subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidable_of_iff _ mem_toFinset

@[simp]
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset

@[simp]
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, coe_toFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_nonempty⟩ := toFinset_nonempty

@[simp]
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩

@[mono]
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[simp]
theorem subset_toFinset {s : Finset α} [Fintype t] : s ⊆ t.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

@[simp]
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[mono]
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

@[gcongr]
alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

@[deprecated (since := "2025-10-25")] alias toFinset_subset_toFinset_of_subset := toFinset_mono

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]
theorem disjoint_toFinset [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by simp only [← disjoint_coe, coe_toFinset]

@[simp]
theorem toFinset_nontrivial [Fintype s] : s.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial, coe_toFinset]

theorem subsingleton_toFinset_iff [Fintype s] : Subsingleton s.toFinset ↔ s.Subsingleton := by
  simp

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

@[simp]
theorem toFinset_inter [Fintype (s ∩ t : Set _)] : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_union [Fintype (s ∪ t : Set _)] : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_diff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp

open scoped symmDiff in
@[simp]
theorem toFinset_symmDiff [Fintype (s ∆ t : Set _)] :
    (s ∆ t).toFinset = s.toFinset ∆ t.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]
theorem toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp

end DecidableEq

-- TODO The `↥` circumvents an elaboration bug. See comment on `Set.toFinset_univ`.
@[simp]
theorem toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅ := by
  ext
  simp

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug in the following two;
it essentially infers `Fintype.{v} (Set.univ.{u} : Set α)` with `v` and `u` distinct.
Reported in https://github.com/leanprover-community/lean/issues/672 -/
@[simp]
theorem toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ := by
  ext
  simp

@[simp]
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty, toFinset_inj]

@[simp]
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj, coe_toFinset, coe_univ]

@[simp]
theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype { x | p x }] :
    Set.toFinset {x | p x} = Finset.univ.filter p := by
  ext
  simp

theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by simp

@[simp]
theorem toFinset_image [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
  Finset.coe_injective <| by simp

@[simp]
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
theorem toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp

@[simp]
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp

theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  rw [mem_filter_univ, mem_toFinset]

end Set

@[simp]
theorem Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset

section Finset

/-! ### `Fintype (s : Finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  Finset.fintypeCoeSort s

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s

end Finset

theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
    ↑(Finset.image f Finset.univ) = Set.range f := by
  simp

instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach

instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach

/- instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩
-/

/-
instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s
-/

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp; rfl

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)

-- adding `@[implicit_reducible]` causes downstream breakage
set_option warn.classDefReducibility false in
/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s

namespace Fintype
variable [Fintype α]

/-- Given `Fintype α`, `finsetEquivSet` is the equiv between `Finset α` and `Set α`. (All
sets on a finite type are finite.) -/
noncomputable def finsetEquivSet : Finset α ≃ Set α where
  toFun := (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset

@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma finsetEquivSet_apply (s : Finset α) : finsetEquivSet s = s := rfl

@[simp] lemma finsetEquivSet_symm_apply (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by simp [finsetEquivSet]

/-- Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finset α` and `Set α`
(all sets on a finite type are finite). -/
@[simps toEquiv]
noncomputable def finsetOrderIsoSet : Finset α ≃o Set α where
  toEquiv := finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]
lemma coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma coe_finsetOrderIsoSet_symm :
    ⇑(finsetOrderIsoSet : Finset α ≃o Set α).symm = ⇑finsetEquivSet.symm := rfl

end Fintype

theorem mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} : b ∈ univ.image f ↔ b ∈ Set.range f := by simp

open Batteries.ExtendedBinder Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck finsetStx] meta def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax
