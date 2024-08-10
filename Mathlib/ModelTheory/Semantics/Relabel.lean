/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Semantics.Basic
import Mathlib.ModelTheory.Syntax.Relabel

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

## Main Results

## Implementation Notes

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Term

@[simp]
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction' t with _ n f ts ih
  · rfl
  · simp [ih]

@[simp]
theorem realize_liftAt {n n' m : ℕ} {t : L.Term (α ⊕ (Fin n))} {v : α ⊕ (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel


@[simp]
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]

@[simp]
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [varFinset, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))

@[simp]
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) := by
  induction' t with a _ _ _ ih
  · cases a <;> rfl
  · simp_rw [varFinsetLeft, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))

@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction' t with _ n f ts ih
  · simp
  · cases n
    · cases f
      · simp only [realize, ih, Nat.zero_eq, constantsOn, mk₂_Functions]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · cases' f with _ f
      · simp only [realize, ih, constantsOn, mk₂_Functions]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
      · exact isEmptyElim f

@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α ⊕ β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction' t with ab n f ts ih
  · cases' ab with a b
    -- Porting note: both cases were `simp [Language.con]`
    · simp [Language.con, realize, funMap_eq_coe_constants]
    · simp [realize, constantMap]
  · simp only [realize, constantsOn, mk₂_Functions, ih]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sum_inl]

theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β ⊕ (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  rcongr x
  rcases x with (a | (b | i)) <;> simp

end Term

variable {n}

namespace BoundedFormula

open Term

theorem realize_castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ cast h) := by
  subst h
  simp only [castLE_rfl, cast_refl, OrderIso.coe_refl, Function.comp_id]

theorem realize_mapTermRel_id [L'.Structure M]
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α → M}
    {v' : β → M} {xs : Fin n → M}
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs : Fin n → M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
  · simp [mapTermRel, Realize, h1]
  · simp [mapTermRel, Realize, h1, h2]
  · simp [mapTermRel, Realize, ih1, ih2]
  · simp only [mapTermRel, Realize, ih, id]

theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : ℕ}
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun n => castLE (add_assoc _ _ _).symm.le).Realize v' xs ↔
      φ.Realize (v xs) (xs ∘ Fin.natAdd _) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
  · simp [mapTermRel, Realize, h1]
  · simp [mapTermRel, Realize, h1, h2]
  · simp [mapTermRel, Realize, ih1, ih2]
  · simp [mapTermRel, Realize, ih, hv]

@[simp]
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → β ⊕ (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  rw [relabel, realize_mapTermRel_add_castLe] <;> intros <;> simp

theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3
  · simp [mapTermRel, Realize]
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
  · simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  · have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      by_cases h : k < m
      · rw [if_pos h]
        refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
        simp only [coe_cast, coe_castAdd, val_last, self_eq_add_right]
        refine le_antisymm
          (le_of_add_le_add_left ((hmn.trans (Nat.succ_le_of_lt h)).trans ?_)) n'.zero_le
        rw [add_zero]
      · rw [if_neg h]
        refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
        simp
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [coe_castSucc, coe_cast]
      split_ifs <;> simp

theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt (add_le_add_right hmn 1), castSucc]

@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

@[simp]
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.Term β} {v : β → M} {xs : Fin n → M} :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)

@[simp]
theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [restrictFreeVar, Realize]
  · simp [restrictFreeVar, Realize]
  · simp [restrictFreeVar, Realize, ih1, ih2]
  · simp [restrictFreeVar, Realize, ih3]

theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  cases' R with R R
  · simp
  · exact isEmptyElim R

@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

variable [Nonempty M]

theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  inhabit M
  simp only [realize_all, realize_liftAt_one_self]
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · refine (congr rfl (funext fun i => ?_)).mp (h default)
    simp
  · refine (congr rfl (funext fun i => ?_)).mp h
    simp



end BoundedFormula

end Language

end FirstOrder
