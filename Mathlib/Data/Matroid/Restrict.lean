/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Dual

/-!
# Matroid Restriction

Given `M : Matroid α` and `R : Set α`, the independent sets of `M` that are contained in `R`
are the independent sets of another matroid `M ↾ R` with ground set `R`,
called the 'restriction' of `M` to `R`.
For `I, R ⊆ M.E`, `I` is a basis of `R` in `M` if and only if `I` is a base
of the restriction `M ↾ R`, so this construction relates `Matroid.Basis` to `Matroid.Base`.

If `N M : Matroid α` satisfy `N = M ↾ R` for some `R ⊆ M.E`,
then we call `N` a 'restriction of `M`', and write `N ≤r M`. This is a partial order.

This file proves that the restriction is a matroid and that the `≤r` order is a partial order,
and gives related API.
It also proves some `Basis` analogues of `Base` lemmas that, while they could be stated in
`Data.Matroid.Basic`, are hard to prove without `Matroid.restrict` API.

## Main Definitions

* `M.restrict R`, written `M ↾ R`, is the restriction of `M : Matroid α` to `R : Set α`: i.e.
  the matroid with ground set `R` whose independent sets are the `M`-independent subsets of `R`.

* `Matroid.Restriction N M`, written `N ≤r M`, means that `N = M ↾ R` for some `R ⊆ M.E`.

* `Matroid.StrictRestriction N M`, written `N <r M`, means that `N = M ↾ R` for some `R ⊂ M.E`.

* `Matroidᵣ α` is a type synonym for `Matroid α`, equipped with the `PartialOrder` `≤r`.

## Implementation Notes

Since `R` and `M.E` are both terms in `Set α`, to define the restriction `M ↾ R`,
we need to either insist that `R ⊆ M.E`, or to say what happens when `R` contains the junk
outside `M.E`.

It turns out that `R ⊆ M.E` is just an unnecessary hypothesis; if we say the restriction
`M ↾ R` has ground set `R` and its independent sets are the `M`-independent subsets of `R`,
we always get a matroid, in which the elements of `R \ M.E` aren't in any independent sets.
We could instead define this matroid to always be 'smaller' than `M` by setting
`(M ↾ R).E := R ∩ M.E`, but this is worse definitionally, and more generally less convenient.

This makes it possible to actually restrict a matroid 'upwards'; for instance, if `M : Matroid α`
satisfies `M.E = ∅`, then `M ↾ Set.univ` is the matroid on `α` whose ground set is all of `α`,
where the empty set is only the independent set.
(Elements of `R` outside the ground set are all 'loops' of the matroid.)
This is mathematically strange, but is useful for API building.

The cost of allowing a restriction of `M` to be 'bigger' than the `M` itself is that
the statement `M ↾ R ≤r M` is only true with the hypothesis `R ⊆ M.E`
(at least, if we want `≤r` to be a partial order).
But this isn't too inconvenient in practice. Indeed `(· ⊆ M.E)` proofs
can often be automatically provided by `aesop_mat`.

We define the restriction order `≤r` to give a `PartialOrder` instance on the type synonym
`Matroidᵣ α` rather than `Matroid α` itself, because the `PartialOrder (Matroid α)` instance is
reserved for the more mathematically important 'minor' order.
-/

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {R I J X Y : Set α}

section restrict

/-- The `IndepMatroid` whose independent sets are the independent subsets of `R`. -/
@[simps] def restrictIndepMatroid (M : Matroid α) (R : Set α) : IndepMatroid α where
  E := R
  Indep I := M.Indep I ∧ I ⊆ R
  indep_empty := ⟨M.empty_indep, empty_subset _⟩
  indep_subset := fun I J h hIJ ↦ ⟨h.1.subset hIJ, hIJ.trans h.2⟩
  indep_aug := by
    rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.Basis' I R) (hI' : M.Basis' I' R)
    rw [basis'_iff_basis_inter_ground] at hIn hI'
    obtain ⟨B', hB', rfl⟩ := hI'.exists_base
    obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB'
    rw [hB'.inter_basis_iff_compl_inter_basis_dual, diff_inter_diff] at hI'

    have hss : M.E \ (B' ∪ (R ∩ M.E)) ⊆ M.E \ (B ∪ (R ∩ M.E)) := by
      apply diff_subset_diff_right
      rw [union_subset_iff, and_iff_left (subset_union_right _ _), union_comm]
      exact hBIB'.trans (union_subset_union_left _ (subset_inter hIY hI.subset_ground))

    have hi : M✶.Indep (M.E \ (B ∪ (R ∩ M.E))) := by
      rw [dual_indep_iff_exists]
      exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩

    have h_eq := hI'.eq_of_subset_indep hi hss
      (diff_subset_diff_right (subset_union_right _ _))
    rw [h_eq, ← diff_inter_diff, ← hB.inter_basis_iff_compl_inter_basis_dual] at hI'

    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset
      (subset_inter hIB (subset_inter hIY hI.subset_ground))
    obtain rfl := hI'.indep.eq_of_basis hJ

    have hIJ' : I ⊂ B ∩ (R ∩ M.E) := hIJ.ssubset_of_ne (fun he ↦ hIn (by rwa [he]))
    obtain ⟨e, he⟩ := exists_of_ssubset hIJ'
    exact ⟨e, ⟨⟨(hBIB' he.1.1).elim (fun h ↦ (he.2 h).elim) id,he.1.2⟩, he.2⟩,
      hI'.indep.subset (insert_subset he.1 hIJ), insert_subset he.1.2.1 hIY⟩
  indep_maximal := by
    rintro A hAX I ⟨hI, _⟩ hIA
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis'_of_subset hIA; use J
    rw [mem_maximals_setOf_iff, and_iff_left hJ.subset, and_iff_left hIJ,
      and_iff_right ⟨hJ.indep, hJ.subset.trans hAX⟩]
    exact fun K ⟨⟨hK, _⟩, _, hKA⟩ hJK ↦ hJ.eq_of_subset_indep hK hJK hKA
  subset_ground I := And.right

/-- Change the ground set of a matroid to some `R : Set α`. The independent sets of the restriction
  are the independent subsets of the new ground set. Most commonly used when `R ⊆ M.E`,
  but it is convenient not to require this. The elements of `R \ M.E` become 'loops'.  -/
def restrict (M : Matroid α) (R : Set α) : Matroid α := (M.restrictIndepMatroid R).matroid

/-- `M ↾ R` means `M.restrict R`. -/
scoped infixl:65  " ↾ " => Matroid.restrict

@[simp] theorem restrict_indep_iff : (M ↾ R).Indep I ↔ M.Indep I ∧ I ⊆ R := Iff.rfl

theorem Indep.indep_restrict_of_subset (h : M.Indep I) (hIR : I ⊆ R) : (M ↾ R).Indep I :=
  restrict_indep_iff.mpr ⟨h,hIR⟩

theorem Indep.of_restrict (hI : (M ↾ R).Indep I) : M.Indep I :=
  (restrict_indep_iff.1 hI).1

@[simp] theorem restrict_ground_eq : (M ↾ R).E = R := rfl

theorem restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite :=
  ⟨hR⟩

@[simp] theorem restrict_dep_iff : (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X ⊆ R := by
  rw [Dep, restrict_indep_iff, restrict_ground_eq]; tauto

@[simp] theorem restrict_ground_eq_self (M : Matroid α) : (M ↾ M.E) = M := by
  refine' eq_of_indep_iff_indep_forall rfl _; aesop

theorem restrict_restrict_eq {R₁ R₂ : Set α} (M : Matroid α) (hR : R₂ ⊆ R₁) :
    (M ↾ R₁) ↾ R₂ = M ↾ R₂ := by
  refine' eq_of_indep_iff_indep_forall rfl _
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ ↦ h.trans hR

@[simp] theorem restrict_idem (M : Matroid α) (R : Set α) : M ↾ R ↾ R = M ↾ R := by
  rw [M.restrict_restrict_eq Subset.rfl]

@[simp] theorem base_restrict_iff (hX : X ⊆ M.E := by aesop_mat) :
    (M ↾ X).Base I ↔ M.Basis I X := by
  simp_rw [base_iff_maximal_indep, basis_iff', restrict_indep_iff, and_iff_left hX, and_assoc]
  aesop

theorem base_restrict_iff' : (M ↾ X).Base I ↔ M.Basis' I X := by
  simp_rw [Basis', base_iff_maximal_indep, mem_maximals_setOf_iff, restrict_indep_iff]

theorem Basis.restrict_base (h : M.Basis I X) : (M ↾ X).Base I := by
  rw [basis_iff'] at h
  simp_rw [base_iff_maximal_indep, restrict_indep_iff, and_imp, and_assoc, and_iff_right h.1.1,
    and_iff_right h.1.2.1]
  exact fun J hJ hJX hIJ ↦ h.1.2.2 _ hJ hIJ hJX

instance restrict_finiteRk [M.FiniteRk] (R : Set α) : (M ↾ R).FiniteRk :=
  let ⟨_, hB⟩ := (M ↾ R).exists_base
  hB.finiteRk_of_finite (hB.indep.of_restrict.finite)

instance restrict_finitary [Finitary M] (R : Set α) : Finitary (M ↾ R) := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin ↦ (hI J hJ hJfin).1,
    fun e heI ↦ singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩

@[simp] theorem Basis.base_restrict (h : M.Basis I X) : (M ↾ X).Base I :=
  (base_restrict_iff h.subset_ground).mpr h

theorem Basis.basis_restrict_of_subset (hI : M.Basis I X) (hXY : X ⊆ Y) : (M ↾ Y).Basis I X := by
  rwa [← base_restrict_iff, M.restrict_restrict_eq hXY, base_restrict_iff]

theorem basis'_restrict_iff : (M ↾ R).Basis' I X ↔ M.Basis' I (X ∩ R) ∧ I ⊆ R := by
  simp_rw [Basis', mem_maximals_setOf_iff, restrict_indep_iff, subset_inter_iff, and_imp]; tauto

theorem basis_restrict_iff' : (M ↾ R).Basis I X ↔ M.Basis I (X ∩ M.E) ∧ X ⊆ R := by
  rw [basis_iff_basis'_subset_ground, basis'_restrict_iff, restrict_ground_eq, and_congr_left_iff,
    ← basis'_iff_basis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR, and_iff_left_iff_imp]
  exact fun h ↦ h.subset.trans hXR

theorem basis_restrict_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Basis I X ↔ M.Basis I X ∧ X ⊆ R := by
  rw [basis_restrict_iff', and_congr_left_iff]
  intro hXR
  rw [← basis'_iff_basis_inter_ground, basis'_iff_basis]

theorem restrict_eq_restrict_iff (M M' : Matroid α) (X : Set α) :
    M ↾ X = M' ↾ X ↔ ∀ I, I ⊆ X → (M.Indep I ↔ M'.Indep I) := by
  refine' ⟨fun h I hIX ↦ _, fun h ↦ eq_of_indep_iff_indep_forall rfl fun I (hI : I ⊆ X) ↦ _⟩
  · rw [← and_iff_left (a := (M.Indep I)) hIX, ← and_iff_left (a := (M'.Indep I)) hIX,
      ← restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff, and_iff_left hI, restrict_indep_iff, and_iff_left hI, h _ hI]

@[simp] theorem restrict_eq_self_iff : M ↾ R = M ↔ R = M.E :=
  ⟨fun h ↦ by rw [← h]; rfl, fun h ↦ by simp [h]⟩

end restrict

section Restriction

variable {N : Matroid α}

/-- `Restriction N M` means that `N = M ↾ R` for some subset `R` of `M.E` -/
def Restriction (N M : Matroid α) : Prop := ∃ R ⊆ M.E, N = M ↾ R

/-- `StrictRestriction N M` means that `N = M ↾ R` for some strict subset `R` of `M.E` -/
def StrictRestriction (N M : Matroid α) : Prop := Restriction N M ∧ ¬ Restriction M N

/-- `N ≤r M` means that `N` is a `Restriction` of `M`. -/
scoped infix:50  " ≤r " => Restriction

/-- `N <r M` means that `N` is a `StrictRestriction` of `M`. -/
scoped infix:50  " <r " => StrictRestriction

/-- A type synonym for matroids with the restriction order.
  (The `PartialOrder` on `Matroid α` is reserved for the minor order)  -/
@[ext] structure Matroidᵣ (α : Type*) where ofMatroid ::
  /-- The underlying `Matroid`.-/
  toMatroid : Matroid α

instance {α : Type*} : CoeOut (Matroidᵣ α) (Matroid α) where
  coe := Matroidᵣ.toMatroid

@[simp] theorem Matroidᵣ.coe_inj {M₁ M₂ : Matroidᵣ α} :
    (M₁ : Matroid α) = (M₂ : Matroid α) ↔ M₁ = M₂ := by
  cases M₁; cases M₂; simp

instance {α : Type*} : PartialOrder (Matroidᵣ α) where
  le := (· ≤r ·)
  le_refl M := ⟨(M : Matroid α).E, Subset.rfl, (M : Matroid α).restrict_ground_eq_self.symm⟩
  le_trans M₁ M₂ M₃ := by
    rintro ⟨R, hR, h₁⟩ ⟨R', hR', h₂⟩
    change _ ≤r _
    rw [h₂] at h₁ hR
    rw [h₁, restrict_restrict_eq _ (show R ⊆ R' from hR)]
    exact ⟨R, hR.trans hR', rfl⟩
  le_antisymm M₁ M₂ := by
    rintro ⟨R, hR, h⟩ ⟨R', hR', h'⟩
    rw [h', restrict_ground_eq] at hR
    rw [h, restrict_ground_eq] at hR'
    rw [← Matroidᵣ.coe_inj, h, h', hR.antisymm hR', restrict_idem]

@[simp] protected theorem Matroidᵣ.le_iff {M M' : Matroidᵣ α} :
    M ≤ M' ↔ (M : Matroid α) ≤r (M' : Matroid α) := Iff.rfl

@[simp] protected theorem Matroidᵣ.lt_iff {M M' : Matroidᵣ α} :
    M < M' ↔ (M : Matroid α) <r (M' : Matroid α) := Iff.rfl

theorem ofMatroid_le_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M ≤ Matroidᵣ.ofMatroid M' ↔ M ≤r M' := by
  simp

theorem ofMatroid_lt_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M < Matroidᵣ.ofMatroid M' ↔ M <r M' := by
  simp

theorem Restriction.refl : M ≤r M :=
  le_refl (Matroidᵣ.ofMatroid M)

theorem Restriction.antisymm {M' : Matroid α} (h : M ≤r M') (h' : M' ≤r M) : M = M' := by
  simpa using (ofMatroid_le_iff.2 h).antisymm (ofMatroid_le_iff.2 h')

theorem Restriction.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤r M₂) (h' : M₂ ≤r M₃) : M₁ ≤r M₃ :=
  le_trans (α := Matroidᵣ α) h h'

theorem restrict_restriction (M : Matroid α) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    M ↾ R ≤r M :=
  ⟨R, hR, rfl⟩

theorem Restriction.eq_restrict (h : N ≤r M) : M ↾ N.E = N := by
  obtain ⟨R, -, rfl⟩ := h; rw [restrict_ground_eq]

theorem Restriction.subset (h : N ≤r M) : N.E ⊆ M.E := by
  obtain ⟨R, hR, rfl⟩ := h; exact hR

theorem Restriction.exists_eq_restrict (h : N ≤r M) : ∃ R ⊆ M.E, N = M ↾ R :=
  h

theorem Restriction.of_subset {R' : Set α} (M : Matroid α) (h : R ⊆ R') : (M ↾ R) ≤r (M ↾ R') := by
  rw [← restrict_restrict_eq M h]; exact restrict_restriction _ _ h

theorem restriction_iff_exists : (N ≤r M) ↔ ∃ R, R ⊆ M.E ∧ N = M ↾ R := by
  use Restriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_restriction M R hR

theorem StrictRestriction.restriction (h : N <r M) : N ≤r M :=
  h.1

theorem StrictRestriction.ne (h : N <r M) : N ≠ M := by
  rintro rfl; rw [← ofMatroid_lt_iff] at h; simp at h

theorem StrictRestriction.irrefl (M : Matroid α) : ¬ (M <r M) :=
  fun h ↦ h.ne rfl

theorem StrictRestriction.ssubset (h : N <r M) : N.E ⊂ M.E := by
  obtain ⟨R, -, rfl⟩ := h.1
  refine h.restriction.subset.ssubset_of_ne (fun h' ↦ h.2 ⟨R, Subset.rfl, ?_⟩)
  rw [show R = M.E from h', restrict_idem, restrict_ground_eq_self]

theorem StrictRestriction.eq_restrict (h : N <r M) : M ↾ N.E = N :=
  h.restriction.eq_restrict

theorem StrictRestriction.exists_eq_restrict (h : N <r M) : ∃ R, R ⊂ M.E ∧ N = M ↾ R :=
  ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩

theorem Restriction.strictRestriction_of_ne (h : N ≤r M) (hne : N ≠ M) : N <r M :=
  ⟨h, fun h' ↦ hne <| h.antisymm h'⟩

theorem Restriction.eq_or_strictRestriction (h : N ≤r M) : N = M ∨ N <r M := by
  simpa using eq_or_lt_of_le (ofMatroid_le_iff.2 h)

theorem restrict_strictRestriction {M : Matroid α} (hR : R ⊂ M.E) : M ↾ R <r M := by
  refine (M.restrict_restriction R hR.subset).strictRestriction_of_ne (fun h ↦ ?_)
  rw [← h, restrict_ground_eq] at hR
  exact hR.ne rfl

theorem Restriction.strictRestriction_of_ground_ne (h : N ≤r M) (hne : N.E ≠ M.E) : N <r M := by
  rw [← h.eq_restrict]
  exact restrict_strictRestriction (h.subset.ssubset_of_ne hne)

theorem StrictRestriction.of_ssubset {R' : Set α} (M : Matroid α) (h : R ⊂ R') :
    (M ↾ R) <r (M ↾ R') :=
  (Restriction.of_subset M h.subset).strictRestriction_of_ground_ne h.ne

theorem Restriction.finite {M : Matroid α} [M.Finite] (h : N ≤r M) : N.Finite := by
  obtain ⟨R, hR, rfl⟩ := h
  exact restrict_finite <| M.ground_finite.subset hR

theorem Restriction.finiteRk {M : Matroid α} [FiniteRk M] (h : N ≤r M) : N.FiniteRk := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

theorem Restriction.finitary {M : Matroid α} [Finitary M] (h : N ≤r M) : N.Finitary := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

theorem finite_setOf_restriction (M : Matroid α) [M.Finite] : {N | N ≤r M}.Finite :=
  (M.ground_finite.finite_subsets.image (fun R ↦ M ↾ R)).subset <|
    by rintro _ ⟨R, hR, rfl⟩; exact ⟨_, hR, rfl⟩

theorem Indep.of_restriction (hI : N.Indep I) (hNM : N ≤r M) : M.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; exact hI.of_restrict

theorem Indep.indep_restriction (hI : M.Indep I) (hNM : N ≤r M) (hIN : I ⊆ N.E) : N.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hI]

theorem Basis.basis_restriction (hI : M.Basis I X) (hNM : N ≤r M) (hX : X ⊆ N.E) : N.Basis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [basis_restrict_iff, and_iff_left (show X ⊆ R from hX)]

theorem Basis.of_restriction (hI : N.Basis I X) (hNM : N ≤r M) : M.Basis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; exact ((basis_restrict_iff hR).1 hI).1

theorem Base.basis_of_restriction (hI : N.Base I) (hNM : N ≤r M) : M.Basis I N.E := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [base_restrict_iff] at hI

theorem Dep.of_restriction (hX : N.Dep X) (hNM : N ≤r M) : M.Dep X := by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_dep_iff] at hX
  exact ⟨hX.1, hX.2.trans hR⟩

theorem Dep.dep_restriction (hX : M.Dep X) (hNM : N ≤r M) (hXE : X ⊆ N.E := by aesop_mat) :
    N.Dep X := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hX.not_indep]

end Restriction

/-!
### `Basis` and `Base`
The lemmas below exploit the fact that `(M ↾ X).Base I ↔ M.Basis I X` to transfer facts about
`Matroid.Base` to facts about `Matroid.Basis`.
Their statements thematically belong in `Data.Matroid.Basic`, but they appear here because their
proofs depend on the API for `Matroid.restrict`,
-/

section Basis

variable {B J : Set α} {e : α}

theorem Basis.transfer (hIX : M.Basis I X) (hJX : M.Basis J X) (hXY : X ⊆ Y) (hJY : M.Basis J Y) :
    M.Basis I Y := by
  rw [← base_restrict_iff]; rw [← base_restrict_iff] at hJY
  exact hJY.base_of_basis_superset hJX.subset (hIX.basis_restrict_of_subset hXY)

theorem Basis.basis_of_basis_of_subset_of_subset (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X)
    (hIY : I ⊆ Y) : M.Basis I Y := by
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _)
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _)
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ

theorem Indep.exists_basis_subset_union_basis (hI : M.Indep I) (hIX : I ⊆ X) (hJ : M.Basis J X) :
    ∃ I', M.Basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J := by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_base_subset_union_base (Basis.base_restrict hJ)
  rw [base_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

theorem Indep.exists_insert_of_not_basis (hI : M.Indep I) (hIX : I ⊆ X) (hI' : ¬M.Basis I X)
    (hJ : M.Basis J X) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  rw [← base_restrict_iff] at hI'; rw [← base_restrict_iff] at hJ
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_base hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

theorem Basis.base_of_base_subset (hIX : M.Basis I X) (hB : M.Base B) (hBX : B ⊆ X) : M.Base I :=
  hB.base_of_basis_superset hBX hIX

theorem Basis.exchange (hIX : M.Basis I X) (hJX : M.Basis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.Basis (insert f (I \ {e})) X := by
  obtain ⟨y,hy, h⟩ := hIX.restrict_base.exchange hJX.restrict_base he
  exact ⟨y, hy, by rwa [base_restrict_iff] at h⟩

theorem Basis.eq_exchange_of_diff_eq_singleton (hI : M.Basis I X) (hJ : M.Basis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} := by
  rw [← base_restrict_iff] at hI hJ; exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ

theorem Basis'.encard_eq_encard (hI : M.Basis' I X) (hJ : M.Basis' J X) : I.encard = J.encard := by
  rw [← base_restrict_iff'] at hI hJ; exact hI.card_eq_card_of_base hJ

theorem Basis.encard_eq_encard (hI : M.Basis I X) (hJ : M.Basis J X) : I.encard = J.encard :=
  hI.basis'.encard_eq_encard hJ.basis'

/-- Any independent set can be extended into a larger independent set. -/
theorem Indep.augment (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard) :
    ∃ e ∈ J \ I, M.Indep (insert e I) := by
  by_contra! he
  have hb : M.Basis I (I ∪ J) := by
    simp_rw [hI.basis_iff_forall_insert_dep (subset_union_left _ _), union_diff_left, mem_diff,
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI ↦ ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_basis_of_subset (subset_union_right I J)
  rw [← hJ'.encard_eq_encard hb] at hIJ
  exact hIJ.not_le (encard_mono hJJ')

end Basis

end Matroid
