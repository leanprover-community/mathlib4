/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Subfunctor.Equalizer

/-!
# Horns

This file introduces horns `Λ[n, i]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex,
where `i : n`. It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
@[simps -isSimp obj]
def horn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := setOf (fun s ↦ Set.range (stdSimplex.asOrderHom s) ∪ {i} ≠ Set.univ)
  map φ s hs h := hs (by
    rw [Set.eq_univ_iff_forall] at h ⊢; intro j
    apply Or.imp _ id (h j)
    intro hj
    exact Set.range_comp_subset_range _ _ hj)

/-- The `i`-th horn `Λ[n, i]` of the standard `n`-simplex -/
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

lemma mem_horn_iff {n : ℕ} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n].obj m) :
    x ∈ (horn n i).obj m ↔ Set.range (stdSimplex.asOrderHom x) ∪ {i} ≠ Set.univ := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
lemma horn_eq_iSup (n : ℕ) (i : Fin (n + 1)) :
    horn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ := by
  ext m j
  simp [stdSimplex.face_obj, horn, Set.eq_univ_iff_forall]
  rfl

instance {n : ℕ} (i : Fin (n + 1)) : HasDimensionLT (horn.{u} n i) n := by
  rw [horn_eq_iSup, hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])

lemma face_le_horn {n : ℕ} (i j : Fin (n + 1)) (h : i ≠ j) :
    stdSimplex.face.{u} {i}ᶜ ≤ horn n j := by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) ↦ stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

@[simp]
lemma horn_obj_zero (n : ℕ) (i : Fin (n + 3)) :
    (horn.{u} (n + 2) i).obj (op (.mk 0)) = ⊤ := by
  ext j
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  let S : Finset (Fin (n + 3)) := {i, j 0}
  have hS : ¬ (S = Finset.univ) := fun hS ↦ by
    have := Finset.card_le_card hS.symm.le
    simp only [Finset.card_univ, Fintype.card_fin, S] at this
    have := this.trans Finset.card_le_two
    lia
  rw [Finset.eq_univ_iff_forall, not_forall] at hS
  obtain ⟨k, hk⟩ := hS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, S] at hk
  refine ⟨k, hk.1, fun a ↦ ?_⟩
  fin_cases a
  exact Ne.symm hk.2

set_option backward.isDefEq.respectTransparency false in
lemma horn_obj_eq_top {n : ℕ} (i : Fin (n + 1)) (m : ℕ) (h : m + 1 < n := by lia) :
    (horn.{u} n i).obj (op ⦋m⦌) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : ∃ (j : Fin (n + 1)), j ≠ i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ ∪ {i} = ⊤ := by ext k; by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have : n ≤ m + 1 := by simpa using this.trans Finset.card_image_le
    lia
  simp only [Set.top_eq_univ, horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.mem_univ, iff_true]
  exact ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩

lemma subcomplex_le_horn_iff {n : ℕ}
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (i : Fin (n + 2)) :
    A ≤ horn (n + 1) i ↔ ¬ stdSimplex.face {i}ᶜ ≤ A := by
  refine ⟨fun hA h ↦ ?_, fun h ↦ ?_⟩
  · replace h := h.trans hA
    rw [stdSimplex.face_singleton_compl, Subcomplex.ofSimplex_le_iff, mem_horn_iff] at h
    apply h
    change Set.range (Fin.succAboveOrderEmb i) ∪ _ = _
    rw [Fin.range_succAboveOrderEmb]
    exact Set.compl_union_self {i}
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases! hd : d < n
    · simp [horn_obj_eq_top i d]
    · obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = .univ := by
          rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
          exact le_antisymm (card_finset_fin_le S) (by lia)
        exact (h (le_trans (by simp) hx)).elim
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          lia
        obtain ⟨j, rfl⟩ : ∃ j, S = {j}ᶜ := by
          rw [Finset.card_eq_one] at hS
          obtain ⟨j, hS⟩ := hS
          exact ⟨j, by simp [← hS]⟩
        exact face_le_horn _ _ (by rintro rfl; tauto)

lemma face_le_horn_iff {n : ℕ} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    stdSimplex.face.{u} S ≤ horn (n + 1) j ↔ S ≠ .univ ∧ S ≠ {j}ᶜ := by
  rw [subcomplex_le_horn_iff, stdSimplex.face_le_face_iff, ← not_iff_not]
  simp only [Finset.le_eq_subset, Decidable.not_not, ne_eq, not_and_or]
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  rw [← Finset.compl_subset_compl, compl_compl,
    Finset.subset_singleton_iff, Finset.compl_eq_empty_iff] at h
  obtain h | h := h
  · exact Or.inl h
  · exact Or.inr (by simp [← h])

lemma objEquiv_symm_notMem_horn_of_isIso {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategory} (f : d ⟶ ⦋n⦌) [IsIso f] :
    stdSimplex.objEquiv.symm f ∉ (horn.{u} n i).obj (op d) := by
  rw [mem_horn_iff, ne_eq, Decidable.not_not]
  ext i
  simpa using Or.inr ⟨inv f i, by change (inv f ≫ f) i = i; cat_disch⟩

lemma objEquiv_symm_δ_mem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) ∈ (horn.{u} (n + 1) j).obj (op ⦋n⦌) ↔ i ≠ j := by
  dsimp
  rw [← Subcomplex.ofSimplex_le_iff, ← stdSimplex.face_singleton_compl, face_le_horn_iff]
  simp

lemma objEquiv_symm_δ_notMem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) ∉ (horn.{u} _ j).obj (op ⦋n⦌) ↔ i = j := by
  simp [objEquiv_symm_δ_mem_horn_iff.{u}]


namespace horn

open SimplexCategory Finset Opposite

section

variable (n : ℕ) (i k : Fin (n + 3))

/-- The (degenerate) subsimplex of `Λ[n+2, i]` concentrated in vertex `k`. -/
def const (m : SimplexCategoryᵒᵖ) : Λ[n + 2, i].obj m :=
  SSet.yonedaEquiv (X := Λ[n + 2, i])
    (SSet.const ⟨stdSimplex.obj₀Equiv.symm k, by simp⟩)

@[simp]
lemma const_val_apply {m : ℕ} (a : Fin (m + 1)) :
    (const n i k (op (.mk m))).val a = k :=
  rfl

end

/-- The edge of `Λ[n, i]` with endpoints `a` and `b`.

This edge only exists if `{i, a, b}` has cardinality less than `n`. -/
@[simps]
def edge (n : ℕ) (i a b : Fin (n + 1)) (hab : a ≤ b) (H : #{i, a, b} ≤ n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ :=
  ⟨stdSimplex.edge n a b hab, by
    have hS : ¬ ({i, a, b} = Finset.univ) := fun hS ↦ by
      have := Finset.card_le_card hS.symm.le
      simp only [card_univ, Fintype.card_fin] at this
      lia
    rw [Finset.eq_univ_iff_forall, not_forall] at hS
    obtain ⟨k, hk⟩ := hS
    simp only [mem_insert, mem_singleton, not_or] at hk
    -- this was produced by `simp? [horn_eq_iSup]`
    simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff, Nat.reduceAdd, mem_compl,
      mem_singleton, exists_prop]
    refine ⟨k, hk.1, fun a ↦ ?_⟩
    fin_cases a
    · exact Ne.symm hk.2.1
    · exact Ne.symm hk.2.2⟩

/-- Alternative constructor for the edge of `Λ[n, i]` with endpoints `a` and `b`,
assuming `3 ≤ n`. -/
@[simps!]
def edge₃ (n : ℕ) (i a b : Fin (n + 1)) (hab : a ≤ b) (H : 3 ≤ n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ :=
  edge n i a b hab <| Finset.card_le_three.trans H

/-- The edge of `Λ[n, i]` with endpoints `j` and `j+1`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps!]
def primitiveEdge {n : ℕ} {i : Fin (n + 1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ := by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl | hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; lia
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

/-- The triangle in the standard simplex with vertices `k`, `k+1`, and `k+2`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps]
def primitiveTriangle {n : ℕ} (i : Fin (n + 4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 3))
    (k : ℕ) (h : k < n + 2) : (Λ[n + 3, i] : SSet.{u}) _⦋2⦌ := by
  refine ⟨stdSimplex.triangle
    (n := n+3) ⟨k, by lia⟩ ⟨k+1, by lia⟩ ⟨k+2, by lia⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, (⟨k, by lia⟩ : Fin (n + 4)), (⟨k + 1, by lia⟩ : Fin (n + 4)),
      (⟨k + 2, by lia⟩ : Fin (n + 4))} = Finset.univ) := fun hS ↦ by
    obtain ⟨i, hi⟩ := i
    by_cases hk : k = 0
    · subst hk
      have := Finset.mem_univ (Fin.last _ : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [Fin.zero_eta, zero_add, Fin.mk_one, mem_insert, Fin.ext_iff, Fin.val_last,
        Fin.val_zero, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        Fin.val_one, Nat.reduceEqDiff, mem_singleton, or_self, or_false] at this
      simp only [Fin.lt_def, Fin.val_last] at hₙ
      lia
    · have := Finset.mem_univ (0 : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [mem_insert, Fin.ext_iff, Fin.val_zero, right_eq_add,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_singleton,
        OfNat.ofNat_ne_zero, or_self, or_false] at this
      obtain rfl | rfl := this <;> tauto
  rw [Finset.eq_univ_iff_forall, not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun a ↦ ?_⟩
  fin_cases a
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

/-- The `j`th face of codimension `1` of the `i`-th horn. -/
def face {n : ℕ} (i j : Fin (n + 2)) (h : j ≠ i) : (Λ[n + 1, i] : SSet.{u}) _⦋n⦌ :=
  yonedaEquiv (Subfunctor.lift (stdSimplex.δ j) (by
    simpa using face_le_horn _ _ h))

/-- Two morphisms from a horn are equal if they are equal on all suitable faces. -/
protected
lemma hom_ext {n : ℕ} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S)
    (h : ∀ (j) (h : j ≠ i), σ₁.app _ (face i j h) = σ₂.app _ (face i j h)) :
    σ₁ = σ₂ := by
  rw [← Subfunctor.equalizer_eq_iff]
  apply le_antisymm (Subfunctor.equalizer_le σ₁ σ₂)
  simp only [horn_eq_iSup, iSup_le_iff,
    Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff,
    ← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
  intro j hj
  exact (Subfunctor.mem_equalizer_iff σ₁ σ₂ (face i j hj)).2 (by apply h)


/-- Given `i` and `j` in `Fin (n + 1)` such that `j ≠ i`, this is
the inclusion of `stdSimplex.face {j}ᶜ` in the horn `horn n i`. -/
def faceι {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    (stdSimplex.face {j}ᶜ : SSet.{u}) ⟶ (Λ[n, i] : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]
lemma faceι_ι {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    faceι i j hij ≫ Λ[n, i].ι = (stdSimplex.face {j}ᶜ).ι := by
  simp [faceι]

/-- Given `i` and `j` in `Fin (n + 2)` such that `j ≠ i`, this is the inclusion
of `Δ[n]` in `horn (n + 1) i` given by `stdSimplex.δ j`. -/
def ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    Δ[n] ⟶ (Λ[n + 1, i] : SSet.{u}) :=
  yonedaEquiv.symm (face i j hij)

lemma yonedaEquiv_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    yonedaEquiv (ι i j hij) = face i j hij := by
  rw [ι, Equiv.apply_symm_apply]

@[reassoc (attr := simp)]
lemma ι_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    ι i j hij ≫ Λ[n + 1, i].ι =
      stdSimplex.{u}.δ j := by
  rw [ι, face, Equiv.symm_apply_apply, Subfunctor.lift_ι]

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    (stdSimplex.faceSingletonComplIso.{u} j).inv ≫ ι i j hij = faceι i j hij := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).hom, Iso.hom_inv_id_assoc]
  rfl

end horn

end SSet
