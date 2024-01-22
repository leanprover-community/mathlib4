/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Joseph Tooby-Smith, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

#align_import algebraic_topology.simplicial_set from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `Open Simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/

set_option autoImplicit true


universe v u

open CategoryTheory CategoryTheory.Limits

open Simplicial

/-- The category of simplicial sets.
This is the category of contravariant functors from
`SimplexCategory` to `Type u`. -/
def SSet : Type (u + 1) :=
  SimplicialObject (Type u)
set_option linter.uppercaseLean3 false in
#align sSet SSet

namespace SSet

instance largeCategory : LargeCategory SSet := by
  dsimp only [SSet]
  infer_instance

instance hasLimits : HasLimits SSet := by
  dsimp only [SSet]
  infer_instance

instance hasColimits : HasColimits SSet := by
  dsimp only [SSet]
  infer_instance

-- Porting note: added an `ext` lemma.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) : f = g :=
  SimplicialObject.hom_ext _ _ w

/-- The ulift functor `SSet.{u} ⥤ SSet.{max u v}` on simplicial sets. -/
def uliftFunctor : SSet.{u} ⥤ SSet.{max u v} :=
  (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

/-- The `n`-th standard simplex `Δ[n]` associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standardSimplex : SimplexCategory ⥤ SSet.{u} :=
  yoneda ⋙ uliftFunctor
set_option linter.uppercaseLean3 false in
#align sSet.standard_simplex SSet.standardSimplex

-- mathport name: standard_simplex
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.standardSimplex.obj (SimplexCategory.mk n)

instance : Inhabited SSet :=
  ⟨Δ[0]⟩

namespace standardSimplex

open Finset Opposite SimplexCategory

@[simp]
lemma map_id (n : SimplexCategory) :
    (SSet.standardSimplex.map (SimplexCategory.Hom.mk OrderHom.id : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- Simplices of the standard simplex identify to morphisms in `SimplexCategory`. -/
def objEquiv (n : SimplexCategory) (m : SimplexCategoryᵒᵖ) :
    (standardSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (standardSimplex.{u}.obj n).obj m :=
  (objEquiv _ _).symm (Hom.mk f)

lemma map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
    (x : (standardSimplex.{u}.obj n).obj m₁) :
    (standardSimplex.{u}.obj n).map f x = (objEquiv _ _).symm (f.unop ≫ (objEquiv _ _) x) := by
  rfl

/-- The canonical bijection `(standardSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
def _root_.SSet.yonedaEquiv (X : SSet.{u}) (n : SimplexCategory) :
    (standardSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  yonedaCompUliftFunctorEquiv X n

/-- The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`. -/
def const (n : ℕ) (k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k )

@[simp]
lemma const_down_toOrderHom (n : ℕ) (k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

/-- The edge of the standard simplex with endpoints `a` and `b`. -/
def edge (n : ℕ) (a b : Fin (n+1)) (hab : a ≤ b) : Δ[n] _[1] := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

lemma coe_edge_down_toOrderHom (n : ℕ) (a b : Fin (n+1)) (hab : a ≤ b) :
    ↑(edge n a b hab).down.toOrderHom = ![a, b] :=
  rfl

/-- The triangle in the standard simplex with vertices `a`, `b`, and `c`. -/
def triangle {n : ℕ} (a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _[2] := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, Matrix.tail_cons, Matrix.head_cons, true_and]

lemma coe_triangle_down_toOrderHom {n : ℕ} (a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b ≤ c) :
    ↑(triangle a b c hab hbc).down.toOrderHom = ![a, b, c] :=
  rfl

end standardSimplex

section

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`. -/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom
set_option linter.uppercaseLean3 false in
#align sSet.as_order_hom SSet.asOrderHom

end

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standardSimplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : SSet.{u} where
  obj m := { α : Δ[n].obj m // ¬Function.Surjective (asOrderHom α) }
  map {m₁ m₂} f α :=
    ⟨Δ[n].map f α.1, by
      intro h
      apply α.property
      exact Function.Surjective.of_comp h⟩
set_option linter.uppercaseLean3 false in
#align sSet.boundary SSet.boundary

-- mathport name: sSet.boundary
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundaryInclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where app m (α : { α : Δ[n].obj m // _ }) := α
set_option linter.uppercaseLean3 false in
#align sSet.boundary_inclusion SSet.boundaryInclusion

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : Fin (n + 1)) : SSet where
  obj m := { α : Δ[n].obj m // Set.range (asOrderHom α) ∪ {i} ≠ Set.univ }
  map {m₁ m₂} f α :=
    ⟨Δ[n].map f α.1, by
      intro h; apply α.property
      rw [Set.eq_univ_iff_forall] at h ⊢; intro j
      apply Or.imp _ id (h j)
      intro hj
      exact Set.range_comp_subset_range _ _ hj⟩
set_option linter.uppercaseLean3 false in
#align sSet.horn SSet.horn

-- mathport name: sSet.horn
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def hornInclusion (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[n] where
  app m (α : { α : Δ[n].obj m // _ }) := α
set_option linter.uppercaseLean3 false in
#align sSet.horn_inclusion SSet.hornInclusion

namespace horn

open SimplexCategory Finset Opposite

/-- The (degenerate) subsimplex of `Λ[n+2, i]` concentrated in vertex `k`. -/
@[simps]
def const (n : ℕ) (i k : Fin (n+3)) (m : SimplexCategoryᵒᵖ) : Λ[n+2, i].obj m := by
  refine ⟨standardSimplex.const _ k _, ?_⟩
  suffices ¬ Finset.univ ⊆ {i, k} by
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or, Fin.forall_fin_one,
      subset_iff, mem_univ, @eq_comm _ _ k]
  intro h
  have := (card_le_card h).trans card_le_two
  rw [card_fin] at this
  omega

/-- The edge of `Λ[n, i]` with endpoints `a` and `b`.

This edge only exists if `{i, a, b}` has cardinality less than `n`. -/
@[simps]
def edge (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : Finset.card {i, a, b} ≤ n) :
    Λ[n, i] _[1] := by
  refine ⟨standardSimplex.edge n a b hab, ?range⟩
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x ∧ ¬b = x by
      simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
        Set.mem_insert_iff, @eq_comm _ _ i, Set.mem_range, forall_true_left, not_forall, not_or,
        not_exists, Fin.forall_fin_two]
    contrapose! H
    replace H : univ ⊆ {i, a, b} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H

/-- Alternative constructor for the edge of `Λ[n, i]` with endpoints `a` and `b`,
assuming `3 ≤ n`. -/
@[simps!]
def edge₃ (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : 3 ≤ n) :
    Λ[n, i] _[1] :=
  horn.edge n i a b hab <| Finset.card_le_three.trans H

/-- The edge of `Λ[n, i]` with endpoints `j` and `j+1`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps!]
def primitiveEdge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i] _[1] := by
  refine horn.edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.coe_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl|hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; omega
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

/-- The triangle in the standard simplex with vertices `k`, `k+1`, and `k+2`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps]
def primitiveTriangle {n : ℕ} (i : Fin (n+4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n+3))
    (k : ℕ) (h : k < n+2) : Λ[n+3, i] _[2] := by
  refine ⟨standardSimplex.triangle
    (n := n+3) ⟨k, by omega⟩ ⟨k+1, by omega⟩ ⟨k+2, by omega⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
    Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
    forall_true_left, not_forall, not_or, unop_op, not_exists,
    standardSimplex.triangle, OrderHom.coe_mk, @eq_comm _ _ i,
    standardSimplex.objMk, standardSimplex.objEquiv, Equiv.ulift]
  dsimp
  by_cases hk0 : k = 0
  · subst hk0
    use Fin.last (n+3)
    simp only [hₙ.ne, not_false_eq_true, Fin.zero_eta, zero_add, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff] <;> omega
  · use 0
    simp only [h₀.ne', not_false_eq_true, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff, hk0]

/-- The `j`th subface of the `i`-th horn. -/
@[simps]
def face {n : ℕ} (i j : Fin (n+2)) (h : j ≠ i) : Λ[n+1, i] _[n] :=
  ⟨(standardSimplex.objEquiv _ _).symm (SimplexCategory.δ j), by
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, SimplexCategory.δ, not_or,
      standardSimplex.objEquiv, asOrderHom, Equiv.ulift]⟩

/-- Two morphisms from a horn are equal if they are equal on all suitable faces. -/
protected
lemma hom_ext {n : ℕ} {i : Fin (n+2)} {S : SSet} (σ₁ σ₂ : Λ[n+1, i] ⟶ S)
    (h : ∀ (j) (h : j ≠ i), σ₁.app _ (face i j h) = σ₂.app _ (face i j h)) :
    σ₁ = σ₂ := by
  apply NatTrans.ext; apply funext; apply Opposite.rec; apply SimplexCategory.rec
  intro m; ext f
  obtain ⟨f', hf⟩ := (standardSimplex.objEquiv _ _).symm.surjective f.1
  obtain ⟨j, hji, hfj⟩ : ∃ j, ¬j = i ∧ ∀ k, f'.toOrderHom k ≠ j := by
    obtain ⟨f, hf'⟩ := f
    subst hf
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using hf'
  have H : f = (Λ[n+1, i].map (factor_δ f' j).op) (face i j hji) := by
    apply Subtype.ext
    apply (standardSimplex.objEquiv _ _).injective
    rw [← hf]
    exact (factor_δ_spec f' j hfj).symm
  have H₁ := congrFun (σ₁.naturality (factor_δ f' j).op) (face i j hji)
  have H₂ := congrFun (σ₂.naturality (factor_δ f' j).op) (face i j hji)
  dsimp at H₁ H₂
  erw [H, H₁, H₂, h _ hji]

/-- The `(δ i).toOrderHom j`th subface of the `i`-th horn, such that `j:Fin (n+1)` sequentially
labels the subfaces which exist. -/
def face' {n : ℕ} (i  : Fin (n+2)) (j: Fin (n+1)) : (Λ[n+1, i]: SSet) _[n] :=by
    refine face i ((δ i).toOrderHom j) ?_
    unfold δ
    simp
    unfold Fin.succAbove
    by_contra h
    split at h
    all_goals
      subst h
      simp_all only [lt_self_iff_false,Fin.castSucc_lt_succ_iff, le_refl, not_true_eq_false]

/-- Every `face` can be written as a `face'`.-/
lemma face_eq_face' {n : ℕ} (i  : Fin (n+2)) (j: Fin (n+2)) (h: j≠i): face i j h
    =face' i (Fin.predAbove (Fin.predAbove 0 i) j) := by
  unfold face'
  congr
  change j = (Fin.succAbove i) (_)
  have ht : (Fin.predAbove 0 i).val= i.val -1 := by
       unfold Fin.predAbove
       split
       · rfl
       · simp_all only [ne_eq, Fin.coe_castPred]
         simp_all only [Fin.castSucc_zero, not_lt, Fin.le_zero_iff, Fin.val_zero,
         ge_iff_le, zero_le, tsub_eq_zero_of_le]
  by_cases h1 : j ≤ Fin.castSucc (Fin.predAbove 0 i)
  · rw [Fin.predAbove_below (Fin.predAbove 0 i) j h1]
    unfold Fin.succAbove
    split
    · rfl
    · rename_i h2
      change j.val ≤ (Fin.predAbove 0 i).val at h1
      rw [ht] at h1
      exfalso
      apply h ∘ (Fin.eq_iff_veq j i).mpr
      apply le_antisymm
      · apply le_trans h1
        exact Nat.sub_le (↑i) 1
      · exact Nat.not_lt.mp h2
  · rw [Fin.predAbove_above (Fin.predAbove 0 i) j (not_le.mp h1)]
    unfold Fin.succAbove
    split
    · rename_i h2
      change ¬ (j.val≤ (Fin.predAbove 0 i).val ) at h1
      rw [ht] at h1
      exfalso
      apply  h ∘ (Fin.eq_iff_veq j i).mpr
      apply le_antisymm
      · exact Nat.le_of_pred_lt h2
      · contrapose! h1
        exact Nat.le_pred_of_lt h1
    · simp_all only [ne_eq, not_lt, Fin.succ_pred]


lemma face'_factor {n : ℕ} (i: Fin (n+2)) (j: Fin (n+1)) : factor_δ (face'.{u} i j).val.down
    ((δ i).toOrderHom j)= 𝟙 ([n]:SimplexCategory):=by
        change δ ((δ i).toOrderHom j)≫  (σ (Fin.predAbove 0 ((δ i).toOrderHom j)))=_
        let l' : Fin (n+2) := ((δ i).toOrderHom j)
        change δ l' ≫  (σ (Fin.predAbove 0 l'))=_
        unfold Fin.predAbove
        split
        · rename_i h1
          let l'' := Fin.pred l' (@Fin.predAbove.proof_1 (n + 1) 0 l' h1)
          rw [show δ l' = δ (Fin.succ l'') by simp_all only [len_mk, Fin.succ_pred]]
          exact δ_comp_σ_succ
        · exact δ_comp_σ_self


namespace FactorMinFace
variable {X : SimplexCategoryᵒᵖ } {n: ℕ }{i : Fin (n+3)} ( α : Λ[n+2,i].obj X)

def  minAsNat (l : ℕ )  :  ℕ  :=
        if l > n+1 then  (n+2) -- Default case (never occurs)
        else if ∀ k, α.1.down.toOrderHom k ≠ (δ i).toOrderHom l
         then l-- Found the index satisfying the condition
         else minAsNat (l+1) -- Check the next index
termination_by _ l => (n+2) - l
decreasing_by
    simp_wf
    rename_i h1 h2
    push_neg at h1 h2
    rw [Nat.succ_sub h1]
    exact Nat.lt.base (n + 1 - l)

lemma minAsNat_lt (l : ℕ ) : minAsNat α l < n+3 := by
    unfold minAsNat
    simp_all only [gt_iff_lt, len_mk, ne_eq]
    split
    · exact Nat.lt.base (n + 2)
    · simp_all only [not_lt, yoneda_obj_obj, len_mk]
      split
      · rename_i h1 h2
        linarith
      · apply minAsNat_lt
termination_by _ l => (n+2) - l
decreasing_by
    simp_wf
    rename_i h1 h2
    push_neg at h1 h2
    rw [Nat.succ_sub h1]
    exact Nat.lt.base (n + 1 - l)


lemma lt_minAsNat_of_succ (l: ℕ)  (hl:  l<n+2): l< minAsNat α (l+1):= by
    unfold minAsNat
    split
    · exact hl
    · split
      · exact Nat.lt.base l
      · rename_i h1 h2
        by_cases hn : (l+1) < n+2
        · let ht:= lt_minAsNat_of_succ (l+1) hn
          exact Nat.lt_of_succ_lt ht
        · have hlp1 : (l+1)+1 > n+2  := by
            exact Nat.not_le.mp hn
          unfold minAsNat
          linarith
termination_by _  => (n+2) - l
decreasing_by
    simp_wf
    rename_i h1 h2
    push_neg at h1 h2
    apply tsub_lt_tsub_right_of_le
    exact Nat.lt_succ.mp hl
    exact Nat.lt.base (n + 1)

lemma not_in_range_if_eq_self (l: ℕ)  (hl:  l<n+2) (heq: minAsNat α l=l) :
    ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom l:=by
      unfold minAsNat at heq
      have h1 : ¬ (l >n+1) := by
        linarith
      simp [h1] at heq
      let h3:= lt_minAsNat_of_succ α l hl
      have h2: minAsNat α (l+1) ≠ l := by
        exact Nat.ne_of_gt h3
      intro k
      simp_all only [gt_iff_lt, not_lt, len_mk, imp_false, ne_eq, not_false_eq_true]

lemma in_range_if_neq_self (l: ℕ)  (hl:  l<n+2) (heq: minAsNat α l≠ l) :
    ¬ ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom l:=by
      unfold minAsNat at heq
      have h1 : ¬ (l >n+1) := by
         linarith
      simp [h1] at heq
      let h3:= lt_minAsNat_of_succ α l hl
      have h2: minAsNat α (l+1) ≠ l := by
        exact Nat.ne_of_gt h3
      tauto

lemma in_range_if_lt_minAsNat_zero (l:ℕ)  (hl: l< (minAsNat α 0)) : (¬ ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom l) ∧ (minAsNat α 0= minAsNat α l):=by
     induction' l with k hk
     · have h1 : 0 < n+2 := by
          exact Nat.succ_pos (n+1)
       have h2 : minAsNat α 0≠ 0:= by
          exact Nat.pos_iff_ne_zero.mp hl
       apply And.intro
       exact in_range_if_neq_self α Nat.zero h1 h2
       rfl
     · have hkl : k < minAsNat α 0:= by
          exact Nat.lt_of_succ_lt hl
       have k_lt_np1 :¬ (k> n+1)  := by
             let hr:= minAsNat_lt α 0
             simp
             linarith
       apply hk at hkl
       rw [hkl.right] at hl
       apply And.intro
       · unfold minAsNat at hl
         simp [k_lt_np1] at hl
         split at hl
         · tauto
         · have ht: minAsNat α (Nat.succ k) ≠ Nat.succ k  := by
              exact Nat.ne_of_gt hl
           apply in_range_if_neq_self
           · let hr:= minAsNat_lt α (k+1)
             linarith
           · exact ht
       · rw [hkl.right]
         have hx: ¬ ∀ (k_1 : Fin (len X.unop + 1)), ¬(Hom.toOrderHom α.1.down) k_1
             = (Hom.toOrderHom (δ i)) k := by
            exact hkl.left
         have hf:  minAsNat α k
             = (if k > n + 1 then n + 2  else if ∀ l, α.1.down.toOrderHom l ≠ (δ i).toOrderHom k
         then k
         else minAsNat α (k+1) ):= by
            rw [minAsNat]
         rw [hf]
         simp [k_lt_np1]
         exact fun a => (hx a).elim

lemma minAsNat_zero_neq : minAsNat α 0 ≠ n+2 := by
    by_contra h
    have h1: ∀ (l : Fin (n+2)) , (¬ ∀ k , α.1.down.toOrderHom k ≠ (δ i).toOrderHom l) := by
        intro l
        have hj: @Nat.cast (Fin (len [n + 1] + 1)) AddMonoidWithOne.toNatCast l.val  = l := by
          exact Fin.cast_val_eq_self l
        rw [← hj]
        have htt : l.val < minAsNat α 0 := by
            simp_all only [len_mk, Fin.is_lt]
        let ht:= in_range_if_lt_minAsNat_zero α  l htt
        exact ht.left
    have hα:= α.prop∘Set.eq_univ_iff_forall.mpr
    simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
            not_forall, not_or, not_exists] at hα
    obtain ⟨x, hx⟩ := hα
    let lx:= (Fin.predAbove (Fin.predAbove 0 i)) x
    have ht :   (Hom.toOrderHom (δ i)) lx =x  := by
        change Fin.succAbove i ((Fin.predAbove (Fin.predAbove 0 i)) x) =_
        by_cases hi: i≠ 0
        · rw [Fin.predAbove_zero hi]
          rw [Fin.eq_iff_veq]
          unfold Fin.succAbove
          unfold Fin.predAbove
          split <;> split
          · rename_i  h2 h3
            rw [Fin.lt_def] at h2
            simp at h2 h3
            let hx2:= hx.left
            rw [Fin.eq_iff_veq] at hx2
            exact (hx2 (Nat.le_antisymm (Nat.le_of_pred_lt h3) (Nat.le_of_pred_lt h2))).elim
          · simp
          · simp
          · rename_i  h2 h3
            rw [Fin.lt_def] at h2
            simp at h2 h3
            rw [Fin.le_def] at h3
            have h4: i.val ≤ i.val -1 := by
                exact Nat.le_trans h3 h2
            change  ¬(i=0)  at hi
            rw [Fin.eq_iff_veq] at hi
            have ht : 0< i.val :=  Nat.pos_of_ne_zero hi
            change i.val ≤ Nat.pred i.val at h4
            rw [Nat.le_pred_iff_lt ht] at h4
            simp at h4
        ·
          simp at hi
          rw [hi]
          rw [Fin.eq_iff_veq]
          simp
          have hpr: Fin.predAbove (0: Fin (n+2)) 0=0 := by
              rfl
          rw [hpr]
          unfold Fin.predAbove
          split
          · rename_i h2
            rw [Fin.lt_def] at h2
            simp at h2
            simp
            exact Nat.sub_add_cancel h2
          ·  rename_i h2
             simp at h2
             rw [h2] at hx
             rw [← hi] at hx
             simp at hx
    rw [← ht] at hx
    let hxr:= hx.right
    exact h1 lx hxr

lemma minAsNat_zero_lt  : minAsNat α 0 < n+2 :=
    Nat.lt_of_le_of_ne (Nat.lt_succ.mp (  minAsNat_lt α 0) ) (minAsNat_zero_neq α)

def min : Fin (n+2) := ⟨minAsNat α 0,  minAsNat_zero_lt α⟩

lemma minAsNat_eq_minAsNat_of_self (l:ℕ)  (hl: l= (minAsNat α 0)) :(minAsNat α 0= minAsNat α l):=by
    by_cases hl2: l=0
    · rw [hl2]
    · let lm1:= Nat.pred l
      have hl1: lm1< l:= Nat.pred_lt hl2
      rw [hl] at hl1
      let h3:= (in_range_if_lt_minAsNat_zero α lm1 hl1).right
      let h4:= (in_range_if_lt_minAsNat_zero α lm1 hl1).left
      rw [h3]
      have hf:  minAsNat α lm1 =
      (if lm1 > n + 1 then n + 2  else if ∀ l, α.1.down.toOrderHom l ≠ (δ i).toOrderHom lm1
         then lm1
         else minAsNat α (lm1+1) ):= by
            rw [minAsNat]
      rw [hf]
      have hlm1N: ¬ (lm1>  n+1):=
         Nat.not_lt.mpr (Nat.lt_succ.mp (Nat.lt_trans hl1 (minAsNat_zero_lt α)))

      simp only [gt_iff_lt, hlm1N, len_mk, ne_eq, ite_false]
      rw [if_neg]
      · rw [show Nat.pred l+1 =l from Nat.succ_pred hl2  ]
      · exact h4

lemma gt_min_if_not_in_range (j: Fin (n+2)) : ( ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom j )→ ((min α)≤ j):= by
      intro h
      rw [Fin.le_def]
      change minAsNat α 0 ≤ j.val
      by_contra hn
      simp at hn
      let hn2:=(in_range_if_lt_minAsNat_zero α j.val hn).left
      have hj:  @Nat.cast (Fin (len [n + 1] + 1)) AddMonoidWithOne.toNatCast j.val  = j := by
          exact Fin.cast_val_eq_self j
      rw [hj] at hn2
      exact hn2 h

lemma min_not_in_range: ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom (min α):=by
      let l :=  (minAsNat α 0)
      have h1: (minAsNat α 0) = (minAsNat α l) := by
       apply  (minAsNat_eq_minAsNat_of_self α l)
       rfl
      have hj:  @Nat.cast (Fin (len [n + 1] + 1)) AddMonoidWithOne.toNatCast l  = (min α) := by
          exact Fin.cast_val_eq_self (min α)
      rw [← hj]
      apply not_in_range_if_eq_self
      · exact minAsNat_zero_lt α
      · exact  id h1.symm



variable {Y : SimplexCategoryᵒᵖ } (φ':X⟶ Y)
lemma min_not_in_range_φ : ∀ k, (φ'.unop ≫ α.1.down).toOrderHom k ≠
    (δ i).toOrderHom (min α):= by
        exact fun k ↦ min_not_in_range α ((Hom.toOrderHom φ'.unop) k)
lemma min_comp_le_min:
    min (Λ[n+2,i].map φ' α) ≤  min α:= by
       exact gt_min_if_not_in_range (Λ[n+2, i].map φ' α) (min α)
          (fun k ↦ min_not_in_range α ((Hom.toOrderHom φ'.unop) k) )
end FactorMinFace


lemma naturality_lt {S : SSet} {n  : ℕ } {i : Fin (n+3)} {X Y :SimplexCategoryᵒᵖ}
    (α : Λ[n+2,i].obj X ) (φ: ([len Y.unop]: SimplexCategory)⟶ [len X.unop])
    (f1 f2 :  S _[n+1])
    (i1 i2 : Fin (n+3))
    (i1_lt_i2 : i1<i2)
    (exclude_i1 :  ∀ k, (φ ≫ α.val.down).toOrderHom k ≠  i1)
    (exclude_i2 :  ∀ k, (φ ≫ α.val.down).toOrderHom k ≠  i2)
    (hface : S.map (δ (Fin.predAbove 0 i2)).op f1
    = S.map (δ (Fin.predAbove (Fin.last (n+1)) i1)).op f2 ):
    S.map ( ((Λ[n+2, i].map φ.op α).val.down) ≫ σ  ( Fin.predAbove 0 i1)).op
    (f1)=S.map φ.op (S.map ( (α.val.down)≫  σ (Fin.predAbove 0 i2)).op
    (f2))  := by
  let α' :([(unop X).len]: SimplexCategory)⟶  [n+2]:= α.val.down
  change S.map (factor_δ (φ ≫ α.val.down) i1).op (_)
             = (S.map (factor_δ α' i2).op ≫ S.map φ.op) (_)
  rw [← S.map_comp, ← op_comp]
  change _= (S.map (factor_δ (φ ≫ α.val.down) i2).op ) (_)
  rw [← (factor_δ_comp_spec_lt i1_lt_i2 exclude_i1 exclude_i2)]
  rw [← (factor_δ_comp_spec_lt' i1_lt_i2 exclude_i1 exclude_i2)]
  rw [op_comp,S.map_comp,op_comp,S.map_comp,types_comp_apply,types_comp_apply]
  rw [(hface),← (factor_δ_comp_lt _ _ _ i1_lt_i2)]

/-- The horn `Λ[n+2,i]⟶ S` constructed from the image of the appropriate to (n+1)-simplies and
the appropriate compatiblity conditions on their faces. -/
def homMk {S : SSet}  {n:ℕ} (i: Fin (n+3))  (face_map : Fin (n+2) →  S _[n+1])
    (hface : (i1 : Fin (n+2))→ (i2 : Fin (n+2)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    =S.map (δ (Fin.predAbove (Fin.last (n+1)) ((δ i).toOrderHom i1))).op (face_map i2) )
    : Λ[n+2,i]⟶ S where
  app X α := by
    let α' :([(unop X).len]: SimplexCategory)⟶  [n+2]:= α.1.down
    let id:= FactorMinFace.min α
    exact S.map (factor_δ α' ((δ i).toOrderHom  id)).op (face_map id)
  naturality X Y φ' := by
     funext α
     let φ: ([len Y.unop]: SimplexCategory)⟶ [len X.unop] := φ'.unop
     simp only [mk_len, op_unop, len_mk, types_comp_apply]
     let i1 := FactorMinFace.min (Λ[n+2, i].map φ' α)
     let i2 := FactorMinFace.min α
     let i1_le_i2 : i1≤i2 := FactorMinFace.min_comp_le_min α φ'
     have h : i1<i2 ∨ i1=i2 := by
      exact lt_or_eq_of_le i1_le_i2
     change S.map (factor_δ _ ((δ i).toOrderHom i1)).op (face_map i1)
        = S.map φ.op (S.map (factor_δ _ (((δ i).toOrderHom i2))).op (face_map i2))
     cases h with
     | inl h =>
                apply naturality_lt
                · exact  Fin.strictMono_succAbove i h
                · exact FactorMinFace.min_not_in_range (Λ[n+2, i].map φ' α)
                · exact FactorMinFace.min_not_in_range_φ α φ'
                · exact hface i1 i2 h
     | inr h => rw [← h,← (types_comp_apply (S.map _) (S.map _)),← S.map_comp, ← op_comp]
                rfl


end horn

section Examples

open Simplicial

/-- The simplicial circle. -/
noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (standardSimplex.map <| SimplexCategory.δ 0 : Δ[0] ⟶ Δ[1])
      (standardSimplex.map <| SimplexCategory.δ 1)
set_option linter.uppercaseLean3 false in
#align sSet.S1 SSet.S1

end Examples

/-- Truncated simplicial sets. -/
def Truncated (n : ℕ) :=
  SimplicialObject.Truncated (Type u) n
set_option linter.uppercaseLean3 false in
#align sSet.truncated SSet.Truncated

instance Truncated.largeCategory (n : ℕ) : LargeCategory (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasLimits : HasLimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasColimits : HasColimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

-- Porting note: added an `ext` lemma.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma Truncated.hom_ext {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (funext w)

/-- The skeleton functor on simplicial sets. -/
def sk (n : ℕ) : SSet ⥤ SSet.Truncated n :=
  SimplicialObject.sk n
set_option linter.uppercaseLean3 false in
#align sSet.sk SSet.sk

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(sk n).obj <| Δ[0]⟩

/-- The category of augmented simplicial sets, as a particular case of
augmented simplicial objects. -/
abbrev Augmented :=
  SimplicialObject.Augmented (Type u)
set_option linter.uppercaseLean3 false in
#align sSet.augmented SSet.Augmented

namespace Augmented

-- porting note: an instance of `Subsingleton (⊤_ (Type u))` was added in
-- `CategoryTheory.Limits.Types` to ease the automation in this definition
/-- The functor which sends `[n]` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
noncomputable def standardSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where
  obj Δ :=
    { left := SSet.standardSimplex.obj Δ
      right := terminal _
      hom := { app := fun Δ' => terminal.from _ } }
  map θ :=
    { left := SSet.standardSimplex.map θ
      right := terminal.from _ }
set_option linter.uppercaseLean3 false in
#align sSet.augmented.standard_simplex SSet.Augmented.standardSimplex

end Augmented

end SSet
