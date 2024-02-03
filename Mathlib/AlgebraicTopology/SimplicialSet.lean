/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Joseph Tooby-Smith, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialObject
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
@[inherit_doc SSet.standardSimplex]
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

namespace SimplexImage
variable {X : SimplexCategoryᵒᵖ } {n: ℕ }{i : Fin (n+3)} ( α : Λ[n+2,i].obj X)

lemma preimage_δ_exe (x : Fin (n+3)) (hx : x ≠ i) : (Hom.toOrderHom (δ i))
    ((Fin.predAbove (Fin.predAbove 0 i)) x)=x := by
        change Fin.succAbove i ((Fin.predAbove (Fin.predAbove 0 i)) x) =_
        by_cases hi: i ≠ 0
        · rw [Fin.predAbove_zero hi,Fin.eq_iff_veq]
          unfold Fin.succAbove Fin.predAbove
          split <;> split <;> rename_i  h2 h3
          any_goals simp only [Fin.succ_pred,Fin.castSucc_castPred]
          all_goals rw [Fin.lt_def] at h2
          all_goals simp only [Fin.coe_castSucc, Fin.coe_pred, not_lt, Fin.castSucc_castPred]
               at h2 h3
          · rw [ne_eq,Fin.eq_iff_veq] at hx
            exact (hx (Nat.le_antisymm (Nat.le_of_pred_lt h3) (Nat.le_of_pred_lt h2))).elim
          · have h4: i.val ≤ i.val -1 := Nat.le_trans h3 h2
            rw [ne_eq,Fin.eq_iff_veq] at hi
            contrapose! h4
            apply Nat.pred_lt_self
            exact Nat.pos_of_ne_zero hi
        · simp only [ne_eq, not_not] at hi
          rw [hi,Fin.eq_iff_veq,Fin.zero_succAbove,Fin.val_succ,
            show Fin.predAbove (0: Fin (n+2)) 0=0 from rfl]
          unfold Fin.predAbove
          split <;> rename_i h2
          · exact Nat.succ_pred_eq_of_pos h2
          · rw [Fin.castSucc_zero, not_lt, Fin.le_zero_iff] at h2
            rw [ h2,← hi] at hx
            exact (hx rfl).elim


/--Returns the smallest `m∈ℕ` such that `(δ i).toOrderHom m` is
  not in the image of `α.1.down.toOrderHom`.-/
def filtered_set_cond : Fin (n+2) →  Prop := fun l =>
 ∀ k, α.1.down.toOrderHom k ≠ (δ i).toOrderHom l

lemma exists_some_staifying :  ∃ x, filtered_set_cond α x := by
  by_contra h
  rw [not_exists] at h
  have hα:= α.prop∘Set.eq_univ_iff_forall.mpr
  simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
          not_forall, not_or, not_exists] at hα
  obtain ⟨x, hx⟩ := hα
  rw [← (preimage_δ_exe x hx.left)] at hx
  exact h (Fin.predAbove (Fin.predAbove 0 i) x) hx.right

noncomputable instance : DecidablePred (filtered_set_cond α) := by
  exact Classical.decPred (filtered_set_cond α)

noncomputable def filtered_set : Finset (Fin (n+2)) := univ.filter (filtered_set_cond α)

lemma filtered_setNonEmpty :  (filtered_set α).Nonempty := by
  unfold filtered_set
  obtain ⟨x, hx⟩ := exists_some_staifying α
  use x
  simp only [mem_filter,mem_univ, true_and]
  exact hx

noncomputable def firstEdgeNIImage : Fin (n+2) := min' (filtered_set α) (filtered_setNonEmpty α)



namespace  firstEdgeNIImage
lemma self_cond: ∀ k, α.1.down.toOrderHom k ≠ (δ i).toOrderHom (firstEdgeNIImage α) := by
   have  ht:= min'_mem (filtered_set α) (filtered_setNonEmpty α)
   unfold filtered_set at ht
   rw [mem_filter] at ht
   exact ht.right

lemma le_cond (j: Fin (n+2)) : (∀ l < j, ¬  ∀  k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom l ) → (j≤(firstEdgeNIImage α)):= by
      intro h
      by_contra hn
      have ht: firstEdgeNIImage α < j := Fin.not_le.mp hn
      apply h at ht
      exact ht (self_cond α)

lemma ge_cond (j: Fin (n+2)) : ( ∀ k, α.1.down.toOrderHom k ≠
    (δ i).toOrderHom j )→ ((firstEdgeNIImage α)≤ j):= by
      intro h
      refine min'_le (filtered_set α) j ?_
      rw [filtered_set,mem_filter,filtered_set_cond]
      simp only [mem_univ, len_mk, yoneda_obj_obj, ne_eq, true_and]
      exact fun k ↦ h k

lemma of_face (j : Fin (n+3)) (h: j ≠ i) : firstEdgeNIImage (face.{u} i j h)  =
    (Fin.predAbove (Fin.predAbove 0 i)) j := by
    refine le_antisymm ?_ ?_
    refine ge_cond (face i j h)  ((Fin.predAbove (Fin.predAbove 0 i)) j) ?_
    by_contra h1
    simp only [not_forall,ne_eq, not_not] at h1
    apply Fin.exists_succAbove_eq_iff.mp at h1
    exact h1 (preimage_δ_exe j h)
    refine le_cond (face i j h) ((Fin.predAbove (Fin.predAbove 0 i)) j) ?_
    intro l hl
    refine (?_ :∀ l ,( l ≠ j)→  ¬ ∀  k, (face.{u} i j h).1.down.toOrderHom k ≠ l )
     ((Hom.toOrderHom (δ i)) l) (Fin.ne_of_lt ?_)
    intro l hl
    simp only [not_forall,ne_eq, not_not]
    exact Fin.exists_succAbove_eq hl
    rw  [← (preimage_δ_exe j h)]
    exact Fin.strictMono_succAbove i hl

variable {Y : SimplexCategoryᵒᵖ } (φ':X⟶ Y)
lemma congr_cond : ∀ k, (φ'.unop ≫ α.1.down).toOrderHom k ≠ (δ i).toOrderHom
    (firstEdgeNIImage α):=
    fun k ↦ self_cond α ((Hom.toOrderHom φ'.unop) k)
lemma congr_le: firstEdgeNIImage (Λ[n+2,i].map φ' α) ≤  firstEdgeNIImage α:=
    ge_cond (Λ[n+2, i].map φ' α) (firstEdgeNIImage α)
      (fun k ↦ self_cond α ((Hom.toOrderHom φ'.unop) k) )
end firstEdgeNIImage
end SimplexImage


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
    (f2)) := by
  let α' :([(unop X).len]: SimplexCategory)⟶  [n+2]:= α.val.down
  change S.map (factor_δ (φ ≫ α.val.down) i1).op (_)
             = (S.map (factor_δ α' i2).op ≫ S.map φ.op) (_)
  rw [← S.map_comp, ← op_comp]
  change _= (S.map (factor_δ (φ ≫ α.val.down) i2).op ) (_)
  rw [← (factor_δ_comp_spec_lt i1_lt_i2 exclude_i1 exclude_i2),← (factor_δ_comp_spec_lt' i1_lt_i2
      exclude_i1 exclude_i2),op_comp,S.map_comp,op_comp,S.map_comp,types_comp_apply,
      types_comp_apply,hface,← (factor_δ_comp_lt _ _ _ i1_lt_i2)]

open SimplexImage in
/-- The horn `Λ[n+2,i]⟶ S` constructed from the image of the appropriate to (n+1)-simplies and
the appropriate compatiblity conditions on their faces. -/
noncomputable def homMk {S : SSet}  {n:ℕ} (i: Fin (n+3))  (face_map : Fin (n+2) →  S _[n+1])
    (hface : (i1 : Fin (n+2))→ (i2 : Fin (n+2)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    =S.map (δ (Fin.predAbove (Fin.last (n+1)) ((δ i).toOrderHom i1))).op (face_map i2) ):
    Λ[n+2,i]⟶ S where
  app X α := by
    let α' :([(unop X).len]: SimplexCategory)⟶  [n+2]:= α.1.down
    let id:= firstEdgeNIImage α
    exact S.map (factor_δ α' ((δ i).toOrderHom  (id))).op (face_map (id))
  naturality X Y φ' := by
     funext α
     let φ: ([len Y.unop]: SimplexCategory)⟶ [len X.unop] := φ'.unop
     change S.map (factor_δ _ ((δ i).toOrderHom _)).op (face_map _)
        = S.map φ.op (S.map (factor_δ _ (((δ i).toOrderHom _))).op (face_map _))
     cases lt_or_eq_of_le (firstEdgeNIImage.congr_le α φ') with
     | inl h =>
          apply naturality_lt
          · exact  Fin.strictMono_succAbove i h
          · exact firstEdgeNIImage.self_cond (Λ[n+2, i].map _ α)
          · exact firstEdgeNIImage.congr_cond α _
          · exact hface (firstEdgeNIImage (Λ[n+2, i].map φ' α))  (firstEdgeNIImage α) h
     | inr h => rw [← h,← types_comp_apply (S.map _) (S.map _),← S.map_comp, ← op_comp]
                rfl

section homMk
variable {S : SSet}  {n:ℕ} (i: Fin (n+3)) (face_map : Fin (n+2) →  S _[n+1])
variable (hface : (i1 : Fin (n+2))→ (i2 : Fin (n+2)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    =S.map (δ (Fin.predAbove (Fin.last (n+1)) ((δ i).toOrderHom i1))).op (face_map i2) )

lemma homMk_face (j: Fin (n+3)) (hij : j≠ i):
    (homMk i face_map hface).app (op [n+1]) (face.{u} i j hij) =
    face_map ((Fin.predAbove (Fin.predAbove 0 i)) j):=by
     change S.map (factor_δ (face.{u} i j hij).1.down
      ((δ i).toOrderHom  (SimplexImage.firstEdgeNIImage (face.{u} i j hij)) )).op
       (face_map (SimplexImage.firstEdgeNIImage (face.{u} i j hij)) )=_
     have hfac : factor_δ ((face.{u} i j hij)).1.down j = 𝟙 ([n+1]:SimplexCategory):= by
        change (δ j≫ σ (Fin.predAbove 0 j)) =_
        by_cases hj: j=0
        · rw [hj]
          exact δ_comp_σ_self' rfl
        · rw [Fin.predAbove_zero hj]
          exact δ_comp_σ_succ' j (Fin.pred j hj)
            ((Fin.pred_eq_iff_eq_succ j hj (Fin.pred j hj)).mp rfl)
     rw [SimplexImage.firstEdgeNIImage.of_face.{u},SimplexImage.preimage_δ_exe j hij,hfac,op_id,
      S.map_id]
     rfl

def hornFaceMap {S :SSet} {n: ℕ } {i : Fin (n+3)} (f : Λ[n+2,i]⟶ S)  (k : Fin (n+2)): S _[n+1]:=
  f.app (op [n+1]) (face i  ((δ i).toOrderHom k) (Fin.exists_succAbove_eq_iff.mp
     (Exists.intro k rfl) ))

lemma hornFaceMap_cond {S :SSet} {n: ℕ } {i : Fin (n+3)} (f : Λ[n+2,i]⟶ S) (i1 : Fin (n+2))
    (i2 : Fin (n+2)) (h: i1< i2) :
   S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (hornFaceMap f i1)
        =S.map (δ (Fin.predAbove (Fin.last (n+1)) ((δ i).toOrderHom i1))).op (hornFaceMap f i2):=by
      dsimp
      unfold hornFaceMap
      rw [← (types_comp_apply (f.app _) (S.map _)),← (types_comp_apply (f.app _) (S.map _))]
      rw [← f.naturality,← f.naturality,types_comp_apply,types_comp_apply]
      apply congrArg
      apply Subtype.ext
      apply congrArg (⇑(standardSimplex.objEquiv [n + 2] (op [n])).symm)
      let i2o:= Fin.succAbove i i2
      let i1o:=Fin.succAbove i i1
      change δ (Fin.predAbove 0 i2o)≫ δ i1o=δ (Fin.predAbove (Fin.last (n + 1)) i1o)≫ δ i2o
      have hi2o : i1o<i2o:= Fin.strictMono_succAbove i  h
      have hi2: i2o≠ 0 := by
          contrapose! hi2o
          simp_all only [Fin.le_zero_iff, Fin.zero_le]
      have hi1: i1o≠ Fin.last (n+1+1) := by
            simp_all only [ne_eq]
            apply Not.intro
            intro a
            rw [a] at hi2o
            exact (Fin.not_le.mpr hi2o) (Fin.le_last i2o)
      rw [Fin.predAbove_zero hi2,Fin.predAbove_last_of_ne_last hi1]
      rw [congrArg δ ((Fin.pred_eq_iff_eq_succ i2o hi2 (Fin.pred i2o hi2)).mp rfl),
      congrArg δ (by rfl : i1o=(Fin.castPred i1o hi1).castSucc),δ_comp_δ]
      exact (Fin.le_pred_iff hi2).mpr hi2o

lemma homMk_surjective {S :SSet} {n: ℕ } (i : Fin (n+3)) (f : Λ[n+2,i]⟶ S) :
    ∃ (fm: Fin (n+2) →  S _[n+1] ) (hf: (i1 : Fin (n+2))→ (i2 : Fin (n+2)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (fm i1)
    =S.map (δ (Fin.predAbove (Fin.last (n+1)) ((δ i).toOrderHom i1))).op (fm i2) ),
    (homMk i fm hf) = f := by
      use hornFaceMap f
      use hornFaceMap_cond f
      apply horn.hom_ext
      unfold hornFaceMap
      intro j hij
      rw [homMk_face]
      dsimp
      apply congrArg
      congr 1
      exact SimplexImage.preimage_δ_exe j hij


lemma homMk_lift_face (j : Fin (n+2)) (lift : Δ[n+2]⟶ S)
    (hlift: (homMk i face_map hface)  = hornInclusion (n+2) i ≫ lift):
    S.map (δ ((δ i).toOrderHom j)).op (lift.app (op [n+2])
    ((standardSimplex.objEquiv ([n+2]) (op [n+2])).invFun  (𝟙 ([n+2]:SimplexCategory))))
    =face_map j:= by
       rw [← (types_comp_apply (lift.app _) (S.map _) ),← lift.naturality,types_comp_apply]
       have hij: ((δ i).toOrderHom j) ≠ i := by
          by_contra hkc
          exact Fin.exists_succAbove_eq_iff.mp (Exists.intro j hkc) rfl
       rw [(Fin.succAbove_right_inj i).mp ((SimplexImage.preimage_δ_exe
        ((Hom.toOrderHom (δ i)) j) hij).symm),← (homMk_face i face_map hface ((δ i).toOrderHom j)
        hij ),hlift,NatTrans.comp_app,types_comp_apply]
       apply congrArg
       rw [face,standardSimplex.map_apply]
       congr
       change _≫ 𝟙 ([n + 2]: SimplexCategory)=_
       rw [Category.comp_id]
       change  (δ ((Hom.toOrderHom (δ i)) (Fin.predAbove (Fin.predAbove 0 i)
          ((Hom.toOrderHom (δ i)) j))))=_
       congr
       exact id ((Fin.succAbove_right_inj i).mp ((SimplexImage.preimage_δ_exe
        ((Hom.toOrderHom (δ i)) j) hij).symm)).symm
end homMk

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
