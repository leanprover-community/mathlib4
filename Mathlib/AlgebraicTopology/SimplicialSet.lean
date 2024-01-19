/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
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

namespace HomMk₃

variable {i : Fin 4}
lemma range_include01_exclude2 {X : SimplexCategoryᵒᵖ } ( α : Λ[3,i].obj X)
    (include_0 : ¬∀ k, α.val.down.toOrderHom k ≠ (δ i).toOrderHom  0)
    (include_1 : ¬∀ k, α.val.down.toOrderHom k ≠ (δ i).toOrderHom  1 ) :
    ∀ k,  α.val.down.toOrderHom k ≠ (δ i).toOrderHom  2 := by
  let hα :=  (α.prop)∘Set.eq_univ_iff_forall.mpr
  simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
    not_forall, not_or, not_exists] at hα
  obtain ⟨x1,hx1⟩ :=  hα
  intro x
  by_contra hXp
  fin_cases x1
  all_goals fin_cases i
  all_goals tauto

variable {i1 i2 : Fin 3} (i1_lt_i2: i1 < i2)

lemma degeneracy_relation :
    (σ (Fin.predAbove 0 ((δ i).toOrderHom i2))
    ≫ σ (Fin.predAbove 0 (Fin.predAbove 2 ((δ i).toOrderHom i1))) )
    = σ ( (Fin.predAbove 0 ((δ i).toOrderHom i1)))
    ≫ σ (Fin.predAbove 0 (Fin.predAbove 0 ((δ i).toOrderHom i2))) := by
  apply Hom.ext'
  rw [← DFunLike.coe_fn_eq]
  rw [← OrderHom.toFun_eq_coe]
  fin_cases i1,i2
  case  a.head.tail.head | a.head.tail.tail.head | a.tail.head.tail.tail.head =>
    funext x
    fin_cases i
    all_goals fin_cases x
    all_goals rfl
  all_goals {
      rw [Fin.lt_def] at i1_lt_i2
      simp at i1_lt_i2
    }

variable {X Y :SimplexCategoryᵒᵖ}
variable {α : Λ[3,i].obj X } {φ: ([len Y.unop]: SimplexCategory)⟶ [len X.unop]}
variable (exclude_i1 :  ∀ k, (φ ≫ α.val.down).toOrderHom k ≠ (δ i).toOrderHom i1)
variable (exclude_i2 :  ∀ k, (φ ≫ α.val.down).toOrderHom k ≠ (δ i).toOrderHom i2)

lemma factorization_of_φ_comp_α_i1:
    (factor_δ (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i1))
    (Fin.predAbove 0 ((δ i).toOrderHom i2))) ≫ δ (Fin.predAbove 0 ((δ i).toOrderHom i2))
    = factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i1) := by
  fin_cases i1
  all_goals fin_cases i2
  case' head.tail.head           => let i1':Fin 3 := 0
  case' head.tail.tail.head      => let i1':Fin 3 := 0
  case' tail.head.tail.tail.head => let i1':Fin 3 := 1
  case head.tail.head | head.tail.tail.head | tail.head.tail.tail.head =>
    let hα :=  (α.prop)∘Set.eq_univ_iff_forall.mpr
    simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
    not_forall, not_or, not_exists] at hα
    obtain ⟨x1,hx1⟩ :=  hα
    apply factor_δ_spec
    intro x
    by_contra hXp
    apply (congrArg ((δ ((δ i).toOrderHom i1')).toOrderHom )) at hXp
    change  ((factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i1'))≫δ _ ).toOrderHom x = _ at hXp
    rw [(factor_δ_spec (φ ≫ α.val.down) ((δ i).toOrderHom i1') exclude_i1 )] at hXp
    fin_cases x1
    all_goals fin_cases i
    all_goals tauto
  all_goals {
    rw [Fin.lt_def] at i1_lt_i2
    simp at i1_lt_i2
  }

lemma factorization_of_φ_comp_α_i2:
    (factor_δ (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i2))
    (Fin.predAbove 2 ((δ i).toOrderHom i1)))≫ δ (Fin.predAbove 2 ((δ i).toOrderHom i1))
    = (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i2)) := by
  fin_cases i1
  all_goals fin_cases i2
  case' head.tail.head           => let i2':Fin 3 := 1
  case' head.tail.tail.head      => let i2':Fin 3 := 2
  case' tail.head.tail.tail.head => let i2':Fin 3 := 2
  case head.tail.head | head.tail.tail.head | tail.head.tail.tail.head =>
      let hα :=  (α.prop)∘Set.eq_univ_iff_forall.mpr
      simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
      not_forall, not_or, not_exists] at hα
      obtain ⟨x1,hx1⟩ :=  hα
      apply factor_δ_spec
      intro x
      by_contra hXp
      apply (congrArg ((δ ((δ i).toOrderHom i2')).toOrderHom )) at hXp
      change  ((factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i2'))≫δ _).toOrderHom x = _ at hXp
      rw [factor_δ_spec (φ ≫ α.val.down) ((δ i).toOrderHom i2')  exclude_i2] at hXp
      fin_cases x1
      all_goals fin_cases i
      all_goals tauto
  all_goals {
      rw [Fin.lt_def] at i1_lt_i2
      simp at i1_lt_i2
    }

lemma naturality_lt {S : SSet}
    {face_map : Fin (3) →  S _[2]}
    (hface : (i1 : Fin (3))→ (i2 : Fin (3)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    = S.map (δ (Fin.predAbove 2 ((δ i).toOrderHom i1))).op (face_map i2) ):
    S.map ( ((Λ[3, i].map φ.op α).val.down) ≫ σ  ( Fin.predAbove 0 ((δ i).toOrderHom i1))).op
    (face_map i1)=S.map φ.op (S.map ( (α.val.down)≫  σ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op
    (face_map i2))  := by
  let α' :([(unop X).len]: SimplexCategory)⟶  [3]:= α.val.down
  change S.map (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i1)).op (face_map i1)
             = (S.map (factor_δ α' ((δ i).toOrderHom i2)).op ≫ S.map φ.op) (face_map i2)
  rw [← S.map_comp, ← op_comp]
  change S.map (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i1)).op (face_map i1)
            = (S.map (factor_δ (φ ≫ α.val.down) ((δ i).toOrderHom i2)).op ) (face_map i2)
  rw [← (factorization_of_φ_comp_α_i1 i1_lt_i2 exclude_i1 exclude_i2)]
  rw [← (factorization_of_φ_comp_α_i2 i1_lt_i2 exclude_i1 exclude_i2)]
  rw [op_comp,S.map_comp,op_comp,S.map_comp,types_comp_apply,types_comp_apply]
  rw [(hface i1 i2 i1_lt_i2)]
  change _ = S.map ((φ ≫ α.val.down)≫(σ (Fin.predAbove 0 ((δ i).toOrderHom i2))
                ≫ σ (Fin.predAbove 0 (Fin.predAbove 2 ((δ i).toOrderHom i1))) ) ).op _
  rw [degeneracy_relation i1_lt_i2]
  rfl
end HomMk₃

/-- The horn `Λ[3,i]⟶ S` constructed from the image of the appropriate to 2-simplies and
the appropriate compatiblity conditions on their faces. -/
def homMk₃ {S : SSet}  (i: Fin 4)  (face_map : Fin (3) →  S _[2])
    (hface : (i1 : Fin (3))→ (i2 : Fin (3)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    =S.map (δ (Fin.predAbove 2 ((δ i).toOrderHom i1))).op (face_map i2) ) : Λ[3,i]⟶ S where
  app X α := by
    let α' :([(unop X).len]: SimplexCategory)⟶  [3]:= α.val.down
    let id: Fin 3:= if ∀ k, α.1.down.toOrderHom k ≠  (δ i).toOrderHom 0 then 0
                    else
                      if ∀ k, α.1.down.toOrderHom k ≠ (δ i).toOrderHom 1 then 1
                      else 2
    exact S.map (factor_δ α'  ((δ i).toOrderHom  id)).op (face_map id)
  naturality X Y φ' := by
     funext α
     simp only [mk_len, op_unop, len_mk, types_comp_apply]
     split
     all_goals split
     all_goals rename_i h1 h2
     all_goals try split
     all_goals try split
     case inl.inl | inr.inl.inr.inl | inr.inr.inr.inr  =>
         rw  [← (types_comp_apply (S.map _) (S.map _)),← S.map_comp]
         rfl
     all_goals rename_i h3
     case inr.inl.inl | inr.inr.inl  =>
         exact False.elim (h1 (fun k => h3 (φ'.unop.toOrderHom k)))
     case inr.inr.inr.inl =>
        exact False.elim (h2 (fun k => h3 (φ'.unop.toOrderHom k)))
     all_goals
        apply HomMk₃.naturality_lt
        · rw [Fin.lt_def]
          simp
        · assumption
        · try exact fun k => (HomMk₃.range_include01_exclude2 α h2 h3) (φ'.unop.toOrderHom k)
          try exact fun k => h3 (φ'.unop.toOrderHom k)
          try rename_i  h4;
          try exact fun k => (HomMk₃.range_include01_exclude2 α h4 h3) (φ'.unop.toOrderHom k)
        · exact hface
def face' {n : ℕ} (i  : Fin (n+2)) (j: Fin (n+1)) : (Λ[n+1, i]: SSet) _[n] :=by
    refine face i ((δ i).toOrderHom j) ?_
    · unfold δ
      simp
      unfold Fin.succAbove
      by_contra h
      aesop_split_hyps
      · aesop_subst h
        simp_all only [lt_self_iff_false]
      · aesop_subst h
        simp_all only [Fin.castSucc_lt_succ_iff, le_refl, not_true_eq_false]

lemma face_eq_face' {n : ℕ} (i  : Fin (n+2)) (j: Fin (n+2)) (h: j≠i): face i j h
=face' i (Fin.predAbove (Fin.predAbove 0 i) j) := by
  unfold face'
  congr
  change j = (σ (Fin.predAbove 0 i) ≫ δ i).toOrderHom  (j)
  change j = (Fin.succAbove i) (Fin.predAbove (Fin.predAbove 0 i) j)
  have ht : (Fin.predAbove 0 i).val= i.val -1 := by
        unfold Fin.predAbove
        split
        · rfl
        · aesop
  by_cases h1 : j ≤ Fin.castSucc (Fin.predAbove 0 i)
  · rw [Fin.predAbove_below (Fin.predAbove 0 i) j h1]
    unfold Fin.succAbove
    split
    · rfl
    · rename_i h2
      change ¬ j.val < i.val at h2
      change j.val ≤ (Fin.predAbove 0 i).val at h1
      rw [ht] at h1
      exfalso
      apply h ∘ (Fin.eq_iff_veq j i).mpr
      apply le_antisymm
      · apply le_trans h1
        exact Nat.sub_le (↑i) 1
      · exact Nat.not_lt.mp h2
  · rw [not_le] at h1
    rw [Fin.predAbove_above (Fin.predAbove 0 i) j h1]
    unfold Fin.succAbove
    split
    · rename_i h2
      change j.val -1 < i.val at h2
      change (Fin.predAbove 0 i).val < j.val at h1
      rw [ht] at h1
      exfalso
      apply h ∘ (Fin.eq_iff_veq j i).mpr
      apply le_antisymm
      · exact Nat.le_of_pred_lt h2
      · contrapose! h1
        exact Nat.le_pred_of_lt h1
    · simp_all only [ne_eq, not_lt, Fin.succ_pred]



lemma face'_factor {n : ℕ} (i: Fin (n+2)) (j: Fin (n+1)) : factor_δ (face'.{u} i j).val.down ((δ i).toOrderHom j)= 𝟙 ([n]:SimplexCategory):=by
        change δ ((δ i).toOrderHom j)≫  (σ (Fin.predAbove 0 ((δ i).toOrderHom j)))=_
        let l' : Fin (n+2) := ((δ i).toOrderHom j)
        change δ l' ≫  (σ (Fin.predAbove 0 l'))=_
        unfold Fin.predAbove
        split
        · rename_i h1
          let l'' := Fin.pred l' (@Fin.predAbove.proof_1 (n + 1) 0 l' h1)
          rw [show δ l' = δ (Fin.succ l'') by aesop]
          exact δ_comp_σ_succ
        · exact δ_comp_σ_self

lemma homMk₃_face {S:SSet} (i: Fin 4) (j : Fin 3) (face_map : Fin (3) →  S _[2])
    (hface : (i1 : Fin (3))→ (i2 : Fin (3)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (face_map i1)
    =S.map (δ (Fin.predAbove 2 ((δ i).toOrderHom i1))).op (face_map i2) ) :
    (homMk₃ i face_map hface).app (op [2]) (face'.{u} i j)= face_map j:= by
      let id :Fin 3:= if ∀ k, (δ ((δ i).toOrderHom j)).toOrderHom k ≠  (δ i).toOrderHom 0 then 0
                    else
                      if ∀ k, (δ ((δ i).toOrderHom j)).toOrderHom k  ≠ (δ i).toOrderHom 1 then 1
                      else 2
      have hid : id = j := by
          fin_cases j
          · have Y0 (i: Fin 4)  :  ∀ k, (δ ((δ i).toOrderHom 0)).toOrderHom k ≠  (δ i).toOrderHom 0  := by
               fin_cases i <;> {intro k;fin_cases k <;> decide}
            simp
            exact fun x h ↦ (Y0 i x h).elim
          ·  have N1 (i: Fin 4)  : ¬ ∀ k, (δ ((δ i).toOrderHom 1)).toOrderHom k ≠  (δ i).toOrderHom 0  := by
              fin_cases i <;> decide
             have Y1 (i: Fin 4)  :  ∀ k, (δ ((δ i).toOrderHom 1)).toOrderHom k ≠  (δ i).toOrderHom 1  := by
                fin_cases i <;> {intro k;fin_cases k <;> decide}
             simp
             split
             · rename_i h2
               exact (N1 i h2).elim
             · split
               · rfl
               · rename_i h2
                 exact (h2 (Y1 i)).elim
          · have N2 (i: Fin 4)  : ¬ ∀ k, (δ ((δ i).toOrderHom 2)).toOrderHom k ≠  (δ i).toOrderHom 0  := by
               fin_cases i <;> decide
            have N22 (i: Fin 4)  : ¬ ∀ k, (δ ((δ i).toOrderHom 2)).toOrderHom k ≠  (δ i).toOrderHom 1  := by
              fin_cases i <;> decide
            simp
            split
            · rename_i h2
              exact (N2 i h2).elim
            · split
              · rename_i h2
                exact (N22 i h2).elim
              · rfl
      have hte : (homMk₃ i face_map hface).app (op [2]) (face' i j) =  S.map (factor_δ (face'.{u} i j).val.down  ((δ i).toOrderHom  j)).op (face_map j):= by
          nth_rewrite 4 [← hid]
          nth_rewrite 3 [← hid]
          unfold homMk₃
          simp
          rfl
      rw[hte,face'_factor,op_id, S.map_id]
      rfl

lemma homMk₃_surjective {S:SSet} (i: Fin 4) (f : Λ[3,i] ⟶ S)   : ∃ (fa: Fin (3)→S _[2])
    (hfa : (i1 : Fin (3))→ (i2 : Fin (3)) → (i1< i2) →
    S.map (δ (Fin.predAbove 0 ((δ i).toOrderHom i2))).op (fa i1)
    =S.map (δ (Fin.predAbove 2 ((δ i).toOrderHom i1))).op (fa i2) ), f=homMk₃ i fa hfa :=by
    refine ⟨fun (j: Fin 3) =>  f.app (op [2]) (face' i j),?_,?_⟩
    · intro i1 i2 i1_lt_i2
      simp
      rw [← (types_comp_apply (f.app _) (S.map _))]
      rw [← (types_comp_apply (f.app _) (S.map _))]
      rw [← f.naturality,← f.naturality]
      rw [types_comp_apply,types_comp_apply]
      apply congrArg
      apply Subtype.ext
      unfold horn
      simp
      rw [standardSimplex.map_apply,standardSimplex.map_apply]
      simp
      apply Hom.ext'
      rw [← DFunLike.coe_fn_eq]
      rw [← OrderHom.toFun_eq_coe]
      unfold face' face
      change
         Fin.succAbove (Fin.succAbove i i1) ∘ Fin.succAbove (Fin.predAbove 0 (Fin.succAbove i i2))
         =
          Fin.succAbove (Fin.succAbove i i2) ∘ Fin.succAbove (Fin.predAbove 2 (Fin.succAbove i i1))
      fin_cases i1, i2
      case  head.tail.head | head.tail.tail.head | tail.head.tail.tail.head =>
        funext x
        fin_cases i
        all_goals fin_cases x
        all_goals rfl
      all_goals {
          rw [Fin.lt_def] at i1_lt_i2
          simp at i1_lt_i2
        }
    · apply horn.hom_ext
      intro j h
      rw [face_eq_face' i j h]
      rw [homMk₃_face]


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
