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
import Mathlib.Data.Fin.OrderHom
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

-- Porting note (#10756): added an `ext` lemma.
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

/--The face of the standard simplex labelled by `j`. -/
def face {n : ℕ} (j : Fin (n+2)) : Δ[n+1] _[n] :=
  (standardSimplex.objEquiv _ _).symm (SimplexCategory.δ j)

/--Given a morphisms `Δ[n+1] ⟶ S` the image of the `ith` face of `Δ[n]`.-/
def faceInc {S : SSet} {n : ℕ} (f : Δ[n+1] ⟶ S) (j : Fin (n+2)) :  S _[n] :=
  f.app (op [n]) (face j)
/--A proposition satified by morphisms `Δ[n+1] ⟶ S` relating to subfaces of faces.-/
def subfaceCond {S : SSet} {n : ℕ} (f : Fin (n+3) → S _[n+1]) : Prop := by
  refine ∀ (i1 i2: Fin (n+3)) (i1_lt_i2: i1 < i2),
    S.δ (i2.pred ?_ ) (f i1) = S.δ (i1.castPred ?_ ) (f i2)
  exact Fin.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt i1_lt_i2)
  exact Fin.ne_of_lt (gt_of_ge_of_gt i2.le_last i1_lt_i2)

theorem faceInc_subfaceCond {S : SSet} {n : ℕ} (f : Δ[n+2] ⟶ S) :
    subfaceCond (faceInc f) := by
  intro i1 i2 i1_lt_i2
  rw [faceInc,faceInc]
  rw [← (types_comp_apply (f.app _) (S.δ _)),← (types_comp_apply (f.app _) (S.δ _))]
  repeat rw [show SimplicialObject.δ S _=S.map _ from rfl]
  rw [← f.naturality,← f.naturality,types_comp_apply,types_comp_apply]
  apply congrArg
  apply congrArg (⇑(standardSimplex.objEquiv [n + 2] (op [n])).symm)
  change δ (i2.pred _) ≫ δ i1=δ (i1.castPred _)≫ δ (i2)
  rw [congrArg δ ((Fin.pred_eq_iff_eq_succ i2 _ (i2.pred _)).mp rfl),
  congrArg δ (by rfl : i1=(i1.castPred _).castSucc),δ_comp_δ]
  exact (Fin.le_pred_iff _).mpr i1_lt_i2

/--The proposition `subfaceCond` in the `n=2` case.-/
lemma subfaceCond₂ {S : SSet}  (f : Fin (3) → S _[1]) : subfaceCond f ↔
    S.δ 0 (f 0) = S.δ 0 (f 1) ∧  S.δ 1 (f 0) = S.δ 0 (f 2) ∧  S.δ 1 (f 1) = S.δ 1 (f 2) := by
  simp only [subfaceCond, Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff, Fin.pred_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT, forall_true_left,
    lt_self_iff_false, Fin.castPred_one, and_self]
  exact and_assoc

/--The proposition `subfaceCond` in the `n=3` case.-/
lemma subfaceCond₃ {S : SSet}  (f : Fin (4) → S _[2]) : subfaceCond f ↔
    S.δ 0 (f 0) = S.δ 0 (f 1) ∧  S.δ 1 (f 0) = S.δ 0 (f 2) ∧  S.δ 2 (f 0) = S.δ 0 (f 3) ∧
    S.δ 1 (f 1) = S.δ 1 (f 2) ∧  S.δ 2 (f 1) = S.δ 1 (f 3) ∧  S.δ 2 (f 2) = S.δ 2 (f 3) := by
  simp only [subfaceCond, Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff, Fin.pred_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT, forall_true_left,
    Fin.succ_pos, Fin.succ_lt_succ_iff, lt_self_iff_false, Fin.castPred_one]
  apply Iff.intro
  · intro h
    rcases h with ⟨h1, h2, h3⟩
    simp_all only [true_and]
    repeat (any_goals apply And.intro)
    all_goals apply Eq.refl
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
    repeat any_goals apply And.intro
    exact h1
    exact h2
    exact h3
    exact h4
    exact h5
    exact h6
    intro hi
    exact ((Fin.not_lt.mpr (Nat.le.step (Nat.le.step Nat.le.refl))) hi).elim
    intro hi
    exact ((Fin.not_lt.mpr (Nat.le.step Nat.le.refl)) hi).elim




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

/--The condition on a `m ∈ Fin (n+2)` such that `(δ i).toOrderHom m` is
  not in the image of `α.1.down.toOrderHom`.-/
def notInImage : Fin (n+2) → Prop := fun l => ∀ k, α.1.down.toOrderHom k ≠ (δ i).toOrderHom l

noncomputable instance : DecidablePred (notInImage α) :=
  Classical.decPred (notInImage α)

/--For the face simplex `notInImage _ k` is `true` if and only if
   `k = ((Fin.predAbove 0 i).predAbove j)` -/
lemma notInImage_face (j : Fin (n+3)) (h: j ≠ i):
    notInImage (face.{u} i j h) k ↔ k = ((Fin.predAbove 0 i).predAbove j) := by
  unfold notInImage
  rw [← not_exists, show (Hom.toOrderHom (δ i)) k =i.succAbove k from rfl]
  change (¬∃ x, Fin.succAbove j x = Fin.succAbove i k ) ↔ _
  rw [Fin.exists_succAbove_eq_iff]
  nth_rewrite 1 [← Fin.succAbove_predAbove_predAbove 0 j h]
  simp only [ne_eq, not_not]
  exact Fin.succAbove_right_inj i

/--For any simplex `α` there is some `k` such that `notInImage α k` is true. -/
lemma notInImage_isSome  : (Fin.find (notInImage α)).isSome  := by
  refine Fin.isSome_find_iff.mpr ?_
  by_contra h
  rw [not_exists] at h
  have hα:= α.prop∘Set.eq_univ_iff_forall.mpr
  simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, Set.mem_range, imp_false,
          not_forall, not_or, not_exists] at hα
  obtain ⟨x, hx⟩ := hα
  rw [← (Fin.succAbove_predAbove_predAbove _ _ hx.left)] at hx
  exact h (Fin.predAbove (Fin.predAbove 0 i) x) hx.right


/--Returns the smallest `m ∈ Fin (n+2)` such that `notInImage α m = true`.``.-/
noncomputable def minNotInImage : Fin (n+2) :=
  Option.get (Fin.find (notInImage α)) (notInImage_isSome α)


lemma minNotInImage_mem : minNotInImage α ∈ Fin.find (notInImage α) :=
Option.get_mem (notInImage_isSome α)


/--The value of `minNotInImage` for a face simplex is
`(Fin.predAbove 0 i).predAbove j`-/
lemma minNotInImage_face (j : Fin (n+3)) (h: j ≠ i) : minNotInImage (face.{u} i j h)  =
    (Fin.predAbove 0 i).predAbove j := by
  rw [← Option.some_inj]
  rw [← show Fin.find (notInImage (face.{u} i j h)) = some (minNotInImage (face.{u} i j h) )
  from Option.eq_some_of_isSome (notInImage_isSome (face i j h))]
  rw [Fin.find_eq_some_iff,notInImage_face]
  apply And.intro
  rfl
  intro k h1
  rw [notInImage_face] at h1
  rw [h1]

end SimplexImage

/-- We say a map `f : Fin (n+2) →  S _[n+1]` is a face map for `i: Fin (n+3)`
if for `i1<i2`, the the  `(i.succAbove i2)-1`th face of `f i1` agrees with the
`(i.succAbove i1)`th face of `f i2`.
-/
def isFaceMap {S : SSet}  {n:ℕ} (i: Fin (n+3))  (f : Fin (n+2) →  S _[n+1]): Prop :=by
  refine ∀ (i1 i2: Fin (n+2)) (i1_lt_i2: i1 < i2),
   S.δ ((i.succAbove i2).pred ?_ ) (f i1) = S.δ ((i.succAbove i1).castPred ?_ ) (f i2)
  exact (Fin.succAbove_ne_zero' (Fin.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt i1_lt_i2) ))
  exact Fin.ne_of_lt (gt_of_ge_of_gt (Fin.succAbove i i2).le_last (i.strictMono_succAbove i1_lt_i2))

/--Given a horn `Λ[n+2,i]⟶ S` we can construct a map `Fin (n+2) →  S _[n+1]` which is a face map.-/
def hornToFaceMap {S :SSet} {n: ℕ } {i : Fin (n+3)} (f : Λ[n+2,i]⟶ S)  (k : Fin (n+2)): S _[n+1]:=
  f.app (op [n+1]) (face i  (i.succAbove k) (Fin.exists_succAbove_eq_iff.mp (Exists.intro k rfl)))

lemma hornToFaceMap_is_face_map {S :SSet} {n: ℕ } {i : Fin (n+3)} (f : Λ[n+2,i]⟶ S):
    isFaceMap i (hornToFaceMap f) :=by
  intro i1 i2 i1_lt_i2
  dsimp only [len_mk,hornToFaceMap]
  repeat rw [show SimplicialObject.δ S _=S.map _ from rfl]
  rw [← (types_comp_apply (f.app _) (S.map _)),← (types_comp_apply (f.app _) (S.map _))]
  rw [← f.naturality,← f.naturality,types_comp_apply,types_comp_apply]
  apply congrArg
  apply Subtype.ext
  apply congrArg (⇑(standardSimplex.objEquiv [n + 2] (op [n])).symm)
  let i2o:=i.succAbove i2
  let i1o:=i.succAbove i1
  change δ ((i.succAbove i2).pred _) ≫ δ i1o=δ (i1o.castPred _)≫ δ (i.succAbove i2)
  rw [congrArg δ ((Fin.pred_eq_iff_eq_succ i2o _ (i2o.pred _)).mp rfl),
  congrArg δ (by rfl : i1o=(i1o.castPred _).castSucc),δ_comp_δ]
  exact (Fin.le_pred_iff _).mpr (Fin.strictMono_succAbove i i1_lt_i2)

lemma face_to_faceMap {S :SSet} {n: ℕ } (i  j: Fin (n+3)) (hij: j ≠ i) (f : Λ[n+2,i]⟶ S):
    f.app (op [n+1]) (face i j hij) = hornToFaceMap f ((Fin.predAbove 0 i).predAbove j) := by
  unfold hornToFaceMap
  apply congrArg
  congr
  rw [Fin.succAbove_predAbove_predAbove _ _ hij]

/--For the horn `Λ[2,0]` the condition `IsFaceMap` is equivelent to `S.δ 1 (f 0) = S.δ 1 (f 1)`-/
theorem isFaceMap₂₀ {S : SSet} (f : Fin 2 →  S _[1]) :
    isFaceMap 0 f ↔ S.δ 1 (f 0) = S.δ 1 (f 1) := by
  simp only [isFaceMap, Fin.zero_succAbove, Fin.pred_succ, Fin.forall_fin_succ, Fin.not_lt_zero,
    IsEmpty.forall_iff, Fin.succ_zero_eq_one, and_true, true_and, Fin.reduceLT, Fin.castPred_one,
    forall_true_left, lt_self_iff_false, Fin.succ_one_eq_two, and_self]


/--For the horn `Λ[2,1]` the condition `IsFaceMap` is equivelent to `S.δ 1 (f 0) = S.δ 0 (f 1)`-/
theorem isFaceMap₂₁ {S : SSet} (f : Fin 2 →  S _[1]) :
    isFaceMap 1 f ↔ S.δ 1 (f 0) = S.δ 0 (f 1) := by
  simp only [isFaceMap, Fin.forall_fin_succ, Fin.not_lt_zero, ne_eq, Fin.one_eq_zero_iff, zero_add,
    OfNat.ofNat_ne_one, not_false_eq_true, Fin.succAbove_ne_zero_zero, IsEmpty.forall_iff,
    Fin.one_succAbove_succ, Fin.pred_succ, Fin.succ_zero_eq_one, and_true, true_and, Fin.reduceLT,
    forall_true_left, lt_self_iff_false, Fin.succ_one_eq_two, and_self]
  rfl

/--For the horn `Λ[2,2]` the condition `IsFaceMap` is equivelent to `S.δ 0 (f 0) = S.δ 0 (f 1)`-/
theorem isFaceMap₂₂ {S : SSet} (f : Fin 2 →  S _[1]) :
    isFaceMap 2 f ↔ S.δ 0 (f 0) = S.δ 0 (f 1) := by
  simp only [isFaceMap, Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff,
    Fin.succ_zero_eq_one, and_true, true_and, Fin.reduceLT, forall_true_left, lt_self_iff_false,
    and_self]
  rfl


/--For the horn `Λ[3,0]` the condition `IsFaceMap` is equivelent to
 `S.δ 1 (f 0) = S.δ 1 (f 1) ∧ S.δ 2 (f 0) = S.δ 1 (f 2) ∧ S.δ 2 (f 1) = S.δ 2 (f 2)`
-/
theorem isFaceMap₃₀ {S : SSet} (f : Fin 3 →  S _[2]) : isFaceMap 0 f ↔
    S.δ 1 (f 0) = S.δ 1 (f 1) ∧ S.δ 2 (f 0) = S.δ 1 (f 2) ∧ S.δ 2 (f 1) = S.δ 2 (f 2)  := by
  simp only [isFaceMap, Fin.zero_succAbove, Fin.pred_succ, Fin.forall_fin_succ, Fin.not_lt_zero,
    IsEmpty.forall_iff, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT,
    Fin.castPred_one, forall_true_left, lt_self_iff_false, and_self]
  exact and_assoc

 /--For the horn `Λ[3,1]` the condition `IsFaceMap` is equivelent to
 `S.δ 1 (f 0) = S.δ 0 (f 1) ∧ S.δ 2 (f 0) = S.δ 0 (f 2) ∧ S.δ 2 (f 1) = S.δ 2 (f 2)`
-/
theorem isFaceMap₃₁ {S : SSet} (f : Fin 3 →  S _[2]) : isFaceMap 1 f ↔
    S.δ 1 (f 0) = S.δ 0 (f 1) ∧ S.δ 2 (f 0) = S.δ 0 (f 2) ∧ S.δ 2 (f 1) = S.δ 2 (f 2)  := by
  simp only [isFaceMap, Fin.forall_fin_succ, Fin.not_lt_zero, ne_eq, Fin.one_eq_zero_iff,
    Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Fin.succAbove_ne_zero_zero,
    IsEmpty.forall_iff, Fin.one_succAbove_succ, Fin.pred_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT, forall_true_left, lt_self_iff_false,
    and_self]
  exact and_assoc

 /--For the horn `Λ[3,2]` the condition `IsFaceMap` is equivelent to
 `S.δ 1 (f 0) = S.δ 0 (f 1) ∧ S.δ 2 (f 0) = S.δ 0 (f 2) ∧ S.δ 2 (f 1) = S.δ 2 (f 1)`
-/
theorem isFaceMap₃₂ {S : SSet} (f : Fin 3 →  S _[2]) : isFaceMap 2 f ↔
    S.δ 0 (f 0) = S.δ 0 (f 1) ∧ S.δ 2 (f 0) = S.δ 0 (f 2) ∧ S.δ 2 (f 1) = S.δ 1 (f 2)  := by
  simp only [isFaceMap, Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT, forall_true_left,
    lt_self_iff_false, and_self]
  exact and_assoc

 /--For the horn `Λ[3,3]` the condition `IsFaceMap` is equivelent to
 `S.δ 0 (f 0) = S.δ 0 (f 1) ∧ S.δ 1 (f 0) = S.δ 0 (f 2) ∧ S.δ 1 (f 1) = S.δ 1 (f 2)`
-/
theorem isFaceMap₃₃ {S : SSet} (f : Fin 3 →  S _[2]) : isFaceMap 3 f ↔
    S.δ 0 (f 0) = S.δ 0 (f 1) ∧ S.δ 1 (f 0) = S.δ 0 (f 2) ∧ S.δ 1 (f 1) = S.δ 1 (f 2)  := by
  simp only [isFaceMap, Fin.forall_fin_succ, Fin.not_lt_zero, IsEmpty.forall_iff,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, and_true, true_and, Fin.reduceLT, forall_true_left,
    lt_self_iff_false, and_self]
  exact and_assoc

open SimplexImage in
/-- From a map `Fin (n+2)→ S _[n+1]` which is a face map, we can construct a morphism
 `Λ[n+2,i] ⟶ S`.-/
noncomputable def homMk {S : SSet}  {n:ℕ} (i: Fin (n+3))  (face_map : Fin (n+2) →  S _[n+1])
    (hface : isFaceMap i face_map):  Λ[n+2,i] ⟶ S where
  app X α := by
    let α' :([(unop X).len]: SimplexCategory)⟶  [n+2]:= α.1.down
    exact S.map (factor_δ α' (i.succAbove (minNotInImage α))).op (face_map (minNotInImage α))
  naturality X Y φ' := by
    funext α
    let φ: ([len Y.unop]: SimplexCategory)⟶ [len X.unop] := φ'.unop
    change S.map (factor_δ _ (i.succAbove _)).op (face_map _)
      = S.map φ.op (S.map (factor_δ _ ((i.succAbove _))).op (face_map _))
    cases lt_or_eq_of_le ((Fin.mem_find_iff.mp (minNotInImage_mem (Λ[n+2, i].map φ' α) )).right
     (minNotInImage α)
      (fun k ↦ (Fin.mem_find_iff.mp (minNotInImage_mem α)).left (φ'.unop.toOrderHom k))) with
    | inl h =>
        let i1:=minNotInImage (Λ[n + 2, i].map φ' α)
        let i2:=minNotInImage α
        have e1: notInImage (φ≫α.1.down) (i.succAbove i1) :=
           (Fin.mem_find_iff.mp (minNotInImage_mem (Λ[n+2, i].map φ' α))).left
        have e2:=
          (fun k ↦ (Fin.mem_find_iff.mp (minNotInImage_mem α)).left ((Hom.toOrderHom φ'.unop) k))
        have i1_lt_i2 :=  Fin.strictMono_succAbove i h
        rw [← types_comp_apply (S.map _) (S.map _) ,← S.map_comp, ← op_comp]
        change S.map (factor_δ (φ≫α.1.down) (i.succAbove i1)).op (face_map i1)=
          S.map (factor_δ (φ≫α.1.down) (i.succAbove i2)).op (face_map i2)
        rw [← factor_δ_spec (factor_δ (φ≫α.1.down) (i.succAbove i2)) _
           (notInImageCond_lt i1_lt_i2 e1 e2), ← factor_δ_spec
           (factor_δ (φ≫α.1.down) (i.succAbove i1)) _ (notInImageCond_gt i1_lt_i2 e1 e2)]
        rw [op_comp,S.map_comp,op_comp,S.map_comp,types_comp_apply, types_comp_apply]
        change S.map (_) (S.δ ((i.succAbove i2).pred _) (face_map i1)) =_
        rw [hface i1 i2 h]
        apply congrFun
        repeat apply congrArg
        unfold factor_δ
        repeat rw [Category.assoc]
        repeat apply congrArg
        exact SimplexCategory.σ_comp_σ_predAbove_zero (i.succAbove i1) (i.succAbove i2) i1_lt_i2
    | inr h => rw [← h,← types_comp_apply (S.map _) (S.map _),← S.map_comp, ← op_comp]
               rfl

lemma faceMap_of_homMk {S : SSet} {n:ℕ} (i: Fin (n+3)) (f : Fin (n+2) → S _[n+1])
    (hf : isFaceMap i f) : hornToFaceMap (homMk i f hf) = f := by
  funext j
  unfold hornToFaceMap homMk
  simp only [unop_op, len_mk, yoneda_obj_obj, ne_eq, face_coe]
  rw [SimplexImage.minNotInImage_face,Fin.succAbove_predAbove_predAbove _ _ (Fin.succAbove_ne i j),
   Fin.predAbove_predAbove_succAbove i 0 j]
  nth_rewrite 2 [show f j= S.map (𝟙 ([n+1]:SimplexCategory)).op (f j) by
   rw [op_id,S.map_id]; rfl ]
  apply  congrFun ∘ (congrArg S.map) ∘ congrArg op
  rw [factor_δ, Fin.predAbove_zero]
  split_ifs with h
  · exact δ_comp_σ_self' h
  · exact δ_comp_σ_succ' (i.succAbove j) ((i.succAbove j).pred h)
     ((Fin.pred_eq_iff_eq_succ (i.succAbove j) h ((i.succAbove j).pred h)).mp rfl)

lemma homMk_of_faceMap {S :SSet} {n: ℕ } (i : Fin (n+3)) (f : Λ[n+2,i]⟶ S):
    homMk i (hornToFaceMap f) (hornToFaceMap_is_face_map f) = f := by
  apply horn.hom_ext
  unfold hornToFaceMap
  intro j hij
  rw [face_to_faceMap,face_to_faceMap,faceMap_of_homMk]
  rfl

/--Two horns are equal iff there face maps are equal.-/
lemma eq_iff_faceMap_eq {S :SSet} {n: ℕ } (i : Fin (n+3)) (f g : Λ[n+2,i]⟶ S):
    f=g ↔ hornToFaceMap f = hornToFaceMap g := by
  apply Iff.intro
  · intro h
    rw [← homMk_of_faceMap i f,← homMk_of_faceMap i g] at h
    apply congrArg hornToFaceMap at h
    rw [faceMap_of_homMk,faceMap_of_homMk] at h
    exact h
  · intro h
    rw [← homMk_of_faceMap i f,← homMk_of_faceMap i g ]
    simp only [h]

/--The relationship the face of a horn and its lift.-/
theorem hornFace_to_lift_face {S :SSet} {n: ℕ } (i : Fin (n+3)) (f : Λ[n+2,i]⟶ S) (l : Δ[n+2] ⟶ S)
    (hl: f= hornInclusion (n+2) i ≫ l) :
    hornToFaceMap f  =  standardSimplex.faceInc l ∘ i.succAbove  := by
  unfold hornToFaceMap standardSimplex.faceInc
  funext j
  rw [hl,NatTrans.comp_app,types_comp_apply]
  apply congrArg
  rfl

theorem lift_face_to_hornFace {S :SSet} {n: ℕ } {i j  : Fin (n+3)} (hij : j ≠ i) (f : Λ[n+2,i]⟶ S)
    (l : Δ[n+2] ⟶ S) (hl: f= hornInclusion (n+2) i ≫ l) :
    standardSimplex.faceInc l j = hornToFaceMap f ((Fin.predAbove 0 i).predAbove j) := by
  rw [← face_to_faceMap i j hij, standardSimplex.faceInc,hl,NatTrans.comp_app,types_comp_apply]
  apply congrArg
  rfl

--To be moved.
lemma Fin.predAbove_le_of_le_castSucc {n: ℕ} (p : Fin (n+1)) {j: Fin (n+1)}  {i : Fin (n+2)}
    (h: i ≤ j.castSucc): p.predAbove i ≤  j:= by
  unfold Fin.predAbove
  split_ifs with h1
  · simp only [Fin.le_def,Fin.coe_pred, tsub_le_iff_right]
    exact Nat.le.step h
  · rw [Fin.le_def]
    exact h
--To be moved
lemma Fin.predAbove_le_of_lt_Succ{n: ℕ} (p : Fin (n+1)) {i : Fin (n+2)} {j: Fin (n+1)}
    (h: i<j.succ): p.predAbove i ≤  j :=
  predAbove_le_of_le_castSucc p (Fin.le_castSucc_iff.mpr h)
--To be moved
lemma Fin.le_predAbove_of_castSucc_lt {n: ℕ} (p : Fin (n+1)) {i : Fin (n+2)} {j: Fin (n+1)}
    (h: j.castSucc<i):  j ≤  p.predAbove i := by
  unfold Fin.predAbove
  split_ifs with h1
  · simp only [Fin.le_def, Fin.coe_pred]
    exact Nat.le_sub_one_of_lt h
  · rw [Fin.le_def]
    exact Nat.lt_succ.mp (Nat.le.step h)
--To be moved.
lemma Fin.le_predAbove_of_succ_le {n: ℕ} (p : Fin (n+1)) {i : Fin (n+2)} {j: Fin (n+1)}
    (h: j.succ ≤ i):  j ≤  p.predAbove i :=
  Fin.le_predAbove_of_castSucc_lt p h


/--The subfaces of the filling face of a lift are related to the subfaces of the faces of the
horn -/
theorem faces_of_filler  {S :SSet} {n: ℕ } {i : Fin (n+3)} (f : Λ[n+2,i]⟶ S)
    (l : Δ[n+2] ⟶ S) (hl: f = hornInclusion (n+2) i ≫ l) (j : Fin (n+2)):
    S.δ j (standardSimplex.faceInc l i) =
    if h : i<j.succ then
    S.δ (i.castPred (Fin.ne_of_lt (gt_of_ge_of_gt j.succ.le_last h))) (hornToFaceMap f j)
    else
    S.δ (i.pred (Fin.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt (Fin.not_lt.mp h)) ))
    (hornToFaceMap f j):= by
  by_cases h: i<j.succ
  · nth_rewrite 1 [show j=j.succ.pred (Fin.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt h) ) from rfl ]
    rw [standardSimplex.faceInc_subfaceCond l i j.succ h,dif_pos h,
    lift_face_to_hornFace (Fin.ne_of_gt h) f l hl]
    repeat apply congrArg
    exact Fin.predAbove_succ_of_le (Fin.predAbove 0 i) j (Fin.predAbove_le_of_lt_Succ 0 h)
  ·  have hi : j.castSucc < i :=   Fin.not_lt.mp h
     nth_rewrite 1 [show j=j.castSucc.castPred
        (Fin.ne_of_lt (gt_of_ge_of_gt i.le_last hi)) from rfl]
     rw [← standardSimplex.faceInc_subfaceCond l j.castSucc i hi,dif_neg h,
     lift_face_to_hornFace (Fin.ne_of_lt hi) f l hl]
     repeat apply congrArg
     exact Fin.predAbove_castSucc_of_le (Fin.predAbove 0 i) j (Fin.le_predAbove_of_castSucc_lt 0 hi)


open standardSimplex in
theorem faces_of_filler₂₀  {S :SSet} (f : Λ[2,0]⟶ S)
    (l : Δ[2] ⟶ S) (hl: f = hornInclusion 2 0 ≫ l) :
    S.δ 0 (faceInc l 0) = S.δ 0 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 0) = S.δ 0 (hornToFaceMap f 1) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, Fin.reduceLT, ↓reduceDite, Fin.succ_one_eq_two]
  apply And.intro
  all_goals rfl

open standardSimplex in
theorem faces_of_filler₂₁ {S :SSet} (f : Λ[2,1]⟶ S)
    (l : Δ[2] ⟶ S) (hl: f = hornInclusion 2 1 ≫ l) :
    S.δ 0 (faceInc l 1) = S.δ 0 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 1) = S.δ 1 (hornToFaceMap f 1) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, lt_self_iff_false, ↓reduceDite, Fin.pred_one,
    Fin.succ_one_eq_two, Fin.reduceLT, Fin.castPred_one, and_self]

open standardSimplex in
theorem faces_of_filler₂₂ {S :SSet} (f : Λ[2,2]⟶ S)
    (l : Δ[2] ⟶ S) (hl: f = hornInclusion 2 2 ≫ l) :
    S.δ 0 (faceInc l 2) = S.δ 1 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 2) = S.δ 1 (hornToFaceMap f 1) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, Fin.reduceLT, ↓reduceDite, Fin.succ_one_eq_two,
    lt_self_iff_false]
  apply And.intro
  all_goals rfl

open standardSimplex in
theorem faces_of_filler₃₀  {S :SSet} (f : Λ[3,0]⟶ S)
    (l : Δ[3] ⟶ S) (hl: f = hornInclusion 3 0 ≫ l) :
    S.δ 0 (faceInc l 0) = S.δ 0 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 0) = S.δ 0 (hornToFaceMap f 1) ∧
    S.δ 2 (faceInc l 0) = S.δ 0 (hornToFaceMap f 2) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, Fin.reduceLT, ↓reduceDite, Fin.succ_one_eq_two, Fin.succ_pos]
  repeat any_goals apply And.intro
  all_goals rfl

open standardSimplex in
theorem faces_of_filler₃₁  {S :SSet} (f : Λ[3,1]⟶ S)
    (l : Δ[3] ⟶ S) (hl: f = hornInclusion 3 1 ≫ l) :
    S.δ 0 (faceInc l 1) = S.δ 0 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 1) = S.δ 1 (hornToFaceMap f 1) ∧
    S.δ 2 (faceInc l 1) = S.δ 1 (hornToFaceMap f 2) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, lt_self_iff_false, ↓reduceDite, Fin.pred_one,
    Fin.succ_one_eq_two, Fin.reduceLT, Fin.castPred_one, dite_eq_ite, ite_eq_left_iff, not_lt,
    true_and]
  have : ¬  Fin.succ (2 : Fin 3)≤ 1 := by exact Fin.not_le.mpr (Fin.coe_sub_iff_lt.mp rfl)
  exact fun a ↦ (this a).elim

open standardSimplex in
theorem faces_of_filler₃₂  {S :SSet} (f : Λ[3,2]⟶ S)
    (l : Δ[3] ⟶ S) (hl: f = hornInclusion 3 2 ≫ l) :
    S.δ 0 (faceInc l 2) = S.δ 1 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 2) = S.δ 1 (hornToFaceMap f 1) ∧
    S.δ 2 (faceInc l 2) = S.δ 2 (hornToFaceMap f 2) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, Fin.reduceLT, ↓reduceDite, Fin.succ_one_eq_two,
    lt_self_iff_false]
  repeat any_goals apply And.intro
  any_goals rfl

open standardSimplex in
theorem faces_of_filler₃₃  {S :SSet} (f : Λ[3,3]⟶ S)
    (l : Δ[3] ⟶ S) (hl: f = hornInclusion 3 3 ≫ l) :
    S.δ 0 (faceInc l 3) = S.δ 2 (hornToFaceMap f 0) ∧
    S.δ 1 (faceInc l 3) = S.δ 2 (hornToFaceMap f 1) ∧
    S.δ 2 (faceInc l 3) = S.δ 2 (hornToFaceMap f 2) := by
  rw [faces_of_filler f l hl,faces_of_filler f l hl,faces_of_filler f l hl]
  simp only [Fin.succ_zero_eq_one, Fin.reduceLT, ↓reduceDite, Fin.succ_one_eq_two]
  repeat any_goals apply And.intro
  any_goals rfl


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

instance Truncated.hasLimits {n : ℕ} : HasLimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasColimits {n : ℕ} : HasColimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

-- Porting note (#10756): added an `ext` lemma.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma Truncated.hom_ext {n : ℕ} {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) :
    f = g :=
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

-- Porting note: an instance of `Subsingleton (⊤_ (Type u))` was added in
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
