/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

open Simplicial

/-- The category of simplicial sets.
This is the category of contravariant functors from
`SimplexCategory` to `Type u`. -/
def SSet : Type (u + 1) :=
  SimplicialObject (Type u)

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

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex -/
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

#adaptation_note
/--
The new unused variable linter in
https://github.com/leanprover/lean4/pull/5338
flags `{ α : Δ[n].obj m // _ }`.
-/
set_option linter.unusedVariables false in
/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundaryInclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where app m (α : { α : Δ[n].obj m // _ }) := α

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

/-- The `i`-th horn `Λ[n, i]` of the standard `n`-simplex -/
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

#adaptation_note
/--
The new unused variable linter in
https://github.com/leanprover/lean4/pull/5338
flags `{ α : Δ[n].obj m // _ }`.
-/
set_option linter.unusedVariables false in
/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def hornInclusion (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[n] where
  app m (α : { α : Δ[n].obj m // _ }) := α

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
    fin_cases j <;> simp [Fin.ext_iff]
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
  rw [H, H₁, H₂, h _ hji]

end horn

section Examples

open Simplicial

/-- The simplicial circle. -/
noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (standardSimplex.map <| SimplexCategory.δ 0 : Δ[0] ⟶ Δ[1])
      (standardSimplex.map <| SimplexCategory.δ 1)

end Examples

/-- Truncated simplicial sets. -/
def Truncated (n : ℕ) :=
  SimplicialObject.Truncated (Type u) n

instance Truncated.largeCategory (n : ℕ) : LargeCategory (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasLimits {n : ℕ} : HasLimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasColimits {n : ℕ} : HasColimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

/-- The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets. -/
def Truncated.uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]
lemma Truncated.hom_ext {n : ℕ} {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) :
    f = g :=
  NatTrans.ext (funext w)

/-- The truncation functor on simplicial sets. -/
abbrev truncation (n : ℕ) : SSet ⥤ SSet.Truncated n := SimplicialObject.truncation n

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(truncation n).obj <| Δ[0]⟩


open SimplexCategory

noncomputable section

/-- The n-skeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
protected abbrev Truncated.sk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.sk n

/-- The n-coskeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
protected abbrev Truncated.cosk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.cosk n

/-- The n-skeleton as an endofunctor on `SSet`. -/
abbrev sk (n : ℕ) : SSet ⥤ SSet := SimplicialObject.sk n

/-- The n-coskeleton as an endofunctor on `SSet`. -/
abbrev cosk (n : ℕ) : SSet ⥤ SSet := SimplicialObject.cosk n

end

section adjunctions

/-- The adjunction between the n-skeleton and n-truncation.-/
noncomputable def skAdj (n : ℕ) : Truncated.sk n ⊣ truncation.{u} n :=
  SimplicialObject.skAdj n

/-- The adjunction between n-truncation and the n-coskeleton.-/
noncomputable def coskAdj (n : ℕ) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

namespace Truncated

instance cosk_reflective (n) : IsIso (coskAdj n).counit :=
  SimplicialObject.Truncated.cosk_reflective n

instance sk_coreflective (n) : IsIso (skAdj n).unit :=
  SimplicialObject.Truncated.sk_coreflective n

/-- Since `Truncated.inclusion` is fully faithful, so is right Kan extension along it.-/
noncomputable def cosk.fullyFaithful (n) :
    (Truncated.cosk n).FullyFaithful :=
  SimplicialObject.Truncated.cosk.fullyFaithful n

instance cosk.full (n) : (Truncated.cosk n).Full :=
  SimplicialObject.Truncated.cosk.full n

instance cosk.faithful (n) : (Truncated.cosk n).Faithful :=
  SimplicialObject.Truncated.cosk.faithful n

noncomputable instance coskAdj.reflective (n) : Reflective (Truncated.cosk n) :=
  SimplicialObject.Truncated.coskAdj.reflective n

/-- Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it.-/
noncomputable def sk.fullyFaithful (n) :
    (Truncated.sk n).FullyFaithful := SimplicialObject.Truncated.sk.fullyFaithful n

instance sk.full (n) : (Truncated.sk n).Full := SimplicialObject.Truncated.sk.full n

instance sk.faithful (n) : (Truncated.sk n).Faithful :=
  SimplicialObject.Truncated.sk.faithful n

noncomputable instance skAdj.coreflective (n) : Coreflective (Truncated.sk n) :=
  SimplicialObject.Truncated.skAdj.coreflective n

end Truncated

end adjunctions

/-- The category of augmented simplicial sets, as a particular case of
augmented simplicial objects. -/
abbrev Augmented :=
  SimplicialObject.Augmented (Type u)

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
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.standardSimplex.map θ
      right := terminal.from _ }

end Augmented

section Spine

variable (X : SSet.{u})

/-- A path in a simplicial set `X` of length `n` is a directed path of `n` edges.-/
@[ext]
structure Path (n : ℕ) where
  vertex (i : Fin (n + 1)) : X _[0]
  arrow (i : Fin n) : X _[1]
  arrow_src (i : Fin n) : X.δ 1 (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin n) : X.δ 0 (arrow i) = vertex i.succ

/-- For `j ≤ k ≤ n`, a path of length `n` restricts to a path of length `k-j`, namely the subpath
spanned by the vertices `j ≤ i ≤ k` and edges `j ≤ i < k`. -/
def Path.interval {n : ℕ} (f : Path X n) (j k : ℕ) (hjk : j ≤ k) (hkn : k ≤ n)
    : Path X (k - j) where
  vertex i := f.vertex (Fin.addNat i j)
  arrow i := f.arrow ⟨Fin.addNat i j, (by omega)⟩
  arrow_src i := by
    have eq := f.arrow_src ⟨Fin.addNat i j, (by omega)⟩
    simp_rw [eq]
    congr 1
    apply Fin.eq_of_val_eq
    simp only [Fin.coe_addNat, Fin.coe_castSucc, Fin.val_natCast]
    have : i.1 + j < n + 1 := by omega
    have : (↑i + j) % (n + 1) = i.1 + j := by exact Nat.mod_eq_of_lt this
    rw [this]
  arrow_tgt i := by
    have eq := f.arrow_tgt ⟨Fin.addNat i j, (by omega)⟩
    simp_rw [eq]
    congr 1
    apply Fin.eq_of_val_eq
    simp only [Fin.coe_addNat, Fin.succ_mk, Fin.val_succ, Fin.val_natCast]
    have : i.1 + 1 + j < n + 1 := by omega
    have : (i.1 + 1 + j) % (n + 1) = i.1 + 1 + j := by exact Nat.mod_eq_of_lt this
    rw [this, Nat.add_right_comm]

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed by
traversing through its vertices in order.-/
@[simps]
def spine (n : ℕ) (Δ : X _[n]) : X.Path n where
  vertex i := X.map (SimplexCategory.const [0] [n] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    apply congr_fun
    congr 2
    ext j
    fin_cases j
    rfl
  arrow_tgt i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    apply congr_fun
    congr 2
    ext j
    fin_cases j
    rfl

variable {X} in
/-- The diagonal of a simplex is the long edge of the simplex.-/
def diagonal {n : ℕ} (Δ : X _[n]) : X _[1] := X.map ((mkOfDiag n).op) Δ

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine.-/
def StrictSegal : Prop := ∀ (n : ℕ), Function.Bijective (X.spine (n := n))

namespace StrictSegal
variable {X : SSet.{u}} {hX : StrictSegal X} {n : ℕ}

/-- In the presence of the strict Segal condition, a path of length `n` extends to an `n`-simplex
whose spine is that path.-/
noncomputable def spineToSimplex : Path X n → X _[n] :=
  (Equiv.ofBijective _ (hX n)).invFun

@[simp]
theorem spineToSimplex_spine (f : Path X n) :
    X.spine n (StrictSegal.spineToSimplex (hX := hX) f) = f :=
  (Equiv.ofBijective _ (hX n)).right_inv f

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex (hX := hX) f) = f.vertex i := by
  rw [← spine_vertex, spineToSimplex_spine]

@[simp]
theorem spineToSimplex_spine_edge (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex (hX := hX) f) = f.arrow i := by
  rw [← spine_arrow, spineToSimplex_spine]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex.-/
noncomputable def spineToDiagonal (f : Path X n) : X _[1] := diagonal (spineToSimplex (hX := hX) f)

@[simp]
theorem spineToSimplex_interval (j k: Fin (n + 1)) (hjk : j ≤ k) (f : Path X n) :
    X.map (subinterval j k hjk).op (spineToSimplex (hX := hX) f) =
      spineToSimplex (hX := hX) (Path.interval X f _ _ hjk (Nat.le_of_lt_succ k.2)) := by
  apply (hX _).injective
  rw [StrictSegal.spineToSimplex_spine]
  ext i
  · unfold Path.interval
    simp only [mkHom, Equiv.invFun_as_coe, spine_vertex, Fin.coe_addNat]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [const_comp, len_mk]
    unfold subinterval
    simp only [spineToSimplex_vertex]
    congr 1
    apply Fin.eq_of_val_eq
    simp
    have : i.1 + j < n + 1 := by omega
    have : (i.1 + j) % (n + 1) = i.1 + j := by exact Nat.mod_eq_of_lt this
    rw [this]
  · unfold Path.interval
    simp only [Equiv.invFun_as_coe, spine_arrow, Fin.coe_addNat]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    have ceq : mkOfSucc i ≫ subinterval j k hjk = mkOfSucc ⟨i + j, (by omega)⟩ := by
      ext ⟨e, he⟩ : 3
      simp at he
      unfold subinterval
      match e with
      | 0 => rfl
      | 1 => ?_
      conv_rhs =>
        apply mkOfSucc_homToOrderHom_one
      simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, Fin.mk_one,
        Fin.isValue, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, Fin.succ_mk,
        Fin.mk.injEq]
      exact Nat.succ_add_eq_add_succ ↑i ↑j
    rw [ceq]
    simp only [spineToSimplex_spine_edge]

@[simp]
theorem spineToSimplex_edge (j k: Fin (n + 1)) (hjk : j ≤ k) (f : Path X n) :
    X.map (mkOfLe j k hjk).op (spineToSimplex (hX := hX) f) =
      spineToDiagonal (hX := hX) (Path.interval X f _ _ hjk (Nat.le_of_lt_succ k.2)) := by
  unfold spineToDiagonal
  rw [← congrArg diagonal (spineToSimplex_interval (hX := hX) j k hjk f)]
  unfold diagonal
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : mkOfLe j k hjk = mkOfDiag (k.1 - j.1) ≫ subinterval j k hjk := by
    ext e : 3
    simp at e
    unfold subinterval mkOfDiag mkOfLe
    simp only [len_mk, Nat.reduceAdd, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk,
      Fin.natCast_eq_last, comp_toOrderHom, OrderHom.mk_comp_mk, Function.comp_apply]
    match e with
    | 0 => simp
    | 1 => ?_
    apply Fin.eq_of_val_eq
    simp only [Fin.val_last]
    exact (Nat.sub_eq_iff_eq_add hjk).mp rfl
  rw [this]

@[simp]
theorem spineToSimplex_edge' (j : Fin (n + 1)) (k : ℕ) (hjk : j.1 + k < n + 1) (f : Path X n) :
    X.map (mkOfLe j ⟨j.1 + k, hjk⟩ (Nat.le_add_right j k)).op (spineToSimplex (hX := hX) f) =
      spineToDiagonal (hX := hX)
        (Path.interval X f j (j + k) (Nat.le_add_right j k) (Nat.le_of_lt_succ hjk)) :=
  spineToSimplex_edge (hX := hX) j ⟨j.1 + k, hjk⟩ (Nat.le_add_right j.1 k) f

end StrictSegal


end Spine

end SSet
