/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

/-!
# 2-truncated Strict Segal simplicial sets

This collects some API which will ultimately be deployed elsewhere
-/

universe v u

namespace SSet

namespace Truncated

open CategoryTheory Category Functor Simplicial SimplexCategory Opposite

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

section

variable (X : SSet.Truncated.{u} 2)

/-- A path in a 2-truncated simplicial set `X` of length `n` is a directed path of `n` edges.-/
@[ext]
structure Path₂ (n : ℕ) where
  /-- A path includes the data of `n+1` 0-simplices in `X`.-/
  vertex (i : Fin (n + 1)) : X _[0]₂
  /-- A path includes the data of `n` 1-simplices in `X`.-/
  arrow (i : Fin n) : X _[1]₂
  /-- The sources of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_src (i : Fin n) : X.map (δ₂ 1).op (arrow i) = vertex i.castSucc
  /-- The targets of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_tgt (i : Fin n) : X.map (δ₂ 0).op (arrow i) = vertex i.succ

/-- The spine of an `2`-simplex in `X` is the path of edges of length `2` formed by
traversing through its vertices in order.-/
@[simps]
def spine₂
    (Δ : X _[2]₂) : X.Path₂ 2 where
  vertex i := X.map (SimplexCategory.const [0] [2] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    unfold δ₂
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : ((mkOfSucc i).op ≫ (δ 1).op) = ([0].const [2] i.castSucc).op := by
      simp [← op_comp, SimplexCategory.δ_one_mkOfSucc]
    exact congrFun (congrArg X.map this) Δ
  arrow_tgt i := by
    unfold δ₂
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply]
    have : (mkOfSucc i).op ≫ (δ 0).op = ([0].const [2] i.succ).op := by
      rw [← op_comp, SimplexCategory.δ_zero_mkOfSucc]
    exact congrFun (congrArg X.map this) Δ

/-- A 2-truncated simplicial set `X` satisfies the strict Segal condition if its 2-simplices are
uniquely determined by their spine. -/
class StrictSegal₂ where
  /-- The inverse to `X.spine₂`.-/
  spineToSimplex₂ : Path₂ X 2 → X _[2]₂
  /-- `spineToSimplex` is a right inverse to `X.spine n`.-/
  spine₂_spineToSimplex₂ (f : Path₂ X 2) : X.spine₂ (spineToSimplex₂ f) = f
  /-- `spineToSimplex` is a left inverse to `X.spine n`.-/
  spineToSimplex₂_spine₂ (Δ : X _[2]₂) : spineToSimplex₂ (X.spine₂ Δ) = Δ

namespace StrictSegal₂
variable {X : SSet.Truncated.{u} 2} [StrictSegal₂ X]

/-- The fields of `StrictSegal` define an equivalence between `X _[n]` and `Path X n`.-/
def spineEquiv₂ : X _[2]₂ ≃ Path₂ X 2 where
  toFun := spine₂ X
  invFun := spineToSimplex₂
  left_inv := spineToSimplex₂_spine₂
  right_inv := spine₂_spineToSimplex₂

theorem spineInjective₂ : Function.Injective (spineEquiv₂ (X := X)) := Equiv.injective _

@[simp]
theorem spineToSimplex₂_vertex (i : Fin 3) (f : Path₂ X 2) :
    X.map (const [0] [2] i).op (spineToSimplex₂ f) = f.vertex i := by
  rw [← spine₂_vertex, spine₂_spineToSimplex₂]

@[simp]
theorem spineToSimplex₂_arrow (i : Fin 2) (f : Path₂ X 2) :
    X.map (mkOfSucc i).op (spineToSimplex₂ f) = f.arrow i := by
  rw [← spine₂_arrow, spine₂_spineToSimplex₂]

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal₂ (f : Path₂ X 2) : X _[1]₂ :=
    X.map ((SimplexCategory.diag 2).op) (spineToSimplex₂ f)

end StrictSegal₂

end

/-- A refl prefunctor between the underlying refl quivers of a 2-truncated simplicial sets induces a
map on paths. -/
def reflPrefunctorPathMap {X Y : SSet.Truncated.{u} 2} (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    {n : ℕ} (σ : Path₂ X n) : Path₂ Y n where
      vertex i := F.obj (σ.vertex i)
      arrow i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).edge
      arrow_src i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).src_eq
      arrow_tgt i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).tgt_eq

/-- The components of a map of 2-truncated simplicial sets built from a map on underlying reflexive
quivers, under the assumption that the codomain is `StrictSegal`. -/
def toStrictSegal₂.mk.app {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    (n : SimplexCategory.Truncated 2) : X.obj (op n) ⟶ Y.obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => F.obj x
  | 1 => exact fun f => (F.map ⟨f, rfl, rfl⟩).edge
  | 2 => exact fun φ => StrictSegal₂.spineToSimplex₂ (reflPrefunctorPathMap F (X.spine₂ φ))

@[simp] theorem toStrictSegal₂.mk.app_zero {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (x : X _[0]₂) :
    mk.app F [0]₂ x = F.obj x := rfl

@[simp] theorem toStrictSegal₂.mk.app_one {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (f : X _[1]₂) :
    mk.app F [1]₂ f = (F.map ⟨f, rfl, rfl⟩).edge := rfl

@[simp] theorem toStrictSegal₂.mk.app_two {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = StrictSegal₂.spineToSimplex₂ (reflPrefunctorPathMap F (X.spine₂ φ)) := rfl

@[simps!]
def toStrictSegal₂.mk {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    (hyp : (φ : X _[2]₂) → (F.map (ev02₂ φ)).edge =
      StrictSegal₂.spineToDiagonal₂ (reflPrefunctorPathMap F (spine₂ X φ))) : X ⟶ Y where
  app := fun n => toStrictSegal₂.mk.app F n.unop
  naturality := by
    rintro ⟨⟨m, hm⟩⟩ ⟨⟨n, hn⟩⟩ ⟨α : (⟨n, hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨m, hm⟩⟩
    rw [show Opposite.op α = α.op by rfl]
    induction' m using SimplexCategory.rec with m
    induction' n using SimplexCategory.rec with n
    dsimp at α ⊢
    let OK {n m hn hm} (f : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩) :=
      X.map f.op ≫ mk.app F ⟨[n], hn⟩ = mk.app F ⟨[m], hm⟩ ≫ Y.map f.op
    show OK α
    have fac : ∀ {n m hn hm} {α : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩} k hk
      {β : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[k], hk⟩}
      {γ : (⟨[k], hk⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩},
      α = β ≫ γ → OK β → OK γ → OK α := by
        rintro _ _ _ _ _ k hk β γ rfl h1 h2
        dsimp only [OK] at h1 h2 ⊢
        rw [op_comp, map_comp, map_comp, assoc, h1, ← assoc, h2, assoc]
    have const10 (α : [1]₂ ⟶ [0]₂) : OK α := by
      ext x
      cases SimplexCategory.eq_const_to_zero α
      dsimp
      sorry
    have const01 (α : [0]₂ ⟶ [1]₂) : OK α := by
      ext x
      sorry
    have const02 (α : [0]₂ ⟶ [2]₂) : OK α := by
      ext x
      sorry
    have nat1m {m hm} (α : [1]₂ ⟶ ⟨[m], hm⟩) : OK α := by
      match m with
      | 0 => apply const10
      | 1 =>
        match α, eq_of_one_to_one α with
        | _, .inr rfl =>
          dsimp [OK]
          rw [(_ : X.map _ = id), (_ : Prefunctor.map _ _ = id)]; rfl
          all_goals sorry
        | _, .inl ⟨i, rfl⟩ =>
          exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const01 ..)
      | 2 =>
        match α, eq_of_one_to_two α with
        | _, .inl rfl =>
          ext x
          sorry
        | _, .inr (.inl rfl) =>
          ext x
          sorry
        | _, .inr (.inr (.inl rfl)) =>
          ext x
          sorry
        | _, .inr (.inr (.inr ⟨i, rfl⟩)) =>
          exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const02 ..)
    have nat2m (α : [2]₂ ⟶ ⟨[m], hm⟩) : OK α := by
      dsimp [OK]
      sorry
      -- apply (cancel_mono (nerve₂.seagull _)).1
      -- simp [nerve₂.seagull]
      -- congr 1 <;> rw [← map_comp, ← op_comp, ← nat1m, ← nat1m, op_comp, map_comp, assoc]
    match n with
      | 0 =>
        match m with
        | 0 =>
          ext x
          simp [SimplexCategory.rec]
          cases SimplexCategory.hom_zero_zero α
          show F.obj (X.map (𝟙 [0]₂).op x) = Y.map (𝟙 [0]₂).op (F.obj x)
          simp [Functor.map_id]
        | 1 => apply const01
        | 2 => apply const02
      | 1 => apply nat1m
      | 2 => apply nat2m

end Truncated

end SSet
