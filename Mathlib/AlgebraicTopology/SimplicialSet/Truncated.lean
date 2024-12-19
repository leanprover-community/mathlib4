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

open CategoryTheory Simplicial SimplexCategory Opposite

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

/-- Abbreviations for face maps in the 2-truncated simplex category. -/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
    (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n + 1], hn'⟩ := SimplexCategory.δ i

/-- Abbreviations for degeneracy maps in the 2-truncated simplex category. -/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨[n+1], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[n], hn'⟩ := SimplexCategory.σ i


@[reassoc (attr := simp)]
lemma δ₂_zero_comp_σ₂_zero : δ₂ (0 : Fin 2) ≫ σ₂ 0 = 𝟙 _ := SimplexCategory.δ_comp_σ_self

@[reassoc (attr := simp)]
lemma δ₂_one_comp_σ₂_zero : δ₂ (1 : Fin 2) ≫ σ₂ 0 = 𝟙 _ := SimplexCategory.δ_comp_σ_succ

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

/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _[0]₂` as its underlying
type. -/
def OneTruncation₂ := X _[0]₂

/-- The hom-types of the refl quiver underlying a simplicial set `S` are types of edges in `S _[1]₂`
together with source and target equalities. -/
@[ext]
structure OneTruncation₂.Hom {X : SSet.Truncated 2} (x y : OneTruncation₂ X) where
  /-- An arrow in `OneTruncation₂.Hom x y` includes the data of a 1-simplex. -/
  edge : X _[1]₂
  /-- An arrow in `OneTruncation₂.Hom x y` includes a source equality. -/
  src_eq : X.map (δ₂ 1).op edge = x
  /-- An arrow in `OneTruncation₂.Hom x y` includes a target equality. -/
  tgt_eq : X.map (δ₂ 0).op edge = y

/-- A 2-truncated simplicial set `X` has an underlying refl quiver `SSet.OneTruncation₂ X`. -/
instance : ReflQuiver (OneTruncation₂ X) where
  Hom x y := OneTruncation₂.Hom x y
  id x :=
    { edge := X.map (σ₂ (n := 0) 0).op x
      src_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply]
      tgt_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply] }

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

-- @[simps!] def toStrictSegal₂.mk {X Y : SSet.Truncated 2} [StrictSegal₂ Y]
--     (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
--     (hyp : (φ : X _[2]₂) → (F.map (ev02₂ φ)).edge =
--       StrictSegal₂.spineToDiagonal₂ (reflPrefunctorPathMap F (spine₂ X φ)))
--     : X ⟶ Y where
--   app := fun n => toStrictSegal₂.mk.app F n.unop
--   naturality := by sorry


end Truncated

end SSet
