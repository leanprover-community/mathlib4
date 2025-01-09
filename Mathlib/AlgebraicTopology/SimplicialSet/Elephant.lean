/-
Copyright (c) 2025 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Util.Superscript

import Mathlib.CategoryTheory.Category.ReflQuiv

open CategoryTheory Category Limits Functor Opposite Simplicial SimplexCategory

namespace SSet.Truncated

/-- Some quick attempts to prove that `[m]` is `n`-truncated (`m ≤ n`). -/
macro "trunc" : tactic =>
  `(tactic| first | decide | assumption | apply zero_le | apply le_rfl |
    simp only [SimplexCategory.len_mk]; omega)

/-- For `X : SSet.Truncated n` and `m ≤ n`, `X _[m]ₙ` is the type of `m`-simplices in `X`. -/
scoped macro:1000 (priority := high)
  X:term " _[" m:term "]"n:subscript(term) : term =>
  `(($X : SSet.Truncated $(⟨n.raw[0]⟩)).obj (Opposite.op ⟨SimplexCategory.mk $m,
    by first | trunc | fail "Failed to prove SSet.Truncated property."⟩))

/-- For `X : SSet.Truncated n` and `p : m ≤ n`, `X _[m, p]ₙ` is the type of `m`-simplices in `X`. -/
scoped macro:1000 (priority := high)
  X:term " _[" m:term "," p:term "]"n:subscript(term) : term =>
    `(($X : SSet.Truncated $(⟨n.raw[0]⟩)).obj
      (Opposite.op ⟨SimplexCategory.mk $m, $p⟩))

-- set_option quotPrecheck false
-- local macro:max (priority := high) "[" n:term "]₂" : term =>
--   `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))


end SSet.Truncated

namespace SimplexCategory.Truncated
open CategoryTheory SimplexCategory

/-- The truncated form of the inclusion functor. -/
def incl {n m : ℕ} (h : n ≤ m) : Truncated n ⥤ Truncated m where
  obj a := ⟨a.1, a.2.trans h⟩
  map := id

lemma incl_comp_inclusion {n m : ℕ} (h : n ≤ m) : incl h ⋙ inclusion m = inclusion n := rfl

end SimplexCategory.Truncated

universe v u

namespace SimplicialObject.Truncated
open CategoryTheory SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated C m ⥤ Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl h).op

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) : truncation m ⋙ trunc C h = truncation n := rfl

end SimplicialObject.Truncated

namespace SSet.Truncated
open CategoryTheory SimplexCategory Simplicial

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated m ⥤ Truncated n :=
  SimplicialObject.Truncated.trunc (Type u) h

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) : truncation m ⋙ trunc h = truncation n := rfl

/-- A path of length `n` in a 1-truncated simplicial set is a directed path of `n` edges. -/
@[ext]
structure Path₁ (X : Truncated.{u} 1) (n : ℕ) where
  vertex (i : Fin (n + 1)) : X _[0]₁
  arrow (i : Fin n) : X _[1]₁
  arrow_src (i : Fin n) : X.map (δ 1).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin n) : X.map (δ 0).op (arrow i) = vertex i.succ

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- A path in any `n + 1`-truncated simplicial set `X` is defined by further 1-truncating `X`, then
taking the 1-truncated path. -/
abbrev Path : ℕ → Type u := trunc (by omega) |>.obj X |>.Path₁

/-- The spine of an `n + 1`-simplex in an `n + 1`-truncated simplicial set `X` is the path of edges
of length `n + 1` formed by traversing through its vertices in order. -/
@[simps]
def spine {m} (hmn : m ≤ n + 1) (Δ : X _[m]ₙ₊₁) : Path X m where
  vertex i := X.map (SimplexCategory.const [0] [m] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 1).op.unop)]
    simp
  arrow_tgt i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 0).op.unop)]
    simp

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if its
`n + 1`-simplices are uniquely determined by their spine. -/
class StrictSegal where
  spineToSimplex {m : ℕ} (hmn : m ≤ n + 1) : Path X m → X _[m]ₙ₊₁
  spine_spineToSimplex {m : ℕ} (hmn : m ≤ n + 1) : X.spine hmn ∘ spineToSimplex hmn = id
  spineToSimplex_spine {m : ℕ} (hmn : m ≤ n + 1) : spineToSimplex hmn ∘ X.spine hmn = id

end SSet.Truncated

namespace SSet
open Truncated CategoryTheory SimplexCategory Simplicial

variable (X : SSet.{u})

/-- A path in a simplicial set is defined by 1-truncating, then taking the
1-truncated path. -/
abbrev Path : ℕ → Type u := truncation 1 |>.obj X |>.Path₁

/-- The spine of an `n + 1` simplex in `X` is the path of edges of length
`n + 1` formed by traversing in order through the vertices of the `n + 1`
truncation. -/
abbrev spine {n : ℕ} : X _[n + 1] → X.Path (n + 1) :=
  truncation (n + 1) |>.obj X |>.spine (Nat.le_refl _)

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
-- TODO: can we define this directly in terms of `Truncated.StrictSegal`?
class StrictSegal where
  spineToSimplex {n : ℕ} : Path X (n + 1) → X _[n + 1]
  spine_spineToSimplex {n : ℕ} : X.spine (n := n) ∘ spineToSimplex = id
  spineToSimplex_spine {n : ℕ} : spineToSimplex ∘ X.spine (n := n) = id

instance strictSegal_of_strictSegal
    [∀ n : ℕ, Truncated.StrictSegal ((truncation (n + 1)).obj X)] :
    StrictSegal X where
  spineToSimplex {n} :=
    Truncated.StrictSegal.spineToSimplex (X := (truncation (n + 1)).obj X) (Nat.le_refl _)
  spine_spineToSimplex {n} :=
    Truncated.StrictSegal.spine_spineToSimplex (Nat.le_refl _)
  spineToSimplex_spine {n} :=
    Truncated.StrictSegal.spineToSimplex_spine (Nat.le_refl _)

end SSet

namespace SSet.Truncated.StrictSegal

open SimplexCategory

variable {n} {X : SSet.Truncated.{u} (n + 1)} [StrictSegal X]

/-- The fields of `StrictSegal` define an equivalence between `X [m]ₙ₊₁` and `Path X m`.-/
def spineEquiv {m : ℕ} (hmn : m ≤ n + 1) : X _[m]ₙ₊₁ ≃ Path X m where
  toFun := spine X hmn
  invFun := spineToSimplex hmn
  left_inv := by
    exact congrFun (spineToSimplex_spine (X := X) hmn)
  right_inv := by
    exact congrFun (spine_spineToSimplex (X := X) hmn)

theorem spineInjective {m : ℕ} (hmn : m ≤ n + 1) : Function.Injective (spineEquiv (X := X) hmn) :=
  Equiv.injective _

@[simp]
theorem spineToSimplex_vertex {m : ℕ} (hmn : m ≤ n + 1) (i : Fin (m + 1)) (f : Path X m) :
    X.map (const (SimplexCategory.mk 0) (SimplexCategory.mk m) i).op (spineToSimplex hmn f) =
      f.vertex i := by
  rw [← spine_vertex]
  congr
  exact (congrFun (spine_spineToSimplex (X := X) hmn) f)

  -- , spine_spineToSimplex]

@[simp]
theorem spineToSimplex_arrow {m : ℕ} (hmn : m ≤ n + 1) (i : Fin m) (f : Path X m) :
    X.map (mkOfSucc i).op (spineToSimplex hmn f) = f.arrow i := by
  rw [← spine_arrow]
  congr
  exact congrFun (spine_spineToSimplex (X := X) hmn) f

/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
def spineToDiagonal {m : ℕ} (hmn : m ≤ n + 1) (f : Path X m) : X _[1]ₙ₊₁ :=
    X.map ((SimplexCategory.diag m).op) (spineToSimplex hmn f)

end SSet.Truncated.StrictSegal

namespace SSet.Truncated


/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _[0]₂` as its underlying
type. -/
def OneTruncation₂ (S : SSet.Truncated 2) := S _[0]₂

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

/-- The hom-types of the refl quiver underlying a simplicial set `S` are types of edges in `S _[1]₂`
together with source and target equalities. -/
@[ext]
structure OneTruncation₂.Hom {S : SSet.Truncated 2} (X Y : OneTruncation₂ S) where
  /-- An arrow in `OneTruncation₂.Hom X Y` includes the data of a 1-simplex. -/
  edge : S _[1]₂
  /-- An arrow in `OneTruncation₂.Hom X Y` includes a source equality. -/
  src_eq : S.map (δ₂ 1).op edge = X
  /-- An arrow in `OneTruncation₂.Hom X Y` includes a target equality. -/
  tgt_eq : S.map (δ₂ 0).op edge = Y

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
instance (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom X Y := OneTruncation₂.Hom X Y
  id X :=
    { edge := S.map (σ₂ (n := 0) 0).op X
      src_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply]
      tgt_eq := by
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero,
          op_id, FunctorToTypes.map_id_apply] }

-- lemma OneTruncation₂.reflPrefunctor_map {S T : SSet.Truncated 2}
--     (F : OneTruncation₂ S ⥤rq OneTruncation₂ T) {X Y : OneTruncation₂ S} (f : Hom)

@[simp]
lemma OneTruncation₂.id_edge {S : SSet.Truncated 2} (X : OneTruncation₂ S) :
    OneTruncation₂.Hom.edge (𝟙rq X) = S.map (σ₂ 0).op X := rfl

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
@[simps]
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map {S T} F := {
    obj := F.app (op ⟨SimplexCategory.mk 0, by decide⟩)
    map := fun f ↦
      { edge := F.app _ f.edge
        src_eq := by rw [← FunctorToTypes.naturality, f.src_eq]
        tgt_eq := by rw [← FunctorToTypes.naturality, f.tgt_eq] }
    map_id := fun X ↦ OneTruncation₂.Hom.ext (by
      dsimp
      rw [← FunctorToTypes.naturality]) }

@[ext]
lemma OneTruncation₂.hom_ext {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y} :
    f.edge = g.edge → f = g := OneTruncation₂.Hom.ext

/-- The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι0₂ : (⟨SimplexCategory.mk 0, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/-- The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι1₂ : (⟨SimplexCategory.mk 0, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/-- The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι2₂ : (⟨SimplexCategory.mk 0, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/-- The initial vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ

/-- The middle vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ

/-- The final vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

/-- The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ0₂ : (⟨SimplexCategory.mk 1, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 1) 0

/-- The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ1₂ : (⟨SimplexCategory.mk 1, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 1) 1

/-- The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ2₂ : (⟨SimplexCategory.mk 1, by decide⟩ : SimplexCategory.Truncated 2) ⟶
    ⟨SimplexCategory.mk 2, by decide⟩ := δ₂ (n := 1) 2

private lemma map_map_of_eq.{w}  {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  change (V.map _ ≫ V.map _) _ = _
  rw [← map_comp]; rfl

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
0th face of a 2-simplex. -/
def ev12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
1st face of a 2-simplex. -/
def ev02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
2nd face of a 2-simplex. -/
def ev01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, map_map_of_eq V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), map_map_of_eq V rfl⟩

/-- A refl prefunctor between the underlying refl quivers of a 2-truncated simplicial sets induces a
map on paths. -/
def reflPrefunctorPathMap {X Y : SSet.Truncated.{u} 2} (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    {n : ℕ} (σ : Path X n) : Path Y n where
      vertex i := F.obj (σ.vertex i)
      arrow i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).edge
      arrow_src i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).src_eq
      arrow_tgt i := (F.map ⟨σ.arrow i, σ.arrow_src i, σ.arrow_tgt i⟩).tgt_eq

/-- The components of a map of 2-truncated simplicial sets built from a map on underlying reflexive
quivers, under the assumption that the codomain is `StrictSegal`. -/
def toStrictSegal₂.mk.app {X Y : SSet.Truncated 2} [StrictSegal Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    (n : SimplexCategory.Truncated 2) : X.obj (op n) ⟶ Y.obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => F.obj x
  | 1 => exact fun f => (F.map ⟨f, rfl, rfl⟩).edge
  | 2 => exact fun φ =>
          StrictSegal.spineToSimplex (X := Y) (Nat.le_refl _)
            (reflPrefunctorPathMap F (X.spine (Nat.le_refl _) φ))

@[simp] theorem toStrictSegal₂.mk.app_zero {X Y : SSet.Truncated 2} [StrictSegal Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (x : X _[0]₂) :
    mk.app F ⟨SimplexCategory.mk 0, by decide⟩ x = F.obj x := rfl

@[simp] theorem toStrictSegal₂.mk.app_one {X Y : SSet.Truncated 2} [StrictSegal Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (f : X _[1]₂) :
    mk.app F ⟨SimplexCategory.mk 1, by decide⟩ f = (F.map ⟨f, rfl, rfl⟩).edge := rfl

@[simp] theorem toStrictSegal₂.mk.app_two {X Y : SSet.Truncated 2} [StrictSegal Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y) (φ : X _[2]₂) :
    mk.app F ⟨SimplexCategory.mk 2, by decide⟩ φ =
      StrictSegal.spineToSimplex
        (Nat.le_refl _) (reflPrefunctorPathMap F (X.spine (Nat.le_refl _) φ)) := rfl

/-- A map of 2-truncated simplicial sets built from a map on underlying reflexive quivers, under
the assumption that the codomain is `StrictSegal`. -/
@[simps!]
def toStrictSegal₂.mk {X Y : SSet.Truncated 2} [StrictSegal Y]
    (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)
    (hyp : (φ : X _[2]₂) → (F.map (ev02₂ φ)).edge =
      StrictSegal.spineToDiagonal
        (Nat.le_refl _) (reflPrefunctorPathMap F (X.spine (Nat.le_refl _) φ))) : X ⟶ Y where
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
    have const10 (α : (⟨[1], by decide⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[0], by decide⟩) :
        OK α := by
      ext x
      cases SimplexCategory.eq_const_to_zero α
      have lem : [1].const [0] 0 = σ₂ (n := 0) 0 := by ext i; match i with | 0 | 1 => rfl
      rw [lem]
      simp only [types_comp_apply, mk.app_zero]
      rw [← OneTruncation₂.id_edge, ← OneTruncation₂.id_edge]
      have := congrArg (fun f => f.edge) (ReflPrefunctor.map_id F x)
      rw [← ReflPrefunctor.map_id]
      simp only [mk.app_one]
      congr 1
      · simp only [OneTruncation₂.id_edge]
        refine congrArg F.obj ?_
        refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
        rw [← map_comp, ← op_comp, δ₂_one_comp_σ₂_zero, op_id, CategoryTheory.Functor.map_id]
      · simp only [OneTruncation₂.id_edge]
        refine congrArg F.obj ?_
        refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
        rw [← map_comp, ← op_comp, δ₂_zero_comp_σ₂_zero, op_id, CategoryTheory.Functor.map_id]
      · have : ∀ f a b (h1 : X.map (δ₂ 1).op f = a) (h2 : X.map (δ₂ 0).op f = b), x = a → x = b →
          f = X.map (σ₂ (n := 0) 0).op x →
          HEq (F.map ⟨f, h1, h2⟩) (F.map (ReflQuiver.id (obj := OneTruncation₂ X) x)) := by
            rintro _ _ _ h1 h2 rfl rfl rfl
            refine congr_arg_heq F.map ?_
            apply OneTruncation₂.hom_ext
            simp only [len_mk, id_eq, Nat.reduceAdd, Fin.isValue]
            rw [← OneTruncation₂.id_edge]
        apply this
        · simp only [SimplexCategory.len_mk]
          refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
          rw [← map_comp, ← op_comp, δ₂_one_comp_σ₂_zero, op_id, CategoryTheory.Functor.map_id]
        · simp only [SimplexCategory.len_mk]
          refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
          rw [← map_comp, ← op_comp, δ₂_zero_comp_σ₂_zero, op_id, CategoryTheory.Functor.map_id]
        · simp
    have const01 (α : (⟨[0], by decide⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[1], by decide⟩) :
        OK α := by
      ext f
      obtain ⟨i : Fin 2, rfl⟩ := exists_eq_const_of_zero α
      match i with
      | 0 =>
        have lem : [0].const [1] 0 = δ₂ 1 := by ext i; match i with | 0 => rfl
        rw [lem]
        simp only [id_eq, types_comp_apply, mk.app_zero, mk.app_one]
        rw [OneTruncation₂.Hom.src_eq]
      | 1 =>
        have lem : [0].const [1] 1 = δ₂ 0 := by ext i; match i with | 0 => rfl
        rw [lem]
        simp only [id_eq, types_comp_apply, mk.app_zero, mk.app_one]
        rw [OneTruncation₂.Hom.tgt_eq]
    have const02 (α : (⟨[0], by decide⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[2], by decide⟩) :
        OK α := by
      ext φ
      obtain ⟨i : Fin 3, rfl⟩ := exists_eq_const_of_zero α
      match i with
      | 0 =>
        have lem : [0].const [2] 0 = ι0₂ := by ext i; match i with | 0 => rfl
        rw [lem]
        dsimp only [id_eq, types_comp_apply, mk.app_zero]
        simp only [mk.app_two]
        sorry
      | 1 =>
        have lem :  [0].const [2] 1 = ι1₂ := by ext i; match i with | 0 => rfl
        rw [lem]
        sorry
      | 2 =>
        have lem :  [0].const [2] 2 = ι2₂ := by ext i; match i with | 0 => rfl
        rw [lem]
        sorry
    have nat1m {m hm} (α : (⟨[1], by decide⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩) :
        OK α := by
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
    have nat2m (α : (⟨[2], by decide⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩) :
        OK α := by
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
          show F.obj (X.map (𝟙 _).op x) = Y.map (𝟙 _).op (F.obj x)
          simp [Functor.map_id]
        | 1 => apply const01
        | 2 => apply const02
      | 1 => apply nat1m
      | 2 => apply nat2m

end SSet.Truncated
