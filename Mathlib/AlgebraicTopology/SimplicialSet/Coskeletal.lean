/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial sets

In this file, we prove that if `X` is `StrictSegal` then `X` is 2-coskeletal,
i.e. `X ≅ (cosk 2).obj X`. In particular, nerves of categories are 2-coskeletal.

This isomorphism follows from the fact that `rightExtensionInclusion X 2` is a right Kan
extension. In fact, we show that when `X` is `StrictSegal` then
`(rightExtensionInclusion X n).IsPointwiseRightKanExtension` holds.

As an example, `SimplicialObject.IsCoskeletal (nerve C) 2` shows that that nerves of categories
are 2-coskeletal.
-/


universe v u

open CategoryTheory Simplicial SimplexCategory Opposite Category Functor Limits

namespace SSet

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`.-/
@[simps!]
def rightExtensionInclusion (X : SSet.{u}) (n : ℕ) :
    RightExtension (Truncated.inclusion (n := n)).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by dsimp; omega⟩ : SimplexCategory.Truncated 2))

open StructuredArrow

namespace StrictSegal
variable (X : SSet.{u}) [StrictSegal X]

namespace isPointwiseRightKanExtensionAt

/-- A morphism in `SimplexCategory` with domain `[0]`, `[1]`, or `[2]` defines an object in the
comma category `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op`.-/
abbrev strArrowMk₂ {i : ℕ} {n : ℕ} (φ : [i] ⟶ [n]) (hi : i ≤ 2) :
    StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  StructuredArrow.mk (Y := op ⟨[i], hi⟩) (by exact φ.op)

/-- Given a term in the cone over the diagram
`(proj (op [n]) ((Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X)` where `X` is
Strict Segal, one can produce an `n`-simplex in `X`. -/
@[simp]
noncomputable def lift {X : SSet.{u}} [StrictSegal X] {n}
    (s : Cone (proj (op [n]) (Truncated.inclusion 2).op ⋙
      (Truncated.inclusion 2).op ⋙ X)) (x : s.pt) : X _[n] :=
  StrictSegal.spineToSimplex {
    vertex := fun i ↦ s.π.app (.mk (Y := op [0]₂) (.op (SimplexCategory.const _ _ i))) x
    arrow := fun i ↦ s.π.app (.mk (Y := op [1]₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))) x
    arrow_src := fun i ↦ by
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) (by simp) ⟶
        strArrowMk₂ ([0].const _ i.castSucc) (by simp) :=
          StructuredArrow.homMk (δ 1).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact congr_fun (s.w φ) x
    arrow_tgt := fun i ↦ by
      dsimp
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) (by simp) ⟶
          strArrowMk₂ ([0].const _ i.succ) (by simp) :=
        StructuredArrow.homMk (δ 0).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact congr_fun (s.w φ) x }

lemma fac_aux₁ {n : ℕ}
    (s : Cone (proj (op [n]) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i : ℕ) (hi : i < n) :
    X.map (mkOfSucc ⟨i, hi⟩).op (lift s x) =
      s.π.app (strArrowMk₂ (mkOfSucc ⟨i, hi⟩) (by omega)) x := by
  dsimp [lift]
  rw [spineToSimplex_arrow]
  rfl

lemma fac_aux₂ {n : ℕ}
    (s : Cone (proj (op [n]) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    X.map (mkOfLe ⟨i, by omega⟩ ⟨j, by omega⟩ hij).op (lift s x) =
      s.π.app (strArrowMk₂ (mkOfLe ⟨i, by omega⟩ ⟨j, by omega⟩ hij) (by omega)) x := by
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  revert i j
  induction k with
  | zero =>
      rintro i j hij hj hik
      obtain rfl : i = j := by omega
      have : mkOfLe ⟨i, Nat.lt_add_one_of_le hj⟩ ⟨i, Nat.lt_add_one_of_le hj⟩ (by omega) =
        [1].const [0] 0 ≫ [0].const [n] ⟨i, Nat.lt_add_one_of_le hj⟩ := Hom.ext_one_left _ _
      rw [this]
      let α : (strArrowMk₂ ([0].const [n] ⟨i, Nat.lt_add_one_of_le hj⟩) (by omega)) ⟶
        (strArrowMk₂ ([1].const [0] 0 ≫ [0].const [n] ⟨i, Nat.lt_add_one_of_le hj⟩) (by omega)) :=
            StructuredArrow.homMk (([1].const [0] 0).op) (by simp; rfl)
      have nat := congr_fun (s.π.naturality α) x
      dsimp only [Fin.val_zero, Nat.add_zero, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
        Int.reduceAdd, Fin.eta, comp_obj, StructuredArrow.proj_obj, op_obj, const_obj_obj,
        const_obj_map, types_comp_apply, types_id_apply, Functor.comp_map, StructuredArrow.proj_map,
        op_map] at nat
      rw [nat, op_comp, Functor.map_comp]
      simp only [types_comp_apply]
      refine congrArg (X.map ([1].const [0] 0).op) ?_
      unfold strArrowMk₂
      rw [lift, StrictSegal.spineToSimplex_vertex]
      congr
  | succ k hk =>
      intro i j hij hj hik
      let α := strArrowMk₂ (mkOfLeComp (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩
          ⟨j, by omega⟩ (by simp)
        (by simp only [Fin.mk_le_mk]; omega)) (by rfl)
      let α₀ := strArrowMk₂ (mkOfLe (n := n) ⟨i + k, by omega⟩ ⟨j, by omega⟩
        (by simp only [Fin.mk_le_mk]; omega)) (by simp)
      let α₁ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨j, by omega⟩
        (by simp only [Fin.mk_le_mk]; omega)) (by simp)
      let α₂ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩ (by simp)) (by simp)
      let β₀ : α ⟶ α₀ := StructuredArrow.homMk ((mkOfSucc 1).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₁ : α ⟶ α₁ := StructuredArrow.homMk ((δ 1).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₂ : α ⟶ α₂ := StructuredArrow.homMk ((mkOfSucc 0).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      have h₀ : X.map α₀.hom (lift s x) = s.π.app α₀ x := by
        obtain rfl : j = (i + k) + 1 := by omega
        exact fac_aux₁ _ _ _ _ (by omega)
      have h₂ : X.map α₂.hom (lift s x) = s.π.app α₂ x :=
        hk i (i + k) (by simp) (by omega) rfl
      change X.map α₁.hom (lift s x) = s.π.app α₁ x
      have : X.map α.hom (lift s x) = s.π.app α x := by
        apply StrictSegal.spineInjective
        apply Path.ext'
        intro t
        dsimp only [spineEquiv]
        rw [Equiv.coe_fn_mk, spine_arrow, spine_arrow,
            ← FunctorToTypes.map_comp_apply]
        match t with
        | 0 =>
            have : α.hom ≫ (mkOfSucc 0).op = α₂.hom :=
              Quiver.Hom.unop_inj (by ext x ; fin_cases x <;> rfl)
            rw [this, h₂, ← congr_fun (s.w β₂) x]
            rfl
        | 1 =>
            have : α.hom ≫ (mkOfSucc 1).op = α₀.hom :=
              Quiver.Hom.unop_inj (by ext x ; fin_cases x <;> rfl)
            rw [this, h₀, ← congr_fun (s.w β₀) x]
            rfl
      rw [← StructuredArrow.w β₁, FunctorToTypes.map_comp_apply, this, ← s.w β₁]
      dsimp

lemma fac_aux₃ {n : ℕ}
    (s : Cone (proj (op [n]) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (φ : [1] ⟶ [n]) :
    X.map φ.op (lift s x) = s.π.app (strArrowMk₂ φ (by omega)) x := by
  obtain ⟨i, j, hij, rfl⟩ : ∃ i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by simp),
      Hom.ext_one_left _ _ rfl rfl⟩
  exact fac_aux₂ _ _ _ _ _ _ (by omega)

end isPointwiseRightKanExtensionAt

open Truncated

open isPointwiseRightKanExtensionAt in
/-- A strict Segal simplicial set is 2-coskeletal. -/
noncomputable def isPointwiseRightKanExtensionAt (n : ℕ) :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtensionAt ⟨[n]⟩ where
  lift s x := lift (X := X) s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f :  _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : ∃ j, SimplexCategory.mk j = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    apply StrictSegal.spineInjective
    dsimp
    ext k
    · dsimp only [spineEquiv, Equiv.coe_fn_mk]
      erw [spine_map_vertex]
      rw [spine_spineToSimplex, spine_vertex]
      let α : strArrowMk₂ f hi ⟶ strArrowMk₂ ([0].const [n] (f.toOrderHom k)) (by omega) :=
        StructuredArrow.homMk (([0].const _ (by exact k)).op) (by simp; rfl)
      exact congr_fun (s.w α).symm x
    · dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
      rw [← FunctorToTypes.map_comp_apply]
      let α : strArrowMk₂ f hi ⟶ strArrowMk₂ (mkOfSucc k ≫ f) (by omega) :=
        StructuredArrow.homMk (mkOfSucc k).op (by simp; rfl)
      exact (isPointwiseRightKanExtensionAt.fac_aux₃ _ _ _ _).trans (congr_fun (s.w α).symm x)
  uniq s m hm := by
    ext x
    apply StrictSegal.spineInjective (X := X)
    dsimp [spineEquiv]
    rw [StrictSegal.spine_spineToSimplex]
    ext i
    · exact congr_fun (hm (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x
    · exact congr_fun (hm (.mk (Y := op [1]₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i))))) x

/-- Since `StrictSegal.isPointwiseRightKanExtensionAt` proves that the appropriate
cones are limit cones, `rightExtensionInclusion X 2` is a pointwise right Kan extension.-/
noncomputable def isPointwiseRightKanExtension :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtension :=
  fun Δ => isPointwiseRightKanExtensionAt X Δ.unop.len

theorem isRightKanExtension :
    X.IsRightKanExtension (𝟙 ((inclusion 2).op ⋙ X)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension X)

/-- When `X` is `StrictSegal`, `X` is 2-coskeletal. -/
instance isCoskeletal : SimplicialObject.IsCoskeletal X 2 where
  isRightKanExtension := isRightKanExtension X

end StrictSegal

end

end SSet

namespace CategoryTheory

namespace Nerve

open SSet

example (C : Type u) [Category.{v} C] :
    SimplicialObject.IsCoskeletal (nerve C) 2 := by infer_instance

/-- The essential data of the nerve functor is contained in the 2-truncation, which is
recorded by the composite functor `nerveFunctor₂`.-/
def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

/-- The natural isomorphism between `nerveFunctor` and `nerveFunctor₂ ⋙ Truncated.cosk 2` whose
components `nerve C ≅ (Truncated.cosk 2).obj (nerveFunctor₂.obj C)` shows that nerves of categories
are 2-coskeletal.-/
noncomputable def cosk₂Iso : nerveFunctor.{v, u} ≅ nerveFunctor₂.{v, u} ⋙ Truncated.cosk 2 :=
  NatIso.ofComponents (fun C ↦ (nerve C).isoCoskOfIsCoskeletal 2)
    (fun _ ↦ (coskAdj 2).unit.naturality _)

end Nerve

end CategoryTheory
