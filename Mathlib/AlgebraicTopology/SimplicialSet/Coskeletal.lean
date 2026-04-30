/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial sets

In this file, we prove that if `X` is `StrictSegal` then `X` is 2-coskeletal,
i.e. `X ≅ (cosk 2).obj X`. In particular, nerves of categories are 2-coskeletal.

This isomorphism follows from the fact that `rightExtensionInclusion X 2` is a right Kan
extension. In fact, we show that when `X` is `StrictSegal` then
`(rightExtensionInclusion X n).IsPointwiseRightKanExtension` holds.

As an example, `SimplicialObject.IsCoskeletal (nerve C) 2` shows that nerves of categories are
2-coskeletal.
-/

@[expose] public section


universe v u

open CategoryTheory Simplicial SimplexCategory Truncated
open Opposite Category Functor Limits

namespace SSet

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`. -/
@[simps! left right_as hom_app]
def rightExtensionInclusion (X : SSet.{u}) (n : ℕ) :
    RightExtension (Truncated.inclusion (n := n)).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

section

open StructuredArrow

namespace StrictSegal
variable {X : SSet.{u}} (sx : StrictSegal X)

namespace isPointwiseRightKanExtensionAt

/-- A morphism in `SimplexCategory` with domain `⦋0⦌`, `⦋1⦌`, or `⦋2⦌` defines an object in the
comma category `StructuredArrow (op ⦋n⦌) (Truncated.inclusion (n := 2)).op`. -/
abbrev strArrowMk₂ {i : ℕ} {n : ℕ} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i ≤ 2 := by lia) :
    StructuredArrow (op ⦋n⦌) (Truncated.inclusion 2).op :=
  StructuredArrow.mk (Y := op ⦋i⦌₂) φ.op

/-- Given a term in the cone over the diagram
`(proj (op ⦋n⦌) ((Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X)` where `X` is
Strict Segal, one can produce an `n`-simplex in `X`. -/
@[simp]
noncomputable def lift {X : SSet.{u}} (sx : StrictSegal X) {n}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙
      (Truncated.inclusion 2).op ⋙ X)) (x : s.pt) : X _⦋n⦌ :=
  sx.spineToSimplex {
    vertex := fun i ↦ s.π.app (.mk (Y := op ⦋0⦌₂) (.op (SimplexCategory.const _ _ i))) x
    arrow := fun i ↦ s.π.app (.mk (Y := op ⦋1⦌₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))) x
    arrow_src := fun i ↦ by
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) ⟶
        strArrowMk₂ (⦋0⦌.const _ i.castSucc) :=
          StructuredArrow.homMk (Hom.tr (δ 1)).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact ConcreteCategory.congr_hom (s.w φ) x
    arrow_tgt := fun i ↦ by
      dsimp
      let φ : strArrowMk₂ (mkOfLe _ _ (Fin.castSucc_le_succ i)) ⟶
          strArrowMk₂ (⦋0⦌.const _ i.succ) :=
        StructuredArrow.homMk (Hom.tr (δ 0)).op
          (Quiver.Hom.unop_inj (by ext x; fin_cases x; rfl))
      exact ConcreteCategory.congr_hom (s.w φ) x }

lemma fac_aux₁ {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i : ℕ) (hi : i < n) :
    X.map (mkOfSucc ⟨i, hi⟩).op (lift sx s x) =
      s.π.app (strArrowMk₂ (mkOfSucc ⟨i, hi⟩)) x := by
  dsimp [lift]
  rw [spineToSimplex_arrow]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma fac_aux₂ {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    X.map (mkOfLe ⟨i, by lia⟩ ⟨j, by lia⟩ hij).op (lift sx s x) =
      s.π.app (strArrowMk₂ (mkOfLe ⟨i, by lia⟩ ⟨j, by lia⟩ hij)) x := by
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  revert i j
  induction k with
  | zero =>
      rintro i j hij hj hik
      obtain rfl : i = j := hik
      have : mkOfLe ⟨i, Nat.lt_add_one_of_le hj⟩ ⟨i, Nat.lt_add_one_of_le hj⟩ (by rfl) =
        ⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩ := Hom.ext_one_left _ _
      rw [this]
      let α : (strArrowMk₂ (⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩)) ⟶
        (strArrowMk₂ (⦋1⦌.const ⦋0⦌ 0 ≫ ⦋0⦌.const ⦋n⦌ ⟨i, Nat.lt_add_one_of_le hj⟩)) :=
            StructuredArrow.homMk ((Hom.tr (⦋1⦌.const ⦋0⦌ 0)).op) (by simp; rfl)
      conv_rhs => dsimp; rw [dsimp% s.π.naturality_apply α x]
      rw [op_comp, Functor.map_comp]
      simp only [types_comp_apply]
      refine congrArg (X.map (⦋1⦌.const ⦋0⦌ 0).op) ?_
      unfold strArrowMk₂
      rw [lift, StrictSegal.spineToSimplex_vertex]
      congr
  | succ k hk =>
      intro i j hij hj hik
      let α := strArrowMk₂ (mkOfLeComp (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩
          ⟨j, by omega⟩ (by simp) (by simp only [Fin.mk_le_mk]; omega))
      let α₀ := strArrowMk₂ (mkOfLe (n := n) ⟨i + k, by omega⟩ ⟨j, by omega⟩
        (by simp only [Fin.mk_le_mk]; omega))
      let α₁ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨j, by omega⟩ hij)
      let α₂ := strArrowMk₂ (mkOfLe (n := n) ⟨i, by omega⟩ ⟨i + k, by omega⟩ (by simp))
      let β₀ : α ⟶ α₀ := StructuredArrow.homMk ((Hom.tr (mkOfSucc 1)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₁ : α ⟶ α₁ := StructuredArrow.homMk ((Hom.tr (δ 1)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      let β₂ : α ⟶ α₂ := StructuredArrow.homMk ((Hom.tr (mkOfSucc 0)).op) (Quiver.Hom.unop_inj
        (by ext x; fin_cases x <;> rfl))
      have h₀ : X.map α₀.hom (lift sx s x) = s.π.app α₀ x := by
        subst hik
        exact fac_aux₁ _ _ _ _ hj
      have h₂ : X.map α₂.hom (lift sx s x) = s.π.app α₂ x :=
        hk i (i + k) (by simp) (by lia) rfl
      change X.map α₁.hom (lift sx s x) = s.π.app α₁ x
      have : X.map α.hom (lift sx s x) = s.π.app α x := by
        apply sx.spineInjective
        apply Path.ext'
        intro t
        dsimp [spineEquiv, α]
        rw [← Functor.map_comp_apply]
        match t with
        | 0 =>
            have : α.hom ≫ (mkOfSucc 0).op = α₂.hom :=
              Quiver.Hom.unop_inj (by ext x; fin_cases x <;> rfl)
            rw [dsimp% [α] this]
            dsimp [α₂] at h₂ ⊢
            rw [h₂, ← dsimp% [α₂] ConcreteCategory.congr_hom (s.w β₂) x]
            rfl
        | 1 =>
            have : α.hom ≫ (mkOfSucc 1).op = α₀.hom :=
              Quiver.Hom.unop_inj (by ext x; fin_cases x <;> rfl)
            rw [dsimp% [α] this]
            dsimp [α₀] at h₀ ⊢
            rw [h₀, ← dsimp% [α₀] ConcreteCategory.congr_hom (s.w β₀) x]
            rfl
      rw [← StructuredArrow.w β₁, Functor.map_comp_apply]
      dsimp [fromPUnit] at this ⊢
      rw [this, ← s.w β₁]
      dsimp

lemma fac_aux₃ {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (Truncated.inclusion 2).op ⋙ (Truncated.inclusion 2).op ⋙ X))
    (x : s.pt) (φ : ⦋1⦌ ⟶ ⦋n⦌) :
    X.map φ.op (lift sx s x) = s.π.app (strArrowMk₂ φ) x := by
  obtain ⟨i, j, hij, rfl⟩ : ∃ i j hij, φ = mkOfLe i j hij :=
    ⟨φ.toOrderHom 0, φ.toOrderHom 1, φ.toOrderHom.monotone (by decide),
      Hom.ext_one_left _ _ rfl rfl⟩
  exact fac_aux₂ _ _ _ _ _ _ (by lia)

end isPointwiseRightKanExtensionAt

open Truncated

set_option backward.defeqAttrib.useBackward true in
open isPointwiseRightKanExtensionAt in
/-- A strict Segal simplicial set is 2-coskeletal. -/
noncomputable def isPointwiseRightKanExtensionAt (n : ℕ) :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtensionAt ⟨⦋n⦌⟩ where
  lift s := ↾fun x ↦ lift sx s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : ∃ j, ⦋j⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    apply sx.spineInjective
    dsimp
    ext k
    · dsimp only [spineEquiv, Equiv.coe_fn_mk]
      rw [dsimp% show op f = f.op from rfl]
      rw [spine_map_vertex, spine_spineToSimplex_apply, spine_vertex]
      let α : strArrowMk₂ f hi ⟶ strArrowMk₂ (⦋0⦌.const ⦋n⦌ (f.toOrderHom k)) :=
        StructuredArrow.homMk ((Hom.tr (⦋0⦌.const _ (by exact k))).op) (by simp; rfl)
      exact ConcreteCategory.congr_hom (s.w α).symm x
    · dsimp only [spineEquiv, Equiv.coe_fn_mk, spine_arrow]
      rw [← Functor.map_comp_apply]
      let α : strArrowMk₂ f ⟶ strArrowMk₂ (mkOfSucc k ≫ f) :=
        StructuredArrow.homMk (Hom.tr (mkOfSucc k)).op (by simp)
      exact (isPointwiseRightKanExtensionAt.fac_aux₃ _ _ _ _).trans
        (ConcreteCategory.congr_hom (s.w α).symm x)
  uniq s m hm := by
    ext x
    apply sx.spineInjective (X := X)
    -- simp? [spineEquiv] says:
    simp only [spineEquiv, RightExtension.coneAt_pt, rightExtensionInclusion_left,
      TypeCat.Fun.toFun_apply, Equiv.coe_fn_mk, lift, Nat.reduceAdd, ObjectProperty.ι_obj,
      const_obj_obj, comp_obj, proj_obj, mk_right, op_obj, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      spine_spineToSimplex_apply]
    ext i
    · exact ConcreteCategory.congr_hom (hm (StructuredArrow.mk
        (Y := op ⦋0⦌₂) (⦋0⦌.const ⦋n⦌ i).op)) x
    · exact ConcreteCategory.congr_hom (hm (.mk (Y := op ⦋1⦌₂)
        (.op (mkOfLe _ _ (Fin.castSucc_le_succ i))))) x

/-- Since `StrictSegal.isPointwiseRightKanExtensionAt` proves that the appropriate
cones are limit cones, `rightExtensionInclusion X 2` is a pointwise right Kan extension. -/
noncomputable def isPointwiseRightKanExtension :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtension :=
  fun Δ => sx.isPointwiseRightKanExtensionAt Δ.unop.len

theorem isRightKanExtension (sx : StrictSegal X) :
    X.IsRightKanExtension (𝟙 ((inclusion 2).op ⋙ X)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    sx.isPointwiseRightKanExtension

/-- When `X` is `StrictSegal`, `X` is 2-coskeletal. -/
theorem isCoskeletal (sx : StrictSegal X) :
    SimplicialObject.IsCoskeletal X 2 where
  isRightKanExtension := sx.isRightKanExtension

/-- When `X` satisfies `IsStrictSegal`, `X` is 2-coskeletal. -/
instance isCoskeletal' [IsStrictSegal X] : SimplicialObject.IsCoskeletal X 2 :=
  isCoskeletal <| ofIsStrictSegal X

end StrictSegal

end

end SSet

namespace CategoryTheory

namespace Nerve

open SSet

instance (C : Type u) [Category.{v} C] :
    SimplicialObject.IsCoskeletal (nerve C) 2 := inferInstance

/-- The essential data of the nerve functor is contained in the 2-truncation, which is
recorded by the composite functor `nerveFunctor₂`. -/
def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

set_option backward.defeqAttrib.useBackward true in
instance (X : Cat.{v, u}) : (nerveFunctor₂.obj X).IsStrictSegal := by
  dsimp [nerveFunctor₂]
  infer_instance

/-- The natural isomorphism between `nerveFunctor` and `nerveFunctor₂ ⋙ Truncated.cosk 2` whose
components `nerve C ≅ (Truncated.cosk 2).obj (nerveFunctor₂.obj C)` shows that nerves of categories
are 2-coskeletal. -/
noncomputable def cosk₂Iso : nerveFunctor.{v, u} ≅ nerveFunctor₂.{v, u} ⋙ Truncated.cosk 2 :=
  NatIso.ofComponents (fun C ↦ (nerve C).isoCoskOfIsCoskeletal 2)
    (fun _ ↦ (coskAdj 2).unit.naturality _)

end Nerve

end CategoryTheory
