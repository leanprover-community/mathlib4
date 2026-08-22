/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# The fundamental groupoid of a Kan complex

...

-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace Edge

-- this should be moved somewhere else
variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- A left homotopy between two edges `e` and `e'` is a `CompStruct e (id _) e'`. -/
abbrev HomotopyL (e e' : Edge x₀ x₁) := CompStruct e (.id x₁) e'

/-- A right homotopy between two edges `e` and `e'` is a `CompStruct (id _) e e'`. -/
abbrev HomotopyR (e e' : Edge x₀ x₁) := CompStruct (.id x₀) e e'

variable [Quasicategory X]

/-- The composition of two edges in a quasicategory. -/
@[no_expose]
noncomputable def comp (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
    Edge x₀ x₂ :=
  Truncated.Edge.comp e₀₁ e₁₂

/-- If `e₀₁ : Edge x₀ x₁` and `e₁₂ : Edge x₁ x₂` are edges in a quasicategory,
this is a structure exhibiting the fact that `e₀₁.edge e₁₂` is a composition
of `e₀₁` and `e₁₂`. -/
@[no_expose]
noncomputable def compStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
    CompStruct e₀₁ e₁₂ (e₀₁.comp e₁₂) :=
  Truncated.Edge.compStruct e₀₁ e₁₂

/-- The associativity of the composition of edges in a quasicategory. -/
@[no_expose]
noncomputable def assoc
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₁ e₁₃ e₀₃) :
    CompStruct e₀₂ e₂₃ e₀₃ :=
  Truncated.Edge.assoc h₀₂ h₁₃ h

/-- The associativity of the composition of edges in a quasicategory. -/
@[no_expose]
noncomputable def assoc'
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₂ e₂₃ e₀₃) :
    CompStruct e₀₁ e₁₃ e₀₃ :=
  Truncated.Edge.assoc' h₀₂ h₁₃ h

/-- In quasicategory, two left homotopic edges are also right homotopic. -/
noncomputable def HomotopyL.homotopyR {e e' : Edge x₀ x₁} (h : HomotopyL e e') :
    HomotopyR e e' :=
  assoc' (.idComp e) (.compId e) h

/-- In quasicategory, two right homotopic edges are also left homotopic. -/
noncomputable def HomotopyR.homotopyL {e e' : Edge x₀ x₁} (h : HomotopyR e e') :
    HomotopyL e e' :=
  assoc (.idComp e) (.compId e) h

/-- If we have structures `CompStruct e₀₁ e₁₂ e₀₂` and
`CompStruct e₀₁' e₁₂' e₀₂'` involving edges in a quasicategory,
`e₀₁` and `e₀₁'` are left homotopic and `e₁₂` and `e₁₂'` are left homotopic,
then `e₀₂` and `e₀₂'` are left homotopic. -/
@[no_expose]
noncomputable def CompStruct.unique
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂)
    {e₀₁' : Edge x₀ x₁} {e₁₂' : Edge x₁ x₂} {e₀₂' : Edge x₀ x₂}
    (h' : CompStruct e₀₁' e₁₂' e₀₂')
    (h₀₁ : HomotopyL e₀₁ e₀₁') (h₁₂ : HomotopyL e₁₂ e₁₂') :
    HomotopyL e₀₂ e₀₂' :=
  Truncated.Edge.CompStruct.unique h h' h₀₁ h₁₂

/-- If we have a structure `CompStruct e₀₁ e₁₂ e₀₂` and `e₀₂` is
left homotopic to `e₀₂'`, then there is a `CompStruct e₀₁ e₁₂ e₀₂'` structure. -/
@[no_expose]
noncomputable def CompStruct.unique'
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) {e₀₂' : Edge x₀ x₂}
    (h' : HomotopyL e₀₂ e₀₂') :
    CompStruct e₀₁ e₁₂ e₀₂' :=
  Edge.assoc' h (.compId _) h'

end Edge

namespace Edge

variable [KanComplex X]

variable {x y : X _⦋0⦌} (e : Edge x y)

lemma exists_right_inverse : ∃ (e' : Edge y x), Nonempty (CompStruct e e' (.id x)) := by
  let φ (j : Fin 3) (hk : j ≠ 0) : Δ[1] ⟶ X :=
    if j = 1 then const x else yonedaEquiv.symm e.edge
  have hφ : horn.IsCompatible φ := by
    rw [horn.isCompatible_iff]
    intro j k
    fin_cases j <;> fin_cases k <;> simp [φ, yonedaEquiv_symm_zero]
  refine ⟨Edge.mk (yonedaEquiv (stdSimplex.δ 0 ≫ hφ.liftOfKanComplex))
    (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_),
    ⟨Edge.CompStruct.mk (yonedaEquiv hφ.liftOfKanComplex) ?_ ?_ ?_⟩⟩
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp),
      hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      dsimp% stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0),
      hφ.δ_liftOfKanComplex 1 (by simp), φ, yonedaEquiv_symm_zero]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [stdSimplex.yonedaEquiv_δ_comp]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 1 (by simp), φ,
      σ_zero_eq_yonedaEquiv_const]

lemma exists_left_inverse : ∃ (e' : Edge y x), Nonempty (CompStruct e' e (.id y)) := by
  obtain ⟨e', ⟨h⟩⟩ := exists_right_inverse e.op
  exact ⟨e'.unop, ⟨h.unop.ofEq rfl rfl (by simp)⟩⟩

instance : Nonempty e.InvStruct := by
  have : KanComplex X := inferInstance
  obtain ⟨e₁, ⟨h₁⟩⟩ := e.exists_left_inverse
  obtain ⟨e₂, ⟨h₂⟩⟩ := e.exists_right_inverse
  exact ⟨{
    inv := e₁
    homInvId :=
      assoc' h₂ (HomotopyR.homotopyL (Edge.assoc h₁ h₂ (.compId _))) (.idCompId _)
    invHomId := h₁
  }⟩

/-- A choice of `Edge.InvStruct` structure in a Kan complex. -/
@[no_expose]
noncomputable def invStruct : e.InvStruct := Classical.arbitrary _

/-- A choice of inverse of an edge in a Kan complex. -/
noncomputable abbrev inv : Edge y x := e.invStruct.inv

/-- If `e` is an edge of Kan complex, then `e.inv` is a right inverse to `e`. -/
noncomputable abbrev homInvId : CompStruct e e.inv (.id x) := e.invStruct.homInvId

/-- If `e` is an edge of Kan complex, then `e.inv` is a left inverse to `e`. -/
noncomputable abbrev invHomId : CompStruct e.inv e (.id y) := e.invStruct.invHomId

end Edge

variable [KanComplex X]

namespace KanComplex

open Truncated.HomotopyCategory₂ in
instance : IsGroupoid (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)) where
  all_isIso := by
    rintro ⟨x : X _⦋0⦌⟩ ⟨y : X _⦋0⦌⟩ f
    obtain ⟨e, rfl⟩ := homMk_surjective f
    let γ := (Edge.ofTruncated e).invStruct
    exact ⟨homMk γ.inv, γ.homInvId.homotopyCategory₂_fac,
      γ.invHomId.homotopyCategory₂_fac⟩

noncomputable instance : Groupoid (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)) :=
  .ofIsGroupoid

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
open Truncated.HomotopyCategory₂ in
/-- If `X` is a Kan complex, then `Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)`
is isomorphic to `FundamentalGroupoid X`. -/
@[implicit_reducible, simps -isSimp]
noncomputable def isoCatFundamentalGroupoid :
    IsoCat (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X))
      (FundamentalGroupoid X) where
  functor :=
    Truncated.HomotopyCategory₂.desc
      (fun x ↦ .mk x) (fun e ↦ FundamentalGroupoid.homMk (Edge.ofTruncated e))
        FundamentalGroupoid.homMk_id Edge.CompStruct.homMk_comp
  inverse := FundamentalGroupoid.desc (fun x ↦ .mk x) (fun e ↦ homMk e.toTruncated)
    (fun h ↦ h.homotopyCategory₂_fac)
  unit_eq := Truncated.HomotopyCategory₂.functor_ext
  counit_eq := FundamentalGroupoid.functor_ext

variable (X) in
/-- If `X` is a Kan complex, then `Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)`
is equivalent to `FundamentalGroupoid X`. -/
noncomputable abbrev equivalenceFundamentalGroupoid :
    Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X) ≌
      (FundamentalGroupoid X) :=
  (isoCatFundamentalGroupoid X).toEquivalence

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma isoCatFundamentalGroupoid_functor_map_homMk
    {x y : X _⦋0⦌} (e : Edge x y) :
    (isoCatFundamentalGroupoid X).functor.map (Truncated.HomotopyCategory₂.homMk e.toTruncated) =
      FundamentalGroupoid.homMk e := by
  simp [isoCatFundamentalGroupoid_functor]

end KanComplex

namespace FundamentalGroupoid

open KanComplex

set_option backward.isDefEq.respectTransparency.types false in
lemma homMk_surjective {x y : X _⦋0⦌} :
    Function.Surjective (homMk : Edge x y → _) := by
  intro f
  obtain ⟨f, rfl⟩ := (isoCatFundamentalGroupoid X).functor.map_surjective f
  obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory₂.homMk_surjective f
  exact ⟨Edge.ofTruncated e, by simp [isoCatFundamentalGroupoid_functor]⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec_of_kanComplex {x y : X _⦋0⦌} (motive : (mk x ⟶ mk y) → Prop)
    (homMk : ∀ (e : Edge x y), motive (homMk e)) (f : mk x ⟶ mk y) :
    motive f := by
  obtain ⟨e, rfl⟩ := homMk_surjective f
  exact homMk e

lemma homMk_eq_iff_nonempty_homotopyL {x y : X _⦋0⦌} {e e' : Edge x y} :
    homMk e = homMk e' ↔ Nonempty (Edge.HomotopyL e e') := by
  change _ ↔ Truncated.HomotopicL e.toTruncated e'.toTruncated
  simp only [← Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicL,
    ← (isoCatFundamentalGroupoid X).functor.map_injective_iff,
    isoCatFundamentalGroupoid_functor_map_homMk]

lemma homMk_eq_iff_nonempty_homotopyR {x y : X _⦋0⦌} {e e' : Edge x y} :
    homMk e = homMk e' ↔ Nonempty (Edge.HomotopyR e e') := by
  rw [homMk_eq_iff_nonempty_homotopyL]
  apply Truncated.homotopicL_iff_homotopicR

lemma homMk_comp_iff {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ ↔ Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ h.homMk_comp⟩
  rw [(Edge.compStruct e₀₁ e₁₂).homMk_comp, homMk_eq_iff_nonempty_homotopyL] at h
  obtain ⟨h⟩ := h
  exact ⟨Edge.CompStruct.unique' (Edge.compStruct e₀₁ e₁₂) h⟩

@[simp]
lemma homMk_inv {x y : X _⦋0⦌} (e : Edge x y) :
    homMk e.inv = inv (homMk e) := by
  simpa [← cancel_mono (homMk e), IsIso.inv_hom_id] using e.invHomId.homMk_comp

end FundamentalGroupoid

end SSet
