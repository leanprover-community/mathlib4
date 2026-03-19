/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Arrow

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Quasicategory/Nerve.lean`,
we show that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in
  `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean`.

-/

@[expose] public section

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.
-/
@[kerodon 003A]
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n + 1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = Λ[n, i].ι ≫ σ := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_def] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_def, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory. -/
@[kerodon 003C]
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

set_option backward.isDefEq.respectTransparency false in
lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : S _⦋n + 2⦌, ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl

open MonoidalCategory

variable {X Y : SSet} (S : X.Subcomplex) (T : Y.Subcomplex)

def Subcomplex.unionProd {X Y : SSet} (S : X.Subcomplex) (T : Y.Subcomplex) :
    (X ⊗ Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

noncomputable def Subcomplex.prodIso (S : X.Subcomplex) (T : Y.Subcomplex) :
    (S.prod T : SSet) ≅ (S : SSet) ⊗ (T : SSet) where
  hom := CartesianMonoidalCategory.lift
    (lift ((S.prod T).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((S.prod T).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (S.ι ⊗ₘ T.ι) (by
    intro n ⟨x, y⟩ ⟨⟨x', y'⟩, h⟩
    refine ⟨sorry, sorry⟩)

noncomputable def Subcomplex.unionProd.ι₁ : X ⊗ T ⟶ unionProd S T :=
  lift (X ◁ T.ι) (by
    intro n ⟨x₁, x₂⟩ h
    simp [unionProd, Set.prod]
    apply Or.inl
    have := h.2
    rw [← this]
    simp at h
    sorry
    )

noncomputable def ι₂ : (S : SSet.{u}) ⊗ Y ⟶ (unionProd S T : SSet.{u}) :=
  lift (S.ι ▷ Y) (by
    ext m ⟨x₁, x₂⟩
    simp [unionProd, Set.prod]
    exact Or.inr x₁.2)

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl

lemma sq : Sq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  max_eq := rfl
  min_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, setOf]
    tauto

lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (sq S T).isPushout.of_iso
    (Subcomplex.prodIso _ _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerRightIso (topIso X) _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

noncomputable
def Subcomplex.unionProdtoSSetIso : (S.unionProd T).toSSet ≅
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) S.ι T.ι).pt where
  hom := by

    sorry
  inv := by
    refine Limits.pushout.desc ?_ ?_ ?_
    . simp [unionProd]
      sorry
    . simp
      sorry
    . sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

noncomputable
def Subcomplex.unionProdιIso : Arrow.mk (S.unionProd T).ι ≅ (S.ι □ T.ι) := by
  refine Arrow.isoMk' _ _ (unionProdtoSSetIso S T) (Iso.refl _) ?_
  · simp
    sorry


end SSet
