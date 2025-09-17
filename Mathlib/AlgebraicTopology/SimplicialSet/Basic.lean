/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.FinCases

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

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

@[simp]
lemma id_app (X : SSet) (n : SimplexCategoryᵒᵖ) :
    NatTrans.app (𝟙 X) n = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_app {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The constant map of simplicial sets `X ⟶ Y` induced by a simplex `y : Y _[0]`. -/
@[simps]
def const {X Y : SSet.{u}} (y : Y _⦋0⦌) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality _ _ _ := by
    ext
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

@[simp]
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌) :
    f ≫ const z = const z := rfl

@[simp]
lemma const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  ext m x
  simp [FunctorToTypes.naturality]

/-- The ulift functor `SSet.{u} ⥤ SSet.{max u v}` on simplicial sets. -/
def uliftFunctor : SSet.{u} ⥤ SSet.{max u v} :=
  (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

/-- Truncated simplicial sets. -/
def Truncated (n : ℕ) :=
  SimplicialObject.Truncated (Type u) n

namespace Truncated

instance largeCategory (n : ℕ) : LargeCategory (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance hasLimits {n : ℕ} : HasLimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance hasColimits {n : ℕ} : HasColimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

/-- The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets. -/
def uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]
lemma hom_ext {n : ℕ} {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) :
    f = g :=
  NatTrans.ext (funext w)

/-- Further truncation of truncated simplicial sets. -/
abbrev trunc (n m : ℕ) (h : m ≤ n := by omega) :
    SSet.Truncated n ⥤ SSet.Truncated m :=
  SimplicialObject.Truncated.trunc (Type u) n m

end Truncated

/-- The truncation functor on simplicial sets. -/
abbrev truncation (n : ℕ) : SSet ⥤ SSet.Truncated n := SimplicialObject.truncation n

/-- For all `m ≤ n`, `truncation m` factors through `SSet.Truncated n`. -/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc n m ≅ truncation m :=
  Iso.refl _

open SimplexCategory

noncomputable section

/-- The n-skeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
protected abbrev Truncated.sk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.sk n

/-- The n-coskeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
protected abbrev Truncated.cosk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.cosk n

/-- The n-skeleton as an endofunctor on `SSet`. -/
abbrev sk (n : ℕ) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.sk n

/-- The n-coskeleton as an endofunctor on `SSet`. -/
abbrev cosk (n : ℕ) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.cosk n

end

section adjunctions

/-- The adjunction between the n-skeleton and n-truncation. -/
noncomputable def skAdj (n : ℕ) : Truncated.sk n ⊣ truncation.{u} n :=
  SimplicialObject.skAdj n

/-- The adjunction between n-truncation and the n-coskeleton. -/
noncomputable def coskAdj (n : ℕ) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

namespace Truncated

instance cosk_reflective (n) : IsIso (coskAdj n).counit :=
  SimplicialObject.Truncated.cosk_reflective n

instance sk_coreflective (n) : IsIso (skAdj n).unit :=
  SimplicialObject.Truncated.sk_coreflective n

/-- Since `Truncated.inclusion` is fully faithful, so is right Kan extension along it. -/
noncomputable def cosk.fullyFaithful (n) :
    (Truncated.cosk n).FullyFaithful :=
  SimplicialObject.Truncated.cosk.fullyFaithful n

instance cosk.full (n) : (Truncated.cosk n).Full :=
  SimplicialObject.Truncated.cosk.full n

instance cosk.faithful (n) : (Truncated.cosk n).Faithful :=
  SimplicialObject.Truncated.cosk.faithful n

noncomputable instance coskAdj.reflective (n) : Reflective (Truncated.cosk n) :=
  SimplicialObject.Truncated.coskAdj.reflective n

/-- Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it. -/
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

section applications
variable {S : SSet}

lemma δ_comp_δ_apply {n} {i j : Fin (n + 2)} (H : i ≤ j) (x : S _⦋n + 2⦌) :
    S.δ i (S.δ j.succ x) = S.δ j (S.δ i.castSucc x) := congr_fun (S.δ_comp_δ H) x

lemma δ_comp_δ'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) =
      S.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) (S.δ i.castSucc x) :=
  congr_fun (S.δ_comp_δ' H) x

lemma δ_comp_δ''_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j)
    (x : S _⦋n + 2⦌) :
    S.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) (S.δ j.succ x) =
      S.δ j (S.δ i x) := congr_fun (S.δ_comp_δ'' H) x

lemma δ_comp_δ_self_apply {n} {i : Fin (n + 2)} (x : S _⦋n + 2⦌) :
    S.δ i (S.δ i.castSucc x) = S.δ i (S.δ i.succ x) := congr_fun S.δ_comp_δ_self x

lemma δ_comp_δ_self'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) = S.δ i (S.δ i.succ x) := congr_fun (S.δ_comp_δ_self' H) x

lemma δ_comp_σ_of_le_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j)
    (x : S _⦋n + 1⦌) :
    S.δ (Fin.castSucc i) (S.σ j.succ x) = S.σ j (S.δ i x) := congr_fun (S.δ_comp_σ_of_le H) x

@[simp]
lemma δ_comp_σ_self_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.castSucc (S.σ i x) = x :=
  congr_fun S.δ_comp_σ_self x

lemma δ_comp_σ_self'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
    (x : S _⦋n⦌) : S.δ j (S.σ i x) = x := congr_fun (S.δ_comp_σ_self' H) x

@[simp]
lemma δ_comp_σ_succ_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.succ (S.σ i x) = x :=
  congr_fun S.δ_comp_σ_succ x

lemma δ_comp_σ_succ'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _⦋n⦌) :
    S.δ j (S.σ i x) = x := congr_fun (S.δ_comp_σ_succ' H) x

lemma δ_comp_σ_of_gt_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
    (x : S _⦋n + 1⦌) : S.δ i.succ (S.σ (Fin.castSucc j) x) = S.σ j (S.δ i x) :=
  congr_fun (S.δ_comp_σ_of_gt H) x

lemma δ_comp_σ_of_gt'_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
    (x : S _⦋n + 1⦌) : S.δ i (S.σ j x) =
      S.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le)))
        (S.δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) x) :=
  congr_fun (S.δ_comp_σ_of_gt' H) x

lemma σ_comp_σ_apply {n} {i j : Fin (n + 1)} (H : i ≤ j) (x : S _⦋n⦌) :
    S.σ i.castSucc (S.σ j x) = S.σ j.succ (S.σ i x) := congr_fun (S.σ_comp_σ H) x

variable {T : SSet} (f : S ⟶ T)

open Opposite

lemma δ_naturality_apply {n : ℕ} (i : Fin (n + 2)) (x : S _⦋n + 1⦌) :
    f.app (op ⦋n⦌) (S.δ i x) = T.δ i (f.app (op ⦋n + 1⦌) x) := by
  change (S.δ i ≫ f.app (op ⦋n⦌)) x = (f.app (op ⦋n + 1⦌) ≫ T.δ i) x
  exact congr_fun (SimplicialObject.δ_naturality f i) x

lemma σ_naturality_apply {n : ℕ} (i : Fin (n + 1)) (x : S _⦋n⦌) :
    f.app (op ⦋n + 1⦌) (S.σ i x) = T.σ i (f.app (op ⦋n⦌) x) := by
  change (S.σ i ≫ f.app (op ⦋n + 1⦌)) x = (f.app (op ⦋n⦌) ≫ T.σ i) x
  exact congr_fun (SimplicialObject.σ_naturality f i) x

end applications

end SSet
