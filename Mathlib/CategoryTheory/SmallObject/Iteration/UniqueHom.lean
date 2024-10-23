/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# Uniqueness of morphisms in the category of iterations of functors

Given a functor `Φ : C ⥤ C` and a natural transformation `ε : 𝟭 C ⟶ Φ`,
we show in this file that there exists a unique morphism
between two arbitrary objects in the category `Functor.Iteration ε j`
when `j : J` and `J` is a well orderered set.

-/

universe u

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {Φ : C ⥤ C} {ε : 𝟭 C ⟶ Φ}
  {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] [OrderBot J] (j : J)

namespace Functor

namespace Iteration

namespace Hom

/-- The (unique) morphism between two objects in `Iteration ε ⊥` -/
def mkOfBot (iter₁ iter₂ : Iteration ε (⊥ : J)) : iter₁ ⟶ iter₂ where
  natTrans :=
    { app := fun ⟨i, hi⟩ => eqToHom (by congr; simpa using hi) ≫ iter₁.isoZero.hom ≫
        iter₂.isoZero.inv ≫ eqToHom (by congr; symm; simpa using hi)
      naturality := fun ⟨i, hi⟩ ⟨k, hk⟩ φ => by
        obtain rfl : i = ⊥ := by simpa using hi
        obtain rfl : k = ⊥ := by simpa using hk
        obtain rfl : φ = 𝟙 _ := rfl
        simp }
  natTrans_app_succ i hi := by simp at hi

section

variable {i : J} {iter₁ iter₂ : Iteration ε (wellOrderSucc i)}
  (hi : i < wellOrderSucc i) (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le)

/-- Auxiliary definition for `mkOfSucc`. -/
noncomputable def mkOfSuccNatTransApp (k : J) (hk : k ≤ wellOrderSucc i) :
    iter₁.F.obj ⟨k, hk⟩ ⟶ iter₂.F.obj ⟨k, hk⟩ :=
  if hk' : k = wellOrderSucc i then
    eqToHom (by subst hk'; rfl) ≫ (iter₁.isoSucc i hi).hom ≫
      whiskerRight (φ.natTrans.app ⟨i, by rfl⟩) _ ≫ (iter₂.isoSucc i hi).inv ≫
      eqToHom (by subst hk'; rfl)
  else
    φ.natTrans.app ⟨k, le_of_lt_wellOrderSucc (by
      obtain hk|rfl := hk.lt_or_eq
      · exact hk
      · tauto)⟩

lemma mkOfSuccNatTransApp_eq_of_le (k : J) (hk : k ≤ i) :
    mkOfSuccNatTransApp hi φ k (hk.trans (self_le_wellOrderSucc i)) =
      φ.natTrans.app ⟨k, hk⟩ :=
  dif_neg (by rintro rfl; simpa using lt_of_le_of_lt hk hi)

@[simp]
lemma mkOfSuccNatTransApp_wellOrderSucc_eq :
    mkOfSuccNatTransApp hi φ (wellOrderSucc i) (by rfl) =
      (iter₁.isoSucc i hi).hom ≫ whiskerRight (φ.natTrans.app ⟨i, by rfl⟩) _ ≫
        (iter₂.isoSucc i hi).inv := by
  dsimp [mkOfSuccNatTransApp]
  rw [dif_pos rfl, comp_id, id_comp]

/-- Auxiliary definition for `mkOfSucc`. -/
@[simps]
noncomputable def mkOfSuccNatTrans :
    iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfSuccNatTransApp hi φ k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    dsimp
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂ | rfl := hk₂.lt_or_eq
    · replace h₂ : k₂ ≤ i := le_of_lt_wellOrderSucc h₂
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k₂ h₂,
        mkOfSuccNatTransApp_eq_of_le hi φ k₁ (hk.trans h₂)]
      exact natTrans_naturality φ k₁ k₂ hk h₂
    · obtain h₁ | rfl := hk.lt_or_eq
      · have h₂ : k₁ ≤ i := le_of_lt_wellOrderSucc h₁
        let f₁ : (⟨k₁, hk⟩ : { l | l ≤ wellOrderSucc i}) ⟶
          ⟨i, self_le_wellOrderSucc i⟩ := homOfLE h₂
        let f₂ : (⟨i, self_le_wellOrderSucc i⟩ : { l | l ≤ wellOrderSucc i}) ⟶
          ⟨wellOrderSucc i, by dsimp; rfl⟩ := homOfLE (self_le_wellOrderSucc i)
        obtain rfl : f = f₁ ≫ f₂ := rfl
        rw [Functor.map_comp, Functor.map_comp, assoc,
          mkOfSuccNatTransApp_eq_of_le hi φ k₁ h₂]
        erw [← natTrans_naturality_assoc φ k₁ i h₂ (by rfl)]
        rw [mkOfSuccNatTransApp_wellOrderSucc_eq]
        dsimp
        change _ ≫ iter₁.mapSucc i hi ≫ _ = _ ≫ _ ≫ iter₂.mapSucc i hi
        rw [iter₁.mapSucc_eq i hi, iter₂.mapSucc_eq i hi, assoc,
          Iso.inv_hom_id_assoc]
        ext X
        dsimp
        rw [← ε.naturality_assoc]
        rfl
      · obtain rfl : f = 𝟙 _ := rfl
        rw [Functor.map_id, Functor.map_id, id_comp, comp_id]

end

/-- The (unique) morphism between two objects in `Iteration ε (wellOrderSucc i)`,
assuming we have a morphism between the truncations to `Iteration ε i`. -/
noncomputable def mkOfSucc
    {i : J} (iter₁ iter₂ : Iteration ε (wellOrderSucc i)) (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) :
    iter₁ ⟶ iter₂ where
  natTrans := mkOfSuccNatTrans hi φ
  natTrans_app_zero := by
    dsimp
    rw [mkOfSuccNatTransApp_eq_of_le _ _ _ bot_le, φ.natTrans_app_zero]
    rfl
  natTrans_app_succ k hk := by
    obtain hk' | rfl := (le_of_lt_wellOrderSucc hk).lt_or_eq
    · dsimp
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k hk'.le,
        mkOfSuccNatTransApp_eq_of_le hi φ (wellOrderSucc k) (wellOrderSucc_le hk'),
        φ.natTrans_app_succ _ hk']
      rfl
    · simp [mkOfSuccNatTransApp_eq_of_le hi φ k (by rfl)]

variable {j} {iter₁ iter₂ : Iteration ε j}

section

variable [IsWellOrderLimitElement j]
  (φ : ∀ (i : J) (hi : i < j), iter₁.trunc hi.le ⟶ iter₂.trunc hi.le)

/-- Auxiliary definition for `mkOfLimit`. -/
def mkOfLimitNatTransApp (i : J) (hi : i ≤ j) :
    iter₁.F.obj ⟨i, hi⟩ ⟶ iter₂.F.obj ⟨i, hi⟩ :=
  if h : i < j
    then
      (φ i h).natTrans.app ⟨i, by rfl⟩
    else by
      obtain rfl : i = j := by
        obtain h' | rfl := hi.lt_or_eq
        · exfalso
          exact h h'
        · rfl
      exact (iter₁.isColimit i (show i ≤ i by rfl)).desc (Cocone.mk _
        { app := fun ⟨k, hk⟩ => (φ k hk).natTrans.app ⟨k, by rfl⟩ ≫
            iter₂.F.map (homOfLE (by exact hk.le))
          naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
            have hf : k₁ ≤ k₂ := by simpa using leOfHom f
            dsimp
            rw [comp_id, congr_app (φ k₁ hk₁) ((truncFunctor ε hf).map (φ k₂ hk₂))]
            erw [natTrans_naturality_assoc (φ k₂ hk₂) k₁ k₂ hf (by rfl)]
            dsimp
            rw [← Functor.map_comp, homOfLE_comp] })

lemma mkOfLimitNatTransApp_eq_of_lt (i : J) (hi : i < j) :
    mkOfLimitNatTransApp φ i hi.le = (φ i hi).natTrans.app ⟨i, by rfl⟩ :=
  dif_pos hi

lemma mkOfLimitNatTransApp_naturality_top (i : J) (hi : i < j) :
    iter₁.F.map (homOfLE (by simpa using hi.le) : ⟨i, hi.le⟩ ⟶ ⟨j, by rfl⟩) ≫
      mkOfLimitNatTransApp φ j (by rfl) =
      mkOfLimitNatTransApp φ i hi.le ≫ iter₂.F.map (homOfLE (by simpa using hi.le)) := by
  rw [mkOfLimitNatTransApp_eq_of_lt φ i hi, mkOfLimitNatTransApp, dif_neg (by simp)]
  exact (iter₁.isColimit j (by rfl)).fac _ ⟨i, hi⟩

/-- Auxiliary definition for `mkOfLimit`. -/
@[simps]
def mkOfLimitNatTrans : iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfLimitNatTransApp φ k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂ | rfl := hk₂.lt_or_eq
    · dsimp
      rw [mkOfLimitNatTransApp_eq_of_lt _ k₂ h₂,
        mkOfLimitNatTransApp_eq_of_lt _ k₁ (lt_of_le_of_lt hk h₂),
        congr_app (φ k₁ (lt_of_le_of_lt hk h₂)) ((truncFunctor ε hk).map (φ k₂ h₂))]
      exact natTrans_naturality (φ k₂ h₂) k₁ k₂ hk (by rfl)
    · obtain h₁ | rfl := hk₁.lt_or_eq
      · exact mkOfLimitNatTransApp_naturality_top _ _ h₁
      · obtain rfl : f = 𝟙 _ := rfl
        simp only [map_id, id_comp, comp_id]

/-- The (unique) morphism between two objects in `Iteration ε j` when `j` is a limit element,
assuming we have a morphism between the truncations to `Iteration ε i` for all `i < j`. -/
def mkOfLimit : iter₁ ⟶ iter₂ where
  natTrans := mkOfLimitNatTrans φ
  natTrans_app_zero := by simp [mkOfLimitNatTransApp_eq_of_lt φ ⊥
    (IsWellOrderLimitElement.bot_lt j)]
  natTrans_app_succ i h := by
    dsimp
    have h' := IsWellOrderLimitElement.wellOrderSucc_lt h
    rw [mkOfLimitNatTransApp_eq_of_lt φ _ h',
      (φ _ h').natTrans_app_succ i (self_lt_wellOrderSucc h),
      mkOfLimitNatTransApp_eq_of_lt φ _ h,
      congr_app (φ i h) ((truncFunctor ε (self_le_wellOrderSucc i)).map (φ (wellOrderSucc i) h'))]
    dsimp

end

instance : Nonempty (iter₁ ⟶ iter₂) := by
  let P := fun (i : J) => ∀ (hi : i ≤ j),
    Nonempty ((truncFunctor ε hi).obj iter₁ ⟶ (truncFunctor ε hi).obj iter₂)
  suffices ∀ i, P i from this j (by rfl)
  refine fun _ => WellFoundedLT.induction _ (fun i hi hi' => ?_)
  obtain rfl | ⟨i, rfl, hi''⟩ | _ := eq_bot_or_eq_succ_or_isWellOrderLimitElement i
  · exact ⟨Hom.mkOfBot _ _⟩
  · exact ⟨Hom.mkOfSucc _ _ hi'' ((hi i hi'' (hi''.le.trans hi')).some)⟩
  · exact ⟨Hom.mkOfLimit (fun k hk => (hi k hk (hk.le.trans hi')).some)⟩

noncomputable instance : Unique (iter₁ ⟶ iter₂) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

end Hom

variable {j} (iter₁ iter₂ iter₃ : Iteration ε j)

/-- The canonical isomorphism between two objects in the category `Iteration ε j`. -/
noncomputable def iso : iter₁ ≅ iter₂ where
  hom := default
  inv := default

@[simp]
lemma iso_refl : iso iter₁ iter₁ = Iso.refl _ := by aesop_cat

lemma iso_trans : iso iter₁ iter₃ = iso iter₁ iter₂ ≪≫ iso iter₂ iter₃ := by aesop_cat

end Iteration

end Functor

end CategoryTheory
