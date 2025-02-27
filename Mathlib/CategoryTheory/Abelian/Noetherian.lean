/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects in an abelian category

-/

universe v u

open CategoryTheory

lemma PartialOrder.isIso_iff_eq {C : Type u} [PartialOrder C]
    {X Y : C} (f : X ⟶ Y) : IsIso f ↔ X = Y := by
  constructor
  · intro _
    exact _root_.le_antisymm (leOfHom f) (leOfHom (inv f))
  · rintro rfl
    obtain rfl : f = 𝟙 _ := rfl
    infer_instance

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MonoOver

variable {X : C} {A B : MonoOver X} (f : A ⟶ B)

instance [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((MonoOver.forget _ ⋙ Over.forget _).map f))

lemma isIso_iff_isIso_left : IsIso f ↔ IsIso f.left := by
  constructor
  · intro
    infer_instance
  · intro
    exact ⟨MonoOver.homMk (inv f.left) (by simpa using (MonoOver.w f).symm),
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩

lemma isIso_left_iff_subobjectMk_eq :
    IsIso f.left ↔ Subobject.mk A.1.hom = Subobject.mk B.1.hom := by
  constructor
  · intro
    exact Subobject.mk_eq_mk_of_comm _ _ (asIso f.left) (by simp)
  · intro h
    exact ⟨Subobject.ofMkLEMk _ _ h.symm.le, by simp [← cancel_mono A.1.hom],
      by simp [← cancel_mono B.1.hom]⟩

end MonoOver

namespace Subobject

instance (X : C) : (representative (X := X)).IsEquivalence := by
  dsimp only [representative]
  infer_instance

end Subobject

namespace Abelian

variable [Abelian C] {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (p : X ⟶ X') (q : Y ⟶ Y') (fac : f ≫ q = p ≫ f')

noncomputable def image.map : Abelian.image f ⟶ Abelian.image f' :=
  kernel.map _ _ q (cokernel.map _ _ p q fac) (by simp)

@[reassoc (attr := simp)]
lemma image.map_ι :
    image.map f f' p q fac ≫ Abelian.image.ι f' = Abelian.image.ι f ≫ q := by
  simp [image.map]

end Abelian

-- to be moved
namespace ObjectProperty

variable (P : ObjectProperty C)

@[mk_iff]
class Is (X : C) : Prop where
  prop : P X

lemma prop_of_is (X : C) [P.Is X] : P X := by rwa [← P.is_iff]

lemma is_of_prop {X : C} (hX : P X) : P.Is X := by rwa [P.is_iff]

end ObjectProperty

def isNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (Subobject X)

variable (X Y : C)

abbrev IsNoetherianObject : Prop := isNoetherianObject.Is X

instance [IsNoetherianObject X] : WellFoundedGT (Subobject X) :=
  isNoetherianObject.prop_of_is X

lemma isNoetherianObject_iff_monotone_chain_condition :
    IsNoetherianObject X ↔ ∀ (f : ℕ →o Subobject X),
      ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m := by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject,
    wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
lemma monotone_chain_condition_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ →o Subobject X) :
    ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f n = f m :=
  (isNoetherianObject_iff_monotone_chain_condition X).1 inferInstance f

lemma isNoetherianObject_iff_not_strictMono :
    IsNoetherianObject X ↔ ∀ (f : ℕ → Subobject X), ¬ StrictMono f := by
  refine ⟨fun _ ↦ not_strictMono_of_wellFoundedGT, fun h ↦ ?_⟩
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject, WellFoundedGT,
    isWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  exact ⟨fun f ↦ h f.toFun (fun a b h ↦ f.map_rel_iff.2 h)⟩

lemma not_strictMono_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ → Subobject X) :
    ¬ StrictMono f :=
  (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

lemma isNoetherianObject_iff_monoOver_chain_condition :
    IsNoetherianObject X ↔ ∀ (F : ℕ ⥤ MonoOver X),
      ∃ (n : ℕ), ∀ (m : ℕ) (a : n ⟶ m), IsIso (F.map a).left := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  constructor
  · intro h G
    obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver _).inverse).monotone⟩
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [MonoOver.isIso_left_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · intro h F
    obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ Subobject.representative)
    refine ⟨n, fun m hm ↦ ?_⟩
    have := hn m (homOfLE hm)
    simpa [← MonoOver.isIso_iff_isIso_left, isIso_iff_of_reflects_iso,
      PartialOrder.isIso_iff_eq] using hn m (homOfLE hm)

variable {X Y}

lemma isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩

@[simps]
noncomputable def MonoOver.abelianImage [Abelian C] (f : X ⟶ Y) :
    MonoOver X ⥤ MonoOver Y where
  obj A := MonoOver.mk' (Abelian.image.ι (A.1.hom ≫ f))
  map {A B} g := MonoOver.homMk (Abelian.image.map _ _ g.left (𝟙 _) (by simp))

noncomputable def Subobject.abelianImage [Abelian C] (f : X ⟶ Y) :
    Subobject X ⥤ Subobject Y :=
  lower (MonoOver.abelianImage f)

lemma Subobject.mk_abelianImageι_eq [Abelian C]
    (f : X ⟶ Y) {Z : C} (π : X ⟶ Z) [Epi π] (ι : Z ⟶ Y) [Mono ι] (fac : π ≫ ι = f):
    mk (Abelian.image.ι f) = mk ι := by
  let g : Z ⟶ Abelian.image f := kernel.lift _ ι (by
    rw [← cancel_epi π, reassoc_of% fac, cokernel.condition, comp_zero])
  have fac₁ : g ≫ Abelian.image.ι f = ι := by simp [g]
  have fac₂ : π ≫ g = Abelian.factorThruImage f := by
    rw [← cancel_mono (Abelian.image.ι f), Category.assoc, fac₁, kernel.lift_ι, fac]
  have := mono_of_mono_fac fac₁
  have := epi_of_epi_fac fac₂
  have := isIso_of_mono_of_epi g
  exact (mk_eq_mk_of_comm _ _ (asIso g) fac₁).symm

lemma Subobject.abelianImage_obj_mk [Abelian C] (f : X ⟶ Y)
    {A B : C} (i : A ⟶ X) [Mono i] (π : A ⟶ B) [Epi π] (ι : B ⟶ Y) [Mono ι]
    (fac : i ≫ f = π ≫ ι) :
    (abelianImage f).obj (.mk i) = .mk ι := by
  exact Subobject.mk_abelianImageι_eq (i ≫ f) π ι fac.symm

lemma Subobject.abelianImage_obj_pullback_obj_of_epi [Abelian C] (p : X ⟶ Y) [Epi p]
    (A : Subobject Y) : (abelianImage p).obj ((pullback p).obj A) = A := by
  revert A
  apply Subobject.ind
  intro A f _
  exact Subobject.abelianImage_obj_mk p (pullback.snd f p) (pullback.fst f p) f
    pullback.condition.symm

lemma Subobject.pullback_obj_injective [Abelian C] (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro A B h
  rw [← abelianImage_obj_pullback_obj_of_epi p A, h, abelianImage_obj_pullback_obj_of_epi]

namespace Abelian

variable [Abelian C]

lemma isNoetherianObject_of_epi (p : X ⟶ Y) [Epi p] [IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.pullback p).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.pullback_obj_injective p (hn m hm)⟩

end Abelian

end CategoryTheory
