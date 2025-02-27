/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects in an abelian category form a Serre class

-/

universe v u

open CategoryTheory ZeroObject

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

lemma isIso_iff_subobjectMk_eq :
    IsIso f ↔ Subobject.mk A.1.hom = Subobject.mk B.1.hom := by
  rw [isIso_iff_isIso_left, isIso_left_iff_subobjectMk_eq]

end MonoOver

namespace Subobject

lemma mk_surjective {X : C} (S : Subobject X) :
    ∃ (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i :=
  ⟨_, S.arrow, inferInstance, by simp⟩

instance (X : C) : (representative (X := X)).IsEquivalence := by
  dsimp only [representative]
  infer_instance

lemma subsingleton_of_isZero {X : C} (hX : IsZero X) : Subsingleton (Subobject X) := by
  suffices ∀ (S : Subobject X), S = .mk (𝟙 _) from ⟨fun S₁ S₂ ↦ by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  let e : A ≅ X :=
    { hom := i
      inv := hX.to_ A
      hom_inv_id := by rw [← cancel_mono i]; apply hX.eq_of_tgt
      inv_hom_id := hX.eq_of_tgt _ _ }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])

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

variable {X} in
lemma not_strictMono_of_isNoetherianObject
    [IsNoetherianObject X] (f : ℕ → Subobject X) :
    ¬ StrictMono f :=
  (isNoetherianObject_iff_not_strictMono X).1 inferInstance f

lemma isNoetherianObject_iff_monoOver_chain_condition :
    IsNoetherianObject X ↔ ∀ (F : ℕ ⥤ MonoOver X),
      IsFiltered.IsEventuallyConstant F := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  constructor
  · intro h G
    obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver _).inverse).monotone⟩
    refine ⟨n, fun m hm ↦ ?_⟩
    rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact hn m (leOfHom hm)
  · intro h F
    obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ Subobject.representative)
    refine ⟨n, fun m hm ↦ ?_⟩
    simpa [← MonoOver.isIso_iff_isIso_left, isIso_iff_of_reflects_iso,
      PartialOrder.isIso_iff_eq] using hn (homOfLE hm)

variable {X} in
lemma monoOver_chain_condition_of_isNoetherianObject [IsNoetherianObject X]
    (F : ℕ ⥤ MonoOver X) : IsFiltered.IsEventuallyConstant F :=
  (isNoetherianObject_iff_monoOver_chain_condition X).1 inferInstance F

variable {X Y}

lemma isNoetherianObject_of_isZero (hX : IsZero X) : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm ↦ Subsingleton.elim _ _⟩

instance [HasZeroObject C] : (isNoetherianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isNoetherianObject.is_iff]
    exact isNoetherianObject_of_isZero (isZero_zero C)⟩

lemma isNoetherianObject_of_mono (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.map i).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.map_obj_injective i (hn m hm)⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isNoetherianObject.is_iff] at hY ⊢
    exact isNoetherianObject_of_mono f

@[simps (config := .lemmasOnly)]
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

instance : (isNoetherianObject (C := C)).IsClosedUnderQuotients where
  prop_of_epi f _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    exact isNoetherianObject_of_epi f

section

variable (S : ShortComplex C)

@[simps]
noncomputable def fromMonoOverOfShortComplex :
    MonoOver S.X₂ ⥤ ShortComplex C where
  obj A :=
    { X₁ := pullback A.1.hom S.f
      X₂ := A.1.left
      X₃ := Abelian.image (A.1.hom ≫ S.g)
      f := pullback.fst _ _
      g := Abelian.factorThruImage _
      zero := by ext; simp [pullback.condition_assoc] }
  map {A B} φ :=
    { τ₁ := ((MonoOver.pullback S.f).map φ).left
      τ₂ := φ.left
      τ₃ := ((MonoOver.abelianImage S.g).map φ).left
      comm₁₂ := by simp [MonoOver.pullback, MonoOver.forget]
      comm₂₃ := by ext; simp [MonoOver.abelianImage] }

variable {S}

lemma shortExact_fromMonoOverOfShortComplex_obj
    (hS : S.ShortExact) (A : MonoOver S.X₂) :
    ((fromMonoOverOfShortComplex S).obj A).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  dsimp [fromMonoOverOfShortComplex]
  exact
    { exact := by
        rw [ShortComplex.exact_iff_exact_up_to_refinements]
        intro Y x₂ hx₂
        dsimp at x₂ hx₂ ⊢
        rw [← cancel_mono (Abelian.image.ι _), Category.assoc,
          kernel.lift_ι, zero_comp] at hx₂
        obtain ⟨A', π, _, x₁, hx₁⟩  :=
          hS.exact.exact_up_to_refinements (x₂ ≫ A.obj.hom) (by simpa using hx₂)
        exact ⟨A', π, inferInstance, pullback.lift (π ≫ x₂) x₁ (by simpa),
          by simp⟩}

end

lemma isIso_monoOver_iff_of_shortExact
    {S : ShortComplex C} (hS : S.ShortExact)
    {A B : MonoOver S.X₂} (φ : A ⟶ B) :
    IsIso φ ↔ IsIso ((MonoOver.pullback S.f).map φ) ∧
      IsIso ((MonoOver.abelianImage S.g).map φ):= by
  constructor
  · intro
    constructor <;> infer_instance
  · rintro ⟨h₁, h₃⟩
    rw [MonoOver.isIso_iff_isIso_left] at h₁ h₃ ⊢
    let ψ := ((fromMonoOverOfShortComplex S).map φ)
    have : IsIso ψ.τ₁ := h₁
    have : IsIso ψ.τ₃ := h₃
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ
      (shortExact_fromMonoOverOfShortComplex_obj hS _)
      (shortExact_fromMonoOverOfShortComplex_obj hS _)

lemma isNoetherianObject_of_shortExact {S : ShortComplex C}
    (hS : S.ShortExact) (h₁ : IsNoetherianObject S.X₁)
    (h₃ : IsNoetherianObject S.X₃) :
    IsNoetherianObject S.X₂ := by
  rw [isNoetherianObject_iff_monoOver_chain_condition]
  intro F₂
  obtain ⟨n₁, hn₁⟩ := monoOver_chain_condition_of_isNoetherianObject
    (F₂ ⋙ MonoOver.pullback S.f)
  obtain ⟨n₃, hn₃⟩ := monoOver_chain_condition_of_isNoetherianObject
    (F₂ ⋙ MonoOver.abelianImage S.g)
  refine ⟨max n₁ n₃, fun m hm ↦ ?_⟩
  rw [isIso_monoOver_iff_of_shortExact hS]
  exact ⟨hn₁.isIso_map _ (homOfLE (le_max_left n₁ n₃)),
    hn₃.isIso_map _ (homOfLE (le_max_right n₁ n₃))⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    exact isNoetherianObject_of_shortExact hS h₁ h₃

instance : (isNoetherianObject (C := C)).IsSerreClass where

end Abelian

end CategoryTheory
