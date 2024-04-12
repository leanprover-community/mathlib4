import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.MorphismProperty

universe v v'

open CategoryTheory Category Limits Preadditive ZeroObject

namespace AddCommGroupCat

lemma isZero (X : AddCommGroupCat) (hX : ∀ (x : X), x = 0) :
    CategoryTheory.Limits.IsZero X := by
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  ext x
  exact hX x

@[simps]
def uliftFunctor : AddCommGroupCat.{v'} ⥤ AddCommGroupCat.{max v v'} where
  obj G := AddCommGroupCat.of (ULift.{v, v'} G.α)
  map f := AddCommGroupCat.ofHom (AddMonoidHom.mk' (uliftFunctor.map f) (by
    rintro ⟨a⟩ ⟨b⟩
    dsimp
    rw [map_add]
    rfl))

@[simps!]
def addEquivULiftFunctorObj (X : AddCommGroupCat.{v'}) :
    uliftFunctor.{v, v'}.obj X ≃+ X :=
  AddEquiv.mk' Equiv.ulift (fun _ _ => rfl)

instance : uliftFunctor.{v, v'}.Additive where

instance : uliftFunctor.{v, v'}.Faithful where
  map_injective {G₁ G₂} f g h := by
    ext x
    change (uliftFunctor.{v, v'}.map f ⟨x⟩).down = (uliftFunctor.{v, v'}.map g ⟨x⟩).down
    rw [h]

instance : uliftFunctor.{v, v'}.Full where
  preimage {X Y} f := AddMonoidHom.mk' (fun x => (f ⟨x⟩).down) (by
    rintro a b
    dsimp
    erw [f.map_add ⟨a⟩ ⟨b⟩]
    rfl)

lemma _root_.CategoryTheory.ShortComplex.ab_exact_iff_ulift
    (S : ShortComplex (AddCommGroupCat.{v'})) :
    (S.map (uliftFunctor.{v, v'})).Exact ↔ S.Exact := by
  simp only [ShortComplex.ab_exact_iff]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂⟩ (congr_arg ULift.up.{v, v'} hx₂)
    exact ⟨x₁.down, congr_arg ULift.down hx₁⟩
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h x₂.down (congr_arg ULift.down.{v, v'} hx₂)
    exact ⟨ULift.up x₁, congr_arg ULift.up hx₁⟩

def ShortComplexIso (S : ShortComplex AddCommGroupCat.{v}) (S' : ShortComplex AddCommGroupCat.{v'}) :=
  S.map (uliftFunctor.{v', v}) ≅ S'.map (uliftFunctor.{v, v'})

@[simps!]
def _root_.AddEquiv.toIsoULift {A : AddCommGroupCat.{v}} {B : AddCommGroupCat.{v'}} (e : A ≃+ B) :
    uliftFunctor.{v', v}.obj A ≅ uliftFunctor.{v, v'}.obj B :=
  AddEquiv.toAddCommGroupCatIso ((addEquivULiftFunctorObj.{v', v} A).trans
    (e.trans (addEquivULiftFunctorObj.{v, v'} B).symm))

lemma mono_iff_ulift {X Y : AddCommGroupCat.{v'}} (f : X ⟶ Y) :
    Mono (uliftFunctor.{v, v'}.map f) ↔ Mono f := by
  simp only [mono_iff_injective]
  constructor
  · intro h x₁ x₂ eq
    exact Equiv.ulift.{v, v'}.symm.injective (h (congr_arg ULift.up eq))
  · intro h x₁ x₂ eq
    exact Equiv.ulift.{v, v'}.injective (h (congr_arg ULift.down eq))

lemma epi_iff_ulift {X Y : AddCommGroupCat.{v'}} (f : X ⟶ Y) :
    Epi (uliftFunctor.{v, v'}.map f) ↔ Epi f := by
  simp only [epi_iff_surjective]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h ⟨y⟩
    exact ⟨x.down, Equiv.ulift.{v, v'}.symm.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y.down
    exact ⟨⟨x⟩, Equiv.ulift.{v, v'}.injective hx⟩

section

variable {X₁ X₂ : AddCommGroupCat.{v}} (f : X₁ ⟶ X₂)
  {X₁' X₂' : AddCommGroupCat.{v'}} (f' : X₁' ⟶ X₂')
  (e₁ : X₁ ≃+ X₁') (e₂ : X₂ ≃+ X₂')
  (comm : ∀ (x₁ : X₁), f' (e₁ x₁) = e₂ (f x₁))

@[simps!]
def arrowIsoMk : Arrow.mk (uliftFunctor.{v', v}.map f) ≅
    Arrow.mk (uliftFunctor.{v, v'}.map f') :=
  Arrow.isoMk e₁.toIsoULift e₂.toIsoULift (by
    ext x₁
    exact Equiv.ulift.injective (comm x₁.down))

lemma mono_iff_of_addEquiv : Mono f ↔ Mono f' := by
  rw [← mono_iff_ulift.{v', v} f, ← mono_iff_ulift.{v, v'} f']
  exact (MorphismProperty.RespectsIso.monomorphisms _).arrow_mk_iso_iff
    (arrowIsoMk f f' e₁ e₂ comm)

lemma epi_iff_of_addEquiv : Epi f ↔ Epi f' := by
  rw [← epi_iff_ulift.{v', v} f, ← epi_iff_ulift.{v, v'} f']
  exact (MorphismProperty.RespectsIso.epimorphisms _).arrow_mk_iso_iff
    (arrowIsoMk f f' e₁ e₂ comm)

end

section

variable
  (S : ShortComplex AddCommGroupCat.{v}) (S' : ShortComplex AddCommGroupCat.{v'})
  (e₁ : S.X₁ ≃+ S'.X₁) (e₂ : S.X₂ ≃+ S'.X₂) (e₃ : S.X₃ ≃+ S'.X₃)
  (commf : ∀ (x₁ : S.X₁), S'.f (e₁ x₁) = e₂ (S.f x₁))
  (commg : ∀ (x₂ : S.X₂), S'.g (e₂ x₂) = e₃ (S.g x₂))

def shortComplexULiftIsoMk : S.map (uliftFunctor.{v', v}) ≅ S'.map (uliftFunctor.{v, v'}) :=
  ShortComplex.isoMk e₁.toIsoULift e₂.toIsoULift e₃.toIsoULift (by
    ext x₁
    exact Equiv.ulift.injective (commf x₁.down)) (by
    ext x₂
    exact Equiv.ulift.injective (commg x₂.down))

lemma _root_.ShortComplex.ab_exact_iff_of_addEquiv :
    S.Exact ↔ S'.Exact := by
  rw [← ShortComplex.ab_exact_iff_ulift.{v', v} S,
    ← ShortComplex.ab_exact_iff_ulift.{v, v'} S']
  exact ShortComplex.exact_iff_of_iso (shortComplexULiftIsoMk S S' e₁ e₂ e₃ commf commg)

lemma _root_.ShortComplex.exact_and_mono_f_iff_of_addEquiv :
    (S.Exact ∧ Mono S.f) ↔ (S'.Exact ∧ Mono S'.f) := by
  rw [ShortComplex.ab_exact_iff_of_addEquiv S S' e₁ e₂ e₃ commf commg,
    mono_iff_of_addEquiv S.f S'.f e₁ e₂ commf]

lemma _root_.ShortComplex.exact_and_epi_g_iff_of_addEquiv :
    (S.Exact ∧ Epi S.g) ↔ (S'.Exact ∧ Epi S'.g) := by
  rw [ShortComplex.ab_exact_iff_of_addEquiv S S' e₁ e₂ e₃ commf commg,
    epi_iff_of_addEquiv S.g S'.g e₂ e₃ commg]

end

section

variable
  {S S' : Arrow₂ AddCommGroupCat.{v}}
  (e₀ : S.X₀ ≃+ S'.X₀) (e₁ : S.X₁ ≃+ S'.X₁) (e₂ : S.X₂ ≃+ S'.X₂)
  (commf : ∀ (x₁ : S.X₀), S'.f (e₀ x₁) = e₁ (S.f x₁))
  (commg : ∀ (x₂ : S.X₁), S'.g (e₁ x₂) = e₂ (S.g x₂))

@[simps!]
def arrow₂IsoMk : S ≅ S' :=
  Arrow₂.isoMk e₀.toAddCommGroupCatIso
    e₁.toAddCommGroupCatIso e₂.toAddCommGroupCatIso
      (by ext; apply commf) (by ext; apply commg)

end

end AddCommGroupCat
