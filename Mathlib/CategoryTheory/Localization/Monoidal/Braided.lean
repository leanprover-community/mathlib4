import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection

open CategoryTheory Category MonoidalCategory Monoidal BraidedCategory

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

lemma one (X Y Z : C) : (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom =
    (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
      (Functor.LaxMonoidal.μ (L') (X ⊗ Y) Z) ≫
        (L').map (α_ X Y Z).hom ≫
          (Functor.OplaxMonoidal.δ (L') X (Y ⊗ Z)) ≫
            ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z) := by
  simp

variable [BraidedCategory C]

def braidingNatIsoC : curriedTensor C ≅ (curriedTensor C).flip :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ β_ X Y))

noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε) := by
  infer_instance

noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε).flip :=
  inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip )

noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _  (isoWhiskerRight (braidingNatIsoC (C := C)) _)

lemma two (X Y : C) : ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
    (Functor.LaxMonoidal.μ (L') X Y) ≫
      (L').map (β_ X Y).hom ≫
        (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso, braidingNatIsoC]
  rfl

lemma three (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y ⊗ (L').obj Z)
      ≫ (Functor.LaxMonoidal.μ (L') Y Z) ▷ (L').obj X =
        (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
          ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj (Y ⊗ Z)) := by
  erw [← ((braidingNatIso L W ε).hom.app ((L').obj X)).naturality
    ((Functor.LaxMonoidal.μ (L') Y Z))]
  rw [two]
  rfl

lemma braiding_naturality {X X' Y Y' : LocalizedMonoidal L W ε} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ g) ≫ ((braidingNatIso L W ε).hom.app Y).app Y' =
      ((braidingNatIso L W ε).hom.app X).app X' ≫ (g ⊗ f) := by
  rw [← id_comp f, ← comp_id g, tensor_comp, id_tensorHom, tensorHom_id,
    tensor_comp, id_tensorHom, tensorHom_id, ← assoc]
  erw [← ((braidingNatIso L W ε).app _).hom.naturality g]
  simp only [assoc]
  congr 1
  exact NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality f) Y'

noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) where
  braiding X Y := ((braidingNatIso L W ε).app X).app Y
  braiding_naturality_right X Y Z f := by
    exact ((braidingNatIso L W ε).app X).hom.naturality f
  braiding_naturality_left {X Y} f Z :=
    NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality f) Z
  hexagon_forward X Y Z := by
    obtain ⟨x, ⟨eX⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨y, ⟨eY⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨z, ⟨eZ⟩⟩ : ∃ x, Nonempty ((L').obj x ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (α_ ((L').obj x) ((L').obj y) ((L').obj z)).hom ≫
        (((braidingNatIso L W ε).app ((L').obj x)).app (((L').obj y) ⊗ ((L').obj z))).hom ≫
          (α_ ((L').obj y) ((L').obj z) ((L').obj x)).hom =
        (((braidingNatIso L W ε).app ((L').obj x)).app ((L').obj y)).hom ▷ ((L').obj z) ≫
          (α_ ((L').obj y) ((L').obj x) ((L').obj z)).hom ≫
          ((L').obj y) ◁ (((braidingNatIso L W ε).app ((L').obj x)).app ((L').obj z)).hom by
      refine Eq.trans ?_ ((((eX.inv ⊗ eY.inv) ⊗ eZ.inv) ≫= this =≫
        (eY.hom ⊗ eZ.hom ⊗ eX.hom)).trans ?_)
      · simp only [Iso.app_hom, associator_conjugation, Functor.flip_obj_obj, assoc,
          Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
        rw [← Iso.eq_comp_inv]
        simp only [assoc]
        rw [← associator_conjugation]
        rw [← braiding_naturality]
        simp only [Functor.flip_obj_obj, inv_hom_id_tensor_assoc, MonoidalCategory.id_tensorHom]
        rw [← whiskerLeft_comp_assoc]
        simp
      · simp only [Functor.flip_obj_obj, Iso.app_hom, assoc, ← tensorHom_id]
        simp only [← assoc]
        rw [← tensor_comp, braiding_naturality]
        simp only [Functor.flip_obj_obj, comp_id, assoc]
        rw [← id_comp eZ.inv, tensor_comp, tensorHom_id]
        simp only [assoc]
        congr 1
        rw [← id_tensorHom, ← tensor_comp, ← braiding_naturality]
        simp only [associator_conjugation, id_comp, Functor.flip_obj_obj, assoc,
          Iso.inv_hom_id_assoc, inv_hom_id_tensor, MonoidalCategory.id_tensorHom,
          MonoidalCategory.whiskerLeft_comp, Iso.cancel_iso_hom_left]
        rw [← whiskerLeft_comp_assoc]
        simp
    simp only [one, Iso.app_hom, two]
    slice_rhs 0 4 =>
      simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
        Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
        Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
    simp only [assoc]
    congr 2
    slice_rhs 3 6 =>
      simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
        Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, MonoidalCategory.whiskerLeft_comp,
        Functor.Monoidal.whiskerLeft_δ_μ_assoc, Functor.OplaxMonoidal.δ_natural_right_assoc]
    simp only [← assoc]
    congr 2
    simp only [← Functor.map_comp]
    conv_rhs => rw [assoc, ← hexagon_forward]
    simp only [Functor.map_comp, assoc]
    congr 1
    simp only [← assoc]
    congr 1
    slice_lhs 3 4 =>
      rw [three, two]
    simp
  hexagon_reverse X Y Z := sorry

end CategoryTheory.Localization.Monoidal
