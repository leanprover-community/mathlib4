import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.HasLimits

universe v u w

namespace CategoryTheory

variable {J : Type u} [Category.{v} J] {F : J ⥤ Type w}

lemma Functor.sections_ext_iff {x y : F.sections} : x = y ↔ ∀ j, x.1 j = y.1 j := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    ext j
    exact h j

namespace Limits

namespace Types

section Limits

variable (c : Cone F)

lemma nonempty_isLimit_iff_bijective_sectionOfCone :
    Nonempty (IsLimit c) ↔ Function.Bijective (Types.sectionOfCone c) := by
  simp only [Function.bijective_iff_existsUnique, isLimit_iff,
    Functor.sections_ext_iff, sectionOfCone]
  constructor
  · intro h x
    exact h x.1 x.2
  · intro h x hx
    exact h ⟨x, hx⟩

variable {c}

lemma sectionOfCone_bijective_of_isLimit (hc : IsLimit c) :
    Function.Bijective (Types.sectionOfCone c) :=
  (nonempty_isLimit_iff_bijective_sectionOfCone c).1 ⟨hc⟩

variable (F)

section

variable [Small.{w} F.sections]

@[simps!]
noncomputable def coneOfSmall : Cone F where
  pt := Shrink F.sections
  π :=
    { app := fun j x => ((equivShrink F.sections).symm x).1 j
      naturality := fun j j' φ => by
        ext t
        obtain ⟨z, rfl⟩ := (equivShrink F.sections).surjective t
        simp }

@[simp]
lemma coneOfSmall_toSections :
    (Types.sectionOfCone (Types.coneOfSmall F)) = (equivShrink F.sections).invFun := by
  ext t
  obtain ⟨z, rfl⟩ := (equivShrink F.sections).surjective t
  simp [sectionOfCone]

noncomputable def isLimitConeOfSmall :
    IsLimit (Types.coneOfSmall F) :=
  Nonempty.some (by simpa only [nonempty_isLimit_iff_bijective_sectionOfCone,
    Types.coneOfSmall_toSections] using (equivShrink F.sections).symm.bijective)

end

lemma hasLimit_iff_small_sections : HasLimit F ↔ Small.{w} F.sections :=
  ⟨fun _ => Small.mk ⟨_, ⟨(Equiv.ofBijective _
      (sectionOfCone_bijective_of_isLimit (limit.isLimit F))).symm⟩⟩,
    fun _ => ⟨_, Types.isLimitConeOfSmall F⟩⟩

end Limits

section Colimits

variable (F)

def Quot'.Rel : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop := fun p p' =>
  ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

def Quot' : Type (max u w) := _root_.Quot (Quot'.Rel F)

variable {F}

variable (c : Cocone F)

def fromQuot' : Quot' F → c.pt :=
  Quot.lift (fun ⟨j, x⟩ => c.ι.app j x) (by
    rintro ⟨j, x⟩ ⟨j', _⟩ ⟨φ : j ⟶ j', rfl : _ = F.map φ x⟩
    exact congr_fun (c.ι.naturality φ).symm x)

@[simp]
lemma fromQuot'_mk (j : J) (x : F.obj j) :
    fromQuot' c (Quot.mk _ ⟨j, x⟩) = c.ι.app j x := rfl

variable {c} in
@[simp]
lemma fromQuot'_naturality {c' : Cocone F} (φ : c ⟶ c') :
    φ.hom ∘ fromQuot' c = fromQuot' c' := by
  ext ⟨j, x⟩
  exact congr_fun (φ.w j) x

namespace SurjectiveFromQuot'OfIsColimit

def cocone : Cocone F where
  pt := Set.range (fromQuot' c)
  ι :=
    { app := fun j x => ⟨c.ι.app j x, ⟨Quot.mk _ ⟨j, x⟩, by simp⟩⟩
      naturality := fun j j' φ => by
        ext x
        rw [Subtype.ext_iff]
        exact congr_fun (c.ι.naturality φ) x }

variable {c}

def isColimit (hc : IsColimit c) : IsColimit (cocone c) where
  desc s x := hc.desc s x.1
  fac s j := by
    ext x
    exact congr_fun (hc.fac s j) x
  uniq s m hm := by
    ext ⟨_, ⟨j, x⟩, rfl⟩
    exact (congr_fun ((hm j).trans (hc.fac s j).symm) x)

lemma surjective_fromQuot' : Function.Surjective (fromQuot' (cocone c)) := by
  rintro ⟨_, ⟨j, x⟩, rfl⟩
  exact ⟨Quot.mk _ ⟨j, x⟩, rfl⟩

end SurjectiveFromQuot'OfIsColimit

section

variable {c}
variable (hc : IsColimit c)

lemma surjective_fromQuot'_of_isColimit :
    Function.Surjective (fromQuot' c) := by
  rw [← fromQuot'_naturality (IsColimit.uniqueUpToIso
    (SurjectiveFromQuot'OfIsColimit.isColimit hc) hc).hom]
  apply Function.Surjective.comp
  · exact (IsColimit.coconePointUniqueUpToIso
      (SurjectiveFromQuot'OfIsColimit.isColimit hc) hc).toEquiv.surjective
  · apply SurjectiveFromQuot'OfIsColimit.surjective_fromQuot'

lemma injective_fromQuot'_of_isColimit :
    Function.Injective (fromQuot' c) := by
  classical
  have := hc
  rintro ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ h
  dsimp at h
  let π : Quot' F → ULift.{w} (Fin 2) :=
    fun x => if (Quot.mk _ ⟨j₁, x₁⟩ = x) then ULift.up 0 else ULift.up 1
  by_contra!
  have : π (Quot.mk _ ⟨j₁, x₁⟩) ≠ π (Quot.mk _ ⟨j₂, x₂⟩) := by
    dsimp only [π]
    rw [if_pos rfl, if_neg (by assumption)]
    simp
  let s : Cocone F := Cocone.mk (ULift.{w} (Fin 2))
    { app := fun j x => π (Quot.mk _ ⟨j, x⟩)
      naturality := fun j j' f => by
        ext x
        exact congr_arg π (Quot.sound ⟨f, rfl⟩).symm }
  have hs : ∀ (j : J) (x : F.obj j),
      (hc.desc s) (c.ι.app j x) = π (Quot.mk _ ⟨j, x⟩) :=
    fun j x => congr_fun (hc.fac s j) x
  apply this
  rw [← hs, ← hs, h]

lemma bijective_fromQuot'_of_isColimit :
    Function.Bijective (fromQuot' c) :=
  ⟨injective_fromQuot'_of_isColimit hc, surjective_fromQuot'_of_isColimit hc⟩

end

lemma nonempty_isColimit_iff_bijective_fromQuot' :
    Nonempty (IsColimit c) ↔ Function.Bijective (fromQuot' c) := by
  refine' ⟨fun hc => bijective_fromQuot'_of_isColimit hc.some, fun hc => ⟨_⟩⟩
  let e := Equiv.ofBijective _ hc
  have h : ∀ (j : J) (x : F.obj j), e.symm (c.ι.app j x) = Quot.mk _ ⟨j, x⟩ :=
    fun j x => e.injective (Equiv.ofBijective_apply_symm_apply _ _ _)
  exact
    { desc := fun s => (fromQuot' s).comp e.symm
      fac := fun s j => by
        ext x
        simp [h]
      uniq := fun s m hm => by
        ext t
        obtain ⟨⟨j, x⟩, rfl⟩ := e.surjective t
        dsimp
        rw [h, fromQuot'_mk]
        exact congr_fun (hm j) x }

variable (F)

section

variable [Small.{w} (Quot' F)]

@[simps!]
noncomputable def coconeOfSmall : Cocone F where
  pt := Shrink (Quot' F)
  ι :=
    { app := fun j x => equivShrink.{w} (Quot' F) (Quot.mk _ ⟨j, x⟩)
      naturality := fun j j' φ => by
        ext x
        dsimp
        congr 1
        exact (Quot.sound ⟨φ, rfl⟩).symm }

@[simp]
lemma fromQuot'_coconeOfSmall :
    fromQuot' (coconeOfSmall F) = equivShrink.{w} (Quot' F) := by
  ext ⟨j, x⟩
  rfl

noncomputable def isColimitCoconeOfSmall :
    IsColimit (Types.coconeOfSmall F) :=
  Nonempty.some (by simpa only [nonempty_isColimit_iff_bijective_fromQuot',
    fromQuot'_coconeOfSmall] using (equivShrink.{w} (Quot' F)).bijective)

end

lemma hasColimit_iff_small_quot' : HasColimit F ↔ Small.{w} (Quot' F) :=
  ⟨fun _ => Small.mk ⟨_, ⟨Equiv.ofBijective _
      (bijective_fromQuot'_of_isColimit (colimit.isColimit F))⟩⟩,
    fun _ => ⟨_, Types.isColimitCoconeOfSmall F⟩⟩

end Colimits

end Types

end Limits

end CategoryTheory
