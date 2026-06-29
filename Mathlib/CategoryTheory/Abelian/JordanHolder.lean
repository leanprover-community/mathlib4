import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Simple
import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.Order.Interval.Basic

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} {x : Subobject X} (f : X ⟶ Y)

noncomputable section Image

variable (f : X ⟶ Y)

/-- The image of a morphism `f g : X ⟶ Y` as a `Subobject Y`. -/
abbrev abImageSubobject : Subobject Y :=
  Subobject.mk (Abelian.image.ι f)

/-- The underlying object of `abImageSubobject f` is (up to isomorphism!)
the same as the chosen object `Abelian.image f`. -/
def abImageSubobjectIso : (abImageSubobject f : C) ≅ Abelian.image f :=
  Subobject.underlyingIso (Abelian.image.ι f)

@[reassoc (attr := simp)]
theorem abImageSubobject_arrow :
    (abImageSubobjectIso f).hom ≫ Abelian.image.ι f =
      (abImageSubobject f).arrow := by simp [abImageSubobjectIso]

@[reassoc (attr := simp)]
theorem abImageSubobject_arrow' :
    (abImageSubobjectIso f).inv ≫ (abImageSubobject f).arrow = Abelian.image.ι f := by
  simp [abImageSubobjectIso]

/-- A factorisation of `f : X ⟶ Y` through `abImageSubobject f`. -/
def factorThruAbImageSubobject : X ⟶ abImageSubobject f :=
  Abelian.factorThruImage f ≫ (abImageSubobjectIso f).inv

instance : Epi (factorThruAbImageSubobject f) := by
  dsimp [factorThruAbImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem abImageSubobject_arrow_comp :
    factorThruAbImageSubobject f ≫ (abImageSubobject f).arrow = f := by
  simp [factorThruAbImageSubobject]

theorem abImageSubobject_arrow_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0) :
    (abImageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruAbImageSubobject f) <| by simp [h]

theorem abImageSubobject_factors_comp_self {W : C} (k : W ⟶ X) :
    (abImageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ Abelian.factorThruImage f, by simp⟩

@[simp]
theorem factorThruAbImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (abImageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruAbImageSubobject f := by
  ext
  simp

@[simp]
theorem factorThruAbImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (abImageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruAbImageSubobject f := by
  ext
  simp

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
theorem abImageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) :
    abImageSubobject (h ≫ f) ≤ abImageSubobject f := by
  refine Subobject.mk_le_mk_of_comm (kernel.lift _ (Abelian.image.ι (h ≫ f)) (by simp)) (by simp)

end Image

section

@[simp]
noncomputable
def Subobject.image {X Y : C} (f : X ⟶ Y) : Subobject X ⥤ Subobject Y where
  obj X' := abImageSubobject (X'.arrow ≫ f)
  map := by
    intro X' X'' h
    refine homOfLE (le_of_comm (kernelSubobjectMap (Arrow.homMk' ?_ ?_ ?_)) ?_)
    · exact 𝟙 _
    · apply cokernel.desc _ (cokernel.π (X''.arrow ≫ f))
      · simp
        sorry
    · simp
    · simp only [kernelSubobjectMap_arrow, Arrow.homMk'_left]
      exact Category.comp_id (kernelSubobject (cokernel.π (X'.arrow ≫ f))).arrow

@[simp]
noncomputable
def Subobject.image_map {X Y : C} (f : X ⟶ Y) (X' : Subobject X) :
    underlying.obj X' ⟶ underlying.obj (abImageSubobject (X'.arrow ≫ f)) :=
  factorThruAbImageSubobject (X'.arrow ≫ f)
  --Abelian.coimage.π (X'.arrow ≫ f) ≫ Abelian.coimageImageComparison (X'.arrow ≫ f)

@[simp]
noncomputable
def Subobject.inverseImage {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X where
  obj Y' := kernelSubobject (f ≫ cokernel.π Y'.arrow)
  map := sorry
  map_id := sorry
  map_comp := sorry

@[simp]
noncomputable
def Subobject.inverseImage' {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X := pullback f

def Subobject.inverseImage_inc (Y' : Subobject Y) :
    kernel f ⟶ kernel (f ≫ cokernel.π Y'.arrow) := by
  sorry

lemma Subobject.inverseImage_comp {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    sorry ≫ Y'.arrow = ((inverseImage f).obj Y').arrow ≫ f := by
  simp
  have : kernel (f ≫ cokernel.π Y'.arrow) ⟶ Y' := by
    sorry
  sorry

/-
Given `Y ⊆ X` correspondence `{ subobjects of X⧸Y } ↔ { subobjects of X containing Y }`
-/
noncomputable
def Subobject.temp_iso (Y : Subobject X) : Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p' := ⟨(inverseImage (cokernel.π Y.arrow)).obj p',
    le_kernelSubobject (cokernel.π Y.arrow ≫ cokernel.π p'.arrow) Y (by simp)⟩
  invFun q := by
    obtain ⟨q, hq : Y ≤ q⟩ := q
    have := Y.ofLE q hq
    have := (image (cokernel.π Y.arrow)).obj q
    exact this
    --have : Mono (q.arrow ≫ cokernel.π Y.arrow) := by
    --  apply Abelian.mono_of_kernel_ι_eq_zero
    --  sorry
    --exact mk (q.arrow ≫ cokernel.π Y.arrow)
  left_inv p' := by
    simp
    sorry
  right_inv := by
    simp
    sorry
  map_rel_iff' := by cat_disch

variable (X Y : C)

/-- An object is simple when it has only two subobjects, `⊥` and `⊤`. -/
@[mk_iff] class IsSimpleSubobject extends
  IsSimpleOrder (Subobject X)

theorem IsSimpleSubobject.congr (e : X ≅ Y) [IsSimpleSubobject X] : IsSimpleSubobject Y where
  __ := (Subobject.mapIsoToOrderIso e.symm).isSimpleOrder

theorem IsSimpleSubobject_iff_isAtom : IsSimpleSubobject (x : C) ↔ IsAtom x := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom, isSimpleSubobject_iff]
  exact x.subobjectOrderIso.isSimpleOrder_iff

theorem IsSimpleSubobject_iff_isCoatom : IsSimpleSubobject (cokernel x.arrow) ↔ IsCoatom x := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom, isSimpleSubobject_iff]
  exact (Subobject.temp_iso _).isSimpleOrder_iff

theorem IsSimpleSubobject_iff_iso (e : X ≅ Y) : IsSimpleSubobject X ↔ IsSimpleSubobject Y := by
  sorry

#check IsModularLattice
#check ComplementedLattice
#check Interval.lattice

theorem covBy_iff_cokernel_is_simple {A B : Subobject X} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleSubobject (cokernel (A.ofLE B hAB)) := by
  set f : Subobject (B : C) ≃o Set.Iic B := B.subobjectOrderIso with hf
  rw [covBy_iff_coatom_Iic hAB]
  have : (cokernel (A.ofLE B hAB)) ≅ cokernel ((Subobject.mk (A.ofLE B hAB)).arrow) := sorry
  rw [IsSimpleSubobject_iff_iso _ _ this]
  rw [IsSimpleSubobject_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  sorry
  --dsimp [Subobject.subobjectOrderIso]
  --simp
  --simp [-OrderIso.isCoatom_iff, Submodule.map_comap_subtype, inf_eq_right.2 hAB]

noncomputable
def Subobject.abSup_MonoFactorisation {A : C} (f g : Subobject A) : MonoFactorisation
    (biprod.desc f.arrow g.arrow) where
  I := underlying.obj (f ⊔ g)
  m := (f ⊔ g).arrow
  m_mono := inferInstance
  e := biprod.desc (ofLE f (f ⊔ g) le_sup_left) (ofLE g (f ⊔ g) le_sup_right)
  fac := by simp only [biprod.desc_eq, Preadditive.add_comp, Category.assoc, ofLE_arrow]

noncomputable
def Subobject.abSup_isImage {A : C} (f g : Subobject A) :
    IsImage (abSup_MonoFactorisation f g) where
  lift F := by
    refine (f ⊔ g).ofLEMk F.m (sup_le ?_ ?_)
    · refine le_mk_of_comm (biprod.inl ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inl_desc]
    · refine le_mk_of_comm (biprod.inr ≫ F.e) ?_
      · simp only [Category.assoc, MonoFactorisation.fac, biprod.inr_desc]
  lift_fac := by simp [abSup_MonoFactorisation]

noncomputable
def Subobject.abSup_isoImage {A : C} (f g : Subobject A) : underlying.obj (f ⊔ g) ≅
    Limits.image (coprod.desc f.arrow g.arrow) :=
  IsImage.isoExt (sup_isImage ..) <| Image.isImage _

-- show (X ⊔ Y) ⊓ Z ≤ X ⊔ Y ⊓ Z
open Subobject in
instance (A : C) : IsModularLattice (Subobject A) where
  sup_inf_le_assoc_of_le := by
    intro X Y Z hXZ

    refine le_of_comm ?_ ?_
    · refine (inf_isPullback (X ⊔ Y) Z).isoPullback.hom ≫ ?_ ≫ (sup_isoImage X (Y ⊓ Z)).inv
      refine ?_ ≫ (biprod.isoCoprod _ _).hom ≫ Limits.factorThruImage _
      have : pullback (X ⊔ Y).arrow Z.arrow ⟶ X ⊞ pullback Y.arrow Z.arrow := by

        let g := biprod.desc X.arrow (pullback.fst Y.arrow Z.arrow ≫ Y.arrow)
        obtain ⟨⟨G, m_g, e_g, fac_g⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation g

        let f := biprod.desc X.arrow Y.arrow
        obtain ⟨⟨I, m_f, e_f, fac_f⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation f

        let W := pullback m_f Z.arrow
        let P := pullback e_f (pullback.fst m_f Z.arrow)

        let e' :=  (pullback.snd e_f (pullback.fst m_f Z.arrow))
        -- e' is epi
        let : Epi e' := Abelian.epi_pullback_of_epi_f e_f (pullback.fst m_f Z.arrow)

        -- combined square is a pullback of f and z
        have pasteWP := IsPullback.paste_vert
          (IsPullback.of_hasPullback e_f (pullback.fst m_f Z.arrow))
          (IsPullback.of_hasPullback m_f Z.arrow)
        rw [fac_f] at pasteWP

        let p₂ : P ⟶ Z := (pullback.snd e_f (pullback.fst m_f Z.arrow) ≫ pullback.snd m_f Z.arrow)

        let u : P ⟶ (pullback Y.arrow Z.arrow) := by
          refine pullback.lift ?_ ?_ ?_
          · -- α
            exact pullback.fst _ _ ≫ biprod.snd
          · -- β
            exact p₂ - (pullback.fst _ _ ≫ biprod.fst ≫ X.ofLE Z hXZ)
          · sorry

        let h : P ⟶ X ⊞ (pullback Y.arrow Z.arrow) :=
          biprod.lift (pullback.fst _ _ ≫ biprod.fst) u

        
        sorry
      sorry

    /-
    have : (underlying.obj ((X ⊔ Y) ⊓ Z)) ≅ pullback (X ⊔ Y).arrow Z.arrow :=
      IsPullback.isoPullback (inf_isPullback (X ⊔ Y) Z)
    -/
    have : underlying.obj X ⟶ underlying.obj Z := X.ofLE Z hXZ
    let φxy : (X : C) ⨿ Y ⟶ A := coprod.desc X.arrow Y.arrow
    let φxyz : ((X : C) ⨿ Y) ⨿ Z ⟶ A := coprod.desc φxy Z.arrow
    have : (Limits.image φxy) ⨿ Z ≅ Limits.image φxyz := by
      let e : ((X : C) ⨿ Y) ⨿ Z ⟶ Limits.image φxy ⨿ Z :=
        coprod.map (factorThruImage φxy) (𝟙 (Z : C))
      let m : (Limits.image φxy) ⨿ Z ⟶ A := by
        refine coprod.desc (image.ι φxy) Z.arrow
      have : Mono m := by
        sorry
      have : StrongEpi e := by
        sorry
      exact Limits.image.isoStrongEpiMono e m (by cat_disch)

    have : underlying.obj (X ⊔ Y) ≅ Limits.image φxy := sup_isoImage X Y
    /-
    have P₂ := IsPullback.of_hasPullback
      (coprod.desc (underlying.map le_sup_left.hom) (underlying.map le_sup_right.hom))
      (((X ⊔ Y) ⊓ Z).ofLE (X ⊔ Y) inf_le_left)

    have := IsPullback.paste_vert P₂ P₁
    simp at this -- pullback of (coprod.desc X.arrow Y.arrow) and Z.arrow

    refine le_of_comm ?_ ?_
    · have := (inf_isPullback (X ⊔ Y) Z).isoPullback.hom
      have : (X ⊔ Y ⊓ Z) ≅ (abImageSubobject (coprod.desc X.arrow (Y ⊓ Z).arrow)) := by
        sorry
      refine ?_ ≫ underlying.map this.inv
      refine ?_ ≫ factorThruAbImageSubobject (coprod.desc X.arrow (Y ⊓ Z).arrow)
      ·
        sorry
    · sorry


    have : underlying.obj X ⨿ underlying.obj Y ⟶ underlying.obj (X ⊔ Y) :=
      coprod.desc (underlying.map le_sup_left.hom) (underlying.map le_sup_right.hom)

    have : X ⊔ Y ≅ (abImageSubobject (coprod.desc X.arrow Y.arrow)) := by
      sorry

    have := factorThruAbImageSubobject (coprod.desc X.arrow Y.arrow)
    --have := Limits.pullback (((X ⊔ Y) ⊓ Z).ofLE (X ⊔ Y) inf_le_left)
    --have := Abelian.epi_pullback_of_epi_f
    simp
    -/
    sorry

instance : JordanHolderLattice (Subobject X) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := inf_covBy_of_covBy_sup_of_covBy_sup_left
  Iso X Y := Nonempty (cokernel (Subobject.ofLE _ _ (inf_le_right : X.1 ⊓ X.2 ≤ X.2)) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right : Y.1 ⊓ Y.2 ≤ Y.2)))
  iso_symm := fun ⟨f⟩ => ⟨f.symm⟩
  iso_trans := fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  second_iso {X} {Y} _ := by
    constructor
    dsimp

    let h₁ := X.ofLE (X ⊔ Y) le_sup_left
    let h₁' := (X ⊓ (X ⊔ Y)).ofLE (X ⊔ Y) inf_le_right

    let h₂ := (X ⊓ Y).ofLE Y inf_le_right
    let h₂' := (X ⊓ Y ⊓ Y).ofLE Y inf_le_right

    suffices cokernel h₁ ≅ cokernel h₂ by sorry

    simp [h₁, h₂]
    -- prove cokernel(X → X ⊔ Y) ≅ cokernel(X ⊓ Y → Y)
    sorry

end

end CategoryTheory
