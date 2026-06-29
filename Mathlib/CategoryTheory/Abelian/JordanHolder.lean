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

/-
Given `Y ⊆ X` correspondence `{ subobjects of X⧸Y } ↔ { subobjects of X containing Y }`
-/
noncomputable
def Subobject.temp_iso (Y : Subobject X) : Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p' := ⟨(Abelian.Subobject.inverseImage (cokernel.π Y.arrow)).obj p',
    le_kernelSubobject (cokernel.π Y.arrow ≫ cokernel.π p'.arrow) Y (by simp)⟩
  invFun q := by
    obtain ⟨q, hq : Y ≤ q⟩ := q
    have := Y.ofLE q hq
    have := (Abelian.Subobject.image (cokernel.π Y.arrow)).obj q
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

lemma Subobject.sup_eq_imageSubobject {A : C} (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (coprod.desc X.arrow Y.arrow) := by
  refine eq_mk_of_comm (image.ι (coprod.desc X.arrow Y.arrow)) ?_ ?_
  · exact (sup_isoImage X Y)
  · simp only [sup_isoImage_hom]
    apply ofLEMk_comp

-- show (X ⊔ Y) ⊓ Z ≤ X ⊔ Y ⊓ Z
open Subobject in
instance (A : C) : IsModularLattice (Subobject A) where
  sup_inf_le_assoc_of_le := by
    intro X Y Z hXZ

    let g := biprod.desc X.arrow (pullback.fst Y.arrow Z.arrow ≫ Y.arrow)
    obtain ⟨⟨G, m_g, e_g, fac_g⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation g

    let f := biprod.desc X.arrow Y.arrow
    obtain ⟨⟨I, m_f, e_f, fac_f⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation f

    let W := pullback m_f Z.arrow
    let m_w := (pullback.snd m_f Z.arrow ≫ Z.arrow)
    let P := pullback e_f (pullback.fst m_f Z.arrow)

    let e' :=  (pullback.snd e_f (pullback.fst m_f Z.arrow))
    -- e' is epi
    have : StrongEpi e' := StrongEpiCategory.strongEpi_of_epi e'

    -- combined square is a pullback of f and z
    have pasteWP := IsPullback.paste_vert
      (.of_hasPullback e_f (pullback.fst m_f Z.arrow)) (.of_hasPullback m_f Z.arrow)
    rw [fac_f] at pasteWP

    let p₂ : P ⟶ Z := (pullback.snd e_f (pullback.fst m_f Z.arrow) ≫ pullback.snd m_f Z.arrow)

    let u : P ⟶ (pullback Y.arrow Z.arrow) := by
      refine pullback.lift ?_ ?_ ?_
      · -- α
        exact pullback.fst _ _ ≫ biprod.snd
      · -- β
        exact p₂ - (pullback.fst _ _ ≫ biprod.fst ≫ X.ofLE Z hXZ)
      · -- composition
        simp only [Category.assoc, Preadditive.sub_comp, ofLE_arrow, p₂]
        rw [eq_sub_iff_add_eq, ← Preadditive.comp_add, AddCommMonoid.add_comm, ← biprod.desc_eq,
          ← Category.assoc]
        exact pasteWP.w

    let h : P ⟶ X ⊞ (pullback Y.arrow Z.arrow) :=
      biprod.lift (pullback.fst _ _ ≫ biprod.fst) u

    have fac : h ≫ g = e' ≫ m_w := by
      simp only [biprod.desc_eq, Preadditive.comp_add, biprod.lift_fst_assoc, Category.assoc,
        biprod.lift_snd_assoc, h, g]
      dsimp only [u]
      rw [pullback.lift_fst_assoc, Category.assoc, ← Preadditive.comp_add, ← biprod.desc_eq,
        pasteWP.w]
      simp [e', m_w]
    rw [← fac_g, ← Category.assoc] at fac

    have goal := imageSubobject_le_mk m_g (e' ≫ m_w) _ fac

    have : (mk m_g) = X ⊔ (Y ⊓ Z) := by
      refine mk_eq_of_comm m_g ?_ ?_
      · refine (image.isoStrongEpiMono e_g m_g fac_g) ≪≫ ?_ ≪≫ (Abelian.Subobject.sup_isoImage _ _).symm
        dsimp [g]

        sorry
      · sorry
    rw [this] at goal

    have : imageSubobject (e' ≫ m_w) = imageSubobject (m_w) :=
      mk_eq_mk_of_comm (image.ι (e' ≫ m_w)) (image.ι m_w)
      ((image.isoStrongEpiMono e' m_w rfl).symm ≪≫
        (image.isoStrongEpiMono (𝟙 _) m_w (Category.id_comp _))) (by simp)

    rw [this] at goal

    have mk_f_eq : mk m_f = X ⊔ Y := by
      refine mk_eq_of_comm m_f ?_ ?_
      · exact image.isoStrongEpiMono e_f m_f fac_f ≪≫ (Abelian.Subobject.sup_isoImage _ _).symm
      · simp only [Iso.trans_hom, Iso.symm_hom, Abelian.Subobject.sup_isoImage_inv,
          Abelian.Subobject.sup_MonoFactorisation, Category.assoc]
        rw [image.lift_fac]
        cat_disch

    have : imageSubobject m_w = (X ⊔ Y) ⊓ Z := by
      --rw [sup_eq_imageSubobject]
      rw [imageSubobject_mono m_w]
      refine mk_eq_of_comm m_w ?_ ?_
      ·
        have := inf_isPullback (mk m_f) Z
        refine ?_ ≪≫ (inf_isPullback _ Z).isoPullback.symm
        sorry
        have := isoOfMkEq m_f (mk m_f) rfl
        refine HasLimit.isoOfNatIso ?_
        refine cospanExt (isoOfMkEq m_f (mk m_f) rfl)  (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        /-
        -/
      · sorry
    rwa [this] at goal

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

end CategoryTheory
