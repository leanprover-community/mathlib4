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
Given `Y ⊆ X` correspondence `{ subobjects of X/Y } ↔ { subobjects of X containing Y }`
-/
noncomputable
def Subobject.cokernelOrderIso (Y : Subobject X) : Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p := ⟨(Abelian.Subobject.inverseImage (cokernel.π Y.arrow)).obj p,
    le_kernelSubobject (cokernel.π Y.arrow ≫ cokernel.π p.arrow) Y (by simp)⟩
  invFun q := (Abelian.Subobject.image (cokernel.π Y.arrow)).obj (q : Subobject X)
  left_inv p := by
    simp
    sorry
  right_inv q := by
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
  exact (Subobject.cokernelOrderIso _).isSimpleOrder_iff

theorem IsSimpleSubobject_iff_iso (e : X ≅ Y) : IsSimpleSubobject X ↔ IsSimpleSubobject Y := by
  sorry

theorem covBy_iff_cokernel_is_simple {A B : Subobject X} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleSubobject (cokernel (A.ofLE B hAB)) := by
  set f : Subobject (B : C) ≃o Set.Iic B := B.subobjectOrderIso with hf
  rw [covBy_iff_coatom_Iic hAB]
  have : (cokernel (A.ofLE B hAB)) ≅ cokernel ((Subobject.mk (A.ofLE B hAB)).arrow) := sorry
  rw [IsSimpleSubobject_iff_iso _ _ this]
  rw [IsSimpleSubobject_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  dsimp [Subobject.subobjectOrderIso]
  have : Subobject.mk ((Subobject.mk (A.ofLE B hAB)).arrow ≫ B.arrow) = A := by
    refine Subobject.mk_eq_of_comm ((Subobject.mk (A.ofLE B hAB)).arrow ≫ B.arrow) ?_ ?_
    · exact Subobject.underlyingIso (A.ofLE B hAB)
    ·
      sorry

  sorry
  --simp
  --simp [-OrderIso.isCoatom_iff, Submodule.map_comap_subtype, inf_eq_right.2 hAB]

-- omit Abelian
lemma Subobject.sup_eq_imageSubobject [HasImages C] [HasBinaryCoproducts C] {A : C}
    (X Y : Subobject A) :
    X ⊔ Y = imageSubobject (coprod.desc X.arrow Y.arrow) := by
  refine eq_mk_of_comm (image.ι (coprod.desc X.arrow Y.arrow)) ?_ ?_
  · exact (sup_isoImage X Y)
  · simp only [sup_isoImage_hom]
    apply ofLEMk_comp

omit [Abelian C] in
lemma Subobject.eq_imageSubobject [HasStrongEpiMonoFactorisations C]
    {X Y : C} {f : X ⟶ Y} {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] :
    mk m = imageSubobject f :=
  mk_eq_mk_of_comm m (image.ι f) (image.isoStrongEpiMono e m comm) (by simp)

-- show (X ⊔ Y) ⊓ Z ≤ X ⊔ Y ⊓ Z
set_option linter.style.emptyLine false in
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

    let e :=  (pullback.snd e_f (pullback.fst m_f Z.arrow))
    -- e is (strong) epi
    have : StrongEpi e := StrongEpiCategory.strongEpi_of_epi e

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

    let h : P ⟶ X ⊞ (pullback Y.arrow Z.arrow) := biprod.lift (pullback.fst _ _ ≫ biprod.fst) u

    have fac : h ≫ g = e ≫ m_w := by
      simp only [biprod.desc_eq, Preadditive.comp_add, biprod.lift_fst_assoc, Category.assoc,
        biprod.lift_snd_assoc, h, g]
      dsimp only [u]
      rw [pullback.lift_fst_assoc, Category.assoc, ← Preadditive.comp_add, ← biprod.desc_eq,
        pasteWP.w]
      simp [e, m_w]
    rw [← fac_g, ← Category.assoc] at fac

    have goal := imageSubobject_le_mk m_g (e ≫ m_w) _ fac
    rw [imageSubobject_epi_comp e m_w, imageSubobject_mono m_w] at goal

    have : (mk m_g) = X ⊔ (Y ⊓ Z) := by
      rw [eq_imageSubobject e_g m_g fac_g, Abelian.Subobject.sup_eq_imageSubobject]
      apply le_antisymm
      · refine imageSubobject_le_mk (image.ι (biprod.desc _ _)) (biprod.desc _ _) ?_ ?_
        · refine biprod.map (𝟙 _) (inf_isPullback Y Z).isoPullback.inv ≫ factorThruImage _
        · ext
          · simp
          · --weird
            simp only [Category.assoc, image.fac, biprod.inr_map_assoc, biprod.inr_desc,
              ← (inf_isPullback Y Z).isoPullback_inv_fst =≫ Y.arrow, IsPullback.isoPullback_inv_fst]
            rw [Category.assoc, ofLE_arrow]
      · refine imageSubobject_le_mk
          (image.ι (biprod.desc X.arrow (pullback.fst Y.arrow Z.arrow ≫ Y.arrow)))
          (biprod.desc X.arrow (Y ⊓ Z).arrow) ?_ ?_
        · refine (biprod.map (eqToHom rfl) (inf_isPullback Y Z).isoPullback.hom) ≫ factorThruImage _
        · ext <;> simp

    rw [this] at goal

    have : mk m_w = (X ⊔ Y) ⊓ Z := by
      refine mk_eq_of_comm m_w ?_ ?_
      · refine ?_ ≪≫ (inf_isPullback _ Z).isoPullback.symm
        have := pullback.map_isIso m_f Z.arrow (X ⊔ Y).arrow Z.arrow
          (isoOfMkEq m_f (X ⊔ Y)
            (by rw [eq_imageSubobject e_f m_f fac_f, Abelian.Subobject.sup_eq_imageSubobject])).hom
            (𝟙 _) (𝟙 _)
          (by simp) (by simp)
        exact
          asIso
            (pullback.map m_f Z.arrow (X ⊔ Y).arrow Z.arrow (isoOfMkEq m_f (X ⊔ Y) _).hom
              (𝟙 (underlying.obj Z)) (𝟙 A) _ _)
      · have := (inf_isPullback (X ⊔ Y) Z).isoPullback_inv_fst =≫ (X ⊔ Y).arrow
        rw [Category.assoc, ofLE_arrow] at this
        simp [pullback.map, this, m_w, ← pullback.condition, pullback.lift_fst_assoc]
    rwa [this] at goal

open Subobject in
instance {A : C} : JordanHolderLattice (Subobject A) where
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

    have : cokernel h₁ ≅ cokernel h₁' := by
      dsimp [h₁, h₁']

      sorry
    suffices cokernel h₁ ≅ cokernel h₂ by sorry

    dsimp [h₁, h₂]
    let x := X.arrow
    let y := Y.arrow
    let f := biprod.desc x y
    obtain ⟨⟨I, m, e, fac_f⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation f

    let u' := biprod.inl ≫ e
    let v' := biprod.inr ≫ e
    let fac_x : x = u' ≫ m := by
      simp [x, u', fac_f, f]
    let fac_y : y = v' ≫ m := by
      simp [y, v', fac_f, f]
    have eq : biprod.fst (Y := (Y : C)) ≫ u' + biprod.snd (X := (X : C)) ≫ v' = e := by
      have := biprod.total (X := (X : C)) (Y := Y) =≫ e
      rw [Category.id_comp] at this
      rw [Preadditive.add_comp] at this
      simpa

    have iso : I ≅ underlying.obj (X ⊔ Y) :=
      image.isoStrongEpiMono e m fac_f ≪≫ (Abelian.Subobject.sup_isoImage X Y).symm

    let q := cokernel.π (X.ofLE (X ⊔ Y) le_sup_left)
    let q' := cokernel.π u'

    let u := (X.ofLE (X ⊔ Y) le_sup_left)
    let v := (Y.ofLE (X ⊔ Y) le_sup_right)

    have : Epi (v' ≫ q') := by
      have := eq =≫ q'
      simp [Preadditive.add_comp, q', cokernel.condition u'] at this
      exact epi_of_epi_fac this

    have : Epi (v ≫ q) := sorry

    have eq_zero : pullback.snd x y ≫ v' ≫ cokernel.π u' = 0 := by
      simp [x, y, v', u']
      have := pullback.condition (f := x) (g := y)
      simp only [fac_x, fac_y, ← Category.assoc, cancel_mono m] at this
      have := this =≫ q'
      simp [q', cokernel.condition u', x, y, v', u'] at this
      exact this.symm

    have := kernel.lift (v' ≫ cokernel.π u') _ eq_zero

    have : (pullback.snd X.arrow Y.arrow) ≫ v ≫ q = 0 := by
      sorry

    refine (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (v ≫ q))).coconePointUniqueUpToIso
      (cokernelIsCokernel _) ≪≫ ?_
    refine cokernel.mapIso (kernel.ι (v ≫ q)) ((X ⊓ Y).ofLE Y inf_le_right) ?_ (Iso.refl _) ?_
    · refine ?_ ≪≫ (inf_isPullback _ _).isoPullback.symm
      refine Iso.mk ?_ ?_ ?_ ?_
      · sorry
      · refine kernel.lift (v ≫ q) (pullback.snd _ _) ?_
        · have := pullback.condition (f := X.arrow) (g := Y.arrow)
          sorry
      · sorry
      · sorry
    · simp
      sorry


end CategoryTheory
