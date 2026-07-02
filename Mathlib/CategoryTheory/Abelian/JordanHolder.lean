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

noncomputable
def Abelian.Subobject.biprod_e {A : C} (X Y : Subobject A) :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).e

noncomputable
def Abelian.Subobject.biprod_m {A : C} {X Y : Subobject A} :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).m

instance {A : C} {X Y : Subobject A} : StrongEpi (Abelian.Subobject.biprod_e X Y) :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).e_strong_epi

instance {A : C} {X Y : Subobject A} : Mono (Abelian.Subobject.biprod_m (X := X) (Y := Y)) :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).m_mono

noncomputable
abbrev Abelian.Subobject.biprod_fac {A : C} {X Y : Subobject A} : biprod_e X Y ≫ biprod_m =
    biprod.desc X.arrow Y.arrow :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).fac

lemma Abelian.Subobject.arrow_fac_biprod_inl {A : C} (X Y : Subobject A) : X.arrow =
    biprod.inl ≫ biprod_e X Y ≫ biprod_m := by
  simp only [biprod_fac, biprod.inl_desc]

lemma Abelian.Subobject.arrow_fac_biprod_inr {A : C} (X Y : Subobject A) : Y.arrow =
    biprod.inr ≫ biprod_e X Y ≫ biprod_m := by
  simp only [biprod_fac, biprod.inr_desc]

instance {A : C} (X Y : Subobject A) :
    Mono (biprod.inl ≫ Abelian.Subobject.biprod_e X Y) := by
  have := (Abelian.Subobject.arrow_fac_biprod_inl X Y).symm
  rw [← Category.assoc] at this
  exact mono_of_mono_fac this

instance {A : C} (X Y : Subobject A) :
    Mono (biprod.inr ≫ Abelian.Subobject.biprod_e X Y) := by
  have := (Abelian.Subobject.arrow_fac_biprod_inr X Y).symm
  rw [← Category.assoc] at this
  exact mono_of_mono_fac this

noncomputable
def Abelian.Subobject.s {A : C} (X Y : Subobject A) : Limits.pullback X.arrow Y.arrow ⟶
    kernel (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y)) := by
  refine kernel.lift _ (pullback.snd _ _) ?_
  have p := pullback.condition (f := X.arrow) (g := Y.arrow)
  simp only [Abelian.Subobject.arrow_fac_biprod_inl X Y, Abelian.Subobject.arrow_fac_biprod_inr X Y,
    ← Category.assoc, biprod_m, cancel_mono _] at p
  have := (p =≫ (cokernel.π (biprod.inl ≫ biprod_e X Y))).symm
  simp only [← Category.assoc]
  rw [this]
  have := cokernel.condition (biprod.inl ≫ biprod_e X Y)
  simp only [Category.assoc] at this ⊢
  cat_disch

@[simps!]
noncomputable
def Abelian.Subobject.biprodInlIso {A : C} (X Y : Subobject A) :
    (X : C) ≅
      kernel (cokernel.π (biprod.inl ≫ biprod_e X Y)) := by
  have := (monoIsKernelOfCokernel _
    (cokernelIsCokernel (biprod.inl ≫ biprod_e X Y))).conePointUniqueUpToIso
      (kernelIsKernel _)
  exact this

noncomputable
def Abelian.Subobject.w {A : C} (X Y : Subobject A) : kernel (biprod.inr ≫ biprod_e X Y ≫
    cokernel.π (biprod.inl ≫ biprod_e X Y)) ⟶
      Subobject.underlying.obj X := by
  refine (kernel.lift (cokernel.π (biprod.inl ≫ biprod_e X Y))
    ((kernel.ι (biprod.inr ≫ biprod_e X Y ≫
      cokernel.π (biprod.inl ≫ biprod_e X Y))) ≫
      (biprod.inr ≫ biprod_e X Y)) ?_) ≫
      (Abelian.Subobject.biprodInlIso X Y).inv
  simp only [Category.assoc, kernel.condition]

lemma Abelian.Subobject.w_u_fac {A : C} (X Y : Subobject A) :
    w X Y ≫ (biprod.inl ≫ biprod_e X Y) =
      (kernel.ι (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y))) ≫
        (biprod.inr ≫ biprod_e X Y) := by
  have := kernel.lift_ι (cokernel.π (biprod.inl ≫ biprod_e X Y))
    ((kernel.ι (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y))) ≫
      (biprod.inr ≫ biprod_e X Y))
    (by simp only [Category.assoc, kernel.condition])
  rw [← this]
  simp only [Category.assoc, w]
  let P := (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (biprod.inl ≫ biprod_e X Y)))
  let Q := (kernelIsKernel (cokernel.π (biprod.inl ≫ biprod_e X Y)))
  have : kernel.ι (cokernel.π (biprod.inl ≫ biprod_e X Y)) =
      (biprodInlIso X Y).inv ≫ biprod.inl ≫ biprod_e X Y := by
    refine (Iso.eq_inv_comp (P.conePointUniqueUpToIso Q)).2 ?_
    simpa using (P.conePointUniqueUpToIso_hom_comp Q) WalkingParallelPair.zero
  rw [this]

noncomputable
def Abelian.Subobject.t {A : C} (X Y : Subobject A) : kernel (biprod.inr ≫ biprod_e X Y ≫
    cokernel.π (biprod.inl ≫ biprod_e X Y)) ⟶ pullback X.arrow Y.arrow := by
  refine pullback.lift ?_ ?_ ?_
  · exact w X Y
  · exact kernel.ι (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y))
  · simp only [arrow_fac_biprod_inl X Y, ← Category.assoc, arrow_fac_biprod_inr X Y, ← w_u_fac X Y]

open Subobject in
noncomputable
def Abelian.Subobject.kerneliso₁ {A : C} (X Y : Subobject A) :
    kernel (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y)) ≅
      underlying.obj (X ⊓ Y) := by
  refine ?_ ≪≫ (inf_isPullback _ _).isoPullback.symm
  refine Iso.mk ?_ ?_ ?_ ?_
  · exact t X Y
  · exact s X Y
  · ext1
    simp only [t, s, equalizer_as_kernel, Category.assoc, kernel.lift_ι, pullback.lift_snd,
      Category.id_comp]
  · ext1
    · simp only [t, Category.assoc, pullback.lift_fst, Category.id_comp]
      have p : pullback.fst X.arrow Y.arrow ≫ biprod.inl ≫ biprod_e X Y =
          pullback.snd X.arrow Y.arrow ≫ biprod.inr ≫ biprod_e X Y := by
        have := pullback.condition (f := X.arrow) (g := Y.arrow)
        simp only [arrow_fac_biprod_inl X Y, arrow_fac_biprod_inr X Y, ← Category.assoc,
          cancel_mono (biprod_m (X := X) (Y := Y))] at this
        simpa only [Category.assoc]
      have := (s X Y) ≫= w_u_fac X Y
      rwa [s, kernel.lift_ι_assoc, ← s, ← p, ← Category.assoc, cancel_mono] at this
    · simp only [s, t, Category.assoc, pullback.lift_snd, kernel.lift_ι, Category.id_comp]

--refine Subobject.eq_of_comp_arrow_eq_iff.mpr ?_

set_option linter.style.emptyLine false in
open Subobject Abelian.Subobject in
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

    have h₁iso : cokernel (X.ofLE (X ⊔ Y) le_sup_left) ≅
        cokernel ((X ⊓ (X ⊔ Y)).ofLE (X ⊔ Y) inf_le_right) := by
      refine cokernel.mapIso _ _ ?_ (Iso.refl _) ?_
      · refine X.isoOfEq (X ⊓ (X ⊔ Y)) (by simp only [le_sup_left, inf_of_le_left])
      · simp

    have h₂iso : cokernel ((X ⊓ Y).ofLE Y inf_le_right) ≅
        cokernel ((X ⊓ Y ⊓ Y).ofLE Y inf_le_right) := by
      refine cokernel.mapIso _ _ ?_ (Iso.refl _) ?_
      · refine (X ⊓ Y).isoOfEq (X ⊓ Y ⊓ Y) (by simp only [_root_.inf_le_right, inf_of_le_left])
      · simp

    refine h₁iso.symm ≪≫ ?_ ≪≫ h₂iso

    have eq : biprod.fst (Y := (Y : C)) ≫ (biprod.inl ≫ biprod_e X Y) + biprod.snd (X := (X : C))
        ≫ (biprod.inr ≫ biprod_e X Y) = (biprod_e X Y) := by
      have := biprod.total (X := (X : C)) (Y := Y) =≫ (biprod_e X Y)
      rw [Category.id_comp] at this
      rw [Preadditive.add_comp] at this
      simpa

    have : Epi (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e X Y)) := by
      have := eq =≫ cokernel.π (biprod.inl ≫ biprod_e X Y)
      simp only [Preadditive.add_comp, Category.assoc,
        cokernel.condition (biprod.inl ≫ biprod_e X Y), comp_zero, zero_add] at this
      exact epi_of_epi_fac this

    have cokeriso₁ : cokernel (kernel.ι (biprod.inr ≫ biprod_e X Y ≫
        cokernel.π (biprod.inl ≫ biprod_e X Y))) ≅ cokernel ((X ⊓ Y).ofLE Y inf_le_right) := by
      refine cokernel.mapIso (kernel.ι (biprod.inr ≫ biprod_e X Y ≫
          cokernel.π (biprod.inl ≫ biprod_e X Y))) ((X ⊓ Y).ofLE Y _) (kerneliso₁ X Y)
          (Iso.refl _) ?_
      · simp only [Iso.refl_hom, Category.comp_id, kerneliso₁, Iso.trans_hom, Iso.symm_hom,
          Category.assoc, IsPullback.isoPullback_inv_snd]
        exact (pullback.lift_snd _ _ _).symm

    refine ?_ ≪≫ ((Abelian.epiIsCokernelOfKernel _ (kernelIsKernel _)).coconePointUniqueUpToIso
      (cokernelIsCokernel _)) ≪≫ cokeriso₁
    simp only [Fork.ι_ofι, Cofork.ofπ_pt]

    refine cokernel.mapIso (X.ofLE (X ⊔ Y) le_sup_left) (biprod.inl ≫ biprod_e X Y) (Iso.refl _)
        ?_ ?_
    · exact (Abelian.Subobject.sup_isoImage X Y) ≪≫ (Abelian.imageIsoImage _).symm
    · simp only [Iso.trans_hom, Abelian.Subobject.sup_isoImage_hom, Iso.symm_hom,
        IsImage.isoExt_inv, image.isImage_lift, Iso.refl_hom, Category.id_comp]
      rw [← cancel_mono biprod_m, Category.assoc, Category.assoc, Category.assoc,
        ← arrow_fac_biprod_inl X Y, biprod_m, image.lift_fac]
      erw [ofLEMk_comp]
      simp

end CategoryTheory
