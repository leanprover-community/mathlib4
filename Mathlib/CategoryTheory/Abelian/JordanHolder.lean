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

instance {A : C} {X Y : Subobject A} : StrongEpi (Abelian.Subobject.biprod_e (X := X) (Y := Y)) :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).e_strong_epi

instance {A : C} {X Y : Subobject A} : Mono (Abelian.Subobject.biprod_m (X := X) (Y := Y)) :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).m_mono

noncomputable
abbrev Abelian.Subobject.biprod_fac {A : C} {X Y : Subobject A} :=
  (Abelian.imageStrongEpiMonoFactorisation (biprod.desc X.arrow Y.arrow)).fac

lemma Abelian.Subobject.arrow_fac_biprod_inl {A : C} (X Y : Subobject A) : X.arrow =
    (biprod.inl ≫ biprod_e X Y) ≫ biprod_m := by
  simp only [Category.assoc, biprod_e, biprod_m, biprod_fac, biprod.inl_desc X.arrow Y.arrow]

lemma Abelian.Subobject.arrow_fac_biprod_inr {A : C} (X Y : Subobject A) : Y.arrow =
    (biprod.inr ≫ biprod_e X Y) ≫ biprod_m := by
  simp only [Category.assoc, biprod_e, biprod_m, biprod_fac, biprod.inr_desc X.arrow Y.arrow]

instance {A : C} (X Y : Subobject A) :
    Mono (biprod.inl ≫ Abelian.Subobject.biprod_e (X := X) (Y := Y)) :=
  mono_of_mono_fac (Abelian.Subobject.arrow_fac_biprod_inl _ _).symm

instance {A : C} (X Y : Subobject A) :
    Mono (biprod.inr ≫ Abelian.Subobject.biprod_e (X := X) (Y := Y)) :=
  mono_of_mono_fac (Abelian.Subobject.arrow_fac_biprod_inr _ _).symm

noncomputable
def Abelian.Subobject.s {A : C} (X Y : Subobject A) : Limits.pullback X.arrow Y.arrow ⟶
    kernel (biprod.inr ≫ biprod_e X Y ≫ cokernel.π (biprod.inl ≫ biprod_e (X := X) (Y := Y))) := by
  refine kernel.lift (biprod.inr ≫ _ ≫ cokernel.π (biprod.inl ≫ _)) (pullback.snd _ _) ?_
  have p := pullback.condition (f := X.arrow) (g := Y.arrow)
  simp only [Abelian.Subobject.arrow_fac_biprod_inl X Y, Abelian.Subobject.arrow_fac_biprod_inr X Y,
    ← Category.assoc, biprod_m, cancel_mono _] at p
  have := (p =≫ (cokernel.π (biprod.inl ≫ biprod_e X Y))).symm
  simp only [← Category.assoc]
  rw [this]
  have := cokernel.condition (biprod.inl ≫ biprod_e (X := X) (Y := Y))
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
    kernel (biprod.inr ≫ (biprod_e X Y) ≫ cokernel.π (biprod.inl ≫ (biprod_e X Y))) ≅
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
/-
    let f := biprod.desc X.arrow Y.arrow
    obtain ⟨⟨I, m, e, fac_f⟩, _⟩ := Abelian.imageStrongEpiMonoFactorisation f

    let u' := biprod.inl ≫ e
    let v' := biprod.inr ≫ e
    let fac_x : X.arrow = u' ≫ m := by
      simp [u', fac_f, f]
    have : Mono u' := mono_of_mono_fac fac_x.symm
    let fac_y : Y.arrow = v' ≫ m := by
      simp [v', fac_f, f]
    have eq : biprod.fst (Y := (Y : C)) ≫ u' + biprod.snd (X := (X : C)) ≫ v' = e := by
      have := biprod.total (X := (X : C)) (Y := Y) =≫ e
      rw [Category.id_comp] at this
      rw [Preadditive.add_comp] at this
      simpa

    have iso : I ≅ underlying.obj (X ⊔ Y) :=
      image.isoStrongEpiMono e m fac_f ≪≫ (Abelian.Subobject.sup_isoImage X Y).symm

    --let q := cokernel.π (X.ofLE (X ⊔ Y) le_sup_left)
    let q' := cokernel.π u'

    --let u := (X.ofLE (X ⊔ Y) le_sup_left)
    --let v := (Y.ofLE (X ⊔ Y) le_sup_right)

    have : Epi (v' ≫ q') := by
      have := eq =≫ q'
      simp only [Preadditive.add_comp, Category.assoc, cokernel.condition u', comp_zero, zero_add,
        q'] at this
      exact epi_of_epi_fac this

    have : Epi (biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e)) := by
      have := eq =≫ q'
      simp only [Preadditive.add_comp, Category.assoc, cokernel.condition u', comp_zero, zero_add,
        q', u', v'] at this
      exact epi_of_epi_fac this

    --have : Epi (v ≫ q) := sorry

    have eq_zero : pullback.snd X.arrow Y.arrow ≫ biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e) = 0 := by
      have := pullback.condition (f := X.arrow) (g := Y.arrow)
      simp only [fac_x, fac_y, ← Category.assoc, cancel_mono m] at this
      have := (this =≫ q').symm
      simpa [q', cokernel.condition u', v', u'] using this

    let s := kernel.lift (biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e)) _ eq_zero

    let k := kernel.ι (biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e))

    let P := (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (biprod.inl ≫ e)))
    let Q := (kernelIsKernel (cokernel.π (biprod.inl ≫ e)))

    let Xiso : underlying.obj X ≅ kernel (cokernel.π (biprod.inl ≫ e)) := by
      have := P.conePointUniqueUpToIso Q
      exact this

    let w := (kernel.lift (cokernel.π (biprod.inl ≫ e)) (k ≫ v') (by simp only [Category.assoc,
      kernel.condition, k, v'])) ≫ Xiso.inv

    have w_u_fac : w ≫ u' = k ≫ v' := by
      have := kernel.lift_ι (cokernel.π (biprod.inl ≫ e)) (k ≫ v') (by simp [k, v'])
      rw [← this]
      simp only [Category.assoc, w, k, v', u']
      have : kernel.ι (cokernel.π (biprod.inl ≫ e)) =  Xiso.inv ≫ biprod.inl ≫ e := by
        refine (Iso.eq_inv_comp (P.conePointUniqueUpToIso Q)).2 ?_
        simpa using (P.conePointUniqueUpToIso_hom_comp Q) WalkingParallelPair.zero
      rw [this]

    let t : kernel (biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e)) ⟶
        pullback X.arrow Y.arrow := by
      refine pullback.lift ?_ ?_ ?_
      · exact w
      · exact k
      · simp [fac_x, fac_y, ← Category.assoc k v' m, ← w_u_fac]
-/

/-
    have : cokernel u' ≅ cokernel (kernel.ι q') := by
      have := (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q')).coconePointUniqueUpToIso (cokernelIsCokernel _)
      simpa [u', q']
-/

/-
    have : (pullback.snd X.arrow Y.arrow) ≫ v ≫ q = 0 := by
      sorry
-/

/-
    have := (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (v' ≫ q'))).coconePointUniqueUpToIso
      (cokernelIsCokernel _)
    simp [u'] at this
-/

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

/-
    let H : kernel (biprod.inr ≫ e ≫ cokernel.π (biprod.inl ≫ e)) ≅ underlying.obj (X ⊓ Y) := by
      refine ?_ ≪≫ (inf_isPullback _ _).isoPullback.symm
      refine Iso.mk ?_ ?_ ?_ ?_
      · exact t
      · exact s
      · simp [s, t, w, k, v', Xiso]
        sorry
      ·
        sorry
    --have := Subobject.eq_of_comp_arrow_eq_iff
-/

    have cokeriso₁ : cokernel (kernel.ι (biprod.inr ≫ (Abelian.Subobject.biprod_e X Y) ≫ cokernel.π (biprod.inl ≫ (Abelian.Subobject.biprod_e X Y)))) ≅ cokernel ((X ⊓ Y).ofLE Y inf_le_right) := by
      refine cokernel.mapIso (kernel.ι (biprod.inr ≫ (Abelian.Subobject.biprod_e X Y) ≫ cokernel.π (biprod.inl ≫ (Abelian.Subobject.biprod_e X Y)))) ((X ⊓ Y).ofLE Y _) ?_ (Iso.refl _) ?_
      · exact (Abelian.Subobject.kerneliso₁ X Y)
      · simp [Abelian.Subobject.kerneliso₁]
        exact (pullback.lift_snd _ _ _).symm

    refine ?_ ≪≫ ((Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (biprod.inr ≫ (Abelian.Subobject.biprod_e X Y) ≫ cokernel.π (biprod.inl ≫ (Abelian.Subobject.biprod_e X Y))))).coconePointUniqueUpToIso
      (cokernelIsCokernel _)) ≪≫ cokeriso₁
    simp
    sorry

end CategoryTheory
