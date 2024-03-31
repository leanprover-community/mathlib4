import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type _} [Category C] [Category D] [Category D'] [Category H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X

lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

lemma hasPointwiseLeftKanExtension [L.IsLocalization W] :
      HasPointwiseLeftKanExtension L F := fun Y => by
    have := Localization.essSurj L W
    rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
      ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
    infer_instance

lemma hasRightDerivedFunctor_of_pointwise :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_pointwise

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension := by
  have := hasPointwiseLeftKanExtension F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

section

variable {X : C} (S : Set (StructuredArrow (W.Q.obj X) W.Q))
  (hS₀ : StructuredArrow.mk (𝟙 (W.Q.obj X)) ∈ S)
  (hS₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : W.Q.obj X ⟶ W.Q.obj Y₁),
    StructuredArrow.mk φ ∈ S → StructuredArrow.mk (φ ≫ W.Q.map f) ∈ S)
  (hS₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : W.Q.obj X ⟶ W.Q.obj Y₂),
    StructuredArrow.mk φ ∈ S → StructuredArrow.mk (φ ≫ Localization.Construction.winv w hw) ∈ S)

open Localization Construction

lemma Localization.induction_structuredArrow' : S = ⊤ := by
  let X₀ : Paths (LocQuiver W) := ⟨X⟩
  suffices ∀ ⦃Y₀ : Paths (LocQuiver W)⦄ (f : X₀ ⟶ Y₀),
    S (StructuredArrow.mk ((Quotient.functor (Localization.Construction.relations W)).map f)) by
      ext g
      simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
      obtain ⟨⟨⟨⟩⟩, X₀, g⟩ := g
      dsimp at g
      obtain ⟨f, rfl⟩ := (Quotient.functor (Localization.Construction.relations W)).map_surjective g
      exact this f
  intro Y₀ f
  induction' f with Z₀ T₀ p q hp
  · apply hS₀
  · obtain f | ⟨w, hw⟩ := q
    · exact hS₁ f _ hp
    · exact hS₂ w hw _ hp

end

section

variable {X : C} (S : Set (StructuredArrow (L.obj X) L))
  [L.IsLocalization W]
  (hS₀ : StructuredArrow.mk (𝟙 (L.obj X)) ∈ S)
  (hS₁ : ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂) (φ : L.obj X ⟶ L.obj Y₁),
    StructuredArrow.mk φ ∈ S → StructuredArrow.mk (φ ≫ L.map f) ∈ S)
  (hS₂ : ∀ ⦃Y₁ Y₂ : C⦄ (w : Y₁ ⟶ Y₂) (hw : W w) (φ : L.obj X ⟶ L.obj Y₂),
    StructuredArrow.mk φ ∈ S → StructuredArrow.mk (φ ≫ (Localization.isoOfHom L W w hw).inv) ∈ S)

lemma Localization.induction_structuredArrow [L.IsLocalization W] : S = ⊤ := by
  have := hS₀
  have := hS₁
  have := hS₂
  let E := Localization.uniq W.Q L W
  let e := Localization.compUniqFunctor W.Q L W
  let S' : Set (StructuredArrow (W.Q.obj X) W.Q) := fun φ =>
    S (StructuredArrow.mk (e.inv.app X ≫ E.functor.map φ.hom ≫ e.hom.app φ.right))
  suffices S' = ⊤ by
    ext φ
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    have hφ : S' (StructuredArrow.mk (E.functor.preimage (e.hom.app X ≫ φ.hom ≫ e.inv.app φ.right))) := by
      rw [this]
      tauto
    simpa [S'] using hφ
  apply induction_structuredArrow'
  · change S _
    simp
    exact hS₀
  · intro Y₁ Y₂ f φ hφ
    change S _
    simp only [StructuredArrow.mk_right, comp_obj, StructuredArrow.mk_hom_eq_self, map_comp, assoc]
    have := hS₁ f (e.inv.app X ≫ E.functor.map φ ≫ e.hom.app Y₁) hφ
    rw [assoc, assoc, ← NatTrans.naturality] at this
    exact this
  · intro Y₁ Y₂ w hw φ hφ
    change S _
    simp only [StructuredArrow.mk_right, comp_obj, StructuredArrow.mk_hom_eq_self, map_comp, assoc]
    have eq : NatTrans.app e.hom Y₂ ≫ (Localization.isoOfHom L W w hw).inv =
        E.functor.map (Localization.Construction.winv w hw) ≫ NatTrans.app e.hom Y₁ := by
      rw [← cancel_mono (Localization.isoOfHom L W w hw).hom, assoc, Iso.inv_hom_id, comp_id,
        assoc, Localization.isoOfHom_hom, ← NatTrans.naturality]
      dsimp
      rw [← Functor.map_comp_assoc]
      erw [(Localization.Construction.wIso w hw).inv_hom_id]
      rw [Functor.map_id, id_comp]
    have := hS₂ w hw (e.inv.app X ≫ E.functor.map φ ≫ e.hom.app Y₂) hφ
    rw [assoc, assoc, eq] at this
    exact this

end

section

variable {Y : C} (S : Set (CostructuredArrow L (L.obj Y)))
  [L.IsLocalization W]
  (hS₀ : CostructuredArrow.mk (𝟙 (L.obj Y)) ∈ S)
  (hS₁ : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y),
    CostructuredArrow.mk φ ∈ S → CostructuredArrow.mk (L.map f ≫ φ) ∈ S)
  (hS₂ : ∀ ⦃X₁ X₂ : C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.obj X₁ ⟶ L.obj Y),
    CostructuredArrow.mk φ ∈ S → CostructuredArrow.mk ((Localization.isoOfHom L W w hw).inv ≫ φ) ∈ S)

@[ext]
lemma _root_.CategoryTheory.CostructuredArrow.obj_ext {C D : Type*} [Category C] [Category D] {S : C ⥤ D}
  {T : D} (f₁ f₂ : CostructuredArrow S T) (h₁ : f₁.left = f₂.left)
    (h₂ : f₁.hom = eqToHom (by rw [h₁]) ≫ f₂.hom )
    : f₁ = f₂ := by
  obtain ⟨X₁, ⟨⟨⟩⟩, φ₁⟩ := f₁
  obtain ⟨X₂, ⟨⟨⟩⟩, φ₂⟩ := f₂
  dsimp at h₁
  subst h₁
  dsimp at h₂
  rw [id_comp] at h₂
  subst h₂
  rfl

lemma Localization.induction_costructuredArrow [L.IsLocalization W] : S = ⊤ := by
  have := hS₂
  let S' : Set (StructuredArrow (L.op.obj (Opposite.op Y)) L.op) :=
    fun φ => S (CostructuredArrow.mk φ.hom.unop)
  have eq := Localization.induction_structuredArrow L.op W.op S' hS₀
    (by intros; apply hS₁; assumption) (by
      intro Y₁ Y₂ w hw φ hφ
      have eq :
        (CostructuredArrow.mk
          (StructuredArrow.mk (φ ≫ (Localization.isoOfHom L.op (MorphismProperty.op W) w hw).inv)).hom.unop) =
          CostructuredArrow.mk ((Localization.isoOfHom L W w.unop hw).inv ≫ φ.unop) := by
        ext
        · rfl
        · dsimp
          simp only [id_comp]
          congr 1
          rw [← cancel_mono (Localization.isoOfHom L W w.unop hw).hom]
          simp only [Opposite.unop_op, Localization.isoOfHom_hom, Localization.isoOfHom_inv_hom_id]
          apply Quiver.Hom.op_inj
          exact Localization.isoOfHom_hom_inv_id L.op W.op w hw
      change S _
      simpa only [← eq] using hS₂ w.unop hw φ.unop hφ)
  ext φ
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  have : S' (StructuredArrow.mk
    (by exact φ.hom.op : L.op.obj (Opposite.op Y) ⟶ L.op.obj (Opposite.op φ.left))) := by
    rw [eq]
    tauto
  exact this

end

section

variable {F L}

def isPointwiseLeftKanExtensionAtOfIso {G : D ⥤ H} (e : F ≅ L ⋙ G)
    [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s := by
    let S : Set (CostructuredArrow L (L.obj Y)) := fun j =>
      e.hom.app j.left ≫ G.map j.hom ≫ e.inv.app Y ≫
        NatTrans.app s.ι (CostructuredArrow.mk (𝟙 (L.obj Y))) = s.ι.app j
    suffices S = ⊤ by
      intro j
      have h : S j := by
        rw [this]
        tauto
      dsimp
      rw [assoc, h]
    apply Localization.induction_costructuredArrow L W
    · change _ = _
      simp
    · intro X₁ X₂ f φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq
      rw [comp_id] at eq
      rw [← eq, ← hφ]
      simp
    · intro X₁ X₂ w hw φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq
      rw [comp_id] at eq
      have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      rw [← cancel_epi (F.map w), eq, ← hφ]
      simp only [NatTrans.naturality_assoc, comp_obj, comp_map,
        NatIso.cancel_natIso_hom_left, ← G.map_comp_assoc,
        Localization.isoOfHom_hom_inv_id_assoc]
  uniq s m hm := by
    dsimp at m hm ⊢
    have eq := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at eq
    simp only [← eq, map_id, comp_id, Iso.inv_hom_id_app_assoc]

noncomputable def isPointwiseLeftKanExtensionOfIso {G : D ⥤ H} (e : F ≅ L ⋙ G)
    [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y => by
  have := Localization.essSurj L W
  exact (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso' (L.objObjPreimageIso Y)
    (isPointwiseLeftKanExtensionAtOfIso W e _)

noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIso (E : LeftExtension L F) [IsIso E.hom]
    [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIso W (asIso E.hom)

lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIso W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension  _

end

end Functor

end CategoryTheory
