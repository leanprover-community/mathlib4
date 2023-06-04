import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Limits

universe w v u

namespace CategoryTheory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
  {I : Type w} [SmallCategory I] {J : Type w} [SmallCategory J]
  (α : I ⥤ C) (β : J ⥤ C)

def into : I ⥤ (Cᵒᵖ ⥤ TypeMax.{w, v}) :=
α ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

def homs₁ : Cᵒᵖ ⥤ C ⥤ Type v :=
coyoneda

def homs₂ : Cᵒᵖ ⥤ J ⥤ Type v :=
coyoneda ⋙ (whiskeringLeft _ _ _).obj β

def homs₃ : Iᵒᵖ ⥤ J ⥤ Type v :=
α.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj β

def homs₄ : Iᵒᵖ ⥤ J ⥤ TypeMax.{w, v} :=
α.op ⋙ (coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}) ⋙ (whiskeringLeft _ _ _).obj β

noncomputable def homs₅ : Iᵒᵖ ⥤ TypeMax.{w, v} :=
homs₄ α β ⋙ colim

noncomputable def homs₆ : TypeMax.{w, v} :=
limit (homs₄ α β ⋙ colim)

noncomputable def colimit_op [HasColimit α] [HasLimit α.op] : Opposite.op (colimit α) ≅ limit α.op :=
sorry

instance a : HasLimitsOfSize.{w, w} (Cᵒᵖ ⥤ TypeMax.{w, v})ᵒᵖ :=
  { has_limits_of_shape := fun _ => hasLimitsOfShape_op_of_hasColimitsOfShape }

-- instance b : HasLimitsOfSize.{w, w} (Type max (max u v) w) := by sorry

--set_option pp.universes true

-- noncomputable def blub_iso : (yoneda.obj (colimit (into β))).obj (limit (into α).op) ≅
--   limit ((into α).op ⋙ yoneda.obj (colimit (into β))) := by
-- sorry


-- Missing: uliftFunctor preserves co(limits)

def my_other_yoneda_lemma (F : Cᵒᵖ ⥤ TypeMax.{w, v}) : yoneda.op ⋙ ((whiskeringRight _ _ _).obj uliftFunctor.{w}).op ⋙ yoneda.obj F ≅
  F ⋙ uliftFunctor.{max u v} :=
  NatIso.ofComponents (fun i => by
    refine' ⟨fun f => ⟨f.app _ ⟨𝟙 _⟩⟩, fun f => ⟨fun Y g => F.map g.down.op f.down, by aesop_cat⟩, _, _⟩
    · ext η
      refine' NatTrans.ext _ _ (funext (fun Y => _))
      ext ⟨f⟩
      convert (congr_fun (η.naturality f.op) ⟨𝟙 _⟩).symm
      simp
    · ext ⟨a⟩
      simp) (by
      intros X Y f
      ext η
      simp
      congr
      convert (congr_fun (η.naturality f) ⟨𝟙 _⟩)
      simp)

def my_yoneda_lemma (F : Cᵒᵖ ⥤ TypeMax.{w, v}) : (into α).op ⋙ yoneda.obj F ≅
  α.op ⋙ F ⋙ uliftFunctor.{max u v} :=
  NatIso.ofComponents (fun i => by
    dsimp
    refine' ⟨fun f => ⟨f.app _ ⟨𝟙 _⟩⟩, fun f => ⟨fun Y g => F.map g.down.op f.down, _⟩, _, _⟩
    · intros Y Z g
      ext ⟨x⟩
      simp [into]
    · ext η Y ⟨f⟩
      dsimp [into] at η
      dsimp [into] at f
      dsimp
      let q := η.app Y
      dsimp at q
      convert (congr_fun (η.naturality f.op) ⟨𝟙 _⟩).symm
      simp
    · ext ⟨a⟩
      simp) (by
      intros i j f
      ext η
      dsimp [into] at η
      simp
      congr
      convert (congr_fun (η.naturality (α.map f.unop).op) ⟨𝟙 _⟩)
      simp [into])

def two_hom_functors : Functor.flip (β ⋙ yoneda ⋙ (whiskeringRight Cᵒᵖ (Type v) TypeMax.{w, v}).obj uliftFunctor.{w}) ≅
  (coyoneda ⋙ (whiskeringRight C (Type v) (Type (max v w))).obj uliftFunctor.{w}) ⋙
          (whiskeringLeft J C (Type (max v w))).obj β :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun j => Iso.refl _) (by aesop_cat)) (by aesop_cat)

theorem homs_calc : ((colimit (into α)) ⟶ colimit (into β)) ≃ homs₆ α β := by
  change (yoneda.obj _).obj (Opposite.op (colimit (into α))) ≃ _

  let t := (yoneda.obj (colimit (into β))).mapIso (colimit_op (into α))
  refine' t.toEquiv.trans _

  have x : PreservesLimitsOfSize.{max u (max v w), max u (max v w)} (yoneda.obj (colimit (into β))) := by infer_instance
  have q := preservesLimitsOfSizeShrink.{w, max u (max v w), w, max u (max v w)} (yoneda.obj (colimit (into β)))
  have y : PreservesLimit (into α).op (yoneda.obj (colimit (into β))) := by infer_instance
  have : HasLimitsOfSize.{w, w} (Type max (max u v) w) := by sorry
  have z : HasLimit ((into α).op ⋙ yoneda.obj (colimit (into β))) := by sorry

  let u := preservesLimitIso (yoneda.obj (colimit (into β))) (into α).op
  refine' u.toEquiv.trans _

  let v := lim.mapIso (my_yoneda_lemma α (colimit (into β)))
  refine' v.toEquiv.trans _

  set! as := colimit (into β) with has

  --have : PreservesLimitsOfSize.{w, w} uliftFunctor.{max u v, max w v} := sorry
  have i₁ :  PreservesLimit (α.op ⋙ colimit (into β)) uliftFunctor.{max u v, max w v} := sorry
  have i₂ : HasLimit (α.op ⋙ colimit (into β)) := sorry
  have i₃ : HasLimit ((α.op ⋙ colimit (into β)) ⋙ uliftFunctor.{max u v, max w v}) := sorry
  let o := @preservesLimitIso _ _ _ _ uliftFunctor.{max u v, max w v} _ _ (α.op ⋙ as) i₁ i₂ i₃

  refine' o.toEquiv.symm.trans _
  refine' Equiv.ulift.trans _
  dsimp [has, into]

  let oo := colimitIsoFlipCompColim ((β ⋙ yoneda ⋙ (whiskeringRight Cᵒᵖ (Type v) TypeMax.{w, v}).obj uliftFunctor.{w}))
  let oo' := isoWhiskerLeft α.op oo
  let oo'' := lim.mapIso oo'
  refine' oo''.toEquiv.trans _
  dsimp [homs₆, homs₄]

  let rr := two_hom_functors β
  let rr' := isoWhiskerRight rr colim
  let rr'' := isoWhiskerLeft α.op rr'
  let rr''' := lim.mapIso rr''
  exact rr'''.toEquiv
