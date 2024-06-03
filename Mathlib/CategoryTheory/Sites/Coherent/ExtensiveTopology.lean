import Mathlib.CategoryTheory.Sites.Coherent.Basic

open CategoryTheory Limits

variable {C : Type*} [Category C] [FinitaryPreExtensive C]

namespace CategoryTheory

lemma Limits.Cofan.isColimit_iff_isIso_sigmaDesc
    {β : Type*} {f : β → C} [HasCoproduct f] (c : Cofan f) :
    IsIso (Sigma.desc c.inj) ↔ Nonempty (IsColimit c) := by
  refine ⟨fun h ↦ ⟨isColimitOfIsIsoSigmaDesc c⟩, fun ⟨hc⟩ ↦ ?_⟩
  have : IsIso (hc.desc c) := by simp; infer_instance
  have : IsIso (((coproductIsCoproduct f).coconePointUniqueUpToIso hc).hom ≫ hc.desc c) :=
    inferInstance
  convert this
  ext
  simp only [colimit.ι_desc, mk_pt, mk_ι_app, IsColimit.coconePointUniqueUpToIso,
    coproductIsCoproduct, colimit.cocone_x, Functor.mapIso_hom, IsColimit.uniqueUpToIso_hom,
    Cocones.forget_map, IsColimit.descCoconeMorphism_hom, IsColimit.ofIsoColimit_desc,
    Cocones.ext_inv_hom, Iso.refl_inv, colimit.isColimit_desc, Category.id_comp,
    IsColimit.desc_self, Category.comp_id]
  rfl

def Limits.Cofan.isColimitTrans {α : Type*} {X : α → C} (c : Cofan X) (hc : IsColimit c)
    {β : α → Type*} {Y : (a : α) → β a → C} (π : (a : α) → (b : β a) → Y a b ⟶ X a)
      (hs : ∀ a, IsColimit (Cofan.mk (X a) (π a))) :
        IsColimit (Cofan.mk (f := fun ⟨a,b⟩ => Y a b) c.pt
          (fun (⟨a, b⟩ : Σ a, _) ↦ π a b ≫ c.inj a)) := by
  refine mkCofanColimit _ ?_ ?_ ?_
  · exact fun t ↦ hc.desc (Cofan.mk _ fun a ↦ (hs a).desc (Cofan.mk t.pt (fun b ↦ t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    simp only [mk_pt]
    apply hc.hom_ext
    intro ⟨a⟩
    apply (hs a).hom_ext
    intro ⟨b⟩
    erw [hc.fac, (hs a).fac]
    specialize h ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc, Discrete.functor_obj, Functor.const_obj_obj,
      mk_ι_app] at h ⊢
    exact h

lemma extensiveTopology.mem_sieves_iff_contains_colimit_cofan {X : C} (S : Sieve X) :
    S ∈ (extensiveTopology C).sieves X ↔
      (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        Nonempty (IsColimit (Cofan.mk X π)) ∧ (∀ a : α, (S.arrows) (π a))) := by
  constructor
  · intro h
    induction h with
    | of X S hS =>
      obtain ⟨α, _, Y, π, h, h'⟩ := hS
      refine ⟨α, inferInstance, Y, π, ?_, fun a ↦ ?_⟩
      · have : IsIso (Sigma.desc (Cofan.mk X π).inj) := by simpa using h'
        exact ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩
      · obtain ⟨rfl, _⟩ := h
        exact ⟨Y a, 𝟙 Y a, π a, Presieve.ofArrows.mk a, by simp⟩
    | top X =>
      refine ⟨Unit, inferInstance, fun _ => X, fun _ => (𝟙 X), ⟨?_⟩, by simp⟩
      have : IsIso (Sigma.desc (Cofan.mk X fun _ ↦ 𝟙 X).inj) := by
        have : IsIso (coproductUniqueIso (fun () => X)).hom := inferInstance
        exact this
      exact Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X _)
    | transitive X R S _ _ a b =>
      obtain ⟨α, w, Y₁, π, h, h'⟩ := a
      choose β _ Y_n π_n H using fun a => b (h' a)
      exact ⟨(Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a),
        ⟨Limits.Cofan.isColimitTrans _ h.some _ (fun a ↦ (H a).1.some)⟩,
        fun c => (H c.fst).2 c.snd⟩
  · intro ⟨α, _, Y, π, h, h'⟩
    apply (extensiveCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
    · exact fun _ _ hh ↦ by cases hh; exact h' _
    · refine ⟨α, inferInstance, Y, π, rfl, ?_⟩
      erw [Limits.Cofan.isColimit_iff_isIso_sigmaDesc (c := Cofan.mk X π)]
      exact h
