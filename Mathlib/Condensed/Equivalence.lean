/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nick Kuhn, Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Closed
/-!
# Sheaves on CompHaus are equivalent to sheaves on Stonean

The forgetful functor from extremally disconnected spaces `Stonean` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `Stonean` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Mathlib has isolated three properties called `CoverDense`, `CoverPreserving` and `CoverLifting`,
which between them imply that `Stonean` is a dense subsite, and it also has the
construction of the equivalence of the categories of sheaves, given these three properties.

## Main theorems

* `Condensed.coverDense`, `Condensed.coverPreserving`, `Condensed.coverLifting`: the
three conditions needed to guarantee the equivalence of the categories of sheaves
on the two sites.
-/

open CategoryTheory Limits

section Sieve

universe v u
variable {C : Type u} [Category.{v} C] [Precoherent C] (X : C)

open CategoryTheory Limits Presieve

theorem coherentTopology.Sieve_of_has_EffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) →
          (S ∈ GrothendieckTopology.sieves (coherentTopology C) X) := by
  rintro ⟨α, ⟨h, ⟨Y, ⟨π, hπ⟩⟩⟩⟩
  change Coverage.saturate _ _ _
  let T := Sieve.generate (Presieve.ofArrows _ π)
  have h_le : T ≤ S := by
      rw [Sieve.sets_iff_generate (Presieve.ofArrows _ π) S]
      refine Presieve.le_of_factorsThru_sieve (Presieve.ofArrows (fun i => Y i) π) S ?h
      intro Y g f
      use Y, 𝟙 Y
      rcases f with ⟨i⟩
      use (π i)
      constructor
      · exact hπ.2 i
      · exact Category.id_comp (π i)
  apply Coverage.saturate_of_superset (coherentCoverage C) h_le (_)
  refine Coverage.saturate.of X _ ?_
  · unfold coherentCoverage
    simp
    use α, inferInstance, Y, π
    constructor
    · rfl
    · exact hπ.1

/--
We show that the Yoneda embedding factors through sheaves for the coherent topology. This uses
1. The yoneda functor is a sheaf for a sieve over X, if X is the colimit of the associated cocone
2. This is true for the coherent topology
-/

example (A B : C) (f : A ⟶ B) : f = (𝟙 A) ≫ f := by exact Eq.symm (Category.id_comp f)

variable {X}

def Sieve.yonedafamily_toCocone (W : C) (P : Presieve X) (x : FamilyOfElements (yoneda.obj W) P)
  (hx : FamilyOfElements.Compatible x):
     Cocone (P.diagram)  where
  pt := W
  ι  := {
    app := fun f => x f.obj.hom f.property
    naturality := by
      intro g₁ g₂ F
      simp only [Functor.id_obj, Functor.comp_obj, fullSubcategoryInclusion.obj, Over.forget_obj,
          Functor.const_obj_obj, Functor.comp_map, fullSubcategoryInclusion.map, Over.forget_map,
          Functor.const_obj_map, Category.comp_id]
      rw [← Category.id_comp (x g₁.obj.hom g₁.property)]
      apply hx
      aesop_cat
  }


def Sieve.yonedaFamilyOfElements_fromCocone (S : Sieve X) (s : Cocone (diagram S.arrows)) :
      FamilyOfElements (yoneda.obj s.pt) (S.arrows) := fun _ f hf => s.ι.app ⟨Over.mk f, hf⟩

lemma Sieve.yonedaFamily_fromCocone_compatible (S : Sieve X) (s : Cocone (diagram S.arrows)) :
    FamilyOfElements.Compatible <| yonedaFamilyOfElements_fromCocone S s := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hgf
  have := s.ι.naturality
  simp
  dsimp [yonedaFamilyOfElements_fromCocone]
  have hgf₁ : S.arrows (g₁ ≫ f₁) := by exact Sieve.downward_closed S hf₁ g₁
  have hgf₂ : S.arrows (g₂ ≫ f₂) := by exact Sieve.downward_closed S hf₂ g₂

  let F : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk (g₂ ≫ f₂) : Over X) := (Over.homMk (𝟙 Z) )
  let F₁ : (Over.mk (g₁ ≫ f₁) : Over X) ⟶ (Over.mk f₁ : Over X) := (Over.homMk g₁)
  let F₂ : (Over.mk (g₂ ≫ f₂) : Over X) ⟶ (Over.mk f₂ : Over X) := (Over.homMk g₂)

  have hF := @this ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ F
  have hF₁ := @this ⟨Over.mk (g₁ ≫ f₁), hgf₁⟩ ⟨Over.mk f₁, hf₁⟩ F₁
  have hF₂ := @this ⟨Over.mk (g₂ ≫ f₂), hgf₂⟩ ⟨Over.mk f₂, hf₂⟩ F₂

  simp at this ⊢
  aesop_cat



theorem Sieve.Yoneda_sheaf_iff_colimit (S : Sieve X) :
    (∀ W : C, Presieve.IsSheafFor (yoneda.obj W) (S : Presieve X)) ↔
      Nonempty (IsColimit S.arrows.cocone) := by
  constructor
  · intro H
    refine Nonempty.intro ?mp.val
    exact {
    desc := fun s => H s.pt (yonedaFamilyOfElements_fromCocone S s)
        (yonedaFamily_fromCocone_compatible S s) |>.choose
    fac := by
      intro s f
      replace H := H s.pt (yonedaFamilyOfElements_fromCocone S s)
         (yonedaFamily_fromCocone_compatible S s)
      have ht := H.choose_spec.1 f.obj.hom f.property
      aesop_cat
    uniq := by
      intro s Fs HFs
      replace H := H s.pt (yonedaFamilyOfElements_fromCocone S s)
          (yonedaFamily_fromCocone_compatible S s)
      apply H.choose_spec.2 Fs
      exact fun _ f hf => HFs ⟨Over.mk f, hf⟩
    }
  · intro H W x hx
    replace H := Classical.choice H
    let s := Sieve.yonedafamily_toCocone W S x hx
    use H.desc s
    constructor
    · exact fun _ f hf => (H.fac s) ⟨Over.mk f, hf⟩
    · intro g hg
      apply H.uniq s g
      rintro ⟨⟨f, _, hom⟩, hf⟩
      apply hg hom hf


theorem coherentTopology.isSheaf_Yoneda (W : C) :
    Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim:= isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [←Sieve.generateFamily_eq] at h_colim

  intro x hx
  let x_ext := FamilyOfElements.sieveExtend x
  have hx_ext := FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (ofArrows Y π)
  have := (Sieve.Yoneda_sheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  rcases this with ⟨t, t_amalg, t_uniq⟩
  use t

  constructor
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate (ofArrows Y π)) _ _ t_amalg
    refine Eq.symm (restrict_extend hx)
  · exact fun y hy => t_uniq y <| isAmalgamation_sieveExtend x y hy


def effectiveEpiFamilyStructId : EffectiveEpiFamilyStruct (fun _ : Unit => X) (fun _ => 𝟙 _) where
  desc := fun e _ => e ()
  fac := by aesop_cat
  uniq := by aesop_cat

instance : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) :=
  ⟨⟨CategoryTheory.effectiveEpiFamilyStructId⟩⟩

-- check `effectiveEpiFamilyStructOfIsColimit` and `isColimitOfEffectiveEpiFamilyStruct`
theorem EffectiveEpiFamily_transitive {α : Type} [Fintype α] (Y : α → C)
    (π : (a : α) → (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α → Type} [∀ (a: α), Fintype (β a)]
    (Y_n : (a : α) → β a → C) (π_n : (a : α) → (b : β a) → (Y_n a b ⟶ Y a))
    (H : ∀ a, EffectiveEpiFamily (Y_n a) (π_n a)) :
EffectiveEpiFamily (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ GrothendieckTopology.sieves (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.Yoneda_sheaf_iff_colimit]
    intro W
    apply coherentTopology.isSheaf_Yoneda
    exact h₂

  let h' := h
  rw [← Sieve.effectiveEpimorphic_family] at h'
  let H' := H
  conv at H' =>
    intro a
    rw [← Sieve.effectiveEpimorphic_family]
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    apply coherentTopology.Sieve_of_has_EffectiveEpiFamily
    rcases hY with ⟨i⟩
    use β i, inferInstance, Y_n i, π_n i
    constructor
    · exact H i
    · intro b
      use Y_n i b, (𝟙 _), π_n i b ≫ π i
      constructor
      · exact ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩
      · exact Category.id_comp (π_n i b ≫ π i)



theorem coherentTopology.Sieve_iff_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
          (S ∈ GrothendieckTopology.sieves (coherentTopology C) X) := by
  constructor
  · exact coherentTopology.Sieve_of_has_EffectiveEpiFamily X S
  · intro h
    induction' h with Y T hS  Y Y R S _ _ a b
    · rcases hS with ⟨a, h, Y', π, h'⟩
      use a, h, Y', π
      constructor
      · tauto
      · intro a'
        cases' h' with h_left h_right
        simp only [Sieve.generate_apply]
        use Y' a', 𝟙 Y' a', π a'
        constructor
        · rw [h_left]
          exact Presieve.ofArrows.mk a'
        · apply Category.id_comp
    · use Unit, Unit.fintype, fun _ => Y, fun _ => (𝟙 Y)
      cases' S with arrows downward_closed
      constructor
      · exact inferInstance
      · simp only [Sieve.top_apply, forall_const]
    · rcases a with ⟨α, w, Y₁, π, ⟨h₁,h₂⟩⟩
      have H : ∀ a : α, ∃ (β : Type) (_ : Fintype β) (Y_n : β → C)
          (π_n: (b : β) →  (Y_n b)⟶ Y₁ a),
            EffectiveEpiFamily Y_n π_n ∧ (∀ b : β, (S.pullback (π a)).arrows (π_n b)) :=
        fun a => b (h₂ a)
      rw [Classical.skolem] at H
      rcases H with ⟨β, H⟩
      rw [Classical.skolem] at H
      rcases H with ⟨_, H⟩
      rw [Classical.skolem] at H
      rcases H with ⟨Y_n, H⟩
      rw [Classical.skolem] at H
      rcases H with ⟨π_n, H⟩
      use Σ x, β x, inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a)
      constructor
      · apply EffectiveEpiFamily_transitive
        · exact h₁
        · exact fun a => (H a).1
      · exact fun c => (H c.fst).2 c.snd


end Sieve

namespace Condensed

universe u w

namespace StoneanCompHaus

lemma coverDense :
    CoverDense (coherentTopology _) Stonean.toCompHaus := by
  constructor
  intro B
  let T := Presieve.singleton (CompHaus.presentation.π B)
  let S := Sieve.generate T
  have hS : S ∈ coherentTopology CompHaus B := by
    apply Coverage.saturate.of
    change ∃ _, _
    refine ⟨Unit, inferInstance,
      fun _ => B.presentation.compHaus, fun _ => (CompHaus.presentation.π B), ?_ , ?_⟩
    · funext X f
      ext
      constructor
      · rintro ⟨⟩
        refine ⟨()⟩
      · rintro ⟨⟩
        simp
    · have := CompHaus.effectiveEpiFamily_tfae
        (fun (_ : Unit) => B.presentation.compHaus)
        (fun (_ : Unit) => (CompHaus.presentation.π B))
      apply (this.out 0 2).mpr
      intro b
      refine ⟨(), ?_⟩
      have hπ :
        Function.Surjective (CompHaus.presentation.π B) := by
          rw [← CompHaus.epi_iff_surjective (CompHaus.presentation.π B)]
          exact CompHaus.presentation.epi_π B
      exact hπ b
  convert hS
  ext Y f
  constructor
  · rintro ⟨⟨obj, lift, map, fact⟩⟩
    obtain ⟨obj_factors⟩ : Projective obj.compHaus := by
      infer_instance
    obtain ⟨p, p_factors⟩ := obj_factors map (CompHaus.presentation.π B)
    refine ⟨(CompHaus.presentation B).compHaus ,?_⟩
    refine ⟨lift ≫ p, ⟨ (CompHaus.presentation.π B)
        , {
        left := Presieve.singleton.mk
        right := by
          rw [Category.assoc, p_factors, fact]
      } ⟩
      ⟩
  · rintro ⟨Z, h, g, hypo1, ⟨_⟩⟩
    cases hypo1
    constructor
    refine
    { obj := CompHaus.presentation B
      lift := h
      map := CompHaus.presentation.π B
      fac := rfl }

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Stonean) (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → Stonean) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
          (S ∈ coverDense.inducedTopology X) := by
  constructor
  · rintro ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩
    unfold CoverDense.inducedTopology
    unfold LocallyCoverDense.inducedTopology
    simp only [Stonean.toCompHaus_obj]
    change _ ∈ GrothendieckTopology.sieves _ _
    apply (coherentTopology.Sieve_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mp
    use α, inferInstance
    use fun i => Stonean.toCompHaus.obj (Y i)
    use fun i => Stonean.toCompHaus.map (π i)
    constructor
    · simp only [Stonean.toCompHaus_obj, Stonean.toCompHaus_map]
      -- Show that an `effectiveEpiFamily` pushes forward to one
      simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
      exact CompHaus.effectiveEpiFamily_of_jointly_surjective
          (fun i => (Y i).compHaus) (fun i => π i) H₁
    · exact fun a => Sieve.image_mem_functorPushforward Stonean.toCompHaus S (H₂ a)
  · intro hS
    unfold CoverDense.inducedTopology at hS
    unfold LocallyCoverDense.inducedTopology at hS
    simp only [Stonean.toCompHaus_obj] at hS
    change _ ∈ GrothendieckTopology.sieves _ _ at hS
    replace hS := (coherentTopology.Sieve_iff_hasEffectiveEpiFamily _).mpr hS
    rcases hS with ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩
    use α, inferInstance
    change ∀ a, ∃ (Y₀: Stonean) (π₀ : Y₀⟶ X) (f₀: Y a ⟶ Y₀.compHaus), S.arrows π₀ ∧
        π a = f₀ ≫ Stonean.toCompHaus.map π₀  at H₂
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨Y₀, H₂⟩
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨π₀, H₂⟩
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨f₀, H₂⟩
    use Y₀ , π₀
    constructor
    · simp only [(Stonean.effectiveEpiFamily_tfae _ _).out 0 2]
      simp only [(CompHaus.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
      intro b
      replace H₁ := H₁ b
      rcases H₁ with ⟨i, x, H₁⟩
      use i, f₀ i x
      aesop_cat
    · intro i
      exact (H₂ i).1

lemma coherentTopology_is_induced :
    coherentTopology Stonean.{u} = coverDense.inducedTopology := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X]
  rw [← coherentTopology.Sieve_iff_hasEffectiveEpiFamily S]


lemma coverPreserving :
  CoverPreserving
    (coherentTopology _)
    (coherentTopology _)
    Stonean.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
  CoverLifting
    (coherentTopology _)
    (coherentTopology _)
    Stonean.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
CoverDense.sheafEquivOfCoverPreservingCoverLifting
  coverDense coverPreserving coverLifting

end StoneanCompHaus

namespace StoneanProfinite

lemma coverDense :
    CoverDense (coherentTopology _) Stonean.toProfinite := by
  sorry
  -- constructor
  -- intro B
  -- let T := Presieve.singleton (CompHaus.presentation.π B.toCompHaus)
  -- let S := Sieve.generate T
  -- have hS : S ∈ coherentTopology Profinite B := by
  --   apply Coverage.saturate.of
  --   change ∃ _, _
  --   refine ⟨Unit, inferInstance,
  --     fun _ => B.presentation.compHaus, fun _ => (CompHaus.presentation.π B), ?_ , ?_⟩
  --   · funext X f
  --     ext
  --     constructor
  --     · rintro ⟨⟩
  --       refine ⟨()⟩
  --     · rintro ⟨⟩
  --       simp
  --   · have := CompHaus.effectiveEpiFamily_tfae
  --       (fun (_ : Unit) => B.presentation.compHaus)
  --       (fun (_ : Unit) => (CompHaus.presentation.π B))
  --     apply (this.out 0 2).mpr
  --     intro b
  --     refine ⟨(), ?_⟩
  --     have hπ :
  --       Function.Surjective (CompHaus.presentation.π B) := by
  --         rw [← CompHaus.epi_iff_surjective (CompHaus.presentation.π B)]
  --         exact CompHaus.presentation.epi_π B
  --     exact hπ b
  -- convert hS
  -- ext Y f
  -- constructor
  -- · rintro ⟨⟨obj, lift, map, fact⟩⟩
  --   obtain ⟨obj_factors⟩ : Projective obj.compHaus := by
  --     infer_instance
  --   obtain ⟨p, p_factors⟩ := obj_factors map (CompHaus.presentation.π B)
  --   refine ⟨(CompHaus.presentation B).compHaus ,?_⟩
  --   refine ⟨lift ≫ p, ⟨ (CompHaus.presentation.π B)
  --       , {
  --       left := Presieve.singleton.mk
  --       right := by
  --         rw [Category.assoc, p_factors, fact]
  --     } ⟩
  --     ⟩
  -- · rintro ⟨Z, h, g, hypo1, ⟨_⟩⟩
  --   cases hypo1
  --   constructor
  --   refine
  --   { obj := CompHaus.presentation B
  --     lift := h
  --     map := CompHaus.presentation.π B
  --     fac := rfl }


  -- have := StoneanCompHaus.coverDense
  -- constructor
  -- intro U
  -- have h := this.is_cover U.toCompHaus
  -- have hh : Stonean.toProfinite ⋙ profiniteToCompHaus = Stonean.toCompHaus := rfl
  -- rw [← hh] at h

  -- convert h
  -- ext X Y f
  -- dsimp [Sieve.coverByImage, Presieve.coverByImage]
  -- refine ⟨fun ⟨S, lift, map, fac⟩ ↦ ?_, fun ⟨S, lift, map, fac⟩ ↦
  --   ⟨Stonean.toProfinite.obj S, lift, map, fac⟩⟩
  -- refine ⟨S.toCompHaus.presentation, ?_, ?_, ?_⟩
  -- sorry

-- theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Profinite) (S : Sieve X) :
--     (∃ (α : Type) (_ : Fintype α) (Y : α → Profinite) (π : (a : α) → (Y a ⟶ X)),
--     EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
--     (S ∈ coverDense.inducedTopology X) := by
--   sorry

-- lemma coherentTopology_is_induced :
--     coherentTopology Profinite.{u} = coverDense.inducedTopology := by
--   sorry

-- lemma coverPreserving :
--     CoverPreserving (coherentTopology _) (coherentTopology _) profiniteToCompHaus := by
--   rw [coherentTopology_is_induced]
--   exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

-- lemma coverLifting :
--     CoverLifting (coherentTopology _) (coherentTopology _) profiniteToCompHaus := by
--   rw [coherentTopology_is_induced]
--   exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

-- noncomputable
-- def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
--     Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
-- CoverDense.sheafEquivOfCoverPreservingCoverLifting
--   coverDense coverPreserving coverLifting

end StoneanProfinite

namespace ProfiniteCompHaus

lemma coverDense :
    CoverDense (coherentTopology _) profiniteToCompHaus := by
  sorry
  -- have := StoneanCompHaus.coverDense
  -- constructor
  -- intro U
  -- have h := this.is_cover U
  -- have hh : Stonean.toProfinite ⋙ profiniteToCompHaus = Stonean.toCompHaus := rfl
  -- rw [← hh] at h
  -- convert h
  -- ext X Y f
  -- dsimp [Sieve.coverByImage, Presieve.coverByImage]
  -- refine ⟨fun ⟨S, lift, map, fac⟩ ↦ ?_, fun ⟨S, lift, map, fac⟩ ↦
  --   ⟨Stonean.toProfinite.obj S, lift, map, fac⟩⟩
  -- refine ⟨S.toCompHaus.presentation, ?_, ?_, ?_⟩
  -- sorry

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : Profinite) (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → Profinite) (π : (a : α) → (Y a ⟶ X)),
    EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
    (S ∈ coverDense.inducedTopology X) := by
  sorry

lemma coherentTopology_is_induced :
    coherentTopology Profinite.{u} = coverDense.inducedTopology := by
  sorry

lemma coverPreserving :
    CoverPreserving (coherentTopology _) (coherentTopology _) profiniteToCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
    CoverLifting (coherentTopology _) (coherentTopology _) profiniteToCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
CoverDense.sheafEquivOfCoverPreservingCoverLifting
  coverDense coverPreserving coverLifting

end ProfiniteCompHaus

end Condensed
