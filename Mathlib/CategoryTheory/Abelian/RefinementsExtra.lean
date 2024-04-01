import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.Balanced
import Mathlib.CategoryTheory.Sites.Limits

universe w v u

namespace CategoryTheory

open Opposite Limits Category

namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace PushoutCocone

variable {Z X₁ X₂ : C} {f₁ : Z ⟶ X₁} {f₂ : Z ⟶ X₂} (c : PushoutCocone f₁ f₂)
  [HasBinaryBiproduct X₁ X₂]

@[simps]
noncomputable def shortComplex : ShortComplex C where
  X₁ := Z
  X₂ := X₁ ⊞ X₂
  X₃ := c.pt
  f := biprod.lift f₁ (-f₂)
  g := biprod.desc c.inl c.inr
  zero := by simp [c.condition]

noncomputable def isColimitOfExactShortComplex [Balanced C]
    (hc : c.shortComplex.Exact) (hc' : Epi c.shortComplex.g) :
    IsColimit c :=
  PushoutCocone.isColimitAux _
    (fun s => hc.desc (biprod.desc s.inl s.inr) (by simp [s.condition]))
    (fun s => by simpa using biprod.inl ≫= hc.g_desc (biprod.desc s.inl s.inr) _)
    (fun s => by simpa using biprod.inr ≫= hc.g_desc (biprod.desc s.inl s.inr) _)
    (fun s m hm => by
      rw [← cancel_epi (PushoutCocone.shortComplex c).g, hc.g_desc]
      aesop_cat)


end PushoutCocone

namespace PullbackCone

variable {X₁ X₂ Y : C} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} (c : PullbackCone f₁ f₂)
  [HasBinaryBiproduct X₁ X₂]


@[simps]
noncomputable def shortComplex : ShortComplex C where
  X₁ := c.pt
  X₂ := X₁ ⊞ X₂
  X₃ := Y
  f := biprod.lift c.fst c.snd
  g := biprod.desc f₁ (-f₂)
  zero := by simp [c.condition]

lemma exact_shortComplex_of_isLimit (hc : IsLimit c)
    [(shortComplex c).HasHomology] : c.shortComplex.Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  let pullbackCone : ∀ {W : C} (φ : W ⟶ X₁ ⊞ X₂), φ ≫ biprod.desc f₁ (-f₂) = 0 →
        PullbackCone f₁ f₂ := fun {W} φ hφ =>
    PullbackCone.mk (φ ≫ biprod.fst) (φ ≫ biprod.snd) (by
      rw [← sub_eq_zero, assoc, assoc, ← Preadditive.comp_sub]
      convert hφ
      aesop_cat)
  exact KernelFork.IsLimit.ofι _ _
    (fun f hf => hc.lift (pullbackCone f hf))
    (fun f hf => by
      dsimp
      ext <;> simp [pullbackCone])
    (fun f hf m hm => by
      have hm₁ := hm =≫ biprod.fst
      have hm₂ := hm =≫ biprod.snd
      dsimp at hm₁ hm₂
      simp only [assoc, biprod.lift_fst, biprod.lift_snd] at hm₁ hm₂
      apply PullbackCone.IsLimit.hom_ext hc
      · simp [hm₁, pullbackCone]
      · simp [hm₂, pullbackCone])

end PullbackCone

end Limits

namespace Abelian

section

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable {X Y Z : C} {f : X ⟶ Y} [Epi f] {π₁ π₂ : Z ⟶ X}

noncomputable def effectiveEpiStructOfEpiOfIsPushout (hc : IsPushout π₁ π₂ f f) :
    EffectiveEpiStruct f where
  desc {W} φ h := PushoutCocone.IsColimit.desc hc.isColimit φ φ (h _ _ hc.w)
  fac {W} φ h := PushoutCocone.IsColimit.inl_desc hc.isColimit _ _ _
  uniq {W} φ h m hm := by
    rw [← cancel_epi f, hm]
    symm
    apply PushoutCocone.IsColimit.inl_desc hc.isColimit

lemma isPushout_of_isPullback_of_epi (hc : IsPullback π₁ π₂ f f) :
    IsPushout π₁ π₂ f f := by
  have hc' : IsColimit (PushoutCocone.mk _ _ hc.w) := by
    apply PushoutCocone.isColimitOfExactShortComplex
    · refine' ShortComplex.exact_of_iso _ (PullbackCone.exact_shortComplex_of_isLimit _ hc.isLimit)
      refine' ShortComplex.isoMk (Iso.refl _)
        { hom := biprod.desc biprod.inl (-biprod.inr)
          inv := biprod.desc biprod.inl (-biprod.inr) }
        (Iso.refl _) (by aesop_cat) (by aesop_cat)
    · dsimp; infer_instance
  exact IsPushout.of_isColimit hc'

end

lemma effective_epi_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    EffectiveEpi f where
  effectiveEpi := ⟨effectiveEpiStructOfEpiOfIsPushout
    (isPushout_of_isPullback_of_epi (IsPullback.of_isLimit (pullbackIsPullback f f)))⟩

variable (C)

def refinementsTopology :
    GrothendieckTopology C where
  sieves X S := ∃ (T : C) (p : T ⟶ X) (_ : Epi p), S p
  top_mem' X := ⟨X, 𝟙 X, inferInstance, by simp⟩
  pullback_stable' X Y S f hS := by
    obtain ⟨T, p, hp, h⟩ := hS
    refine' ⟨pullback f p, pullback.fst, inferInstance, _⟩
    dsimp
    rw [pullback.condition]
    apply S.downward_closed h
  transitive' X S hS R hR := by
    obtain ⟨T, p, hp, h⟩ := hS
    obtain ⟨U, q, hq, h'⟩ := hR h
    exact ⟨_, q ≫ p, epi_comp _ _, h'⟩

instance : Preregular C where
  exists_fac {X Y Z} f g _ := by
    obtain ⟨A, π, hπ, i, fac⟩ := surjective_up_to_refinements_of_epi g f
    exact ⟨A, π, effective_epi_of_epi π, i, fac.symm⟩

lemma refinementsTopology_eq_regularTopology :
    refinementsTopology C = regularTopology C := by
  apply le_antisymm
  · rintro X S ⟨T, p, _, hp⟩
    refine (regularTopology C).superset_covering ?_
      (Coverage.saturate.of X _ ⟨_, p, rfl, effective_epi_of_epi p⟩)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟨⟩⟩
    exact hp
  · apply ((Coverage.gi C).gc _ _).2
    rintro X S ⟨Y, s, rfl, _⟩
    exact ⟨_, s, inferInstance, _, 𝟙 _, s, ⟨Unit.unit⟩, by simp⟩

lemma refinementsTopology_subcanonical :
    Sheaf.Subcanonical (refinementsTopology C) := by
  rw [refinementsTopology_eq_regularTopology]
  exact regularCoverage.subcanonical

end

namespace refinementsTopology

lemma epi_iff_isLocallySurjective_yoneda_map {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Sheaf.IsLocallySurjective ((refinementsTopology_subcanonical C).yoneda.map f) := by
  rw [epi_iff_surjective_up_to_refinements f]
  constructor
  · intro hf
    refine' ⟨fun {U} (y : U.unop ⟶ Y) => _⟩
    obtain ⟨A', π, hπ, x, fac⟩ := hf y
    dsimp
    exact ⟨A', π, hπ, x, fac.symm⟩
  · intro hf
    intro A y
    obtain ⟨A', π, hπ, x, fac⟩ := Presheaf.imageSieve_mem (refinementsTopology C)
      ((refinementsTopology_subcanonical C).yoneda.map f).val y
    exact ⟨A', π, hπ, x, fac.symm⟩

lemma epi_iff_epi_yoneda_map {C : Type u} [SmallCategory C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Epi ((refinementsTopology_subcanonical C).yoneda.map f) := by
  rw [epi_iff_isLocallySurjective_yoneda_map, Sheaf.epi_iff_isLocallySurjective]

end refinementsTopology

end Abelian

end CategoryTheory
