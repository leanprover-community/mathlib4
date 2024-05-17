import Mathlib.CategoryTheory.Sites.OneHypercover

universe w v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

namespace GrothendieckTopology

variable (H : ∀ ⦃X : C⦄, OneHypercover.{w} J X → Prop)

class IsGeneratingOneHypercoverFamily : Prop where
  le {X : C} (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S

variable (J) in
lemma exists_oneHypercover_of_isGeneratingOneHypercoverFamily
    [GrothendieckTopology.IsGeneratingOneHypercoverFamily H] {X : C}
    (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S :=
  IsGeneratingOneHypercoverFamily.le _ hS

variable (J) in
abbrev IsGeneratedByOneHypercovers : Prop :=
  IsGeneratingOneHypercoverFamily.{w} (J := J) ⊤

structure Cover.Relation₂ {X : C} (S : J.Cover X) (f₁ f₂ : S.Arrow) where
  Y : C
  p₁ : Y ⟶ f₁.Y
  p₂ : Y ⟶ f₂.Y
  w : p₁ ≫ f₁.f = p₂ ≫ f₂.f

namespace Cover

variable {X : C} (S : J.Cover X)

@[simps]
def preOneHypercover  :
    PreOneHypercover X where
  I₀ := S.Arrow
  X f := f.Y
  f f := f.f
  I₁ f₁ f₂ := S.Relation₂ f₁ f₂
  Y _ _ ρ := ρ.Y
  p₁ _ _ ρ := ρ.p₁
  p₂ _ _ ρ := ρ.p₂
  w _ _ ρ := ρ.w

@[simp]
lemma preOneHypercover_sieve₀ : S.preOneHypercover.sieve₀ = S.1 := by
  ext Y f
  constructor
  · rintro ⟨_, a, _, ⟨f⟩, rfl⟩
    exact S.1.downward_closed f.hf _
  · intro hf
    exact ⟨Y, 𝟙 _, f, ⟨(⟨_, f, hf⟩ : S.Arrow)⟩, by simp⟩

lemma preOneHypercover_sieve₁ {i₁ i₂ : S.preOneHypercover.I₀} {W : C}
    (p₁ : W ⟶ S.preOneHypercover.X i₁)
    (p₂ : W ⟶ S.preOneHypercover.X i₂)
    (w : p₁ ≫ i₁.f = p₂ ≫ i₂.f) :
    S.preOneHypercover.sieve₁ p₁ p₂ = ⊤ := by
  ext Y f
  constructor
  · simp
  · intro
    exact ⟨⟨_, p₁, p₂, w⟩, f, rfl, rfl⟩

@[simps toPreOneHypercover]
def OneHypercover {X : C} (S : J.Cover X) :
    J.OneHypercover X where
  toPreOneHypercover := S.preOneHypercover
  mem₀ := by simp
  mem₁ i₁ i₂ W p₁ p₂ w := by simp [preOneHypercover_sieve₁ _ _ _ w]

end Cover

instance : IsGeneratedByOneHypercovers.{max u v} J where
  le {X} S hS := ⟨Cover.OneHypercover ⟨_, hS⟩, by simp, by simp⟩

end GrothendieckTopology

namespace Presheaf

section

variable (H : ∀ ⦃X : C⦄, GrothendieckTopology.OneHypercover.{w} J X → Prop)
  [GrothendieckTopology.IsGeneratingOneHypercoverFamily H] (P : Cᵒᵖ ⥤ A)

namespace IsSheafOfIsGeneratingOneHypercover

open GrothendieckTopology

variable (hP : ∀ ⦃X : C⦄ (E : J.OneHypercover X)
  (_ : H E), Nonempty (IsLimit (E.multifork P)))

lemma hom_ext {X : C} (S : Sieve X) (hS : S ∈ J X) {T : A}
    {x y : T ⟶ P.obj (Opposite.op X)}
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), x ≫ P.map f.op = y ≫ P.map f.op) :
    x = y := by
  obtain ⟨E, hE, le⟩ :=
    J.exists_oneHypercover_of_isGeneratingOneHypercoverFamily H S hS
  apply Multifork.IsLimit.hom_ext (hP E hE).some
  intro j
  exact h _ (le _ (Sieve.ofArrows_mk _ _ _))

variable {P H}
variable {X : C} {S : Sieve X}
  {E : J.OneHypercover X} (hE : H E) (le : E.sieve₀ ≤ S)

section

variable (F : Multifork (Cover.index ⟨S, J.superset_covering le E.mem₀⟩ P))

noncomputable def lift : F.pt ⟶ P.obj (Opposite.op X) :=
  Multifork.IsLimit.lift (hP E hE).some
    (fun i => F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩)
    (fun ⟨⟨i₁, i₂⟩, j⟩ => F.condition
        { h₁ := le _ ((Sieve.ofArrows_mk _ _ i₁))
          h₂ := le _ ((Sieve.ofArrows_mk _ _ i₂))
          w := E.w j })

@[reassoc]
lemma fac' (i : E.I₀) :
    lift hP hE le F ≫ P.map (E.f i).op =
      F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩ :=
  Multifork.IsLimit.fac (hP E hE).some _ _ i

lemma fac {Y : C} (f : Y ⟶ X) (hf : S f) :
    lift hP hE le F ≫ P.map f.op = F.ι ⟨Y, f, hf⟩ := by
  apply hom_ext H P hP _ (J.pullback_stable f E.mem₀)
  intro Z g
  rintro ⟨T, a, b, hb, fac⟩
  obtain ⟨i, rfl, hi⟩ := hb.exists
  dsimp at hi
  rw [id_comp] at hi
  subst hi
  rw [assoc, ← P.map_comp, ← op_comp, ← fac,
    op_comp, P.map_comp, fac'_assoc]
  exact F.condition
    { h₁ := le _ (Sieve.ofArrows_mk _ _ _)
      h₂ := hf
      w := fac }

end

noncomputable def isLimit :
    IsLimit (Cover.multifork ⟨S, J.superset_covering le E.mem₀⟩ P) :=
  Multifork.IsLimit.mk _ (fun F => lift hP hE le F) (fun F => by
    rintro ⟨Y, f, hf⟩
    apply fac) (fun F m hm => by
      apply hom_ext H P hP S (J.superset_covering le E.mem₀)
      intro Y f hf
      dsimp
      rw [fac _ _ _ _ _ hf]
      exact hm ⟨_, _, hf⟩)

end IsSheafOfIsGeneratingOneHypercover

lemma isSheaf_iff_of_isGeneratingOneHypercover :
    IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : J.OneHypercover X)
      (_ : H E), Nonempty (IsLimit (E.multifork P)) := by
  constructor
  · intro hP X E _
    exact ⟨E.isLimitMultifork ⟨_, hP⟩⟩
  · intro hP
    rw [isSheaf_iff_multifork]
    rintro X ⟨S, hS⟩
    obtain ⟨E, hE, le⟩ :=
      J.exists_oneHypercover_of_isGeneratingOneHypercoverFamily H S hS
    exact ⟨IsSheafOfIsGeneratingOneHypercover.isLimit hP hE le⟩

end

variable (J)

lemma isSheaf_iff_of_isGeneratedByOneHypercovers
      [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J]
      (P : Cᵒᵖ ⥤ A) :
    IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : GrothendieckTopology.OneHypercover.{w} J X),
        Nonempty (IsLimit (E.multifork P)) := by
  rw [isSheaf_iff_of_isGeneratingOneHypercover.{w} ⊤]
  simp

end Presheaf

end CategoryTheory
