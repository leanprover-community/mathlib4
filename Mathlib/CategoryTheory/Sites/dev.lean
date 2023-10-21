import Mathlib.CategoryTheory.Sites.SheafOfTypes

universe v u

open CategoryTheory Limits Presieve Opposite

variable {C : Type u} [Category.{v} C] {B : C} {I : Type*} (X : I → C) (π : (i : I) → X i ⟶ B)
  [(ofArrows X π).hasPullbacks] (F : Cᵒᵖ ⥤ Type (max u v))

instance (i j : I) : HasPullback (π i) (π j) :=
  Presieve.hasPullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

def FamilyOfElements' := ∀ i, F.obj (op (X i))

def FamilyOfElements'.PullbackCompatible (x : FamilyOfElements' X F) : Prop :=
  ∀ i j, F.map (pullback.fst (f := π i) (g := π j)).op (x i) =
    F.map (pullback.snd (f := π i) (g := π j)).op (x j)

def FamilyOfElements'.IsAmalgamation  (x : FamilyOfElements' X F) (t : F.obj (op B)) : Prop :=
  ∀ i, F.map (π i).op t = x i

-- def FamilyOfElements.pullbackCompatibleArrows (x : FamilyOfElements F (ofArrows X π)) : Prop :=
--   ∀ i j, F.map (pullback.fst (f := π i) (g := π j)).op (x (π i) (ofArrows.mk _)) =
--     F.map (pullback.snd (f := π i) (g := π j)).op (x (π j) (ofArrows.mk _))

theorem isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor F ↔
    ∀ (x : FamilyOfElements' X F), x.PullbackCompatible X π F → ∃! t, x.IsAmalgamation X π F t := by
  refine ⟨?_, ?_⟩
  · intro h x' hx'
    have hh : ∀ Y (f : Y ⟶ B) (hf : (ofArrows X π) f), (∃ (i : I) (hi : X i = Y), eqToHom hi ≫ f  = π i) := by
      intro Y f hf
      cases' hf with i
      refine ⟨i, rfl, ?_⟩
      simp
    let x : FamilyOfElements F (ofArrows X π) := by
      intro Y f hf
      let i := (hh Y f hf).choose
      let hi := (hh Y f hf).choose_spec.choose
      rw [← hi]
      exact x' i
    specialize h x ?_
    · rw [pullbackCompatible_iff]
      intro Y₁ Y₂ f₁ f₂ hf₁ hf₂
      cases' hf₁ with i₁
      cases' hf₂ with i₂
      dsimp [FamilyOfElements'.PullbackCompatible] at hx'
      sorry
    · sorry
  · intro h x hx
    rw [pullbackCompatible_iff] at hx
    let x' : FamilyOfElements' X F := fun i ↦ x (π i) (ofArrows.mk _)
    specialize h x' (fun i j ↦ hx (ofArrows.mk _) (ofArrows.mk _))
    obtain ⟨t, hA, ht⟩ := h
    refine ⟨t, ?_, ?_⟩
    · intro Y f hf
      cases' hf with i
      exact hA i
    · intro y hy
      apply ht
      intro i
      exact hy (π i) (ofArrows.mk _)
