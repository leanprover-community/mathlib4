import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace CategoryTheory

namespace Quotient

variable {C : Type _} [Category C] [Preadditive C] (r : HomRel C) [Congruence r]
  (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))

namespace Preadditive

def add {X Y : Quotient r} (f g : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn₂ f g (fun a b => Quot.mk _ (a + b))
    (fun f g₁ g₂ h₁₂ => by
      simp only [compClosure_eq_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ (Congruence.isEquiv.refl f) h₁₂)
    (fun f₁ f₂ g h₁₂ => by
      simp only [compClosure_eq_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ h₁₂ (Congruence.isEquiv.refl g))

def neg {X Y : Quotient r} (f : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn f (fun a => Quot.mk _ (-a))
    (fun f g => by
      intro hfg
      simp only [compClosure_eq_self] at hfg
      erw [functor_map_eq_iff]
      apply Congruence.isEquiv.symm
      convert hr f g _ _ hfg (Congruence.isEquiv.refl (-f-g)) using 1 <;> abel)

end Preadditive

def preadditive : Preadditive (Quotient r) where
  homGroup P Q :=
    { add := Preadditive.add r hr
      add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ; exact congr_arg (functor r).map (add_assoc _ _ _)
      zero := Quot.mk _ 0
      zero_add := by rintro ⟨_⟩ ; exact congr_arg (functor r).map (zero_add _)
      add_zero := by rintro ⟨_⟩ ; exact congr_arg (functor r).map (add_zero _)
      add_comm := by rintro ⟨_⟩ ⟨_⟩ ; exact congr_arg (functor r).map (add_comm _ _)
      neg := Preadditive.neg r hr
      add_left_neg := by rintro ⟨_⟩ ; exact congr_arg (functor r).map (add_left_neg _) }
  add_comp := by
    rintro _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact congr_arg (functor r).map (Preadditive.add_comp _ _ _ _ _ _ )
  comp_add := by
    rintro _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact congr_arg (functor r).map (Preadditive.comp_add _ _ _ _ _ _ )

lemma functor_additive : @Functor.Additive _ _ _ _ _ (preadditive r hr) (functor r) :=
  letI := preadditive r hr
  { map_add := rfl }

end Quotient

end CategoryTheory
