import Mathlib.RingTheory.Smooth.StandardSmooth

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is standard-smooth, if `B` is a standard-smooth `A`-algebra. -/
def IsStandardSmooth (f : A →+* B) : Prop :=
  @Algebra.IsStandardSmooth.{0, 0} A _ B _ f.toAlgebra

/-- A ring morphism `A →+* B` is standard-smooth, if `B` is a standard-smooth `A`-algebra. -/
def IsStandardSmoothOfRelativeDimension (n : ℕ) (f : A →+* B) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension.{0, 0} A _ B _ f.toAlgebra n

namespace IsStandardSmooth

lemma comp (g : B →+* C) (f : A →+* B) (hg : g.IsStandardSmooth) (hf : f.IsStandardSmooth) :
    IsStandardSmooth (g.comp f) := by
  rw [IsStandardSmooth]
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsStandardSmooth.{0, 0} A B := hf
  letI : Algebra.IsStandardSmooth.{0, 0} B C := hg
  sorry
  --apply Algebra.IsStandardSmooth.trans (R := A) (S := B) (T := C)

section Localization

variable {Aᵣ Bᵣ : Type*} [CommRing Aᵣ] [CommRing Bᵣ] [Algebra A Aᵣ] [Algebra B Bᵣ]
variable (f : A →+* B)
variable (r : A) [IsLocalization.Away r Aᵣ] [IsLocalization.Away (f r) Bᵣ]

lemma isLocalizationAway_map (hf : f.IsStandardSmooth) :
    (IsLocalization.Away.map Aᵣ Bᵣ f r).IsStandardSmooth := sorry

end Localization

end IsStandardSmooth

end RingHom
