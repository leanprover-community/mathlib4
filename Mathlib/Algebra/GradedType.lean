import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory Category Limits

universe u

abbrev GradedType (M : Type _) := M → Type u

variable {M}

class HasGradedHSMul [Add M] (X Y : GradedType M) (Z : outParam (GradedType M)) where
  γhsmul' (a b c : M) (h : a + b = c) (α : X a) (β : Y b) : Z c

def HasGradedHSMul.γhsmul [Add M] {X Y : GradedType M} {Z : outParam (GradedType M)}
    [HasGradedHSMul X Y Z] {a b : M} (α : X a) (β : Y b) {c : M} (h : a + b = c) : Z c :=
  @HasGradedHSMul.γhsmul' M _ X Y Z _ a b c h α β

notation a " •[" b "] " c:80 => HasGradedHSMul.γhsmul a c b

variable [AddMonoid M] (X Y Z : GradedType M) (XY YZ XYZ : outParam (GradedType M))
  [HasGradedHSMul X Y XY] [HasGradedHSMul Y Z YZ]
  [HasGradedHSMul X YZ XYZ] [HasGradedHSMul XY Z XYZ]

class IsAssocGradedHSMul where
  γhsmul_assoc : ∀ ⦃a b c : M⦄ (α : X a) (β : Y b) (γ : Z c) (ab bc abc : M)
    (hab : a + b = ab) (hbc : b + c = bc) (habc : ab + c = abc),
      (α •[hab] β) •[habc] γ =
        α •[show a + bc = abc by rw [← hbc, ← add_assoc, hab, habc]] (β •[hbc] γ)

@[simp]
lemma γhsmul_assoc_of_third_degree_eq_zero
    [IsAssocGradedHSMul X Y Z XY YZ XYZ]
    {a b : M} (α : X a) (β : Y b) (γ : Z 0) (ab : M) (hab : a + b = ab) :
  (α •[hab] β) •[add_zero _] γ = α •[hab] β •[add_zero _] γ := by
  apply IsAssocGradedHSMul.γhsmul_assoc

variable {X Y Z}

namespace CochainComplex

open HomComplex

variable {C : Type _} [Category C] [Preadditive C] (K L M N : CochainComplex C ℤ)

instance : HasGradedHSMul (Cochain K L) (Cochain L M) (Cochain K M) where
  γhsmul' _ _ _ h α β := α.comp β h

instance : One (Cochain K K 0) := ⟨Cochain.ofHom (𝟙 K)⟩

instance : IsAssocGradedHSMul (Cochain K L) (Cochain L M) (Cochain M N) (Cochain K M)
    (Cochain L N) (Cochain K N) where
  γhsmul_assoc a b c α β γ ab bc abc hab hbc habc :=
    Cochain.comp_assoc _ _ _ hab hbc (by linarith)

example {n : ℤ} (α : Cochain K L n) :
    (1 : Cochain K K 0) •[zero_add n] α = α := Cochain.id_comp α

example {a b c : ℤ} (α : Cochain K L a) (β : Cochain L M b) (γ : Cochain M N c) :
    (α •[rfl] β) •[rfl] γ = α •[(add_assoc a b c).symm] (β •[rfl] γ) :=
  by apply IsAssocGradedHSMul.γhsmul_assoc

example {a b : ℤ} (α : Cochain K L a) (β : Cochain L M b) (γ : Cochain M N 0) :
    (α •[rfl] β) •[add_zero _] γ = α •[rfl] (β •[add_zero _] γ) := by simp


end CochainComplex
