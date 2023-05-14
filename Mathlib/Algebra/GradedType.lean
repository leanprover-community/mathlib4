import Mathlib.Algebra.Group.Defs

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
