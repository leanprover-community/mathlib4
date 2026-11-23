/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Germs of Algebra-Valued Functions

Let `l` be a filter on a type `α`. Two functions `α → A` have the same germ along `l` if they agree
eventually along `l`; for example, if `l` is the neighborhood filter of a point, germs are germs in
the usual sense. If `A` is an `R`-algebra, then the ring of germs `Germ l A` is an `R`-algebra, and
the map sending a function to its germ is an algebra homomorphism `Filter.Germ.coeAlgHom`.
-/

@[expose] public section

namespace Filter.Germ

variable {α R A : Type*} {l : Filter α} [CommSemiring R] [Semiring A] [Algebra R A]

/--
If `A` is an `R`-algebra, then germs of `A`-valued functions form an `R`-algebra. The scalar
multiplication is the existing one on germs, acting pointwise on representatives.
-/
instance instAlgebra : Algebra R (Germ l A) :=
  Algebra.ofModule
    (fun r x y ↦ inductionOn₂ x y fun f g ↦ congrArg ofFun (smul_mul_assoc r f g))
    (fun r x y ↦ inductionOn₂ x y fun f g ↦ congrArg ofFun (mul_smul_comm r f g))

/--
The image of a scalar `r` in the algebra of germs is the germ of the constant function with value
`algebraMap R A r`.
-/
theorem algebraMap_apply (r : R) :
    algebraMap R (Germ l A) r = ((algebraMap R (α → A) r : α → A) : Germ l A) :=
  congrArg ofFun (Algebra.algebraMap_eq_smul_one r).symm

variable (R l) in
/-- The algebra homomorphism mapping a function to its germ. -/
def coeAlgHom : (α → A) →ₐ[R] Germ l A where
  __ := coeRingHom l
  commutes' r := (algebraMap_apply r).symm

/-- As a function, `Filter.Germ.coeAlgHom` is the map sending a function to its germ. -/
@[simp]
theorem coe_coeAlgHom : (coeAlgHom R l : (α → A) → Germ l A) = ofFun := rfl

end Filter.Germ
