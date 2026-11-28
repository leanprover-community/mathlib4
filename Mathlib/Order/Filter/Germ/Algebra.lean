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
multiplication is the existing one on germs, acting pointwise on representatives. The algebra map
sends a scalar to the germ of the corresponding constant function; this choice ensures that the
instance agrees definitionally with `Semiring.toNatAlgebra` and `Ring.toIntAlgebra`.
-/
instance instAlgebra : Algebra R (Germ l A) where
  algebraMap := (coeRingHom l).comp (algebraMap R (α → A))
  commutes' r x := inductionOn x fun f ↦ congrArg ofFun (Algebra.commutes r f)
  smul_def' r x := inductionOn x fun f ↦ congrArg ofFun (Algebra.smul_def r f)

/--
The image of a scalar `r` in the algebra of germs is the germ of the constant function with value
`algebraMap R A r`.
-/
theorem algebraMap_apply (r : R) :
    algebraMap R (Germ l A) r = ((algebraMap R (α → A) r : α → A) : Germ l A) :=
  rfl

variable (R l) in
/-- The algebra homomorphism mapping a function to its germ. -/
def coeAlgHom : (α → A) →ₐ[R] Germ l A where
  __ := coeRingHom l
  commutes' _ := rfl

/-- As a function, `Filter.Germ.coeAlgHom` is the map sending a function to its germ. -/
@[simp]
theorem coe_coeAlgHom : (coeAlgHom R l : (α → A) → Germ l A) = ofFun := rfl

end Filter.Germ
