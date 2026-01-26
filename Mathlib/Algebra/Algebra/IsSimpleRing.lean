import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# Facts about algebras when the coefficient ring is a simple ring
-/

@[expose] public section

variable (R A : Type*) [CommRing R] [Semiring A] [Algebra R A] [IsSimpleRing R] [Nontrivial A]

instance : FaithfulSMul R A :=
  faithfulSMul_iff_algebraMap_injective R A |>.2 <| RingHom.injective _
