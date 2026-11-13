module

import Mathlib.LinearAlgebra.Multilinear.Basic

variable {ι R S M' N : Type*} {M : ι → Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid N]
  [∀ i, Module R (M i)] [Module R M'] [Module R N] [Module S N]

abbrev piM := Π i, M i

section Multilinear

variable (f : (Π i, M i) →ₘₗ[R] N)
/--
info: f : (Π (i : ι), M i) →ₘₗ[R] N
-/
#guard_msgs in
#check f

variable (g : (ι → M') →ₘₗ[R] N)
/--
info: g : (ι → M') →ₘₗ[R] N
-/
#guard_msgs in
#check g

variable (h : piM (M := M) →ₘₗ[R] N)
/--
info: h : (Π (i : ι), M i) →ₘₗ[R] N
-/
#guard_msgs in
#check h

end Multilinear

section MultiSemilinear

variable (f : (Π i, M i) →ₘₛₗ[σ] N)
/--
info: f : (Π (i : ι), M i) →ₘₛₗ[σ] N
-/
#guard_msgs in
#check f

variable (g : (ι → M') →ₘₛₗ[σ] N)
/--
info: g : (ι → M') →ₘₛₗ[σ] N
-/
#guard_msgs in
#check g

variable (h : piM (M := M) →ₘₛₗ[σ] N)
/--
info: h : (Π (i : ι), M i) →ₘₛₗ[σ] N
-/
#guard_msgs in
#check h

end MultiSemilinear
