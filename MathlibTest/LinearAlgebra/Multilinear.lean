module

import Mathlib.LinearAlgebra.Multilinear.Basic

variable {ι R M' N : Type*} {M : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)]
  [AddCommMonoid M'] [AddCommMonoid N] [∀ i, Module R (M i)] [Module R M'] [Module R N]

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

abbrev piM := Π i, M i

variable (h : piM (M := M) →ₘₗ[R] N)
/--
info: h : (Π (i : ι), M i) →ₘₗ[R] N
-/
#guard_msgs in
#check h
