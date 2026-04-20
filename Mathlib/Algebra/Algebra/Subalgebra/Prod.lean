/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Products of subalgebras

In this file we define the product of two subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.prod`: the product of two subalgebras.
-/

@[expose] public section


namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }

@[simp, norm_cast]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl

open Subalgebra in
theorem prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁) := rfl

@[simp]
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp

theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Subalgebra

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B. -/
abbrev pullback (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Subalgebra R (A × B) := equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] B :=
  (snd R A B).comp (pullback f g).val

theorem pullback_comm_sq (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  AlgHom.ext fun x ↦ x.prop

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem isUnit_pullback_mk_iff (f : A →ₐ[R] C) (g : B →ₐ[R] C) {a : A × B}
    (a_in : a ∈ f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔
      IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A →+* C) (g : B →+* C) a_in

theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h

theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h

end Ring

end AlgHom
