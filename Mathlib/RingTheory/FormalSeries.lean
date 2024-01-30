/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Set.Finite

/-!
# Abstract Formal Power Series
In this file we introduce formal power series as coefficient maps.  We use `structure` instead of
`abbrev`, because we will consider multiplication actions of polynomials and (under boundedness
conditions) other formal series using convolution.

We borrow from `MVPowerSeries`

## Definitions
* `FormalSeries`
## Main results
*
## To do:
* When exponent type is a product, compare with iterating FormalSeries construction
* Boundedness conditions? It looks like smul applied to linear maps to Hahn series is good enough.
* Residues (or more generally, taking the coefficient of one variable)
* Derivatives of Log series
* Hasse derivatives for exponents in a binomial ring.
## References
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118
-/

variable {Γ C : Type*} [DecidableEq Γ]

/-- The type of formal series with coefficients in `C` with exponents in `Γ`.
For example:
 * Formal Taylor series in one variable are obtained with `Γ = ℕ`.
 * Formal Taylor series in a set `X` of variables is obtained with
 `Γ = (∀ (x : X), ℤ)`.

See the type `MonomialType` for the standard way of constructing the appropriate `Γ`.
-/
@[ext] structure FormalSeries (Γ C) where
/-- The coefficient function of a formal series. -/
  coef : Γ → C

namespace FormalSeries

/-- The monomial formal series is a formal series with a single term with coefficient `c` at
index `e`. -/
@[simps]
def monomial [Zero C] (c : C) (e : Γ) : FormalSeries Γ C where
  coef m := if m = e then c else 0

/-- The constant formal series is a formal series with a single term with coefficient `c` at
index `0`. -/
@[simps!]
def const [One Γ] [Zero C] (c : C) : FormalSeries Γ C := monomial c 1

/-- The space of formal series has a zero element if the space of its coefficients has a zero. -/
@[simps]
instance instZero [Zero C] : Zero (FormalSeries Γ C) where
  zero := { coef := fun _ ↦ 0 }

/-- The space of formal series has an one element if the space of its coefficients has an one. -/
instance instOne [One C] [Zero C] [One Γ] : One (FormalSeries Γ C) where
  one := const 1

/-- The coefficients of the formal series 1 are zeroes unless the index is zero where the coefficient is one -/
lemma one_coef [One C] [Zero C] [One Γ] (m : Γ) :
  (1 : FormalSeries Γ C).coef m = if m = 1 then 1 else 0 := rfl

/-- The constant zero is equal to the zero series -/
@[simp] lemma const_zero [One Γ] [AddCommMonoid C] :
    (const 0 : FormalSeries Γ C) = 0 := by
  ext m
  simp only [const_coef, ite_self, instZero_zero_coef]

/-- The constant one is equal to the one series -/
lemma const_one [One Γ] [Zero C] [One C] :
    (const 1 : FormalSeries Γ C) = 1 := rfl

/-- The monomial with coefficient 1 at index 0 is equal to the one series -/
lemma monomial_one [One Γ] [Zero C] [One C] :
    (monomial 1 1 : FormalSeries Γ C) = 1 := rfl

/-- The monomial with zero coefficients at every index is equal to the zero series -/
@[simp] lemma monomial_zero [Zero C] (e : Γ) :
    (monomial 0 e : FormalSeries Γ C) = 0 := by
  ext m
  simp only [monomial_coef, ite_self, instZero_zero_coef]

/-- The space of formal series has addition if the space of its coefficients has addition. -/
@[simps]
instance instAdd [Add C] : Add (FormalSeries Γ C) where
  add := fun f₁ f₂ ↦ { coef := fun m ↦ f₁.coef m + f₂.coef m }

/-- The space of formal series has negation if the space of its coefficients has negation. -/
@[simps]
instance instNeg [Neg C] : Neg (FormalSeries Γ C) where
  neg := fun f ↦ { coef := fun p ↦ -f.coef p }

/-- The space of formal series has a scalar multiplication by a given type of scalars if the space
of its coefficients has a scalar multiplication by the same type of scalars. -/
@[simps]
instance instSmul {R V : Type*} [SMul R V] : SMul R (FormalSeries Γ V) where
  smul := fun r f ↦ { coef := fun p ↦ r • f.coef p }

/-- The space of formal series is an additive monoid if the space of its coefficients is an
additive monoid. -/
@[simps!]
instance [AddMonoid C] : AddMonoid (FormalSeries Γ C) where
  add_assoc f g h := by
    ext p
    simp only [instAdd_add_coef, add_assoc]
  zero_add f := by
    ext p
    simp only [instAdd_add_coef, instZero_zero_coef, zero_add]
  add_zero f := by
    ext p
    simp only [instAdd_add_coef, instZero_zero_coef, add_zero]

/-- The space of formal series is an additive commutative monoid if the space of its coefficients
is an additive commutative monoid. -/
instance [AddCommMonoid C] : AddCommMonoid (FormalSeries Γ C) where
  add_comm f g := by
    ext p
    simp only [instAdd_add_coef, add_comm]

/-- The space of formal series is an additive group if the space of its coefficients is an
additive group. -/
instance [AddGroup C] : AddGroup (FormalSeries Γ C) where
  add_left_neg f := by
    ext p
    simp only [instAdd_add_coef, instNeg_neg_coef, add_left_neg, instZero_zero_coef]

/-- The space of formal series is an additive commutative group if the space of its coefficients
is an additive commutative group. -/
instance [AddCommGroup C] : AddCommGroup (FormalSeries Γ C) where
  add_comm f g := by
    ext p
    simp only [instAdd_add_coef, add_comm]

/-- The space of formal series is an `R`-module for a semiring `R` if the space of its coefficients
is an `R`-module. -/
instance instModule {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    Module R (FormalSeries Γ V) where
  one_smul := by
    intro
    ext
    simp only [instSmul_smul_coef, one_smul]
  mul_smul := by
    intros
    ext
    simp only [instSmul_smul_coef, mul_smul]
  smul_zero := by
    intro
    ext
    simp only [instSmul_smul_coef, instZero_zero_coef, smul_zero]
  smul_add := by
    intros
    ext
    simp only [instSmul_smul_coef, instAdd_add_coef, smul_add]
  add_smul := by
    intros
    ext
    simp only [instSmul_smul_coef, instAdd_add_coef, add_smul]
  zero_smul := by
    intro
    ext
    simp only [instSmul_smul_coef, zero_smul, instZero_zero_coef]

section FiniteFiberAction

variable {G : Type*} [AddCommMonoid C]

/-- The primage of any element for any `G`-transformation is finite. -/
def isFiniteFibered (G : Type*) (Γ : Type*) [SMul G Γ] : Prop :=
  ∀(g : G) (m : Γ), Set.Finite {n : Γ | g • n = m}

/-- The formal series for a finite fibered convolution action.  The dependence on `h` means we don't
make it an instance. -/
noncomputable def FinFibSmul [SMul G Γ] (h : isFiniteFibered G Γ) : SMul G (
    FormalSeries Γ C) where
  smul := fun g f => {
  coef := fun m => Finset.sum (Set.Finite.toFinset (h g m)) fun n => coef f n
  }

/-!
noncomputable def FinFibMulAction [Monoid G] [MulAction G Γ] (h : isFiniteFibered G Γ) :
    haveI : SMul G (FormalSeries Γ C) := FinFibSmul h
    MulAction G (FormalSeries Γ C) where
  smul := (FinFibSmul h).smul
  one_smul := by
    intro
    ext
    unfold coef HSMul.hSMul instHSMul SMul.smul FinFibSmul
    simp only [one_smul, Set.setOf_eq_eq_singleton, Set.toFinite_toFinset, Set.toFinset_singleton,
      Finset.sum_singleton]
  mul_smul := by
    intros g k f
    ext m
    unfold coef HSMul.hSMul instHSMul SMul.smul FinFibSmul
    simp only
    have h' : ∀ i ∈ (Set.Finite.toFinset (h (g * k) m)),
        (fun x => k • x) i ∈ (Set.Finite.toFinset (h g m)) := by
      intros n hn
      simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, smul_smul]
    refine (Finset.sum_fiberwise_of_maps_to' h' (fun x => h • x)).symm -- needs massaging
    sorry
-/

/-- The formal series for a finite fibered convolution action of a monoid ring.  The dependence on
the finite fibered hypothesis means we don't make it an instance. The `m`-th coeff is the sum over
`{(g, n) | g • n = m}` of `x(g) • coef f(n)`. -/
noncomputable def FinFibMonoidAlgSmul (R : Type*) [Semiring R] [SMul G Γ]
   [SMul R C] (h : isFiniteFibered G Γ) : SMul (MonoidAlgebra R G) (FormalSeries Γ C) where
  smul x f := {
    coef := fun m => x.sum (fun g _ => Finset.sum (Set.Finite.toFinset (h g m))
    fun n => (x g) • f.coef n)
  }

/-!
noncomputable def FinFibMonoidAlgModule (R : Type*) [Semiring R] [Monoid G] [SMul G Γ]
   [SMul R C] (h : isFiniteFibered G Γ) : Module (MonoidAlgebra R G) (FormalSeries Γ C) where
  smul := (FinFibMonoidAlgSmul R h).smul
  one_smul := by

    sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

-- action of rational functions when an expansion is chosen.

-/
end FiniteFiberAction

end FormalSeries
