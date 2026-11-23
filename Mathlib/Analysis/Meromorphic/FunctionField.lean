/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Order.Filter.Germ.Algebra
public import Mathlib.Topology.Perfect

/-!
# The Field of Meromorphic Functions on a Connected Set

Functions meromorphic on a set `U` with values in a normed field `𝕜'` form a subalgebra
`MeromorphicOn.subalgebra 𝕜 𝕜' U` of the algebra of all functions `𝕜 → 𝕜'`. This algebra is
never a field: functions supported on discrete sets are zero divisors. Classically, meromorphic
functions that agree outside a discrete set are identified. We realize this identification by
passing to germs along the filter `Filter.codiscreteWithin U`: the image of the subalgebra in the
algebra of germs is the ring `MeromorphicOn.functionRing 𝕜 𝕜' U` of meromorphic functions on `U`.
It carries a natural pointwise inverse, and if `U` is preconnected with at least two points, it is a
field, with instance `MeromorphicOn.FunctionRing.instField` available under `Fact` assumptions on
`U`.

The key input is the identity theorem for meromorphic functions, in the form of
`MeromorphicOn.mul_inv_eventuallyEq`: on a preconnected set, a meromorphic function `f` that does
not vanish along `codiscreteWithin U` satisfies `f * f⁻¹ =ᶠ[codiscreteWithin U] 1`, so that the
pointwise inverse is a genuine inverse.
-/

@[expose] public section

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {U : Set 𝕜} {f : 𝕜 → 𝕜'}

namespace MeromorphicOn

/-!
## The Algebra of Meromorphic Functions
-/

variable (𝕜 𝕜' U) in
/-- Functions meromorphic on `U`, as a subalgebra of the algebra of all functions `𝕜 → 𝕜'`. -/
def subalgebra : Subalgebra 𝕜 (𝕜 → 𝕜') where
  carrier := {f | MeromorphicOn f U}
  zero_mem' := const 0
  one_mem' := const 1
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  algebraMap_mem' c := const (algebraMap 𝕜 𝕜' c)

@[simp]
theorem mem_subalgebra_iff : f ∈ subalgebra 𝕜 𝕜' U ↔ MeromorphicOn f U := Iff.rfl

/-!
## The Ring of Meromorphic Functions Modulo Equality Along `codiscreteWithin U`
-/

variable (𝕜 𝕜' U) in
/--
The ring of meromorphic functions on `U`: functions meromorphic on `U`, modulo equality along the
filter `codiscreteWithin U`, realized as a subalgebra of the algebra of germs along that filter. If
`U` is preconnected with at least two points, this algebra is a field, see
`MeromorphicOn.FunctionRing.instField`.
-/
def functionRing : Subalgebra 𝕜 (Germ (codiscreteWithin U) 𝕜') :=
  (subalgebra 𝕜 𝕜' U).map (Germ.coeAlgHom 𝕜 _)

/-- Membership in `functionRing 𝕜 𝕜' U` means: the germ has a meromorphic representative. -/
theorem mem_functionRing_iff {γ : Germ (codiscreteWithin U) 𝕜'} :
    γ ∈ functionRing 𝕜 𝕜' U ↔
      ∃ f : 𝕜 → 𝕜', MeromorphicOn f U ∧ (f : Germ (codiscreteWithin U) 𝕜') = γ :=
  Subalgebra.mem_map

/-- The germ of a meromorphic function lies in `functionRing 𝕜 𝕜' U`. -/
theorem coe_mem_functionRing (hf : MeromorphicOn f U) :
    (f : Germ (codiscreteWithin U) 𝕜') ∈ functionRing 𝕜 𝕜' U :=
  mem_functionRing_iff.2 ⟨f, hf, rfl⟩

/--
The surjective algebra homomorphism mapping a meromorphic function to the element of
`functionRing 𝕜 𝕜' U` that it represents.
-/
def toFunctionRingAlgHom : subalgebra 𝕜 𝕜' U →ₐ[𝕜] functionRing 𝕜 𝕜' U :=
  ((Germ.coeAlgHom 𝕜 _).comp (subalgebra 𝕜 𝕜' U).val).codRestrict _
    fun f ↦ coe_mem_functionRing f.property

theorem toFunctionRingAlgHom_surjective :
    Function.Surjective (toFunctionRingAlgHom (𝕜 := 𝕜) (𝕜' := 𝕜') (U := U)) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨f, hf, rfl⟩ := mem_functionRing_iff.1 hγ
  exact ⟨⟨f, hf⟩, rfl⟩

namespace FunctionRing

/-!
### Inverses in the Ring of Meromorphic Functions Modulo Equality Along `codiscreteWithin U`

The ring of meromorphic functions modulo equality along the filter `codiscreteWithin U` inherits the
pointwise inverse of germs, using the junk-value convention `(0 : 𝕜')⁻¹ = 0`: the inverse of a
function meromorphic on `U` is meromorphic on `U`, so the subalgebra is closed under `Inv` without
any hypotheses on `U`.
-/

noncomputable instance : Inv (functionRing 𝕜 𝕜' U) where
  inv a := ⟨(a : Germ (codiscreteWithin U) 𝕜')⁻¹, by
    obtain ⟨f, hf, hfa⟩ := mem_functionRing_iff.1 a.property
    exact mem_functionRing_iff.2 ⟨f⁻¹, hf.inv, by rw [Germ.coe_inv, hfa]⟩⟩

@[simp, norm_cast]
theorem coe_inv (a : functionRing 𝕜 𝕜' U) :
    ((a⁻¹ : functionRing 𝕜 𝕜' U) : Germ (codiscreteWithin U) 𝕜') =
      (a : Germ (codiscreteWithin U) 𝕜')⁻¹ := rfl

noncomputable instance : Div (functionRing 𝕜 𝕜' U) where
  div a b := a * b⁻¹

protected theorem div_eq_mul_inv (a b : functionRing 𝕜 𝕜' U) : a / b = a * b⁻¹ := rfl

@[simp, norm_cast]
theorem coe_div (a b : functionRing 𝕜 𝕜' U) :
    ((a / b : functionRing 𝕜 𝕜' U) : Germ (codiscreteWithin U) 𝕜') =
      (a : Germ (codiscreteWithin U) 𝕜') / (b : Germ (codiscreteWithin U) 𝕜') :=
  (div_eq_mul_inv _ _).symm

protected theorem inv_zero : (0 : functionRing 𝕜 𝕜' U)⁻¹ = 0 :=
  Subtype.ext (congrArg Germ.ofFun (funext fun _ ↦ inv_zero))

/-!
### Nontriviality and the Field Structure
-/

/--
The ring of meromorphic functions modulo equality along `codiscreteWithin U` is nontrivial whenever
`codiscreteWithin U` is nontrivial.
-/
theorem nontrivial (h : (codiscreteWithin U).NeBot) : Nontrivial (functionRing 𝕜 𝕜' U) :=
  ⟨0, 1, fun hcon ↦ zero_ne_one (α := 𝕜') (Germ.const_inj.1 (congrArg Subtype.val hcon))⟩

instance [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Nontrivial (functionRing 𝕜 𝕜' U) :=
  nontrivial (h₁U.out.codiscreteWithin_neBot h₂U.out)

/--
On a preconnected set, every nonzero element of `functionRing 𝕜 𝕜' U` is invertible, with the
pointwise inverse as its inverse.
-/
protected theorem mul_inv_cancel (hU : IsPreconnected U) {a : functionRing 𝕜 𝕜' U} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  obtain ⟨f, hf, hfa⟩ := mem_functionRing_iff.1 a.property
  have h0 : ¬ f =ᶠ[codiscreteWithin U] 0 := fun h ↦ ha (Subtype.ext (hfa ▸ Germ.coe_eq.2 h))
  apply Subtype.ext
  push_cast
  rw [← hfa, ← Germ.coe_inv, ← Germ.coe_mul]
  exact Germ.coe_eq.2 (hf.mul_inv_eventuallyEq hU h0)

/-- On a preconnected set `U` with at least two points, `functionRing 𝕜 𝕜' U` is a field. -/
theorem isField (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsField (functionRing 𝕜 𝕜' U) where
  exists_pair_ne := (nontrivial (h₁U.codiscreteWithin_neBot h₂U)).exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel ha := ⟨_, FunctionRing.mul_inv_cancel h₁U ha⟩

/--
The field of meromorphic functions on a preconnected set with at least two points: field instance
for the ring of meromorphic functions, with the pointwise inverse.
-/
noncomputable instance instField [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Field (functionRing 𝕜 𝕜' U) where
  __ := (inferInstance : CommRing (functionRing 𝕜 𝕜' U))
  inv := Inv.inv
  div := Div.div
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne _
  mul_inv_cancel _ ha := FunctionRing.mul_inv_cancel h₁U.out ha
  inv_zero := FunctionRing.inv_zero
  nnqsmul := _
  qsmul := _

/--
On a preconnected set with at least two points, the ring of meromorphic functions is a domain.
-/
theorem isDomain (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsDomain (functionRing 𝕜 𝕜' U) :=
  (isField h₁U h₂U).isDomain

end FunctionRing

end MeromorphicOn
