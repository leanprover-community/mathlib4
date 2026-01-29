/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Finsupp.Supported

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Module structure on monoid algebras

## Main results

* `MonoidAlgebra.module`, `AddMonoidAlgebra.module`: lift a module structure to monoid algebras

## Implementation notes

We do not state the equivalent of `DistribMulAction M (MonoidAlgebra S M)` for `AddMonoidAlgebra`
because mathlib does not have the notion of distributive actions of additive groups.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single
open Module

variable {R S M N G : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

section SMul

section DistribMulAction
variable [Monoid S] [Semiring R] [DistribMulAction S R]

@[to_additive (dont_translate := S) (relevant_arg := M) distribMulAction]
instance distribMulAction : DistribMulAction S R[M] := coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (relevant_arg := M) (attr := simp)]
lemma mapDomain_smul (f : M → N) (s : S) (x : R[M]) : mapDomain f (s • x) = s • mapDomain f x := by
  ext; simp [Finsupp.mapDomain_smul]

end DistribMulAction

@[to_additive (dont_translate := R)]
instance instIsTorsionFree [Semiring R] [Semiring k] [Module R k] [Module.IsTorsionFree R k] :
    Module.IsTorsionFree R (MonoidAlgebra k G) := Finsupp.moduleIsTorsionFree

@[to_additive (dont_translate := R) faithfulSMul]
instance faithfulSMul [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M] :
    FaithfulSMul R S[M] :=
  coeffEquiv.faithfulSMul _

section Module
variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

@[to_additive (dont_translate := R) (relevant_arg := M)]
instance module : Module R S[M] := coeffEquiv.module _

variable (R) in
/-- `MonoidAlgebra.coeff` as a linear equiv. -/
@[to_additive (relevant_arg := M) (attr := simps! apply symm_apply)
/-- `MonoidAlgebra.coeff` as a linear equiv. -/]
def coeffLinearEquiv [Semiring R] [Semiring S] [Module R S] : S[M] ≃ₗ[R] M →₀ S :=
  coeffEquiv.linearEquiv _

variable (R S s) in
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/
@[to_additive (relevant_arg := M)
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/]
def supported : Submodule R S[M] := (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap

@[to_additive] lemma mem_supported : x ∈ supported R S s ↔ ↑x.coeff.support ⊆ s := .rfl

@[to_additive]
lemma mem_supported' : x ∈ supported R S s ↔ ∀ m ∉ s, x.coeff m = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

variable (R S s) in
@[to_additive (relevant_arg := M)]
lemma supported_eq_map :
    supported R S s = (Finsupp.supported S R s).map (coeffLinearEquiv R).symm.toLinearMap :=
  Submodule.comap_equiv_eq_map_symm ..

variable (R S s) in
@[to_additive (dont_translate := R) (relevant_arg := M)]
lemma supported_eq_span_single : supported R R s = .span R ((fun m ↦ single m 1) '' s) := by
  simp [supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp]

@[to_additive (attr := gcongr)]
lemma supported_mono (hst : s ⊆ t) : supported R S s ≤ supported R S t := fun _ h ↦ h.trans hst

/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
@[to_additive (dont_translate := R) (attr := simps!)
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/]
def supportedEquivFinsupp (s : Set M) : supported R S s ≃ₗ[R] s →₀ S :=
  { toFun x := ⟨x.1.coeff, x.2⟩
    invFun x := ⟨.ofCoeff x.1, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
   ≪≫ₗ Finsupp.supportedEquivFinsupp s

end Module

/-- This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` when `M = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ S[M]` and then it can be an instance.
TODO: Generalise to a group acting on another, instead of just the left multiplication action.
-/
def comapDistribMulActionSelf [Group G] [Semiring S] : DistribMulAction G S[G] :=
  have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  coeffEquiv.distribMulAction _

@[to_additive (dont_translate := R)]
lemma single_mem_span_single [Semiring R] [Nontrivial R] {m : M} {s : Set M} :
    single m 1 ∈ Submodule.span R ((single · (1 : R)) '' s) ↔ m ∈ s := by
  refine (Set.mem_image_equiv (f := (coeffLinearEquiv R).toEquiv)).symm.trans ?_
  change _ ∈ (Submodule.span R _).map (coeffLinearEquiv R).toLinearMap ↔ _
  simp [Submodule.map_span, ← Set.image_comp, Finsupp.single_mem_span_single]

end SMul

/-! #### Copies of `ext` lemmas and bundled `single`s from `Finsupp` -/

section ExtLemmas
variable [Semiring S]

/-- `MonoidAlgebra.single` as a `DistribMulActionHom`. -/
@[to_additive (dont_translate := R) (relevant_arg := M) singleDistribMulActionHom
/-- `AddMonoidAlgebra.single` as a `DistribMulActionHom`. -/]
def singleDistribMulActionHom [Monoid R] [DistribMulAction R S] (a : M) : S →+[R] S[M] where
  __ := singleAddHom a
  map_smul' S m := by simp

/-- A copy of `Finsupp.distribMulActionHom_ext'` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := N) (attr := ext) distribMulActionHom_ext'
/-- A copy of `Finsupp.distribMulActionHom_ext'` for `AddMonoidAlgebra`. -/]
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R S] {f g : S[M] →+[R] N}
    (h : ∀ a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) :
    f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(h a) x)

/-- A copy of `Finsupp.lsingle` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (relevant_arg := M)
/-- A copy of `Finsupp.lsingle` for `AddMonoidAlgebra`. -/]
def lsingle [Semiring R] [Module R S] (a : M) : S →ₗ[R] S[M] :=
  (coeffLinearEquiv _).symm.toLinearMap.comp <| Finsupp.lsingle a

@[to_additive (attr := simp)]
lemma lsingle_apply [Semiring R] [Module R S] (a : M) (b : S) :
    lsingle (R := R) a b = single a b :=
  rfl

/-- A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`. -/
@[to_additive (attr := ext high) (relevant_arg := M)]
lemma lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
    ⦃f g : S[M] →ₗ[R] N⦄
    (H : ∀ (x : M), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(H a) x)

end ExtLemmas

section MiscTheorems
variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

lemma smul_of (m : M) (r : R) : r • of R M m = single m r := by simp

/-- The image of an element `m : M` in `R[M]` belongs the submodule generated by
`s : Set M` if and only if `m ∈ s`. -/
lemma of_mem_span_of_iff [Nontrivial R] : of R M m ∈ Submodule.span R (of R M '' s) ↔ m ∈ s :=
  single_mem_span_single

/-- If the image of an element `m : M` in `R[M]` belongs the submodule generated by the
closure of some `s : Set M` then `m ∈ closure s`. -/
lemma mem_closure_of_mem_span_closure [Nontrivial R]
    (h : of R M m ∈ Submodule.span R (Submonoid.closure <| of R M '' s)) :
    m ∈ Submonoid.closure s := by
  rw [← MonoidHom.map_mclosure] at h; simpa using of_mem_span_of_iff.1 h

theorem liftNC_smul (f : S →+* R) (g : M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

end MiscTheorems

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (S) [Semiring S] [DistribSMul R S] [Mul M]

@[to_additive (dont_translate := R S) isScalarTower_self]
instance isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
  smul_assoc t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

/-- Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so we can take
`R = S` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
@[to_additive (dont_translate := R S) smulCommClass_self]
instance smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
  smul_comm t a b := by
    classical ext; simp [coeff_mul, coeff_smul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

@[to_additive (dont_translate := R S) smulCommClass_symm_self]
instance smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M] :=
  have := SMulCommClass.symm S R S; .symm ..

end NonUnitalNonAssocAlgebra

section Submodule

variable [CommSemiring S] [Monoid M]
variable {V : Type*} [AddCommMonoid V]
variable [Module S V] [Module S[M] V] [IsScalarTower S S[M] V]

/-- A submodule over `S` which is stable under scalar multiplication by elements of `M` is a
submodule over `S[M]` -/
def submoduleOfSMulMem (W : Submodule S V) (h : ∀ (g : M) (v : V), v ∈ W → of S M g • v ∈ W) :
    Submodule S[M] V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S]

/-- The image of an element `m : M` in `R[M]` belongs the submodule generated by
`s : Set M` if and only if `m ∈ s`. -/
lemma of'_mem_span [Nontrivial R] {m : M} {s : Set M} :
    of' R M m ∈ Submodule.span R (of' R M '' s) ↔ m ∈ s := single_mem_span_single

/-- If the image of an element `m : M` in `R[M]` belongs the submodule generated by
the closure of some `s : Set M` then `m ∈ closure s`. -/
lemma mem_closure_of_mem_span_closure [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
    (h : of' R M m ∈ Submodule.span R (Submonoid.closure <| of' R M '' s)) :
    m ∈ AddSubmonoid.closure s := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← h'] at h
  simpa using of'_mem_span.1 h

lemma liftNC_smul [AddZeroClass M] (f : S →+* R) (g : Multiplicative M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

end Semiring
end AddMonoidAlgebra
