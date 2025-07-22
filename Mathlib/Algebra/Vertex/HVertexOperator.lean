/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Heterogeneous vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.

## Definitions
* `HVertexOperator`: An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* `HVertexOperator.coeff`: The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
* State-field maps

## Main results
* `HahnSeries Γ R`-module structure on `HVertexOperator Γ R V W`.  This means we can consider
  products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`, where `(X-Y)^n` is expanded as
  `X^n(1-Y/X)^n` in `R((X))((Y))`

## TODO
* equiv for order equivalences, maps for order embeddings
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials and `X` for multivariable
  polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

noncomputable section

variable {Γ Γ₁ Γ₂ R S U V W X Y : Type*}

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

variable [PartialOrder Γ] [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficients of a heterogeneous vertex operator, viewed as a linear map to formal power
series with coefficients in linear maps. -/
@[simps]
def coeff : HVertexOperator Γ R V W →ₗ[R] Γ → V →ₗ[R] W where
  toFun A n := {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W) (hf : ∀ x : V , (Function.support (f · x)).IsPWO) :
    HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.of_coeff := of_coeff

@[simp]
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ (x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

theorem coeff_smul (A : HVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  simp

theorem coeff_nsmul (A : HVertexOperator Γ R V W) {n : ℕ} : (n • A).coeff = n • (A.coeff) := by
  simp

end Coeff

section Module

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [PartialOrder Γ₁]
  [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

--#synth Module (HahnSeries Γ R) (HVertexOperator Γ₁ R V W) -- LinearMap.module

@[simp]
theorem smul_eq {x : HahnSeries Γ R} {A : HVertexOperator Γ₁ R V W} {v : V} :
    (x • A) v = x • (A v) :=
  rfl

@[simp]
theorem single_zero_smul_eq_smul {r : R} {A : HVertexOperator Γ₁ R V W} :
    (HahnSeries.single (0 : Γ)) r • A = r • A := by
  ext
  simp

@[simp]
theorem coeff_single_smul_vadd {A : HVertexOperator Γ₁ R V W} (g : Γ) (g₁ : Γ₁) (r : R) :
    coeff ((HahnSeries.single g) r • A) (g +ᵥ g₁) = r • coeff A g₁ := by
  ext v
  rw [coeff_apply_apply, smul_eq, HahnModule.coeff_single_smul_vadd, LinearMap.smul_apply,
    coeff_apply_apply]

theorem coeff_single_smul {Γ} [PartialOrder Γ] [AddCommGroup Γ] [IsOrderedCancelAddMonoid Γ]
    [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] {A : HVertexOperator Γ₁ R V W} (g : Γ) (g₁ : Γ₁)
    (r : R) :
    coeff ((HahnSeries.single g) r • A) g₁ = r • coeff A (-g +ᵥ g₁) := by
  have : g₁ = g +ᵥ (-g +ᵥ g₁) := neg_vadd_eq_iff.mp rfl
  nth_rw 1 [this]
  exact coeff_single_smul_vadd (A := A) (V := V) (W := W) g (-g +ᵥ g₁) r

section arrowCongrLeft

--variable [AddCommMonoid Γ] [AddAction Γ Γ₁] [AddAction Γ Γ₂]

theorem arrowCongrLeft_coeff_apply {f : Γ₁ ↪ Γ₂} {A : HVertexOperator Γ₁ R V W} {a : Γ₁} :
    (f.arrowCongrLeft A.coeff) (f a) = A.coeff a := by
  simp

theorem arrowCongrLeft_coeff_notin_range {f : Γ₁ ↪ Γ₂} {A : HVertexOperator Γ₁ R V W}
    {b : Γ₂} (hb : b ∉ Set.range f) :
    (f.arrowCongrLeft A.coeff) b = 0 :=
  dif_neg hb

theorem support_arrowCongrLeft_subset {f : Γ₁ ↪ Γ₂} {A : HVertexOperator Γ₁ R V W} :
    (f.arrowCongrLeft A.coeff).support ⊆ Set.range f := by
  intro g hg
  contrapose! hg
  simp [arrowCongrLeft_coeff_notin_range hg]

omit [PartialOrder Γ₁] in
@[simp]
theorem arrowCongrLeft_zero {f : Γ₁ ↪ Γ₂} :
    f.arrowCongrLeft (0 : Γ₁ → (V →ₗ[R] W)) = 0 := by
  ext1 g
  by_cases h : g ∈ f '' Set.univ <;> simp [Function.Embedding.arrowCongrLeft, Function.extend]

theorem support_arrowCongrLeft_coeff_injective {f : Γ₁ ↪ Γ₂} :
    Function.Injective fun (A : HVertexOperator Γ₁ R V W) ↦ (f.arrowCongrLeft A.coeff) := by
  intro A B h
  ext v g
  simp only [funext_iff] at h
  have h₁ := h (f g)
  simp only [Function.Embedding.arrowCongrLeft_apply] at h₁
  rw [← coeff_apply_apply, h₁, coeff_apply_apply]

theorem arrowCongrLeft_comp {Γ₃ : Type*} {f : Γ₁ ↪ Γ₂} {f' : Γ₂ ↪ Γ₃}
    (A : HVertexOperator Γ₁ R V W) :
    (f'.arrowCongrLeft) (f.arrowCongrLeft A.coeff) = (f.trans f').arrowCongrLeft A.coeff := by
  simp

/-!
Need:
 * transport smul of finsupps along monoidHom embeddings
 * abstract composition along independent embeddings, show they agree with joint embedding
 * commutator (in VertexOperator file)

-/


end arrowCongrLeft

section equivDomain

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- An isomorphism of heterogeneous vertex operator spaces induced by ordered isomorphisms. -/
@[simps]
def equivDomain [PartialOrder Γ₂] (f : Γ ≃o Γ₂) :
    HVertexOperator Γ R V W ≃ₗ[R] HVertexOperator Γ₂ R V W where
  toFun A := {
    toFun v := (HahnModule.of R) (HahnSeries.equivDomain f ((HahnModule.of R).symm (A v)))
    map_add' _ _ := by ext; simp
    map_smul' r x := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun A := {
    toFun v := (HahnModule.of R) (HahnSeries.equivDomain f.symm ((HahnModule.of R).symm (A v)))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- An isomorphism of heterogeneous vertex operator spaces induced by reversing lex order. -/
def lexRevEquivBase (Γ Γ₂) [PartialOrder Γ] [PartialOrder Γ₂] :
    HVertexOperator (Γ ×ₗ Γ₂) R V W ≃ₗ[R] HVertexOperator (Γ₂ ×ᵣ Γ) R V W :=
  equivDomain (Prod.RevLex.lexEquiv Γ Γ₂)

theorem lexRevEquivBase_apply_apply_coeff (Γ Γ₂) [PartialOrder Γ] [PartialOrder Γ₂]
    (A : HVertexOperator (Lex (Γ × Γ₂)) R V W) (v : V) (g : RevLex (Γ₂ × Γ)) :
    ((lexRevEquivBase Γ Γ₂ A) v).coeff g =
      ((HahnModule.of R).symm (A v)).coeff ((Prod.RevLex.lexEquiv Γ Γ₂).symm g) :=
  rfl

theorem lexRevEquivBase_symm_apply_apply_coeff (Γ Γ₂) [PartialOrder Γ] [PartialOrder Γ₂]
    (A : HVertexOperator (RevLex (Γ₂ × Γ)) R V W) (v : V) (g : Lex (Γ × Γ₂)) :
    (((lexRevEquivBase Γ Γ₂).symm A) v).coeff g =
      ((HahnModule.of R).symm (A v)).coeff ((Prod.RevLex.lexEquiv Γ Γ₂) g) :=
  rfl

variable {Γ' Γ₁' F : Type*} [PartialOrder Γ'] [AddCommMonoid Γ'] [IsOrderedCancelAddMonoid Γ']
[PartialOrder Γ₁'] [AddAction Γ' Γ₁'] [IsOrderedCancelVAdd Γ' Γ₁'] [EquivLike S Γ Γ']
[AddMonoidHomClass S Γ Γ'] [OrderIsoClass S Γ Γ'] (f : S) [EquivLike F Γ₁ Γ₁']
[OrderIsoClass F Γ₁ Γ₁'] [AddActionSemiHomClass F f Γ₁ Γ₁'] (f₁ : F)

open scoped HahnModule

/-!
/-- A Hahn-semilinear isomorphism of heterogeneous vertex operator spaces induced by ordered
isomorphisms. -/
def equivDomainSemi :
    HVertexOperator Γ₁ R V W ≃ₛₗ[(HahnSeries.equivDomainRingHom (Γ := Γ) (R := R) f).toRingHom]
      HVertexOperator Γ₁' R V W :=
  ((LinearEquiv.congrSemilinear (R := R) (M := V) (R₂ := HahnSeries Γ R) (M₂ := HahnModule Γ₁ R W)
    (σ₂ := HahnSeries.C) (by simp)).trans
    (LinearEquiv.arrowCongrRight (HahnSeries.C) (σ₃ := HahnSeries.C)
      (HahnModule.equivDomainModuleHom (R := R) (V := W) f f₁))).trans
    (LinearEquiv.congrSemilinear (R := R) (M := V) (R₂ := HahnSeries Γ' R)
      (M₂ := HahnModule Γ₁' R W) (σ₂ := HahnSeries.C) (by simp)).symm

@[simp]
theorem equivDomainSemi_apply_apply (A : HVertexOperator Γ₁ R V W) (v : V) :
    equivDomainSemi f f₁ A v = HahnModule.equivDomainModuleHom f f₁ (A v) := by
  simp [equivDomainSemi]

@[simp]
theorem equivDomainSemi_symm_apply_apply (A : HVertexOperator Γ₁' R V W) (v : V) :
    (equivDomainSemi f f₁).symm A v =
      (HahnModule.equivDomainModuleHom f f₁).symm (A v) := by
  simp [equivDomainSemi]

theorem equivDomainSemi_smul (x : HahnSeries Γ R) (A : HVertexOperator Γ₁ R V W) :
    equivDomainSemi f f₁ (x • A) =
      (HahnSeries.equivDomainRingHom f x) • equivDomainSemi f f₁ A := by
  ext
  simp [equivDomainSemi, LinearEquiv.map_smulₛₗ]
-- add symm

theorem equivDomainSemi_base_smul (r : R) (A : HVertexOperator Γ₁ R V W) :
    equivDomainSemi f f₁ (r • A) = r • equivDomainSemi f f₁ A := by
  have : r • A = (HahnSeries.C (R := R) (Γ := Γ) r) • A := by
    rw [HahnSeries.C_apply, single_zero_smul_eq_smul]
  rw [this, equivDomainSemi_smul]
  simp
--Prod.RevLex.lexEquivVAdd
/-- The Hahn-semilinear isomorphism between heterogeneous vertex operators on a Lex product and
heterogeneous vertex operators on a RevLex product. -/
def lexRevSemiEquiv : HVertexOperator (Γ₁' ×ₗ Γ₁) R V W ≃ₛₗ[(HahnSeries.equivDomainRingHom (R := R)
    (Prod.RevLex.lexEquivAddHom Γ' Γ)).toRingHom]
    HVertexOperator (Γ₁ ×ᵣ Γ₁') R V W :=
  equivDomainSemi (R := R) (V := V) (W := W) (Prod.RevLex.lexEquivAddHom Γ' Γ)
    (Prod.RevLex.lexEquivVAdd Γ' Γ Γ₁' Γ₁)

@[simp]
theorem lexRevSemiEquiv_apply_apply_coeff (A : HVertexOperator (Γ₁' ×ₗ Γ₁) R V W) (v : V)
    (g : Γ₁' ×ₗ Γ₁) :
    ((HahnModule.of R).symm (A.lexRevSemiEquiv (Γ := Γ) (Γ' := Γ') v)).coeff
      (Prod.RevLex.lexEquiv Γ₁' Γ₁ g) =
        ((HahnModule.of R).symm (A v)).coeff g := by
  rfl

@[simp]
theorem lexRevSemiEquiv_symm_apply_apply_coeff (A : HVertexOperator (Γ₁ ×ᵣ Γ₁') R V W) (v : V)
    (g : Γ₁ ×ᵣ Γ₁') :
    ((HahnModule.of R).symm ((lexRevSemiEquiv (Γ := Γ) (Γ' := Γ')).symm A v)).coeff
      ((Prod.RevLex.lexEquiv Γ₁' Γ₁).symm g) =
        ((HahnModule.of R).symm (A v)).coeff g := by
  rfl

theorem lexRevSemiEquiv_base_smul (A : HVertexOperator (Γ₁' ×ₗ Γ₁) R V W) (r : R) :
    lexRevSemiEquiv (Γ := Γ) (Γ' := Γ') (r • A) = r • lexRevSemiEquiv (Γ := Γ) (Γ' := Γ') A := by
  ext g v
  simp only [RingEquiv.toRingHom_eq_coe, lexRevSemiEquiv]
  rw [equivDomainSemi_base_smul]
-/
end equivDomain

end Module

section CoeffOps

variable [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Swap inputs for a function on a product. -/
@[simps!]
def swapEquiv : ((Γ₁ × Γ) → V) ≃ₗ[R] ((Γ × Γ₁) → V) where
  toFun A g := A (g.2, g.1)
  map_add' A B := by ext; simp
  map_smul' r A := by ext; simp
  invFun A g := A (g.2, g.1)
  left_inv A := by simp
  right_inv A := by simp
--#find_home! swapEquiv --Mathlib.Algebra.Module.Equiv.Basic

/-- The commutator of two formal series of endomorphisms. -/
def commutator (A : Γ → V →ₗ[R] V) (B : Γ₁ → V →ₗ[R] V) : (Γ × Γ₁) → V →ₗ[R] V :=
  fun g ↦ (A g.1) * (B g.2) - (B g.2) * (A g.1)

theorem Jacobi (A : Γ → V →ₗ[R] V) (B : Γ₁ → V →ₗ[R] V) (C : Γ₂ → V →ₗ[R] V) (g : Γ) (g₁ : Γ₁)
    (g₂ : Γ₂) :
    (commutator (commutator A B) C ((g, g₁), g₂)) +
    (commutator (commutator B C) A ((g₁, g₂), g)) +
    (commutator (commutator C A) B ((g₂, g), g₁)) = 0 := by
  simp only [commutator, sub_mul, mul_assoc, mul_sub]
  abel

/-- The associator on functions on a triple product. -/
@[simps!]
def assocEquiv : ((Γ × Γ₁) × Γ₂ → V →ₗ[R] W) ≃ₗ[R] (Γ × (Γ₁ × Γ₂) → V →ₗ[R] W) where
  toFun A g := A ((g.1, g.2.1), g.2.2)
  map_add' A B := by ext; simp
  map_smul' r A := by ext; simp
  invFun A g := A (g.1.1, (g.1.2, g.2))
  left_inv A := by simp
  right_inv A := by simp

-- scalar action by finsupps.

end CoeffOps

section Products

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ₁] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V)

open HahnModule

theorem lexComp_support_isPWO (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V)
    (u : U) :
    (fun x ↦ (fun (g : Γ₁ ×ₗ Γ) ↦
      A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1) x u).support.IsPWO := by
  refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
  · refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [Set.image_subset_iff, Function.support_subset_iff, Set.mem_preimage,
      Function.mem_support, Lex.forall, ofLex_toLex, Prod.forall]
    intro _ _ h
    contrapose! h
    simp [h]
  · intro g₁
    simp only [Function.mem_support, ofLex_toLex]
    exact HahnSeries.isPWO_support _

/-- The bilinear composition of two heterogeneous vertex operators, yielding a heterogeneous vertex
operator on the Lex product. Note that the exponent group of the left factor ends up on the right
side of the Lex product. -/
def lexComp : HVertexOperator Γ R V W →ₗ[R] HVertexOperator Γ₁ R U V →ₗ[R]
    HVertexOperator (Γ₁ ×ₗ Γ) R U W where
  toFun A := {
    toFun B :=
      of_coeff (fun g ↦ (coeff A (ofLex g).2) ∘ₗ (coeff B (ofLex g).1))
        (fun u ↦ lexComp_support_isPWO A B u)
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem lexComp_apply_apply_coeff (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V)
    (g : Γ₁ ×ₗ Γ) :
    (lexComp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

@[simp]
theorem lexComp_apply_apply_apply_coeff (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ₁ R U V)
    (u : U) (g : Γ₁ ×ₗ Γ) :
    ((HahnModule.of R).symm (lexComp A B u)).coeff g =
      A.coeff (ofLex g).2 (B.coeff (ofLex g).1 u) := by
  rfl

/-- The bilinear composition of two heterogeneous vertex operators, yielding a heterogeneous vertex
operator on the RevLex product. -/
def revLexComp : HVertexOperator Γ R V W →ₗ[R] HVertexOperator Γ₁ R U V →ₗ[R]
      HVertexOperator (Γ ×ᵣ Γ₁) R U W :=
  LinearMap.compr₂ (lexComp (Γ := Γ) (Γ₁ := Γ₁) (U := U) (V := V) (W := W))
    (lexRevEquivBase Γ₁ Γ (R := R) (V := U) (W := W)).toLinearMap

theorem revLexComp_apply_apply_apply_coeff (A : HVertexOperator Γ R V W)
    (B : HVertexOperator Γ₁ R U V) (v : U) (g : RevLex (Γ × Γ₁)) :
    (revLexComp A B v).coeff g =
      ((of R).symm (lexComp A B v)).coeff ((Prod.RevLex.lexEquiv Γ₁ Γ).symm g) := by
  rfl

-- TODO: comp_assoc

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the left
factor, as a linear map. -/
def LexResLeft (g' : Γ₁) : HVertexOperator (Γ₁ ×ₗ Γ) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := HVertexOperator.of_coeff (fun g => coeff A (toLex (g', g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_ResLeft (A : HVertexOperator (Γ₁ ×ₗ Γ) R V W) (g' : Γ₁) (g : Γ) :
    coeff (LexResLeft g' A) g = coeff A (toLex (g', g)) :=
  rfl

theorem coeff_left_lex_supp.isPWO (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, g'))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp only [Function.support_subset_iff, ne_eq, Set.mem_image, Function.mem_support]
  exact fun x h ↦ Exists.intro (toLex (x, g')) ⟨h, rfl⟩

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the right
factor. -/
def LexResRight (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) : HVertexOperator Γ R V W :=
  HVertexOperator.of_coeff (fun g => coeff A (toLex (g, g')))
    (fun v => coeff_left_lex_supp.isPWO A g' v)

theorem coeff_ResRight (A : HVertexOperator (Γ ×ₗ Γ₁) R V W) (g' : Γ₁) (g : Γ) :
    coeff (LexResRight A g') g = coeff A (toLex (g, g')) := rfl

/-- The right residue as a linear map. -/
@[simps]
def ResRight.linearMap (g' : Γ₁) :
    HVertexOperator (Γ ×ₗ Γ₁) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := LexResRight A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Products

end HVertexOperator

section PiLex
/-! 2025-7-20
I need some API for dealing with embeddings of the form `V((z))((w)) ↪ V⟦z, z⁻¹, w, w⁻¹⟧` and three-
variable variants, so I can compare coefficients in, e.g., Dong's Lemma efficiently. I think a
potentially good way is an `embCoeff` function, like `HahnSeries.embDomain`, but replacing the
order-preserving requirement with an algebraic condition. For example, commuting two operators
should allow me to commute in all domains with a fixed embedding of `ℤ × ℤ`. I need:
 * a way to strip order off `A.coeff` (or just ask for an injective group hom)
 * functions to permute variables, or just embed.
 * Commutators of vertex operators as bare functions.
 * Scalar multiplication by Finsupps.
 * Translation from embedded positive `binomialPow` to `Finsupp`.
 * Comparison of commutator with usual composition
How do I express weak associativity in terms of power series? This seems to require a substitution.

One way: use `embCoeff f A = f.arrowCongrLeft A.coeff`.
-/

-- Order.PiLex
-- use Prod.swap?
/-! We consider permutations on Lex Pi types. We need this for the following situation:
To describe locality of vertex operators, we want to say that
`(X - Y) ^ N • A(X) B(Y) = (X - Y) ^ N • B(Y) A(X)`. However, the left side naturally lies in
`V →ₗ[R] V((X))((Y))` while the right side lies in `V →ₗ[R] V((Y))((X))`. We can compare them by
forgetting the Hahn series structure, and showing that the coefficient functions are equal after
switching variables. One way to phrase this is that applying `(HahnModule.of R).symm` then
`HahnSeries.coeff`, we get functions to `ℤ ×ₗ ℤ`. Composing with `ofLex` yields functions `ℤ × ℤ`.

One way to look at locality is that for any `u ∈ V`, we have `Y ^ k • A(X)B(Y)u ∈ V((X))[[Y]]` for
suitably large `k`, and `X ^ m • B(Y)A(X)u ∈ V((Y))[[X]]` for suitably large `m`.  We conclude that
locality means there are `k, m, N` such that both `X ^ m * Y ^ k * (X - Y) ^ N • A(X) B(Y) u` and
`X ^ m * Y ^ k * (X - Y) ^ N • B(Y) A(X) u` lie in `V[[X,Y]]`, and are equal there.

One problem is that I want to say that `(X - Y) ^ N` expanded in `R((X))((Y))` is the same as
`(X - Y) ^ N` expanded in `R((Y))((X))`. Thus, I would like some API for transferring polynomials
along variable permutations. Switching variables on `(X - Y) ^ N` is the same as multiplying by
`(-1) ^ N`, but when we have more variables, a permutation yields more than just a sign change.

Perhaps it is best to have lemmas identifying UnitBinomial with HahnSeries finsupps, so that
permutations still yield Hahn series.  I think we only need 3 variables most of the time, so
permutations on `(X - Y) ^ k * (X - Z) ^ m * (Y - Z) ^ n` may be enough. For Dong's Lemma, I need
to use the fact that `(X - Z) = (X - Y) + (Y - Z)`.

So, maybe I should make a notation `X i` for the variable, and the field `A (X i)` a type synonym
for `A`, so Hahn series on `ℤ ×ₗ ⋯ ×ₗ ℤ` are given by `V((X 1)) ⋯ ((X n))`.

See Algebra.MvPolynomial.Basic:

def MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

def X (n : σ) : MvPolynomial σ R :=
  monomial (Finsupp.single n 1) 1

def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)

@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id] }

Wrong: Define a vertex operator as `HVertexOperator (σ → ℤ) R V V` for a singleton type `σ`?

Composition gives ProdLex types, so composite types in general should be PiLex, using an ordered
version of `consPiProdEquiv`. Comparison should take place using `rename` along permutations.
Associativity is delicate: we have `Γ₁ ×ₗ (Γ₂ ×ₗ Γ₃)` and `(Γ₁ ×ₗ Γ₂) ×ₗ Γ₃`, so we need something
like a `LexAssoc` operation.  We say two `VertexOperators` `Commute` if transposition yields an
identity on coefficients, and they are `IsLocal` if they `Commute` after multiplying by transposed
binomials. We say two `VertexOperators` `IsAssociate` if their coefficients match (need a variable
change from `X` to `X + Y` here?), and `IsWeakAssociate` if they associate after multiplying by
suitable binomials.  In general, associativity of intertwining operators needs some analytic input,
like from differential equations?

Maybe have type aliases for different orders?

theorem `Pi.lex_desc` {α} [Preorder ι] [DecidableEq ι] [Preorder α] {f : ι → α} {i j : ι}
    (h₁ : i ≤ j) (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f := sorry

Define binomials `X i - X j` as `varMinus i j` for `i j : σ`.  Or maybe `varMinus hij` for
`hij : i < j`. This might make it hard to compare `varMinus i j` with `varMinus j i` for
a permuted order. Binomials are also Finsupps, so we can make a function to MvPolynomial, and
compare them that way. Since this is special to vertex operators, perhaps this should go in the
vertex operator file.

-/

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def Lexx (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

theorem xxx (x y : ∀ i, β i) : Lexx r s x y ↔ Pi.Lex r s x y := Iff.rfl

theorem lex_basis_lt : (toLex (0,1) : ℤ ×ₗ ℤ) < (toLex (1,0) : ℤ ×ₗ ℤ) :=
  compareOfLessAndEq_eq_lt.mp rfl
--#find_home! lex_basis_lt --[Mathlib.Data.Prod.Lex]

theorem revLex_basis_lt : (toRevLex (1, 0) : ℤ ×ᵣ ℤ) < (toRevLex (0, 1) : ℤ ×ᵣ ℤ) :=
  Prod.RevLex.lt_iff.mpr <| Or.inl <| compareOfLessAndEq_eq_lt.mp rfl
--#find_home! revLex_basis_lt --[Mathlib.Data.Prod.RevLex]

end PiLex

namespace HVertexOperator

section binomialPow

variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [CommRing R] [CommRing S]
[BinomialRing S] [Module S Γ] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
[PartialOrder Γ₁] [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [Module S W] [Algebra S R]
[IsScalarTower S R W]

omit [BinomialRing S] [Module S W] [Algebra S R] in
theorem exists_binomialPow_smul_support_bound {g g' : Γ} (g₁ : Γ₁) (h : g < g') (n : S)
    (A : HVertexOperator Γ₁ R V W) (v : V) :
    ∃ (k : ℕ), ∀ (m : ℕ) (_ : k < m),
      (-(n • g) - m • (g' - g)) +ᵥ g₁ ∉ ((HahnModule.of R).symm (A v)).support :=
  Set.PartiallyWellOrderedOn.exists_notMem_of_gt ((HahnModule.of R).symm (A v)).isPWO_support
    fun _ _ hkl ↦ not_le_of_gt <| VAdd.vadd_lt_vadd_of_lt_of_le
      (sub_lt_sub_left (nsmul_lt_nsmul_left (sub_pos.mpr h) hkl) (-(n • g))) <| Preorder.le_refl g₁

theorem binomialPow_smul_coeff {g g' : Γ} (g₁ : Γ₁) (h : g < g') (n : S)
    (A : HVertexOperator Γ₁ R V W) (v : V) :
    ((HahnModule.of R).symm (HahnSeries.binomialPow (A := R) g g' n • A v)).coeff g₁ =
      ∑ᶠ m : ℕ, Int.negOnePow m • Ring.choose n m •
        ((HahnModule.of R).symm (A v)).coeff ((- (n • g) - (m • (g' - g))) +ᵥ g₁) := by
  let f : ℕ → Γ × Γ₁ := fun k ↦  ((n • g) + k • (g' - g), (- (n • g) - (k • (g' - g))) +ᵥ g₁)
  let s := Finset.range <| (exists_binomialPow_smul_support_bound g₁ h n A v).choose + 1
  rw [HahnModule.coeff_smul, finsum_eq_sum_of_support_subset (s := s)]
  · classical
    refine Eq.trans (b := ∑ ij ∈ (Finset.image f s),
      (HahnSeries.binomialPow R g g' n).coeff ij.1 •
        ((HahnModule.of R).symm (A v)).coeff ij.2) ?_ ?_
    · refine Finset.sum_of_injOn (fun k ↦ k) (Function.Injective.injOn fun ⦃x y⦄ a ↦ a) ?_ ?_ ?_
      · rw [Set.mapsTo', Set.image_id', Finset.coe_subset]
        intro ij hij
        obtain ⟨h₁, h₂, h₃⟩ := (Finset.mem_vaddAntidiagonal _ _ _).mp hij
        rw [HahnSeries.mem_support] at h₁
        have hij1 : ∃ k : ℕ, (n • g + k • (g' - g)) = ij.1 := by
          contrapose! h₁
          exact HahnSeries.binomialPow_coeff_eq_zero R h n h₁
        obtain ⟨k, hk⟩ := hij1
        have hij2 : ij.2 = (-(n • g) - k • (g' - g)) +ᵥ g₁ := by
          rw [← h₃, vadd_vadd, ← hk, sub_add_add_cancel, neg_add_cancel, zero_vadd]
        have : k ∈ s := by
          contrapose! h₂
          rw [Finset.mem_range_succ_iff, not_le] at h₂
          rw [hij2]
          exact (exists_binomialPow_smul_support_bound g₁ h n A v).choose_spec k h₂
        exact Finset.mem_image.mpr (Exists.intro k ⟨this, by simp [f, hk, ← hij2]⟩)
      · intro ij hij hn
        simp only [Set.image_id', Finset.mem_coe, Finset.mem_vaddAntidiagonal, not_and] at hn
        have : ij.1 +ᵥ ij.2 = g₁ := by
          obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hij
          simp only [f, Prod.eq_iff_fst_eq_snd_eq] at hk₂
          rw [← hk₂.1, ← hk₂.2, vadd_vadd, add_add_sub_cancel, add_neg_cancel, zero_vadd]
        by_cases h1 : (HahnSeries.binomialPow R g g' n).coeff ij.1 = 0
        · rw [h1, zero_smul]
        · specialize hn h1
          by_cases h2 : ((HahnModule.of R).symm (A v)).coeff ij.2 = 0
          · rw [h2, smul_zero]
          · exact ((hn h2) this).elim
      · intro ij hij
        simp
    · refine (Finset.sum_of_injOn
      (fun k ↦ ((n • g) + k • (g' - g), (- (n • g) - (k • (g' - g))) +ᵥ g₁))
      (fun k hk l hl hkl ↦ ?_) ?_ ?_ ?_).symm
      · simp only [Prod.mk.injEq, add_right_inj] at hkl
        obtain ⟨hkl1, hkl2⟩ := hkl
        contrapose! hkl1
        obtain hk | eq | hk := lt_trichotomy k l
        · exact ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) hk
        · exact (hkl1 eq).elim
        · exact Ne.symm <| ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) hk
      · intro k hk
        exact Finset.mem_coe.mpr <| Finset.mem_image_of_mem f hk
      · intro k hk hkn
        rw [Finset.mem_image] at hk
        rw [Set.mem_image] at hkn
        exact (hkn hk).elim
      · intro k hks
        simp only
        rw [HahnSeries.binomialPow_coeff_eq R h n k, ← smul_assoc, ← smul_assoc,
          smul_one_smul]
  · refine Function.support_subset_iff'.mpr ?_
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range, Nat.not_lt_eq, Order.add_one_le_iff] at hk
    have := (exists_binomialPow_smul_support_bound g₁ h n A v).choose_spec k hk
    rw [HahnSeries.mem_support, Mathlib.Tactic.PushNeg.not_ne_eq] at this
    rw [this, smul_zero, smul_zero]

omit [Module S W] [IsScalarTower S R W] in
theorem binomialPow_smul_injective {g g' : Γ} (n : S) :
    Function.Injective (HahnSeries.binomialPow (A := R) g g' n • · :
      HVertexOperator Γ₁ R V W → HVertexOperator Γ₁ R V W) := by
  refine Function.HasLeftInverse.injective ?_
  use (HahnSeries.binomialPow (A := R) g g' (-n) • ·)
  intro A
  simp only [smul_smul, HahnSeries.binomialPow_add, neg_add_cancel]
  rw [show OfNat.ofNat (α := S) 0 = Nat.cast 0 by norm_cast,
    HahnSeries.binomialPow_zero, HahnSeries.single_zero_one, one_smul]

end binomialPow

end HVertexOperator

section HStateField

variable (Γ R U₀ U₁ U₂ V W : Type*) [CommRing R] [AddCommGroup U₀] [Module R U₀] [AddCommGroup U₁]
[Module R U₁] [AddCommGroup U₂] [Module R U₂] [AddCommGroup V] [Module R V] [AddCommGroup W]
[Module R W]

/-- A heterogeneous state-field map is a linear map from a vector space `U` to the space of
heterogeneous fields (or vertex operators) from `V` to `W`.  Equivalently, it is a bilinear map
`U →ₗ[R] V →ₗ[R] HahnModule Γ R W`.  When `Γ = ℤ` and `U = V = W`, then the multiplication map in a
vertex algebra has this form, but in other cases, we use this for module structures and intertwining
operators. -/
abbrev HStateFieldMap [PartialOrder Γ] := U₀ →ₗ[R] HVertexOperator Γ R V W

namespace HStateField

section

variable {Γ' Γ₁ Γ₁' : Type*} [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
[PartialOrder Γ'] [AddCommMonoid Γ'] [IsOrderedCancelAddMonoid Γ']
[PartialOrder Γ₁] [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [PartialOrder Γ₁'] [AddAction Γ' Γ₁']
[IsOrderedCancelVAdd Γ' Γ₁'] (f : Γ ≃+o Γ') (f₁ : OrderedAddActionEquiv f.toEquiv Γ₁ Γ₁')

open scoped HahnModule
/-!
/-- A semilinear equivalence between state field maps induced by additive order isomorphisms. -/
def equivDomain :
    HStateFieldMap Γ₁ R U₀ V W ≃ₛₗ[(HahnSeries.equivDomainRingHom (Γ := Γ) (R := R) f).toRingHom]
      HStateFieldMap Γ₁' R U₀ V W :=
  ((LinearEquiv.congrSemilinear (R := R) (M := U₀) (R₂ := HahnSeries Γ R)
    (M₂ := HVertexOperator Γ₁ R V W) (σ₂ := HahnSeries.C) (by simp)).trans
    (LinearEquiv.semiCongrRight (HahnSeries.C) (σ₃ := HahnSeries.C)
      (HVertexOperator.equivDomainSemi (R := R) (V := V) f f₁))).trans
    (LinearEquiv.congrSemilinear (R := R) (M := U₀) (R₂ := HahnSeries Γ' R)
      (M₂ := HVertexOperator Γ₁' R V W) (σ₂ := HahnSeries.C) (by simp)).symm

@[simp]
theorem equivDomain_apply_apply (Y : HStateFieldMap Γ₁ R U₀ V W) (u : U₀) (v : V) :
    equivDomain Γ R U₀ V W f f₁ Y u v =
      HahnModule.equivDomainModuleHom f f₁ (Y u v) := by
  dsimp [equivDomain]
  erw [HVertexOperator.equivDomainSemi_apply_apply]

@[simp]
theorem equivDomain_symm_apply_apply (Y : HStateFieldMap Γ₁' R U₀ V W) (u : U₀) (v : V) :
    (equivDomain Γ R U₀ V W f f₁).symm Y u v =
      (HahnModule.equivDomainModuleHom f f₁).symm (Y u v) := by
  dsimp [equivDomain]
  erw [HVertexOperator.equivDomainSemi_symm_apply_apply]
-/
end

theorem compLeft_isPWO {Γ} [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R V U₂ W)
    (x : HahnModule Γ₁ R V) (u₂ : U₂) :
    (fun (g : Γ₁ ×ₗ Γ) ↦ ((HahnModule.of R).symm
      (Y₁ (((HahnModule.of R).symm x).coeff (ofLex g).1) u₂)).coeff (ofLex g).2).support.IsPWO := by
  refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
  · refine Set.IsPWO.mono (HahnSeries.isPWO_support ((HahnModule.of R).symm x)) ?_
    intro g hg
    contrapose! hg
    simp only [HahnSeries.mem_support, ne_eq, not_not] at hg
    simp [hg]
  · intro g
    simp only [Function.mem_support, ofLex_toLex]
    exact HahnSeries.isPWO_support _

variable {Γ}

/-- Composition of state-field maps by left-insertion. In traditional notation, if `Y₁(-,z)` and
`Y₂(-,w)` are state-field maps, then this is `Y₁(Y₂(u₀,w)u₁,z)u₂`. -/
@[simps!]
def compLeft [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R V U₂ W)
    (Y₂ : HStateFieldMap Γ₁ R U₀ U₁ V) :
    U₀ →ₗ[R] U₁ →ₗ[R] U₂ →ₗ[R] HahnModule (Γ₁ ×ₗ Γ) R W where
  toFun u₀ := {
    toFun u₁ := {
      toFun u₂ := (HahnModule.of R) ⟨fun (g : Γ₁ ×ₗ Γ) ↦ ((HahnModule.of R).symm
        (Y₁ (((HahnModule.of R).symm (Y₂ u₀ u₁)).coeff (ofLex g).1) u₂)).coeff (ofLex g).2,
          compLeft_isPWO R U₂ V W Y₁ (Y₂ u₀ u₁) u₂⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Composition of state-field maps with reversed variable order. -/
def CompLeftRev [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R V U₂ W)
    (Y₂ : HStateFieldMap Γ₁ R U₀ U₁ V) :
    U₀ →ₗ[R] U₁ →ₗ[R] HVertexOperator (Γ ×ᵣ Γ₁) R U₂ W :=
  LinearMap.compr₂ (compLeft R U₀ U₁ U₂ V W Y₁ Y₂)
    (HVertexOperator.lexRevEquivBase (R := R) (V := U₂) (W := W) Γ₁ Γ).toLinearMap

theorem compRight_isPWO {Γ} [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R U₀ V W)
    (u₀ : U₀) (x : HahnModule Γ₁ R V) :
    (Function.support fun (g : Γ₁ ×ₗ Γ) ↦ ((HahnModule.of R).symm
      ((Y₁ u₀) (((HahnModule.of R).symm x).coeff (ofLex g).1))).coeff (ofLex g).2).IsPWO := by
  refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
  · refine Set.IsPWO.mono (HahnSeries.isPWO_support ((HahnModule.of R).symm x)) ?_
    intro g hg
    contrapose! hg
    simp only [HahnSeries.mem_support, ne_eq, not_not] at hg
    simp [hg]
  · intro g
    simp only [Function.mem_support, ofLex_toLex]
    exact HahnSeries.isPWO_support _

/-- Composition of state-field maps by right-insertion. In traditional notation, if `Y₁(-,z)` and
`Y₂(-,w)` are state-field maps, then this is `Y₁(u₀,z)Y₂(u₁,w)u₂`. -/
@[simps!]
def compRight [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R U₀ V W)
    (Y₂ : HStateFieldMap Γ₁ R U₁ U₂ V) :
    U₀ →ₗ[R] U₁ →ₗ[R] U₂ →ₗ[R] HahnModule (Γ₁ ×ₗ Γ) R W where
  toFun u₀ := {
    toFun u₁ := {
      toFun u₂ := (HahnModule.of R) ⟨fun (g : Γ₁ ×ₗ Γ) ↦ ((HahnModule.of R).symm
        (Y₁ u₀ (((HahnModule.of R).symm (Y₂ u₁ u₂)).coeff (ofLex g).1))).coeff (ofLex g).2,
          compRight_isPWO R U₀ V W Y₁ u₀ (Y₂ u₁ u₂)⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem compRight_eq_lexComp [PartialOrder Γ] [PartialOrder Γ₁] (Y₁ : HStateFieldMap Γ R U₀ V W)
    (Y₂ : HStateFieldMap Γ₁ R U₁ U₂ V) (u₀ : U₀) (u₁ : U₁) (u₂ : U₂) :
    compRight R U₀ U₁ U₂ V W Y₁ Y₂ u₀ u₁ u₂ = HVertexOperator.lexComp (Y₁ u₀) (Y₂ u₁) u₂ := by
  ext
  simp [compRight, HVertexOperator.lexComp]

end HStateField

end HStateField

namespace HVertexOperator

-- Can I just use `curry` to say this is a HVertexOperator Γ R (U ⊗[R] V) W?  So, the multiplication
-- in a vertex algebra is just HVertexOperator ℤ R (V ⊗[R] V) V?
-- Then composition is easier, but tensor products slow everything down.

section TensorComp

open TensorProduct

variable [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The standard equivalence between heterogeneous state field maps and heterogeneous vertex
operators on the tensor product. May be unnecessary. -/
def uncurry [PartialOrder Γ] [AddCommGroup U] [Module R U] :
    (U →ₗ[R] HVertexOperator Γ R V W) ≃ₗ[R] HVertexOperator Γ R (U ⊗[R] V) W :=
  lift.equiv R U V (HahnModule Γ R W)

@[simp]
theorem uncurry_apply [PartialOrder Γ] [AddCommGroup U] [Module R U]
    (A : U →ₗ[R] HVertexOperator Γ R V W) (u : U) (v : V) : uncurry A (u ⊗ₜ v) = A u v :=
  rfl

@[simp]
theorem uncurry_symm_apply [PartialOrder Γ] [AddCommGroup U] [Module R U]
    (A : HVertexOperator Γ R (U ⊗[R] V) W) (u : U) (v : V) : uncurry.symm A u v = A (u ⊗ₜ v) :=
  rfl

section Composition

/-! Given heterogeneous vertex operators `Y_{UV}^W : U ⊗ V → W((z))` and
`Y_{WX}^Y : W ⊗ X → Y((w))`, we wish to compose them to get a heterogeneous vertex operator
`U ⊗ V ⊗ X → Y((w))((z))`.

-/

variable [PartialOrder Γ] [PartialOrder Γ₁] [AddCommGroup U] [Module R U] [AddCommGroup X]
[Module R X] [AddCommGroup Y] [Module R Y]

/-- Left iterated vertex operator. -/
def leftTensorComp (A : HVertexOperator Γ R (U ⊗[R] V) X)
    (B : HVertexOperator Γ₁ R (X ⊗[R] W) Y) :
    ((U ⊗[R] V) ⊗[R] W) →ₗ[R] HahnModule Γ R (HahnModule Γ₁ R Y) :=
  (HahnModule.map B) ∘ₗ HahnModule.rightTensorMap ∘ₗ (TensorProduct.map A LinearMap.id)

/-!
`simps!` yields
((A.leftTensorComp B) a).coeff g =
  B (((HahnModule.of R).symm (HahnModule.rightTensorMap
    ((TensorProduct.map A LinearMap.id) a))).coeff g)

 Iterate starting with `Y_{UV}^W : U ⊗ V → W((z))` and `Y_{WX}^Y : W ⊗ X → Y((w))`, make
`leftTensorComp`: `Y_{UVX}^Y (t_1, t_2) : U ⊗ V ⊗ X → W((z)) ⊗ X → (W ⊗ X)((z)) → Y((w))((z))`.
First: `Y_{UV}^W ⊗ id X : U ⊗ V ⊗ X → W((z)) ⊗ X`
Second: `W((z)) ⊗ X → (W ⊗ X)((z))` is `HahnModule.rightTensorMap`.
Third: `(W ⊗ X)((z)) → Y((w))((z))` is `HahnModule.map` applied to `Y_{WX}^Y`.

`rightTensorComp`: `Y_{XW}^Y (x, t_0) Y_{UV}^W (u, t_1) v`

Define things like order of a pair, creativity?

-/

end Composition

end TensorComp


section Binomial -- delete this. Important adaptations go to VertexOperator.lean

theorem toLex_vAdd_of_sub (k l m n : ℤ) :
    toLex ((m : ℤ) , (n : ℤ)) +ᵥ toLex (k - m, l - n) = toLex (k, l) := by
  rw [vadd_eq_add, ← toLex_add, Prod.mk_add_mk, Int.add_comm, Int.sub_add_cancel, Int.add_comm,
    Int.sub_add_cancel]
--#find_home! toLex_vAdd_of_sub --[Mathlib.RingTheory.HahnSeries.Multiplication]

variable [PartialOrder Γ] [AddCommMonoid Γ] [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

-- Don't bother defining this!!!

/-- `-Y + X` as a unit of `R((X))((Y))` -/
def subLeft (R) [CommRing R] : HahnSeries (ℤ ×ₗ ℤ) R :=
  HahnSeries.binomialPow R (toLex (0, 1)) (toLex (1, 0)) (1 : ℤ) --(isUnit_neg_one (α := R)) (1 : R)

theorem subLeft_eq : subLeft R = HahnSeries.single (toLex (0,1)) 1 -
    HahnSeries.single (toLex (1,0)) (1 : R) := by
  rw [subLeft, ← HahnSeries.binomialPow_one (R := ℤ) R lex_basis_lt, Int.natCast_one]

@[simp]
theorem subLeft_leadingCoeff [Nontrivial R] : (subLeft R).leadingCoeff = (1 : R) := by
  rw [subLeft_eq, HahnSeries.leadingCoeff_sub, HahnSeries.leadingCoeff_of_single]
  rw [HahnSeries.orderTop_single one_ne_zero, HahnSeries.orderTop_single one_ne_zero,
    WithTop.coe_lt_coe]
  exact lex_basis_lt

theorem subLeft_order [Nontrivial R] : (subLeft R).order = toLex (0,1) := by
  rw [subLeft_eq, ← WithTop.coe_eq_coe, HahnSeries.order_eq_orderTop_of_ne, HahnSeries.orderTop_sub,
    HahnSeries.orderTop_single one_ne_zero]
  · rw [HahnSeries.orderTop_single one_ne_zero, HahnSeries.orderTop_single one_ne_zero]
    exact compareOfLessAndEq_eq_lt.mp rfl
  · refine HahnSeries.leadingCoeff_ne_iff.mp ?_
    rw [← subLeft_eq, subLeft_leadingCoeff]
    exact one_ne_zero

/-!
@[simp]
theorem coeff_subLeft_smul (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subLeft R) • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k - 1, l)) - A.coeff (toLex (k, l - 1)) := by
  rw [subLeft_eq, add_smul, coeff_add, Pi.add_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.coeff_single_smul_vadd, one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.coeff_single_smul_vadd, neg_one_smul, ← sub_eq_add_neg]


--describe coefficients of powers
theorem coeff_subLeft_pow_smul (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l n : ℤ) :
    ((subLeft R) ^ n • A).coeff (toLex (k, l)) = ∑??
-/

/-- `X - Y` as a unit of `R((Y))((X))`. -/
def subRight (R) [CommRing R] : HahnSeries (ℤ ×ᵣ ℤ) R :=
    HahnSeries.binomialPow (Γ := ℤ ×ᵣ ℤ) R (toRevLex (1, 0)) (toRevLex (0, 1)) (1 : ℤ)

/-!
theorem subRight_eq : subRight R = HahnSeries.single (toRevLex (1,0)) (-1 : R) +
    HahnSeries.single (toRevLex (0,1)) (1 : R) := by
  rw [subRight]


theorem subRight_leadingCoeff [Nontrivial R] : (subRight R).val.leadingCoeff = (1 : R) := by
  rw [subRight_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_order [Nontrivial R] : (subRight R).val.order = toLex (0,1) := by
  rw [subRight_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_smul_eq (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) :
    (subRight R) • A = (subRight R).val • A :=
  rfl

theorem coeff_subRight_smul (A : HVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subRight R) • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k, l - 1)) - A.coeff (toLex (k - 1, l)) := by
  rw [subRight_smul_eq, subRight_eq, add_smul, coeff_add, Pi.add_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.sub_apply, smul_eq]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.coeff_single_smul_vadd, neg_one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.coeff_single_smul_vadd, one_smul, neg_add_eq_sub]

--describe coefficients of powers

theorem subLeft_smul_eq_subRight_smul (A B : HVertexOperator (ℤ ×ₗ ℤ) R V W)
    (h : ∀ (k l : ℤ), A.coeff (toLex (k, l)) = B.coeff (toLex (l, k))) (k l : ℤ) :
    ((subLeft R) • A).coeff (toLex (k, l)) = ((subRight R) • B).coeff (toLex (l, k)) := by
  rw [subLeft_smul_eq, coeff_subLeft_smul, coeff_subRight_smul, h k (l-1), h (k-1) l]
-/

end Binomial

end HVertexOperator
