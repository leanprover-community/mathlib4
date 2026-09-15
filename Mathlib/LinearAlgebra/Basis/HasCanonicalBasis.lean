/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Canonical Bases for vector spaces

This file introduces the notion of canonical bases for modules,
which allows us to work with an implicit notion of the canonical basis for familiar spaces.

-/

universe u v w u' v' w'

/-- `HasCanonicalBasis 𝕜 V ι f` means that the `𝕜`-module `V` is canonically
represented by an `ι`-indexed basis with elements `f`.

`f` is an outParam so that theorems about a particular basis can use the simp-normal `Pi.single`
rather than `Pi.basisFun`. -/
class HasCanonicalBasis (𝕜 : Type u) (V : Type v) (ι : outParam <| Type w)
    --TODO: can some of these be `semiOutParam`/regular params?
    (f : outParam <| ι → V) [Semiring 𝕜] [AddCommGroup V]
    [Module 𝕜 V] where
  /-- The underlying basis -/
  basis : Basis ι 𝕜 V
  coe_basis_eq : basis = f

namespace HasCanonicalBasis

@[simp]
lemma basis_apply (𝕜 : Type u) (V : Type v) (ι : outParam <| Type w)
    (f : outParam <| ι → V) [Semiring 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [hc : HasCanonicalBasis 𝕜 V ι f] (i : ι) :
    hc.basis i = f i := by
  simp [coe_basis_eq]

end HasCanonicalBasis

variable {𝕜 : Type u} {ι : Type w} [DecidableEq ι] [Fintype ι]

noncomputable instance EuclideanSpace.hasCanonicalBasis [RCLike 𝕜] :
    HasCanonicalBasis 𝕜 (EuclideanSpace 𝕜 ι) ι (EuclideanSpace.single · 1) where
  basis := PiLp.basisFun 2 𝕜 ι
  coe_basis_eq := by ext : 1; simp

variable [Ring 𝕜]

noncomputable instance Pi.hasCanonicalBasis : HasCanonicalBasis 𝕜 (ι → 𝕜) ι (Pi.single · 1) where
  basis := Pi.basisFun 𝕜 ι
  coe_basis_eq := by ext; simp

/-
Note: this could be generalised to a product of vector spaces that each have a
`HasCanonicalBasis` instance, but for now this isn't necessary, and the index
type would be a very ugly type, which is undesirable.
-/
noncomputable instance [Ring 𝕜] (p : ENNReal) :
  HasCanonicalBasis 𝕜 (PiLp p (fun (_ : ι) ↦ 𝕜)) ι (Pi.single · 1) where
  basis := (PiLp.basisFun p 𝕜 ι)
  coe_basis_eq := by ext; simp

noncomputable instance : HasCanonicalBasis 𝕜 𝕜 (Fin 1) (fun _ ↦ 1) where
  basis := Basis.singleton _ 𝕜
  coe_basis_eq := by ext i; aesop

/-- This abbrev provides us with a way of reindexing canonical bases, which is useful
in the context of defining canonical bases for products. -/
noncomputable abbrev reindex {V : Type v} {κ : Type w'}
    {f : ι → V} {g : κ → V} [Semiring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (hc : HasCanonicalBasis 𝕜 V ι f) (e : ι ≃ κ) (he : ∀ (i : κ), g i = hc.basis (e.symm i)) :
    HasCanonicalBasis 𝕜 V κ g where
  basis := Basis.reindex (HasCanonicalBasis.basis) e
  coe_basis_eq := by ext; simp [Basis.reindex_apply, he]

variable (𝕜) in
/-- Constructs a "canonical basis" on a product of two modules equipped with a canonical basis.
This isn't an instance since have a sum as the index type for our bases is in general undesirable
(e.g. this would force `𝕜 × 𝕜`  to have basis `Fin 1 ⊕ Fin 1` rather than `Fin 2`) -/
noncomputable abbrev prod {V : Type v} {W : Type v'} {κ : Type w'}
    [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W]
    (f : ι → V) (g : κ → W) [HasCanonicalBasis 𝕜 V ι f] [HasCanonicalBasis 𝕜 W κ g] :
    HasCanonicalBasis 𝕜 (V × W) (ι ⊕ κ) (Sum.elim (LinearMap.inl 𝕜 _ _ ∘ f)
      (LinearMap.inr 𝕜 _ _ ∘ g)) where
  basis := Basis.prod HasCanonicalBasis.basis HasCanonicalBasis.basis
  coe_basis_eq := by ext <;> simp [Basis.prod_apply, Sum.elim]

/--
The canonical basis for `𝕜 × 𝕜`
-/
noncomputable instance : HasCanonicalBasis 𝕜 (𝕜 × 𝕜) (Fin 2) (![(1, 0), (0, 1)]) :=
  reindex (prod 𝕜 _ _) finSumFinEquiv
    (fun i ↦  by fin_cases i <;> simp [finSumFinEquiv, prod, Sum.elim, Fin.addCases])

/--
The canonical basis for `𝕜 × 𝕜 × 𝕜`.
-/
noncomputable instance : HasCanonicalBasis 𝕜 (𝕜 × 𝕜 × 𝕜) (Fin 3)
    (![(1, 0, 0), (0, 1, 0), (0, 0, 1)]) :=
  reindex (prod 𝕜 _ _) finSumFinEquiv
    (fun i ↦  by fin_cases i <;> simp [finSumFinEquiv, prod, Sum.elim, Fin.addCases])

-- TODO: maybe we also want to manually construct an instance on `𝕜 × 𝕜 × 𝕜 × 𝕜`
