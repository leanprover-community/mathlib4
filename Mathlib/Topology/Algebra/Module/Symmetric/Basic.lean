/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.SymmetricMap -- future: move that file to Symmetric.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous symmetric multilinear maps

In this file we define bundled continuous symmetric maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and symmetric maps.

## Notation

`M [Sym^ι]→L[R] N`: notation for `R`-linear continuous symmetric maps from `M` to `N`; the arguments
are indexed by `i : ι`.

## Keywords

multilinear map, symmetric map, continuous
-/

@[expose] public section

open Function Matrix

/-- A continuous symmetric map from `ι → M` to `N`, denoted `M [Sym^ι]→L[R] N`,
is a continuous map that is

- multilinear : `f (update m i (c • x)) = c • f (update m i x)` and
  `f (update m i (x + y)) = f (update m i x) + f (update m i y)`;
- symmetric : `f (v ∘ (Equiv.swap i j)) = f v` for all `i, j`.
-/
structure ContinuousSymmetricMap (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι ↦ M) N, M [Sym^ι]→ₗ[R] N where

/-- Projection to `ContinuousMultilinearMap`s. -/
add_decl_doc ContinuousSymmetricMap.toContinuousMultilinearMap

/-- Projection to `SymmetricMap`s. -/
add_decl_doc ContinuousSymmetricMap.toSymmetricMap

@[inherit_doc]
notation M " [Sym^" ι "]→L[" R "] " N:100 => ContinuousSymmetricMap R M N ι

namespace ContinuousSymmetricMap

section Semiring

variable {R M M' N N' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : M [Sym^ι]→L[R] N)

theorem toContinuousMultilinearMap_injective :
    Injective (ContinuousSymmetricMap.toContinuousMultilinearMap :
      M [Sym^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι ↦ M) N)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem range_toContinuousMultilinearMap :
    Set.range
        (toContinuousMultilinearMap :
          M [Sym^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι ↦ M) N) =
      {f | ∀ (v : ι → M) (i j : ι), [DecidableEq ι] → f (v ∘ (Equiv.swap i j)) = f v} :=
  Set.ext fun f ↦ ⟨fun ⟨g, hg⟩ ↦ hg ▸ g.2, fun h ↦ ⟨⟨f, h⟩, rfl⟩⟩

instance funLike : FunLike (M [Sym^ι]→L[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' _ _ h := toContinuousMultilinearMap_injective <| DFunLike.ext' h

instance continuousMapClass : ContinuousMapClass (M [Sym^ι]→L[R] N) (ι → M) N where
  map_continuous f := f.cont

initialize_simps_projections ContinuousSymmetricMap (toFun → apply)

@[continuity]
theorem coe_continuous : Continuous f := f.cont

@[simp]
theorem coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f :=
  rfl

@[simp]
theorem coe_mk (f : ContinuousMultilinearMap R (fun _ : ι ↦ M) N) (h) : ⇑(mk f h) = f :=
  rfl

-- not a `simp` lemma because this projection is a reducible call to `mk`, so `simp` can prove
-- this lemma
theorem coe_toSymmetricMap : ⇑f.toSymmetricMap = f := rfl

@[ext]
theorem ext {f g : M [Sym^ι]→L[R] N} (H : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ H

theorem toSymmetricMap_injective :
    Injective (toSymmetricMap : (M [Sym^ι]→L[R] N) → (M [Sym^ι]→ₗ[R] N)) := fun f g h ↦
  DFunLike.ext' <| by convert DFunLike.ext'_iff.1 h

@[simp]
theorem range_toSymmetricMap :
    Set.range (toSymmetricMap : M [Sym^ι]→L[R] N → (M [Sym^ι]→ₗ[R] N)) =
      {f : M [Sym^ι]→ₗ[R] N | Continuous f} :=
  Set.ext fun f ↦ ⟨fun ⟨g, hg⟩ ↦ hg ▸ g.cont, fun h ↦ ⟨{ f with cont := h }, DFunLike.ext' rfl⟩⟩

@[simp]
theorem map_update_add [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
theorem map_update_smul [DecidableEq ι] (m : ι → M) (i : ι) (c : R) (x : M) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

@[grind =]
theorem map_eq_map_of_swap [DecidableEq ι] (v : ι → M) (i j : ι) : f (v ∘ Equiv.swap i j) = f v :=
  f.map_eq_map_of_swap' v i j

/-- Restrict the codomain of a continuous symmetric map to a submodule. -/
@[simps!]
def codRestrict (f : M [Sym^ι]→L[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) : M [Sym^ι]→L[R] p :=
  { f.toSymmetricMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }

instance : Zero (M [Sym^ι]→L[R] N) := ⟨⟨0, by simp⟩⟩

instance : Inhabited (M [Sym^ι]→L[R] N) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : M [Sym^ι]→L[R] N) = 0 :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_zero : (0 : M [Sym^ι]→L[R] N).toContinuousMultilinearMap = 0 :=
  rfl

@[simp]
theorem toSymmetricMap_zero : (0 : M [Sym^ι]→L[R] N).toSymmetricMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M] [Module A N]
  [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N] [DistribMulAction R'' N]
  [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

instance : SMul R' (M [Sym^ι]→L[A] N) :=
  ⟨fun c f ↦ ⟨c • f.1, fun v i j _ ↦ by simp [f.map_eq_map_of_swap v i j]⟩⟩

@[simp]
theorem coe_smul (f : M [Sym^ι]→L[A] N) (c : R') : ⇑(c • f) = c • ⇑f :=
  rfl

theorem smul_apply (f : M [Sym^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_smul (c : R') (f : M [Sym^ι]→L[A] N) :
    (c • f).toContinuousMultilinearMap = c • f.toContinuousMultilinearMap :=
  rfl

@[simp]
theorem toSymmetricMap_smul (c : R') (f : M [Sym^ι]→L[A] N) :
    (c • f).toSymmetricMap = c • f.toSymmetricMap :=
  rfl

instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' (M [Sym^ι]→L[A] N) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_comm _ _ _⟩

instance [SMul R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' (M [Sym^ι]→L[A] N) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_assoc _ _ _⟩

instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] :
    IsCentralScalar R' (M [Sym^ι]→L[A] N) :=
  ⟨fun _ _ ↦ ext fun _ ↦ op_smul_eq_smul _ _⟩

instance : MulAction R' (M [Sym^ι]→L[A] N) := fast_instance%
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ ↦ rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

instance : Add (M [Sym^ι]→L[R] N) :=
  ⟨fun f g ↦ ⟨f.1 + g.1, fun v i j _ ↦ by
    simp [f.map_eq_map_of_swap v i j, g.map_eq_map_of_swap v i j]⟩⟩

@[simp]
theorem coe_add : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp]
theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_add (f g : M [Sym^ι]→L[R] N) : (f + g).1 = f.1 + g.1 :=
  rfl

@[simp]
theorem toSymmetricMap_add (f g : M [Sym^ι]→L[R] N) :
    (f + g).toSymmetricMap = f.toSymmetricMap + g.toSymmetricMap :=
  rfl

instance addCommMonoid : AddCommMonoid (M [Sym^ι]→L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- Evaluation of a `ContinuousSymmetricMap` at a vector as an `AddMonoidHom`. -/
def applyAddHom (v : ι → M) : M [Sym^ι]→L[R] N →+ N :=
  ⟨⟨fun f ↦ f v, rfl⟩, fun _ _ ↦ rfl⟩

@[simp]
theorem sum_apply {α : Type*} (f : α → M [Sym^ι]→L[R] N) (m : ι → M) {s : Finset α} :
    (∑ a ∈ s, f a) m = ∑ a ∈ s, f a m :=
  map_sum (applyAddHom m) f s

/-- Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`. -/
@[simps]
def toMultilinearAddHom : M [Sym^ι]→L[R] N →+ ContinuousMultilinearMap R (fun _ : ι ↦ M) N :=
  ⟨⟨fun f ↦ f.1, rfl⟩, fun _ _ ↦ rfl⟩

end ContinuousAdd

/-- If `f` is a continuous symmetric map, then `f.toContinuousLinearMap m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
@[simps! apply]
def toContinuousLinearMap [DecidableEq ι] (m : ι → M) (i : ι) : M →L[R] N :=
  f.1.toContinuousLinearMap m i

/-- The Cartesian product of two continuous symmetric maps, as a continuous symmetric map. -/
@[simps!]
def prod (f : M [Sym^ι]→L[R] N) (g : M [Sym^ι]→L[R] N') : M [Sym^ι]→L[R] (N × N') :=
  ⟨f.1.prod g.1, fun v i j _ ↦ by
    simp [f.map_eq_map_of_swap v i j, g.map_eq_map_of_swap v i j]⟩

/-- Combine a family of continuous symmetric maps with the same domain and codomains `M' i` into a
continuous symmetric map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, M [Sym^ι]→L[R] M' i) : M [Sym^ι]→L[R] ∀ i, M' i :=
  ⟨ContinuousMultilinearMap.pi fun i ↦ (f i).1, by
    intro v i j _; ext j'; simp [(f j').map_eq_map_of_swap]⟩

@[simp]
theorem coe_pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [Sym^ι]→L[R] M' i) :
    ⇑(pi f) = fun m j ↦ f j m :=
  rfl

theorem pi_apply {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [Sym^ι]→L[R] M' i) (m : ι → M)
    (j : ι') : pi f m j = f j m :=
  rfl

section

variable (R M N)

/-- The natural equivalence between continuous linear maps from `M` to `N`
and continuous 1-multilinear symmetric maps from `M` to `N`. -/
@[simps! apply_apply symm_apply_apply apply_toContinuousMultilinearMap]
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M →L[R] N) ≃ M [Sym^ι]→L[R] N where
  toFun f :=
    { SymmetricMap.ofSubsingleton R M N i f with
      toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R M N i f }
  invFun f := (ContinuousMultilinearMap.ofSubsingleton R M N i).symm f.1
  right_inv _ := toContinuousMultilinearMap_injective <|
    (ContinuousMultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

@[simp]
theorem ofSubsingleton_toSymmetricMap [Subsingleton ι] (i : ι) (f : M →L[R] N) :
    (ofSubsingleton R M N i f).toSymmetricMap = SymmetricMap.ofSubsingleton R M N i f :=
  rfl

variable (ι) {N}

/-- The constant map is symmetric when `ι` is empty. -/
@[simps! toContinuousMultilinearMap apply]
def constOfIsEmpty [IsEmpty ι] (m : N) : M [Sym^ι]→L[R] N :=
  { SymmetricMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ ↦ M) m }

@[simp]
theorem constOfIsEmpty_toSymmetricMap [IsEmpty ι] (m : N) :
    (constOfIsEmpty R M ι m).toSymmetricMap = SymmetricMap.constOfIsEmpty R M ι m :=
  rfl

end

/-- If `g` is continuous symmetric and `f` is a continuous linear map, then `g (f m₁, ..., f mₙ)`
is again a continuous symmetric map, that we call `g.compContinuousLinearMap f`. -/
def compContinuousLinearMap (g : M [Sym^ι]→L[R] N) (f : M' →L[R] M) : M' [Sym^ι]→L[R] N :=
  { g.toSymmetricMap.compLinearMap (f : M' →ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ ↦ f }

@[simp]
theorem compContinuousLinearMap_apply (g : M [Sym^ι]→L[R] N) (f : M' →L[R] M) (m : ι → M') :
    g.compContinuousLinearMap f m = g (f ∘ m) :=
  rfl

/-- Composing a continuous symmetric map with a continuous linear map gives again a
continuous symmetric map. -/
def _root_.ContinuousLinearMap.compContinuousSymmetricMap (g : N →L[R] N') (f : M [Sym^ι]→L[R] N) :
    M [Sym^ι]→L[R] N' :=
  { (g : N →ₗ[R] N').compSymmetricMap f.toSymmetricMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]
theorem _root_.ContinuousLinearMap.compContinuousSymmetricMap_coe (g : N →L[R] N')
    (f : M [Sym^ι]→L[R] N) : ⇑(g.compContinuousSymmetricMap f) = g ∘ f :=
  rfl

/-- A continuous linear equivalence of domains
defines an equivalence between continuous symmetric maps.

This is available as a continuous linear isomorphism at
`ContinuousLinearEquiv.continuousSymmetricMapCongrLeft`.

This is `ContinuousSymmetricMap.compContinuousLinearMap` as an equivalence. -/
@[simps -fullyApplied apply]
def _root_.ContinuousLinearEquiv.continuousSymmetricMapCongrLeftEquiv (e : M ≃L[R] M') :
    M [Sym^ι]→L[R] N ≃ M' [Sym^ι]→L[R] N where
  toFun f := f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [Function.comp_def]
  right_inv f := by ext; simp [Function.comp_def]

/-- A continuous linear equivalence of codomains
defines an equivalence between continuous symmetric maps. -/
@[simps -fullyApplied apply]
def _root_.ContinuousLinearEquiv.continuousSymmetricMapCongrRightEquiv (e : N ≃L[R] N') :
    M [Sym^ι]→L[R] N ≃ M [Sym^ι]→L[R] N' where
  toFun := (e : N →L[R] N').compContinuousSymmetricMap
  invFun := (e.symm : N' →L[R] N).compContinuousSymmetricMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]

@[simp]
theorem _root_.ContinuousLinearEquiv.compContinuousSymmetricMap_coe
    (e : N ≃L[R] N') (f : M [Sym^ι]→L[R] N) :
    ⇑(e.continuousSymmetricMapCongrRightEquiv f) = e ∘ f :=
  rfl

/-- Continuous linear equivalences between domains and codomains
define an equivalence between the spaces of continuous symmetric maps. -/
def _root_.ContinuousLinearEquiv.continuousSymmetricMapCongrEquiv
    (e : M ≃L[R] M') (e' : N ≃L[R] N') : M [Sym^ι]→L[R] N ≃ M' [Sym^ι]→L[R] N' :=
  e.continuousSymmetricMapCongrLeftEquiv.trans e'.continuousSymmetricMapCongrRightEquiv

/-- `ContinuousSymmetricMap.pi` as an `Equiv`. -/
@[simps]
def piEquiv {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, TopologicalSpace (N i)]
    [∀ i, Module R (N i)] : (∀ i, M [Sym^ι]→L[R] N i) ≃ M [Sym^ι]→L[R] ∀ i, N i where
  toFun := pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] N i).compContinuousSymmetricMap f

/-- In the specific case of continuous symmetric maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of a symmetric map along the first variable. -/
theorem cons_add (f : ContinuousSymmetricMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous symmetric maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of a symmetric map along the first variable. -/
theorem vecCons_add (f : ContinuousSymmetricMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous symmetric maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a symmetric map along the first variable. -/
theorem cons_smul (f : ContinuousSymmetricMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m) :=
  f.toMultilinearMap.cons_smul m c x

/-- In the specific case of continuous symmetric maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a symmetric map along the first variable. -/
theorem vecCons_smul (f : ContinuousSymmetricMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m) :=
  f.toMultilinearMap.cons_smul m c x

theorem map_piecewise_add [DecidableEq ι] (m m' : ι → M) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/-- Additivity of a continuous symmetric map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι → Type*} [Fintype ι] [DecidableEq ι] (g' : ∀ i, α i → M) (A : ∀ i, Finset (α i))

/-- If `f` is continuous symmetric, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset :
    (f fun i ↦ ∑ j ∈ A i, g' i j) = ∑ r ∈ piFinset A, f fun i ↦ g' i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/-- If `f` is continuous symmetric, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [∀ i, Fintype (α i)] :
    (f fun i ↦ ∑ j, g' i j) = ∑ r : ∀ i, α i, f fun i ↦ g' i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [Module A M] [Module A N] [IsScalarTower R A M]
  [IsScalarTower R A N]

/-- Reinterpret a continuous `A`-symmetric map as a continuous `R`-symmetric map, if `A` is an
algebra over `R` and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : M [Sym^ι]→L[A] N) : M [Sym^ι]→L[R] N :=
  { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]
theorem coe_restrictScalars (f : M [Sym^ι]→L[A] N) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  (f g : M [Sym^ι]→L[R] N)

@[simp]
theorem map_update_sub [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _

@[simp]
theorem map_vecCons_sub {n} (f : M [Sym^Fin (n + 1)]→L[R] N) (x y : M) (v : Fin n → M) :
    f (Matrix.vecCons (x - y) v) = f (Matrix.vecCons x v) - f (Matrix.vecCons y v) := by
  rw [vecCons, ← Fin.update_cons_zero 0, map_update_sub]
  simp [vecCons]

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup N]

instance : Neg (M [Sym^ι]→L[R] N) :=
  ⟨fun f ↦ { -f.toSymmetricMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply (m : ι → M) : (-f) m = -f m :=
  rfl

instance : Sub (M [Sym^ι]→L[R] N) :=
  ⟨fun f g ↦
    { f.toSymmetricMap - g.toSymmetricMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

@[simp] theorem coe_sub : ⇑(f - g) = ⇑f - ⇑g := rfl

theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl

instance : AddCommGroup (M [Sym^ι]→L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end IsTopologicalAddGroup

end Ring

section CommSemiring

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  (f : M [Sym^ι]→L[R] N)

theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ι → M) (s : Finset ι) :
    f (s.piecewise (fun i ↦ c i • m i) m) = (∏ i ∈ s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous symmetric map along all coordinates at the same time,
writing `f (fun i ↦ c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ι → M) :
    (f fun i ↦ c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

/-- If two continuous `R`-symmetric maps from `R` are equal on 1, then they are equal.

This is the symmetric version of `ContinuousLinearMap.ext_ring`. -/
@[ext]
theorem ext_ring [Finite ι] [TopologicalSpace R] ⦃f g : R [Sym^ι]→L[R] M⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  toSymmetricMap_injective <| SymmetricMap.ext_ring h

end CommSemiring

section DistribMulAction

variable {R A M N ι : Type*} [Monoid R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [Module A M] [Module A N] [DistribMulAction R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

instance [ContinuousAdd N] : DistribMulAction R (M [Sym^ι]→L[A] N) := fast_instance%
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ ↦ rfl

end DistribMulAction

section Module

variable {R A M N ι : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-- The space of continuous symmetric maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : Module R (M [Sym^ι]→L[A] N) := fast_instance%
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ ↦
    rfl

/-- Linear map version of the map `toMultilinearMap` associating to a continuous symmetric map
the corresponding multilinear map. -/
@[simps]
def toContinuousMultilinearMapLinear :
    M [Sym^ι]→L[A] N →ₗ[R] ContinuousMultilinearMap A (fun _ : ι ↦ M) N where
  toFun := toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear map version of the map `toSymmetricMap`
associating to a continuous symmetric map the corresponding symmetric map. -/
@[simps -fullyApplied apply]
def toSymmetricMapLinear : (M [Sym^ι]→L[A] N) →ₗ[R] (M [Sym^ι]→ₗ[A] N) where
  toFun := toSymmetricMap
  map_add' := by simp
  map_smul' := by simp

/-- `ContinuousSymmetricMap.pi` as a `LinearEquiv`. -/
@[simps +simpRhs]
def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R (M' i)] [∀ i, ContinuousConstSMul R (M' i)] :
    (∀ i, M [Sym^ι]→L[A] M' i) ≃ₗ[R] M [Sym^ι]→L[A] ∀ i, M' i :=
  { piEquiv with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

end Module

section SMulRight

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N] [ContinuousSMul R N]
  (f : M [Sym^ι]→L[R] R) (z : N)

/-- Given a continuous `R`-symmetric map `f` taking values in `R`, `f.smulRight z` is the
continuous symmetric map sending `m` to `f m • z`. -/
@[simps! toContinuousMultilinearMap apply]
def smulRight : M [Sym^ι]→L[R] N :=
  { f.toSymmetricMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

end SMulRight

section Semiring

variable {R M M' N N' ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul R N] [AddCommMonoid N']
  [Module R N'] [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul R N']

/-- `ContinuousSymmetricMap.compContinuousLinearMap` as a bundled `LinearMap`. -/
@[simps]
def compContinuousLinearMapₗ (f : M →L[R] M') : (M' [Sym^ι]→L[R] N) →ₗ[R] (M [Sym^ι]→L[R] N) where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

variable (R M N N')

/-- `ContinuousLinearMap.compContinuousSymmetricMap` as a bundled bilinear map. -/
def _root_.ContinuousLinearMap.compContinuousSymmetricMapₗ :
    (N →L[R] N') →ₗ[R] (M [Sym^ι]→L[R] N) →ₗ[R] (M [Sym^ι]→L[R] N') :=
  LinearMap.mk₂ R ContinuousLinearMap.compContinuousSymmetricMap (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl) (fun f g₁ g₂ ↦ by ext1; apply f.map_add) fun c f g ↦ by ext1; simp

end Semiring

end ContinuousSymmetricMap

namespace ContinuousMultilinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [Fintype ι]
  [DecidableEq ι] (f : ContinuousMultilinearMap R (fun _ : ι ↦ M) N)

/-- Symmetrization of a continuous multilinear map. -/
@[simps -isSimp apply_toContinuousMultilinearMap]
def symmetrization : ContinuousMultilinearMap R (fun _ : ι ↦ M) N →+ M [Sym^ι]→L[R] N where
  toFun f :=
    { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, f.domDomCongr σ
      map_eq_map_of_swap' v i j _ := by
        simp only [MultilinearMap.toFun_eq_coe, coe_coe, sum_apply, domDomCongr_apply, comp_apply]
        rw [Finset.sum_bijective (Equiv.mulLeft (Equiv.swap i j))
          (Equiv.mulLeft (Equiv.swap i j)).bijective] <;> simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]

theorem symmetrization_apply_apply (v : ι → M) :
    symmetrization f v = ∑ σ : Equiv.Perm ι,  f (v ∘ σ) := by
  simp [symmetrization, Function.comp_def]

@[simp]
theorem symmetrization_apply_toSymmetricMap :
    (symmetrization f).toSymmetricMap = MultilinearMap.symmetrization f.1 := by
  ext v
  simp [symmetrization_apply_apply, MultilinearMap.symmetrization_apply, Function.comp_def]

end ContinuousMultilinearMap
