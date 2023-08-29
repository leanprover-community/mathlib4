/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
import Mathlib.LinearAlgebra.Alternating
import Mathlib.Topology.Algebra.Module.Multilinear

/-!
# Continuous alternating multilinear maps

In this file we define bundled continuous alternating maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and alternating maps.

## Notation

`M [Λ^ι]→L[R] N`: notation for `R`-linear continuous alternating maps from `M` to `N`; the arguments
are indexed by `i : ι`.

## Keywords

multilinear map, alternating map, continuous
-/

open Function Matrix

open scoped BigOperators

/-- A continuous alternating map is a continuous map from `ι → M` to `N` that is

- multilinear : `f (update m i (c • x)) = c • f (update m i x)` and
  `f (update m i (x + y)) = f (update m i x) + f (update m i y)`;
- alternating : `f v = 0` whenever `v` has two equal coordinates.
-/
structure ContinuousAlternatingMap (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι => M) N, AlternatingMap R M N ι where

/-- Projection to `ContinuousMultilinearMap`s. -/
add_decl_doc ContinuousAlternatingMap.toContinuousMultilinearMap

/-- Projection to `AlternatingMap`s. -/
add_decl_doc ContinuousAlternatingMap.toAlternatingMap

notation M "[Λ^" ι "]→L[" R "]" N:100 => ContinuousAlternatingMap R M N ι

namespace ContinuousAlternatingMap

section Semiring

variable {R M M' N N' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : M [Λ^ι]→L[R] N)

theorem toContinuousMultilinearMap_injective :
    Injective (ContinuousAlternatingMap.toContinuousMultilinearMap :
      M [Λ^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι => M) N)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem range_toContinuousMultilinearMap :
    Set.range
        (toContinuousMultilinearMap :
          M [Λ^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι => M) N) =
      {f | ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → f v = 0} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

instance continuousMapClass : ContinuousMapClass (M [Λ^ι]→L[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' _ _ h := toContinuousMultilinearMap_injective <| FunLike.ext' h
  map_continuous f := f.cont

initialize_simps_projections ContinuousAlternatingMap (toFun → apply)

@[continuity]
theorem coe_continuous : Continuous f := f.cont

@[simp]
theorem coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f :=
  rfl

@[simp]
theorem coe_mk (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h) : ⇑(mk f h) = f :=
  rfl

-- not a `simp` lemma because this projection is a reducible call to `mk`, so `simp` can prove
-- this lemma
theorem coe_toAlternatingMap : ⇑f.toAlternatingMap = f := rfl

@[ext]
theorem ext {f g : M [Λ^ι]→L[R] N} (H : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ H

theorem ext_iff {f g : M [Λ^ι]→L[R] N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

theorem toAlternatingMap_injective :
    Injective (toAlternatingMap : M [Λ^ι]→L[R] N → AlternatingMap R M N ι) := fun f g h =>
  FunLike.ext' <| by convert FunLike.ext'_iff.1 h
                     -- 🎉 no goals

@[simp]
theorem range_toAlternatingMap :
    Set.range (toAlternatingMap : M [Λ^ι]→L[R] N → AlternatingMap R M N ι) =
      {f : AlternatingMap R M N ι | Continuous f} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, FunLike.ext' rfl⟩⟩

@[simp]
theorem map_add [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_add' m i x y

@[simp]
theorem map_smul [DecidableEq ι] (m : ι → M) (i : ι) (c : R) (x : M) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
  f.toAlternatingMap.map_eq_zero_of_not_injective v hv

/-- Restrict the codomain of a continuous alternating map to a submodule. -/
@[simps!]
def codRestrict (f : M [Λ^ι]→L[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) : M [Λ^ι]→L[R] p :=
  { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }

instance : Zero (M [Λ^ι]→L[R] N) :=
  ⟨⟨0, (0 : AlternatingMap R M N ι).map_eq_zero_of_eq⟩⟩

instance : Inhabited (M [Λ^ι]→L[R] N) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : M [Λ^ι]→L[R] N) = 0 :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_zero : (0 : M [Λ^ι]→L[R] N).toContinuousMultilinearMap = 0 :=
  rfl

@[simp]
theorem toAlternatingMap_zero : (0 : M [Λ^ι]→L[R] N).toAlternatingMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M] [Module A N]
  [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N] [DistribMulAction R'' N]
  [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

instance : SMul R' (M [Λ^ι]→L[A] N) :=
  ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
theorem coe_smul (f : M [Λ^ι]→L[A] N) (c : R') : ⇑(c • f) = c • ⇑f :=
  rfl

theorem smul_apply (f : M [Λ^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_smul (c : R') (f : M [Λ^ι]→L[A] N) :
    (c • f).toContinuousMultilinearMap = c • f.toContinuousMultilinearMap :=
  rfl

@[simp]
theorem toAlternatingMap_smul (c : R') (f : M [Λ^ι]→L[A] N) :
    (c • f).toAlternatingMap = c • f.toAlternatingMap :=
  rfl

instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' (M [Λ^ι]→L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

instance [SMul R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' (M [Λ^ι]→L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] : IsCentralScalar R' (M [Λ^ι]→L[A] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance : MulAction R' (M [Λ^ι]→L[A] N) :=
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

instance : Add (M [Λ^ι]→L[R] N) :=
  ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
theorem coe_add : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp]
theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_add (f g : M [Λ^ι]→L[R] N) : (f + g).1 = f.1 + g.1 :=
  rfl

@[simp]
theorem toAlternatingMap_add (f g : M [Λ^ι]→L[R] N) :
    (f + g).toAlternatingMap = f.toAlternatingMap + g.toAlternatingMap :=
  rfl

instance addCommMonoid : AddCommMonoid (M [Λ^ι]→L[R] N) :=
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/-- Evaluation of a `ContinuousAlternatingMap` at a vector as an `AddMonoidHom`. -/
def applyAddHom (v : ι → M) : M [Λ^ι]→L[R] N →+ N :=
  ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩

@[simp]
theorem sum_apply {α : Type*} (f : α → M [Λ^ι]→L[R] N) (m : ι → M) {s : Finset α} :
    (∑ a in s, f a) m = ∑ a in s, f a m :=
  (applyAddHom m).map_sum f s

/-- Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`. -/
@[simps]
def toMultilinearAddHom : M [Λ^ι]→L[R] N →+ ContinuousMultilinearMap R (fun _ : ι => M) N :=
  ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩

end ContinuousAdd

/-- If `f` is a continuous alternating map, then `f.toContinuousLinearMap m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
@[simps! apply]
def toContinuousLinearMap [DecidableEq ι] (m : ι → M) (i : ι) : M →L[R] N :=
  f.1.toContinuousLinearMap m i

/-- The cartesian product of two continuous alternating maps, as a continuous alternating map. -/
@[simps!]
def prod (f : M [Λ^ι]→L[R] N) (g : M [Λ^ι]→L[R] N') : M [Λ^ι]→L[R] (N × N') :=
  ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩

/-- Combine a family of continuous alternating maps with the same domain and codomains `M' i` into a
continuous alternating map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, M [Λ^ι]→L[R] M' i) : M [Λ^ι]→L[R] ∀ i, M' i :=
  ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩

@[simp]
theorem coe_pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [Λ^ι]→L[R] M' i) :
    ⇑(pi f) = fun m j => f j m :=
  rfl

theorem pi_apply {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [Λ^ι]→L[R] M' i) (m : ι → M)
    (j : ι') : pi f m j = f j m :=
  rfl

section

variable (R M)

/-- The evaluation map from `ι → M` to `M` is alternating at a given `i` when `ι` is subsingleton.
-/
@[simps! toContinuousMultilinearMap apply]
def ofSubsingleton [Subsingleton ι] (i' : ι) : M [Λ^ι]→L[R] M :=
  { AlternatingMap.ofSubsingleton R _ i' with
    toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R _ i' }

@[simp]
theorem ofSubsingleton_toAlternatingMap [Subsingleton ι] (i' : ι) :
    (ofSubsingleton R M i').toAlternatingMap = AlternatingMap.ofSubsingleton R M i' :=
  rfl

variable (ι)

/-- The constant map is alternating when `ι` is empty. -/
@[simps! toContinuousMultilinearMap apply]
def constOfIsEmpty [IsEmpty ι] (m : N) : M [Λ^ι]→L[R] N :=
  { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }

@[simp]
theorem constOfIsEmpty_toAlternatingMap [IsEmpty ι] (m : N) :
    (constOfIsEmpty R M ι m).toAlternatingMap = AlternatingMap.constOfIsEmpty R M ι m :=
  rfl

end

/-- If `g` is continuous alternating and `f` is a continuous linear map, then `g (f m₁, ..., f mₙ)`
is again a continuous alternating map, that we call `g.compContinuousLinearMap f`. -/
def compContinuousLinearMap (g : M [Λ^ι]→L[R] N) (f : M' →L[R] M) : M' [Λ^ι]→L[R] N :=
  { g.toAlternatingMap.compLinearMap (f : M' →ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }

@[simp]
theorem compContinuousLinearMap_apply (g : M [Λ^ι]→L[R] N) (f : M' →L[R] M) (m : ι → M') :
    g.compContinuousLinearMap f m = g (f ∘ m) :=
  rfl

/-- Composing a continuous alternating map with a continuous linear map gives again a
continuous alternating map. -/
def _root_.ContinuousLinearMap.compContinuousAlternatingMap (g : N →L[R] N') (f : M [Λ^ι]→L[R] N) :
    M [Λ^ι]→L[R] N' :=
  { (g : N →ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe (g : N →L[R] N')
    (f : M [Λ^ι]→L[R] N) : ⇑(g.compContinuousAlternatingMap f) = g ∘ f :=
  rfl

/-- A continuous linear equivalence of domains defines an equivalence between continuous
alternating maps. -/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapComp (e : M ≃L[R] M') :
    M [Λ^ι]→L[R] N ≃ M' [Λ^ι]→L[R] N where
  toFun f := f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [(· ∘ ·)]
                   -- ⊢ ↑((fun f => compContinuousLinearMap f ↑e) ((fun f => compContinuousLinearMap …
                        -- 🎉 no goals
  right_inv f := by ext; simp [(· ∘ ·)]
                    -- ⊢ ↑((fun f => compContinuousLinearMap f ↑(ContinuousLinearEquiv.symm e)) ((fun …
                         -- 🎉 no goals

/-- A continuous linear equivalence of codomains defines an equivalence between continuous
alternating maps. -/
def _root_.ContinuousLinearEquiv.compContinuousAlternatingMap (e : N ≃L[R] N') :
    M [Λ^ι]→L[R] N ≃ M [Λ^ι]→L[R] N' where
  toFun := (e : N →L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' →L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
                   -- ⊢ ↑(ContinuousLinearMap.compContinuousAlternatingMap (↑(ContinuousLinearEquiv. …
                        -- 🎉 no goals
  right_inv f := by ext; simp [(· ∘ ·)]
                    -- ⊢ ↑(ContinuousLinearMap.compContinuousAlternatingMap (↑e) (ContinuousLinearMap …
                         -- 🎉 no goals

@[simp]
theorem _root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe
    (e : N ≃L[R] N') (f : M [Λ^ι]→L[R] N) : ⇑(e.compContinuousAlternatingMap f) = e ∘ f :=
  rfl

/-- Continuous linear equivalences between domains and codomains define an equivalence between the
spaces of continuous alternating maps. -/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongr (e : M ≃L[R] M') (e' : N ≃L[R] N') :
    M [Λ^ι]→L[R] N ≃ M' [Λ^ι]→L[R] N' :=
  e.continuousAlternatingMapComp.trans e'.compContinuousAlternatingMap

/-- `ContinuousAlternatingMap.pi` as an `Equiv`. -/
@[simps]
def piEquiv {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, TopologicalSpace (N i)]
    [∀ i, Module R (N i)] : (∀ i, M [Λ^ι]→L[R] N i) ≃ M [Λ^ι]→L[R] ∀ i, N i where
  toFun := pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] N i).compContinuousAlternatingMap f
  left_inv f := by ext; rfl
                   -- ⊢ ↑((fun f i => ContinuousLinearMap.compContinuousAlternatingMap (ContinuousLi …
                        -- 🎉 no goals
  right_inv f := by ext; rfl
                    -- ⊢ ↑(pi ((fun f i => ContinuousLinearMap.compContinuousAlternatingMap (Continuo …
                         -- 🎉 no goals

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of an alternating map along the first variable. -/
theorem cons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of an alternating map along the first variable. -/
theorem vecCons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of an alternating map along the first variable. -/
theorem cons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m) :=
  f.toMultilinearMap.cons_smul m c x

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of an alternating map along the first variable. -/
theorem vecCons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m) :=
  f.toMultilinearMap.cons_smul m c x

theorem map_piecewise_add [DecidableEq ι] (m m' : ι → M) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/-- Additivity of a continuous alternating map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι → Type*} [Fintype ι] [DecidableEq ι] (g' : ∀ i, α i → M) (A : ∀ i, Finset (α i))

/-- If `f` is continuous alternating, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset :
    (f fun i => ∑ j in A i, g' i j) = ∑ r in piFinset A, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/-- If `f` is continuous alternating, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g' i j) = ∑ r : ∀ i, α i, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [Module A M] [Module A N] [IsScalarTower R A M]
  [IsScalarTower R A N]

/-- Reinterpret a continuous `A`-alternating map as a continuous `R`-alternating map, if `A` is an
algebra over `R` and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : M [Λ^ι]→L[A] N) : M [Λ^ι]→L[R] N :=
  { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]
theorem coe_restrictScalars (f : M [Λ^ι]→L[A] N) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable {R M M' N N' ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [AddCommGroup N] [Module R N]
  [TopologicalSpace N] [AddCommGroup N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : M [Λ^ι]→L[R] N)

@[simp]
theorem map_sub [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_sub _ _ _ _

section TopologicalAddGroup

variable [TopologicalAddGroup N]

instance : Neg (M [Λ^ι]→L[R] N) :=
  ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply (m : ι → M) : (-f) m = -f m :=
  rfl

instance : Sub (M [Λ^ι]→L[R] N) :=
  ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

@[simp] theorem coe_sub : ⇑(f - g) = ⇑f - ⇑g := rfl

theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl

instance : AddCommGroup (M [Λ^ι]→L[R] N) :=
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end TopologicalAddGroup

end Ring

section CommSemiring

variable {R M M' N N' ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : M [Λ^ι]→L[R] N)

theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ι → M) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous alternating map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ι → M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

end CommSemiring

section DistribMulAction

variable {R A M N ι : Type*} [Monoid R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [Module A M] [Module A N] [DistribMulAction R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

instance [ContinuousAdd N] : DistribMulAction R (M [Λ^ι]→L[A] N) :=
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

end DistribMulAction

section Module

variable {R A M N ι : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-- The space of continuous alternating maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : Module R (M [Λ^ι]→L[A] N) :=
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

/-- Linear map version of the map `toMultilinearMap` associating to a continuous alternating map
the corresponding multilinear map. -/
@[simps]
def toContinuousMultilinearMapLinear :
    M [Λ^ι]→L[A] N →ₗ[R] ContinuousMultilinearMap A (fun _ : ι => M) N where
  toFun := toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ContinuousAlternatingMap.pi` as a `LinearEquiv`. -/
@[simps (config := { simpRhs := true })]
def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R (M' i)] [∀ i, ContinuousConstSMul R (M' i)] :
    (∀ i, M [Λ^ι]→L[A] M' i) ≃ₗ[R] M [Λ^ι]→L[A] ∀ i, M' i :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Module

section SmulRight

variable {R A M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N] [ContinuousSMul R N]
  (f : M [Λ^ι]→L[R] R) (z : N)

/-- Given a continuous `R`-alternating map `f` taking values in `R`, `f.smulRight z` is the
continuous alternating map sending `m` to `f m • z`. -/
@[simps! toContinuousMultilinearMap apply]
def smulRight : M [Λ^ι]→L[R] N :=
  { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

end SmulRight

section Semiring

variable {R M M' N N' ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul R N] [AddCommMonoid N']
  [Module R N'] [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul R N']

/-- `ContinuousAlternatingMap.compContinuousLinearMap` as a bundled `LinearMap`. -/
@[simps]
def compContinuousLinearMapₗ (f : M →L[R] M') : (M' [Λ^ι]→L[R] N) →ₗ[R] (M [Λ^ι]→L[R] N) where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
                      -- ⊢ ↑((fun g => compContinuousLinearMap g f) (g + g')) x✝ = ↑((fun g => compCont …
                           -- 🎉 no goals
  map_smul' c g := by ext; simp
                      -- ⊢ ↑(AddHom.toFun { toFun := fun g => compContinuousLinearMap g f, map_add' :=  …
                           -- 🎉 no goals

variable (R M N N')

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled bilinear map. -/
def _root_.ContinuousLinearMap.compContinuousAlternatingMapₗ :
    (N →L[R] N') →ₗ[R] (M [Λ^ι]→L[R] N) →ₗ[R] (M [Λ^ι]→L[R] N') :=
  LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun f₁ f₂ g => rfl)
    (fun c f g => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp
                                          -- ⊢ ↑(ContinuousLinearMap.compContinuousAlternatingMap f (g₁ + g₂)) x✝ = ↑(Conti …
                                                -- 🎉 no goals
                                                                                 -- ⊢ ↑(ContinuousLinearMap.compContinuousAlternatingMap f (c • g)) x✝ = ↑(c • Con …
                                                                                       -- 🎉 no goals

end Semiring

end ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [TopologicalAddGroup N] [Fintype ι]
  [DecidableEq ι] (f g : ContinuousMultilinearMap R (fun _ : ι => M) N)

/-- Alternatization of a continuous multilinear map. -/
@[simps (config := { isSimp := false }) apply_toContinuousMultilinearMap]
def alternatization : ContinuousMultilinearMap R (fun _ : ι => M) N →+ M [Λ^ι]→L[R] N where
  toFun f :=
    { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
                  -- ⊢ ↑((fun f => { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, ↑Equiv.Perm. …
                       -- 🎉 no goals
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]
                     -- ⊢ ↑(ZeroHom.toFun { toFun := fun f => { toContinuousMultilinearMap := ∑ σ : Eq …
                          -- 🎉 no goals

theorem alternatization_apply_apply (v : ι → M) :
    alternatization f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) := by
  simp [alternatization, (· ∘ ·)]
  -- 🎉 no goals

@[simp]
theorem alternatization_apply_toAlternatingMap :
    (alternatization f).toAlternatingMap = MultilinearMap.alternatization f.1 := by
  ext v
  -- ⊢ ↑(ContinuousAlternatingMap.toAlternatingMap (↑alternatization f)) v = ↑(↑Mul …
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, (· ∘ ·)]
  -- 🎉 no goals

end ContinuousMultilinearMap
