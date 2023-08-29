/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.Basic

#align_import topology.algebra.module.linear_pmap from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Partially defined linear operators over topological vector spaces

We define basic notions of partially defined linear operators, which we call unbounded operators
for short.
In this file we prove all elementary properties of unbounded operators that do not assume that the
underlying spaces are normed.

## Main definitions

* `LinearPMap.IsClosed`: An unbounded operator is closed iff its graph is closed.
* `LinearPMap.IsClosable`: An unbounded operator is closable iff the closure of its graph is a
  graph.
* `LinearPMap.closure`: For a closable unbounded operator `f : LinearPMap R E F` the closure is
  the smallest closed extension of `f`. If `f` is not closable, then `f.closure` is defined as `f`.
* `LinearPMap.HasCore`: a submodule contained in the domain is a core if restricting to the core
  does not lose information about the unbounded operator.

## Main statements

* `LinearPMap.closable_iff_exists_closed_extension`: an unbounded operator is closable iff it has a
  closed extension.
* `LinearPMap.closable.exists_unique`: there exists a unique closure
* `LinearPMap.closureHasCore`: the domain of `f` is a core of its closure

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/


open Topology

variable {R E F : Type*}

variable [CommRing R] [AddCommGroup E] [AddCommGroup F]

variable [Module R E] [Module R F]

variable [TopologicalSpace E] [TopologicalSpace F]

namespace LinearPMap

/-! ### Closed and closable operators -/


/-- An unbounded operator is closed iff its graph is closed. -/
def IsClosed (f : E →ₗ.[R] F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))
#align linear_pmap.is_closed LinearPMap.IsClosed

variable [ContinuousAdd E] [ContinuousAdd F]

variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- An unbounded operator is closable iff the closure of its graph is a graph. -/
def IsClosable (f : E →ₗ.[R] F) : Prop :=
  ∃ f' : LinearPMap R E F, f.graph.topologicalClosure = f'.graph
#align linear_pmap.is_closable LinearPMap.IsClosable

/-- A closed operator is trivially closable. -/
theorem IsClosed.isClosable {f : E →ₗ.[R] F} (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.submodule_topologicalClosure_eq⟩
#align linear_pmap.is_closed.is_closable LinearPMap.IsClosed.isClosable

/-- If `g` has a closable extension `f`, then `g` itself is closable. -/
theorem IsClosable.leIsClosable {f g : E →ₗ.[R] F} (hf : f.IsClosable) (hfg : g ≤ f) :
    g.IsClosable := by
  cases' hf with f' hf
  -- ⊢ IsClosable g
  have : g.graph.topologicalClosure ≤ f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  -- ⊢ Submodule.topologicalClosure (graph g) = graph (Submodule.toLinearPMap (Subm …
  rw [Submodule.toLinearPMap_graph_eq]
  -- ⊢ ∀ (x : E × F), x ∈ Submodule.topologicalClosure (graph g) → x.fst = 0 → x.sn …
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this hx) hx'
  -- 🎉 no goals
#align linear_pmap.is_closable.le_is_closable LinearPMap.IsClosable.leIsClosable

/-- The closure is unique. -/
theorem IsClosable.existsUnique {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    ∃! f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph := by
  refine' exists_unique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph _
  -- ⊢ graph x✝¹ = graph x✝
  rw [← hy₁, ← hy₂]
  -- 🎉 no goals
#align linear_pmap.is_closable.exists_unique LinearPMap.IsClosable.existsUnique

open Classical

/-- If `f` is closable, then `f.closure` is the closure. Otherwise it is defined
as `f.closure = f`. -/
noncomputable def closure (f : E →ₗ.[R] F) : E →ₗ.[R] F :=
  if hf : f.IsClosable then hf.choose else f
#align linear_pmap.closure LinearPMap.closure

theorem closure_def {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure = hf.choose := by
  simp [closure, hf]
  -- 🎉 no goals
#align linear_pmap.closure_def LinearPMap.closure_def

theorem closure_def' {f : E →ₗ.[R] F} (hf : ¬f.IsClosable) : f.closure = f := by simp [closure, hf]
                                                                                 -- 🎉 no goals
#align linear_pmap.closure_def' LinearPMap.closure_def'

/-- The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `LinearPMap`). -/
theorem IsClosable.graph_closure_eq_closure_graph {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    f.graph.topologicalClosure = f.closure.graph := by
  rw [closure_def hf]
  -- ⊢ Submodule.topologicalClosure (graph f) = graph (Exists.choose hf)
  exact hf.choose_spec
  -- 🎉 no goals
#align linear_pmap.is_closable.graph_closure_eq_closure_graph LinearPMap.IsClosable.graph_closure_eq_closure_graph

/-- A `LinearPMap` is contained in its closure. -/
theorem le_closure (f : E →ₗ.[R] F) : f ≤ f.closure := by
  by_cases hf : f.IsClosable
  -- ⊢ f ≤ closure f
  · refine' le_of_le_graph _
    -- ⊢ graph f ≤ graph (closure f)
    rw [← hf.graph_closure_eq_closure_graph]
    -- ⊢ graph f ≤ Submodule.topologicalClosure (graph f)
    exact (graph f).le_topologicalClosure
    -- 🎉 no goals
  rw [closure_def' hf]
  -- 🎉 no goals
#align linear_pmap.le_closure LinearPMap.le_closure

theorem IsClosable.closure_mono {f g : E →ₗ.[R] F} (hg : g.IsClosable) (h : f ≤ g) :
    f.closure ≤ g.closure := by
  refine' le_of_le_graph _
  -- ⊢ graph (closure f) ≤ graph (closure g)
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  -- ⊢ Submodule.topologicalClosure (graph f) ≤ graph (closure g)
  rw [← hg.graph_closure_eq_closure_graph]
  -- ⊢ Submodule.topologicalClosure (graph f) ≤ Submodule.topologicalClosure (graph …
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)
  -- 🎉 no goals
#align linear_pmap.is_closable.closure_mono LinearPMap.IsClosable.closure_mono

/-- If `f` is closable, then the closure is closed. -/
theorem IsClosable.closure_isClosed {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosed := by
  rw [IsClosed, ← hf.graph_closure_eq_closure_graph]
  -- ⊢ _root_.IsClosed ↑(Submodule.topologicalClosure (graph f))
  exact f.graph.isClosed_topologicalClosure
  -- 🎉 no goals
#align linear_pmap.is_closable.closure_is_closed LinearPMap.IsClosable.closure_isClosed

/-- If `f` is closable, then the closure is closable. -/
theorem IsClosable.closureIsClosable {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosable :=
  hf.closure_isClosed.isClosable
#align linear_pmap.is_closable.closure_is_closable LinearPMap.IsClosable.closureIsClosable

theorem isClosable_iff_exists_closed_extension {f : E →ₗ.[R] F} :
    f.IsClosable ↔ ∃ (g : E →ₗ.[R] F) (_ : g.IsClosed), f ≤ g :=
  ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩
#align linear_pmap.is_closable_iff_exists_closed_extension LinearPMap.isClosable_iff_exists_closed_extension

/-! ### The core of a linear operator -/


/-- A submodule `S` is a core of `f` if the closure of the restriction of `f` to `S` is again `f`.-/
structure HasCore (f : E →ₗ.[R] F) (S : Submodule R E) : Prop where
  le_domain : S ≤ f.domain
  closure_eq : (f.domRestrict S).closure = f
#align linear_pmap.has_core LinearPMap.HasCore

theorem hasCore_def {f : E →ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) :
    (f.domRestrict S).closure = f :=
  h.2
#align linear_pmap.has_core_def LinearPMap.hasCore_def

/-- For every unbounded operator `f` the submodule `f.domain` is a core of its closure.

Note that we don't require that `f` is closable, due to the definition of the closure. -/
theorem closureHasCore (f : E →ₗ.[R] F) : f.closure.HasCore f.domain := by
  refine' ⟨f.le_closure.1, _⟩
  -- ⊢ closure (domRestrict (closure f) f.domain) = closure f
  congr
  -- ⊢ domRestrict (closure f) f.domain = f
  ext x y hxy
  -- ⊢ x ∈ (domRestrict (closure f) f.domain).domain ↔ x ∈ f.domain
  · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
    -- ⊢ x ∈ f.domain → x ∈ (closure f).domain
    intro hx
    -- ⊢ x ∈ (closure f).domain
    exact f.le_closure.1 hx
    -- 🎉 no goals
  let z : f.closure.domain := ⟨y.1, f.le_closure.1 y.2⟩
  -- ⊢ ↑(domRestrict (closure f) f.domain) x = ↑f y
  have hyz : (y : E) = z := by simp
  -- ⊢ ↑(domRestrict (closure f) f.domain) x = ↑f y
  rw [f.le_closure.2 hyz]
  -- ⊢ ↑(domRestrict (closure f) f.domain) x = ↑(closure f) z
  exact domRestrict_apply (hxy.trans hyz)
  -- 🎉 no goals
#align linear_pmap.closure_has_core LinearPMap.closureHasCore

/-! ### Topological properties of the inverse -/

section Inverse

variable {f : E →ₗ.[R] F}

/-- If `f` is invertible and closable as well as its closure being invertible, then
the graph of the inverse of the closure is given by the closure of the graph of the inverse. -/
theorem closure_inverse_graph (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.closure.inverse.graph = f.inverse.graph.topologicalClosure := by
  rw [inverse_graph hf, inverse_graph hcf, ← hf'.graph_closure_eq_closure_graph]
  -- ⊢ Submodule.map (LinearEquiv.prodComm R E F) (Submodule.topologicalClosure (gr …
  apply SetLike.ext'
  -- ⊢ ↑(Submodule.map (LinearEquiv.prodComm R E F) (Submodule.topologicalClosure ( …
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.prodComm_apply]
  -- ⊢ (fun a => Prod.swap a) '' _root_.closure ↑(graph f) = _root_.closure ((fun a …
  apply (image_closure_subset_closure_image continuous_swap).antisymm
  -- ⊢ _root_.closure (Prod.swap '' ↑(graph f)) ⊆ Prod.swap '' _root_.closure ↑(gra …
  have h1 := Set.image_equiv_eq_preimage_symm f.graph (LinearEquiv.prodComm R E F).toEquiv
  -- ⊢ _root_.closure (Prod.swap '' ↑(graph f)) ⊆ Prod.swap '' _root_.closure ↑(gra …
  have h2 := Set.image_equiv_eq_preimage_symm (_root_.closure f.graph)
    (LinearEquiv.prodComm R E F).toEquiv
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.prodComm_apply,
    LinearEquiv.coe_toEquiv_symm] at h1 h2
  rw [h1, h2]
  -- ⊢ _root_.closure (↑↑(LinearEquiv.symm (LinearEquiv.prodComm R E F)) ⁻¹' ↑(grap …
  apply continuous_swap.closure_preimage_subset
  -- 🎉 no goals

/-- Assuming that `f` is invertible and closable, then the closure is invertible if and only
if the inverse of `f` is closable. -/
theorem inverse_isClosable_iff (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable) :
    f.inverse.IsClosable ↔ LinearMap.ker f.closure.toFun = ⊥ := by
  constructor
  -- ⊢ IsClosable (inverse f) → LinearMap.ker (closure f).toFun = ⊥
  · intro ⟨f', h⟩
    -- ⊢ LinearMap.ker (closure f).toFun = ⊥
    rw [LinearMap.ker_eq_bot']
    -- ⊢ ∀ (m : { x // x ∈ (closure f).domain }), ↑(closure f).toFun m = 0 → m = 0
    intro ⟨x, hx⟩ hx'
    -- ⊢ { val := x, property := hx } = 0
    simp only [Submodule.mk_eq_zero]
    -- ⊢ x = 0
    rw [toFun_eq_coe, eq_comm, image_iff] at hx'
    -- ⊢ x = 0
    have : (0, x) ∈ graph f'
    -- ⊢ (0, x) ∈ graph f'
    · rw [← h, inverse_graph hf]
      -- ⊢ (0, x) ∈ Submodule.topologicalClosure (Submodule.map (LinearEquiv.prodComm R …
      rw [← hf'.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hx'
      apply image_closure_subset_closure_image continuous_swap
      -- ⊢ (0, x) ∈ Prod.swap '' _root_.closure ↑(graph f)
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      -- ⊢ ∃ a b, (a, b) ∈ _root_.closure ↑(graph f) ∧ b = 0 ∧ a = x
      exact ⟨x, 0, hx', rfl, rfl⟩
      -- 🎉 no goals
    exact graph_fst_eq_zero_snd f' this rfl
    -- 🎉 no goals
  · intro h
    -- ⊢ IsClosable (inverse f)
    use f.closure.inverse
    -- ⊢ Submodule.topologicalClosure (graph (inverse f)) = graph (inverse (closure f))
    exact (closure_inverse_graph hf hf' h).symm
    -- 🎉 no goals

/-- If `f` is invertible and closable, then taking the closure and the inverse commute. -/
theorem inverse_closure (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.inverse.closure = f.closure.inverse := by
  apply eq_of_eq_graph
  -- ⊢ graph (closure (inverse f)) = graph (inverse (closure f))
  rw [closure_inverse_graph hf hf' hcf,
    ((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

end Inverse

end LinearPMap
