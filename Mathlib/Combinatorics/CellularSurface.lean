/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Cellular surfaces, CSS codes, and k = 2g

A `CellularSurface` encodes the combinatorial data of a 2-cell embedding of a graph
on a closed surface: vertices, edges with endpoints, and faces whose boundaries are
closed directed trails. The boundary operators ∂₁ (vertex-edge) and ∂₂ (edge-face)
are matrices over F₂, and the chain complex condition ∂₁ ∘ ∂₂ = 0 is proved from the
closed walk axiom.

The rank theorems `rank(∂₁) = V - 1` and `rank(∂₂) = F - 1` follow from kernel
characterisations: for connected graphs, `ker(∂₁ᵀ) = span{1}` over F₂.

A `SurfaceTiling` with genus g gives a CSS quantum error-correcting code encoding
`k = 2g` logical qubits: the first Betti number of the surface. This follows from
the rank theorems and Euler's formula `V - E + F = 2 - 2g`.

## Main definitions

* `CellularSurface` — combinatorial 2-cell embedding of a graph on a closed surface
* `CellularSurface.d1` — the boundary operator ∂₁ (vertex-edge incidence over F₂)
* `CellularSurface.d2` — the boundary operator ∂₂ (edge-face boundary over F₂)
* `SurfaceTiling` — a surface tiling with Euler characteristic `2 - 2g`
* `CSSFromTiling` — a CSS quantum code from a surface tiling

## Main results

* `CellularSurface.d1_mul_d2_eq_zero` — ∂₁ ∘ ∂₂ = 0
* `CellularSurface.d1_rank_eq` — rank(∂₁) = V - 1 for connected graphs
* `CellularSurface.d2_rank_eq` — rank(∂₂) = F - 1 for connected dual graphs
* `css_k_eq_2g` — the CSS surface code encodes 2g logical qubits
* `CellularSurface.css_k_eq_2g_from_surface` — end-to-end from combinatorial data

## References

* Breuckmann & Terhal, *Constructions and noise threshold of hyperbolic surface codes*,
  IEEE Trans. Inf. Theory 62(6), 2016, arXiv:1506.04029
* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

@[expose] public section

open Matrix Finset

attribute [local instance] ZMod.instField

/-! ## CellularSurface -/

/-- A `CellularSurface` is the combinatorial data of a 2-cell embedding of a
graph on a closed surface. Faces are given as closed directed trails:
ordered sequences of directed edges forming closed walks in the graph. -/
structure CellularSurface where
  /-- Number of vertices (0-cells) -/
  nV : ℕ
  /-- Number of edges (1-cells) -/
  nE : ℕ
  /-- Number of faces (2-cells) -/
  nF : ℕ
  /-- Source vertex of each edge -/
  edge_src : Fin nE → Fin nV
  /-- Target vertex of each edge -/
  edge_tgt : Fin nE → Fin nV
  /-- No loops: every edge has distinct endpoints -/
  edge_ne : ∀ e, edge_src e ≠ edge_tgt e
  /-- Number of edges bounding each face -/
  face_len : Fin nF → ℕ
  /-- Every face boundary is nonempty -/
  face_len_pos : ∀ f, 0 < face_len f
  /-- The sequence of edges traversed by face f's boundary -/
  face_edge : (f : Fin nF) → Fin (face_len f) → Fin nE
  /-- Traversal direction for each boundary step: `true` = src → tgt -/
  face_dir : (f : Fin nF) → Fin (face_len f) → Bool
  /-- Trail condition: no edge is traversed twice in a single face boundary -/
  face_inj : ∀ f, Function.Injective (face_edge f)
  /-- **Closed walk**: the end vertex of step `i` equals the start vertex of the
      cyclically next step. -/
  face_closed : ∀ (f : Fin nF) (i : Fin (face_len f)),
    let j : Fin (face_len f) :=
      ⟨(i.val + 1) % face_len f, Nat.mod_lt _ (face_len_pos f)⟩
    (if face_dir f i then edge_tgt (face_edge f i) else edge_src (face_edge f i)) =
    (if face_dir f j then edge_src (face_edge f j) else edge_tgt (face_edge f j))

namespace CellularSurface

variable (S : CellularSurface)

/-- Cyclic successor on face boundary indices. -/
def nextIdx (f : Fin S.nF) (i : Fin (S.face_len f)) : Fin (S.face_len f) :=
  ⟨(i.val + 1) % S.face_len f, Nat.mod_lt _ (S.face_len_pos f)⟩

/-- The starting vertex when traversing step `i` of face `f`'s boundary. -/
def stepStart (f : Fin S.nF) (i : Fin (S.face_len f)) : Fin S.nV :=
  if S.face_dir f i then S.edge_src (S.face_edge f i)
  else S.edge_tgt (S.face_edge f i)

/-- The ending vertex when traversing step `i` of face `f`'s boundary. -/
def stepEnd (f : Fin S.nF) (i : Fin (S.face_len f)) : Fin S.nV :=
  if S.face_dir f i then S.edge_tgt (S.face_edge f i)
  else S.edge_src (S.face_edge f i)

theorem stepEnd_eq_stepStart_next (f : Fin S.nF) (i : Fin (S.face_len f)) :
    S.stepEnd f i = S.stepStart f (S.nextIdx f i) :=
  S.face_closed f i

/-! ### Boundary operators over F₂ -/

/-- The boundary operator ∂₁: vertex–edge incidence matrix over F₂. -/
def d1 : Matrix (Fin S.nV) (Fin S.nE) (ZMod 2) :=
  fun v e => (if S.edge_src e = v then 1 else 0) + (if S.edge_tgt e = v then 1 else 0)

/-- The boundary operator ∂₂: edge–face boundary matrix over F₂. -/
def d2 : Matrix (Fin S.nE) (Fin S.nF) (ZMod 2) :=
  fun e f => ∑ i : Fin (S.face_len f), if S.face_edge f i = e then 1 else 0

/-! ### ∂₁ ∘ ∂₂ = 0 -/

theorem nextIdx_injective (f : Fin S.nF) : Function.Injective (S.nextIdx f) := by
  intro a b h
  simp only [nextIdx, Fin.mk.injEq] at h
  have ha := a.isLt; have hb := b.isLt
  ext
  by_cases ha' : a.val + 1 < S.face_len f <;> by_cases hb' : b.val + 1 < S.face_len f
  · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h; omega
  · rw [Nat.mod_eq_of_lt ha', show b.val + 1 = S.face_len f from by omega, Nat.mod_self] at h
    omega
  · rw [show a.val + 1 = S.face_len f from by omega, Nat.mod_self, Nat.mod_eq_of_lt hb'] at h
    omega
  · omega

theorem nextIdx_bijective (f : Fin S.nF) : Function.Bijective (S.nextIdx f) :=
  Finite.injective_iff_bijective.mp (S.nextIdx_injective f)

noncomputable def nextPerm (f : Fin S.nF) : Equiv.Perm (Fin (S.face_len f)) :=
  Equiv.ofBijective _ (S.nextIdx_bijective f)

theorem d1_eq_start_add_end (v : Fin S.nV) (f : Fin S.nF) (i : Fin (S.face_len f)) :
    S.d1 v (S.face_edge f i) =
      (if S.stepStart f i = v then 1 else 0) +
      (if S.stepEnd f i = v then 1 else 0) := by
  unfold d1 stepStart stepEnd
  rcases S.face_dir f i with _ | _ <;> simp [add_comm]

/-- **∂₁ ∘ ∂₂ = 0**: the chain complex condition for cellular surfaces over F₂. -/
theorem d1_mul_d2_eq_zero : S.d1 * S.d2 = 0 := by
  ext v f
  simp only [Matrix.mul_apply, d2, Matrix.zero_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have step2 : ∀ i : Fin (S.face_len f),
      ∑ e : Fin S.nE, S.d1 v e * (if S.face_edge f i = e then 1 else 0) =
      S.d1 v (S.face_edge f i) := by
    intro i
    conv_lhs =>
      arg 2; ext e
      rw [show S.d1 v e * (if S.face_edge f i = e then 1 else 0) =
          (if e = S.face_edge f i then S.d1 v e else 0) from by
        split_ifs with h1 h2 h2 <;> simp_all [eq_comm]]
    rw [Finset.sum_ite_eq']; simp [Finset.mem_univ]
  simp_rw [step2, S.d1_eq_start_add_end v f, Finset.sum_add_distrib]
  have step5 : ∀ i, (if S.stepEnd f i = v then (1 : ZMod 2) else 0) =
      (if S.stepStart f (S.nextIdx f i) = v then 1 else 0) := by
    intro i; rw [← S.stepEnd_eq_stepStart_next]
  simp_rw [step5]
  rw [show ∑ i, (if S.stepStart f (S.nextIdx f i) = v then (1 : ZMod 2) else 0) =
      ∑ i, (if S.stepStart f i = v then 1 else 0) from
    Equiv.sum_comp (S.nextPerm f) (fun j => if S.stepStart f j = v then 1 else 0)]
  have : ∀ (x : ZMod 2), x + x = 0 := by decide
  exact this _

/-! ### Rank theorems -/

theorem d1_col_sum_eq_zero (e : Fin S.nE) :
    ∑ v : Fin S.nV, S.d1 v e = 0 := by
  simp only [d1, Finset.sum_add_distrib]
  have hsum : ∀ (a : Fin S.nV),
      ∑ v : Fin S.nV, (if a = v then (1 : ZMod 2) else 0) = 1 := fun a => by
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)
      (fun b _ hne => if_neg (Ne.symm hne)), if_pos rfl]
  simp only [hsum]; decide

theorem one_mem_ker_d1T :
    (1 : Fin S.nV → ZMod 2) ∈ LinearMap.ker S.d1ᵀ.mulVecLin := by
  rw [LinearMap.mem_ker]; ext e
  simp only [mulVecLin_apply, mulVec, dotProduct, transpose_apply, Pi.zero_apply,
    Pi.one_apply, mul_one]
  exact S.d1_col_sum_eq_zero e

theorem one_ne_zero_fin (hV : 0 < S.nV) :
    (1 : Fin S.nV → ZMod 2) ≠ 0 := by
  intro h; exact absurd (congr_fun h ⟨0, hV⟩) (by simp)

theorem d1_rank_le (hV : 0 < S.nV) : S.d1.rank ≤ S.nV - 1 := by
  rw [← rank_transpose S.d1]
  have hrn := LinearMap.finrank_range_add_finrank_ker S.d1ᵀ.mulVecLin
  simp only [rank, Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrn ⊢
  have hker_ne : LinearMap.ker S.d1ᵀ.mulVecLin ≠ ⊥ := by
    rw [ne_eq, LinearMap.ker_eq_bot']; push Not
    exact ⟨1, (LinearMap.mem_ker.mp S.one_mem_ker_d1T), S.one_ne_zero_fin hV⟩
  have hker_pos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker S.d1ᵀ.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker_ne
  omega

/-- The underlying simple graph of a CellularSurface. -/
def toSimpleGraph : SimpleGraph (Fin S.nV) where
  Adj u v := ∃ e : Fin S.nE,
    (S.edge_src e = u ∧ S.edge_tgt e = v) ∨ (S.edge_src e = v ∧ S.edge_tgt e = u)
  symm u v := fun ⟨e, h⟩ => ⟨e, h.symm⟩
  loopless := ⟨fun v ⟨e, h⟩ => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact S.edge_ne e (h1.trans h2.symm)⟩

theorem d1T_mulVec_entry (x : Fin S.nV → ZMod 2) (e : Fin S.nE) :
    (S.d1ᵀ *ᵥ x) e = x (S.edge_src e) + x (S.edge_tgt e) := by
  simp only [mulVec, dotProduct, transpose_apply, d1, add_mul, Finset.sum_add_distrib]
  have hsum : ∀ (a : Fin S.nV),
      ∑ v : Fin S.nV, (if a = v then (1 : ZMod 2) else 0) * x v = x a := fun a => by
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)
      (fun b _ hne => by simp [Ne.symm hne])]; simp
  simp only [hsum]

theorem ker_d1T_edge_eq {x : Fin S.nV → ZMod 2}
    (hx : x ∈ LinearMap.ker S.d1ᵀ.mulVecLin) (e : Fin S.nE) :
    x (S.edge_src e) = x (S.edge_tgt e) := by
  have h := congr_fun (LinearMap.mem_ker.mp hx) e
  simp only [mulVecLin_apply, Pi.zero_apply] at h
  rw [S.d1T_mulVec_entry x e] at h
  have : ∀ (a b : ZMod 2), a + b = 0 → a = b := by decide
  exact this _ _ h

theorem walk_preserves_ker {x : Fin S.nV → ZMod 2}
    (hx : x ∈ LinearMap.ker S.d1ᵀ.mulVecLin)
    {u v : Fin S.nV} (w : S.toSimpleGraph.Walk u v) :
    x u = x v := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨e, h | h⟩ := hadj
    · have := S.ker_d1T_edge_eq hx e; rw [h.1, h.2] at this; exact this.trans ih
    · have := S.ker_d1T_edge_eq hx e; rw [h.1, h.2] at this; exact this.symm.trans ih

theorem ker_d1T_le_span_one (hconn : S.toSimpleGraph.Connected) :
    LinearMap.ker S.d1ᵀ.mulVecLin ≤ Submodule.span (ZMod 2) {1} := by
  intro x hx
  rw [Submodule.mem_span_singleton]
  have hV : 0 < S.nV := by obtain ⟨⟨_, hlt⟩⟩ := hconn.nonempty; omega
  have hconst : ∀ u v : Fin S.nV, x u = x v := fun u v =>
    S.walk_preserves_ker hx (hconn.preconnected u v).some
  exact ⟨x ⟨0, hV⟩, funext fun v => by
    simp [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, hconst ⟨0, hV⟩ v]⟩

theorem ker_d1T_finrank_eq_one (hconn : S.toSimpleGraph.Connected) (hV : 0 < S.nV) :
    Module.finrank (ZMod 2) (LinearMap.ker S.d1ᵀ.mulVecLin) = 1 := by
  have heq : LinearMap.ker S.d1ᵀ.mulVecLin =
      Submodule.span (ZMod 2) {(1 : Fin S.nV → ZMod 2)} :=
    le_antisymm (S.ker_d1T_le_span_one hconn)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr S.one_mem_ker_d1T)
  rw [heq]; exact finrank_span_singleton (S.one_ne_zero_fin hV)

/-- **rank(∂₁) = V - 1** for connected graphs. -/
theorem d1_rank_eq (hconn : S.toSimpleGraph.Connected) (hV : 1 < S.nV) :
    (S.d1.rank : ℤ) = S.nV - 1 := by
  have hle := S.d1_rank_le (by omega)
  have hge : S.nV - 1 ≤ S.d1.rank := by
    rw [← rank_transpose S.d1]
    have hrn := LinearMap.finrank_range_add_finrank_ker S.d1ᵀ.mulVecLin
    simp only [rank, Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrn ⊢
    rw [S.ker_d1T_finrank_eq_one hconn (by omega)] at hrn; omega
  omega

/-! ### Dual graph and rank(∂₂) -/

/-- The dual graph: faces as vertices, adjacent when sharing a boundary edge. -/
def toDualSimpleGraph : SimpleGraph (Fin S.nF) where
  Adj f1 f2 := f1 ≠ f2 ∧ ∃ e : Fin S.nE,
    (∃ i, S.face_edge f1 i = e) ∧ (∃ j, S.face_edge f2 j = e)
  symm _ _ := fun ⟨hne, e, h1, h2⟩ => ⟨hne.symm, e, h2, h1⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

theorem d2_entry (f : Fin S.nF) (e : Fin S.nE) :
    S.d2 e f = if ∃ i, S.face_edge f i = e then 1 else 0 := by
  simp only [d2]; split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun k _ hki =>
      if_neg (fun hk => hki (S.face_inj f (hk.trans hi.symm))))]; simp [hi]
  · push Not at h; exact Finset.sum_eq_zero (fun i _ => if_neg (h i))

theorem d2_rank_le (hF : 0 < S.nF) (htwo_vec : S.d2 *ᵥ 1 = 0) :
    S.d2.rank ≤ S.nF - 1 := by
  unfold rank
  have hrn := LinearMap.finrank_range_add_finrank_ker S.d2.mulVecLin
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrn ⊢
  have hker_ne : LinearMap.ker S.d2.mulVecLin ≠ ⊥ := by
    rw [ne_eq, LinearMap.ker_eq_bot']; push Not
    exact ⟨1, by rwa [show S.d2.mulVecLin 1 = S.d2 *ᵥ 1 from rfl],
      fun h => absurd (congr_fun h ⟨0, hF⟩) (by simp)⟩
  have : 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker S.d2.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker_ne
  omega

theorem ker_d2_dual_adj_eq {y : Fin S.nF → ZMod 2}
    (hy : y ∈ LinearMap.ker S.d2.mulVecLin)
    (htwo : ∀ e, (Finset.univ.filter fun f : Fin S.nF => S.d2 e f ≠ 0).card = 2)
    {f₁ f₂ : Fin S.nF} (hadj : S.toDualSimpleGraph.Adj f₁ f₂) :
    y f₁ = y f₂ := by
  obtain ⟨hne, e, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hadj
  have hd₁ : S.d2 e f₁ = 1 := by rw [S.d2_entry]; exact if_pos ⟨i, hi⟩
  have hd₂ : S.d2 e f₂ = 1 := by rw [S.d2_entry]; exact if_pos ⟨j, hj⟩
  obtain ⟨a, b, hab, hFe_eq⟩ := Finset.card_eq_two.mp (htwo e)
  have hf₁_mem : f₁ ∈ ({a, b} : Finset _) := by
    rw [← hFe_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hd₁]⟩
  have hf₂_mem : f₂ ∈ ({a, b} : Finset _) := by
    rw [← hFe_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hd₂]⟩
  have hker_e : ∑ f, S.d2 e f * y f = 0 := by
    have := congr_fun (LinearMap.mem_ker.mp hy) e
    simpa [mulVecLin_apply, mulVec, dotProduct] using this
  have hpair : y a + y b = 0 := by
    have hsplit : ∑ f, S.d2 e f * y f =
        ∑ f ∈ Finset.univ.filter (fun f => S.d2 e f ≠ 0), S.d2 e f * y f := by
      symm; apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hf
      rw [hf, zero_mul]
    rw [hsplit, hFe_eq, Finset.sum_pair hab] at hker_e
    have hzmod2 : ∀ (x : ZMod 2), x ≠ 0 → x = 1 := by decide
    have ha_ne := (Finset.mem_filter.mp (hFe_eq ▸ Finset.mem_insert_self a {b})).2
    have hb_ne := (Finset.mem_filter.mp (hFe_eq ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl)))).2
    rwa [hzmod2 _ ha_ne, hzmod2 _ hb_ne, one_mul, one_mul] at hker_e
  have hab_eq : y a = y b := by
    have : ∀ (x z : ZMod 2), x + z = 0 → x = z := by decide
    exact this _ _ hpair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf₁_mem hf₂_mem
  rcases hf₁_mem with rfl | rfl <;> rcases hf₂_mem with rfl | rfl
  · exact absurd rfl hne
  · exact hab_eq
  · exact hab_eq.symm
  · exact absurd rfl hne

theorem d2_mulVec_one_of_two_sides
    (htwo : ∀ e, (Finset.univ.filter fun f : Fin S.nF => S.d2 e f ≠ 0).card = 2) :
    S.d2 *ᵥ 1 = 0 := by
  ext e
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply]
  rw [show ∑ f, S.d2 e f = ∑ f ∈ Finset.univ.filter (fun f => S.d2 e f ≠ 0), S.d2 e f from by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf; simpa using hf]
  obtain ⟨a, b, hab, hFe_eq⟩ := Finset.card_eq_two.mp (htwo e)
  rw [hFe_eq, Finset.sum_pair hab]
  have hzmod2 : ∀ (x : ZMod 2), x ≠ 0 → x = 1 := by decide
  have ha := (Finset.mem_filter.mp (hFe_eq ▸ Finset.mem_insert_self a {b})).2
  have hb := (Finset.mem_filter.mp (hFe_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton.mpr rfl)))).2
  rw [hzmod2 _ ha, hzmod2 _ hb]; decide

/-- **rank(∂₂) = F - 1** for connected dual graphs with the two-sides condition. -/
theorem d2_rank_eq (hconn_dual : S.toDualSimpleGraph.Connected) (hF : 1 < S.nF)
    (htwo : ∀ e, (Finset.univ.filter fun f : Fin S.nF => S.d2 e f ≠ 0).card = 2) :
    (S.d2.rank : ℤ) = S.nF - 1 := by
  have hF_pos : 0 < S.nF := by omega
  have hmem : (1 : Fin S.nF → ZMod 2) ∈ LinearMap.ker S.d2.mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply]; exact S.d2_mulVec_one_of_two_sides htwo
  have heq : LinearMap.ker S.d2.mulVecLin =
      Submodule.span (ZMod 2) {(1 : Fin S.nF → ZMod 2)} :=
    le_antisymm
      (by intro y hy; rw [Submodule.mem_span_singleton]
          have hconst : ∀ a b : Fin S.nF, y a = y b := fun a b =>
            by induction (hconn_dual.preconnected a b).some with
               | nil => rfl
               | cons hadj _ ih => exact (S.ker_d2_dual_adj_eq hy htwo hadj).trans ih
          exact ⟨y ⟨0, hF_pos⟩, funext fun v => by
            simp [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, hconst ⟨0, hF_pos⟩ v]⟩)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hmem)
  have hle := S.d2_rank_le hF_pos (S.d2_mulVec_one_of_two_sides htwo)
  have hge : S.nF - 1 ≤ S.d2.rank := by
    have hker : Module.finrank (ZMod 2) (LinearMap.ker S.d2.mulVecLin) = 1 := by
      rw [heq]; exact finrank_span_singleton (fun h => absurd (congr_fun h ⟨0, hF_pos⟩) (by simp))
    have hrn := LinearMap.finrank_range_add_finrank_ker S.d2.mulVecLin
    simp only [rank, Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrn ⊢
    rw [hker] at hrn; omega
  omega

end CellularSurface

/-! ## CSS quantum codes from surface tilings -/

/-- A tiling of a closed orientable surface of genus `g`. -/
structure SurfaceTiling where
  /-- Number of vertices -/
  V : ℕ
  /-- Number of edges -/
  E : ℕ
  /-- Number of faces -/
  F : ℕ
  /-- Genus of the surface -/
  g : ℕ
  /-- The primal graph is non-degenerate -/
  hV : 0 < V
  /-- The dual graph is non-degenerate -/
  hF : 0 < F
  /-- Euler's formula -/
  euler : (V : ℤ) - E + F = 2 - 2 * g

/-- A CSS quantum code from a surface tiling. -/
structure CSSFromTiling (T : SurfaceTiling) where
  /-- X-check matrix (vertex-edge incidence) -/
  H_X : Matrix (Fin T.V) (Fin T.E) (ZMod 2)
  /-- Z-check matrix (face-edge incidence) -/
  H_Z : Matrix (Fin T.F) (Fin T.E) (ZMod 2)
  /-- CSS orthogonality -/
  orthogonal : H_X * H_Zᵀ = 0

namespace CSSFromTiling

variable {T : SurfaceTiling}

/-- The number of logical qubits: k = E - rank(H_X) - rank(H_Z). -/
noncomputable def k (css : CSSFromTiling T) : ℤ :=
  (T.E : ℤ) - css.H_X.rank - css.H_Z.rank

end CSSFromTiling

/-- **The CSS surface code theorem**: k = 2g. -/
theorem css_k_eq_2g (T : SurfaceTiling) (css : CSSFromTiling T)
    (hX : (css.H_X.rank : ℤ) = T.V - 1)
    (hZ : (css.H_Z.rank : ℤ) = T.F - 1) :
    css.k = 2 * T.g := by
  unfold CSSFromTiling.k
  linarith [T.euler]

/-! ## Assembly: CellularSurface → k = 2g -/

/-- Extract a `SurfaceTiling` from a `CellularSurface` with given genus. -/
def CellularSurface.toSurfaceTiling (S : CellularSurface) (g : ℕ)
    (hV : 0 < S.nV) (hF : 0 < S.nF)
    (euler : (S.nV : ℤ) - S.nE + S.nF = 2 - 2 * g) : SurfaceTiling where
  V := S.nV
  E := S.nE
  F := S.nF
  g := g
  hV := hV
  hF := hF
  euler := euler

/-- **End-to-end theorem**: a CellularSurface with connected primal and dual graphs
on a genus-g surface encodes exactly 2g logical qubits. -/
theorem CellularSurface.css_k_eq_2g_from_surface (S : CellularSurface) (g : ℕ)
    (hV : 1 < S.nV) (hF : 1 < S.nF)
    (euler : (S.nV : ℤ) - S.nE + S.nF = 2 - 2 * g)
    (hconn : S.toSimpleGraph.Connected)
    (hconn_dual : S.toDualSimpleGraph.Connected)
    (htwo : ∀ e, (Finset.univ.filter fun f : Fin S.nF => S.d2 e f ≠ 0).card = 2) :
    let T := S.toSurfaceTiling g (by omega) (by omega) euler
    let css : CSSFromTiling T :=
      { H_X := S.d1
        H_Z := S.d2ᵀ
        orthogonal := by rw [Matrix.transpose_transpose]; exact S.d1_mul_d2_eq_zero }
    css.k = 2 * g := by
  intro T css
  apply css_k_eq_2g
  · exact S.d1_rank_eq hconn hV
  · show (S.d2ᵀ.rank : ℤ) = S.nF - 1
    rw [rank_transpose]
    exact S.d2_rank_eq hconn_dual hF htwo
