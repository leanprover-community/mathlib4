/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.WeaklyPolyhedralLike

/-!
# A pairing for the pushout-product of a horn inclusion and a boundary inclusion

Let `l : Fin (m + 2)` and `n : ℕ`. In this file, we construct a regular pairing
for the subcomplex `unionProd Λ[m + 1, l] ∂Δ[n]` of `Δ[m + 1] ⊗ Δ[n]`. It follows
immediately that the inclusion of the union of `Λ[m + 1, l] ⊗ Δ[n]` and
`Δ[m + 1] ⊗ ∂Δ[n]` in `Δ[m + 1] ⊗ Δ[n]` is a (strong) anodyne extension
(which is inner when `l ≠ 0` and `l ≠ Fin.last _`).

The main construction works only when `l ≠ Fin.last _`, i.e. `l = k.castSucc`
for `k : Fin (m + 1)`: the remaining case is obtained using symmetries and
the case `k = 0`.

In order to do the case of `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]` for `k : Fin (m + 1)`,
we follow the proof by Sean Moss. Let us consider a nondegenerate `d`-simplex `x` of
`Δ[m + 1] ⊗ Δ[n]` which does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`.
`x` can be thought as a "walk" on the vertices `{0, ..., m + 1} × {0, ..., n}`
of `Δ[m + 1] ⊗ Δ[n]` (this is actually a strictly monotone map
`Fin (d + 1) → Fin (m + 2) × Fin (n + 1)`).
The condition that `x` does not belong to `unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
translates by saying that `x` reaches all the rows
(see the lemma `prodStdSimplex.pairingCore.mem_range_right`)
and all the columns expect the `k.castSucc`-th
(see the lemma `prodStdSimplex.pairingCore.mem_range_left`). This puts
constraints for each `i` on the vector from `x i` to `x (i + 1)`:
it has to be `(0, 1)`, `(1,0)`, `(1,1)`, `(2, 0)` or `(2, 1)` (the last two
cases may appear only if the `k.castSucc`-th column is skipped).
We introduce a predicate `IsIndex` taking `x` and `l : Fin (d + 1)` as arguments
and which is satisfied if `l` is the smallest `i` such that `x l` is
in the `k.succ` column, `l ≠ 0`, and the vector from `x (l.pred _)` to `x l`
is exactly `(1, 0)`.

The type (I) simplices for the pairing are those `x` such that there exists `l`
such that the predicate `IsIndex` hold. The corresponding type (II) simplex
is obtained by removing `x (l.pred _)` from the walk.


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

namespace prodStdSimplex

namespace pairingCore

variable {m : ℕ} {k : Fin (m + 1)} {n : ℕ}
  (x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N) {d : ℕ}

section

variable (hd : x.dim = d)

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. In particular,
`x` induces a strictly monotone map from `Fin (d + 1)` to
`{0, ..., m + 1} × {0, ..., n}`. We introduce a predicate on elements in
`Fin (d + 1)` which shall be satisfied for `l.succ` (`l : Fin d`)
if `x l.castSucc = (k.castSucc, t)` and `x l.succ = (k.succ, t)`
for some `t`. The nondegenerate simplices `x` such that there exists
such a `l` shall be the type (I) simplices of a pairing, and the
corresponding type (II) simplex shall be obtained by deleting `x l.castSucc`. -/
def IsIndex : Fin (d + 1) → Prop :=
  Fin.cases False (fun l ↦
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
    (x.cast hd).simplex.1 l.succ = k.succ ∧
    (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc)

@[simp]
lemma isIndex_zero : IsIndex x hd 0 ↔ False := Iff.rfl

lemma isIndex_succ (l : Fin d) :
    IsIndex x hd l.succ ↔
      (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
      (x.cast hd).simplex.1 l.succ = k.succ ∧
      (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := Iff.rfl

lemma mem_range_left (i : Fin (m + 2)) (hi : i ≠ k.castSucc) :
    i ∈ Set.range (x.cast hd).simplex.1 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto

lemma mem_range_right (i : Fin (n + 1)) :
    i ∈ Set.range (x.cast hd).simplex.2 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the finite subset of `Fin (d + 1)` consisting of those `l` such
that `x l` is of the form `(k.succ, _)`. -/
noncomputable def finset : Finset (Fin (d + 1)) :=
  { l : Fin (d + 1) | (x.cast hd).simplex.1 l = k.succ }

@[simp]
lemma mem_finset_iff (l : Fin (d + 1)) :
    dsimp% l ∈ finset x hd ↔ (x.cast hd).simplex.1 l = k.succ := by
  simp [finset]

lemma nonempty_finset : (finset x hd).Nonempty := by
  obtain ⟨i, hi⟩ := mem_range_left x hd k.succ (by grind)
  exact ⟨i, by simpa using hi⟩

/-- Let `x` be a nondegenerate `d`-simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the smallest `l : Fin (d + 1)` such that `x l` is of the form `(k.succ, _)`. -/
noncomputable def min : Fin (d + 1) := (finset x hd).min' (nonempty_finset x hd)

lemma simplex_fst_min : dsimp% (x.cast hd).simplex.1 (min x hd) = k.succ := by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i ≤ k.castSucc ↔ i < min x hd := by
  contrapose!
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | h := h.lt_or_eq
    · by_contra! h'
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h'.le
      dsimp at this
      rw [simplex_fst_min, ← not_lt] at this
      tauto
    · exact Finset.min'_le _ _ (by simpa using h.symm)
  · rw [Fin.castSucc_lt_iff_succ_le, ← simplex_fst_min x hd]
    exact stdSimplex.monotone_apply _ h

end

namespace IsIndex

section

variable {x} {hd : x.dim = d} {l : Fin d} (hl : IsIndex x hd l.succ)

include hl

lemma simplex_fst_castSucc :
    dsimp% (x.cast hd).simplex.1 l.castSucc = k.castSucc := hl.1

lemma simplex_fst_succ :
    dsimp% (x.cast hd).simplex.1 l.succ = k.succ := hl.2.1

lemma simplex_snd_succ :
    dsimp% (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc := hl.2.2

lemma succ_le_simplex_fst_iff (i : Fin (d + 1)) :
    dsimp% k.succ ≤ (x.cast hd).simplex.1 i ↔ l.succ ≤ i := by
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.simplex_fst_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.simplex_fst_succ]
    exact stdSimplex.monotone_apply _ hi

lemma simplex_fst_le_castSucc_iff (i : Fin (d + 1)) :
    dsimp% (x.cast hd).simplex.1 i ≤ k.castSucc ↔ i < l.succ := by
  rw [Fin.le_castSucc_iff, ← not_le, hl.succ_le_simplex_fst_iff, not_le]

lemma min_eq : min x hd = l.succ :=
  le_antisymm (Finset.min'_le _ _ (by simpa using hl.simplex_fst_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi ↦ by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_simplex_fst_iff, ← hi]))

lemma unique {l' : Fin d} (hl' : IsIndex x hd l'.succ) : l = l' := by
  rw [← Fin.succ_inj, ← hl.min_eq, hl'.min_eq]

end

section

variable {x} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

/-- The type (II) simplex obtained as a face of a type (I) simplex. -/
@[simps]
noncomputable def δ :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N where
  dim := d
  simplex := (Δ[m + 1] ⊗ Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    dsimp
    simp only [Subcomplex.mem_unionProd_iff, prod_δ_snd, mem_boundary_iff_notMem_range,
      Set.mem_range, stdSimplex.δ_apply, not_exists, prod_δ_fst, mem_horn_iff_notMem_range,
      ne_eq, exists_prop, not_or, not_forall, Decidable.not_not, not_and]
    refine ⟨fun j ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨i, hi⟩ := mem_range_right x hd j
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · refine ⟨l, ?_⟩
        rw [Fin.succAbove_castSucc_self, ← hi, ← hl.simplex_snd_succ]
        rfl
      · exact ⟨_, hi⟩
    · obtain ⟨i, hi⟩ := mem_range_left x hd j hj
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · exact (hj (by rw [← hi, hl.simplex_fst_castSucc])).elim
      · exact ⟨_, hi⟩

end

end IsIndex

variable (k n) in
/-- The type of type (I) simplices for the pairing -/
structure Type₁ where
  /-- the nondegenerate simplex -/
  x : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N
  /-- the dimension of the 1-codimensional face -/
  d : ℕ
  hd : x.dim = d + 1
  /-- the index attached to the type (II) simplex -/
  index : Fin (d + 1)
  isIndex : IsIndex x hd index.succ

variable {x} in
/-- Constructor for `Type₁ k n`. -/
@[simps]
def IsIndex.type₁ {hd : x.dim = d + 1} {i : Fin (d + 1)}
    (h : IsIndex x hd i.succ) : Type₁.{u} k n where
  x := x
  d := d
  hd := hd
  index := i
  isIndex := h

namespace Type₁

lemma ext_iff {s t : Type₁.{u} k n} :
    s = t ↔ s.x = t.x := by
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  obtain rfl : d = d' := by grind
  obtain rfl : l = l' := by grind
  rfl

/-- The type (II) simplex obtained as a face of a type (I) simplex. -/
noncomputable abbrev δ (s : Type₁.{u} k n) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N :=
  s.isIndex.δ

end Type₁

/-- Let `x` be a nondegenerate simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the property that `x` is a type (II) simplex for the pairing
`prodStdSimplex.pairingCore` that is constructed below. -/
def IsType₂ : Prop :=
  ∀ (d : ℕ) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

namespace IsType₂

variable (hx : IsType₂ x) {d : ℕ} (hd : x.dim = d)

/-- Auxiliary definition for `IsType₂.simplex`. This gives the underlying
data of the type (I) simplex reconstructed from a type (II) simplex. -/
noncomputable def φ (i : Fin (d + 2)) : Fin (m + 2) × Fin (n + 1) :=
  if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

@[simp]
lemma φ_castSucc :
    φ x hd (min x hd).castSucc = ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩ := by
  simp [φ]

@[simp]
lemma φ_succAbove (i : Fin (d + 1)) :
    φ x hd ((min x hd).castSucc.succAbove i) =
      objEquiv (x.cast hd).simplex i := by
  simp [φ]

lemma φ_of_ne (i : Fin (d + 2)) (hi : i ≠ (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex ((min x hd).predAbove i) :=
  if_neg hi

lemma φ_of_lt (i : Fin (d + 2)) (hi : i < (min x hd).castSucc) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.castPred (by grind)) := by
  rw [φ_of_ne _ _ _ hi.ne, Fin.predAbove_of_le_castSucc _ _ hi.le]

lemma φ_of_gt (i : Fin (d + 2)) (hi : (min x hd).castSucc < i) :
    φ x hd i = objEquiv (x.cast hd).simplex (i.pred (by aesop)) := by
  rw [φ_of_ne _ _ _ hi.ne', Fin.predAbove_of_castSucc_lt _ _ hi]

@[simp]
lemma φ_succ_snd : (φ x hd (min x hd).succ).2 = (φ x hd (min x hd).castSucc).2 := by
  have := φ_succAbove x hd (min x hd)
  rw [Fin.succAbove_castSucc_self] at this
  rw [this, φ_castSucc]
  rfl

@[simp]
lemma φ_succ_fst : (φ x hd (min x hd).succ).1 = k.succ := by
  have := φ_succAbove x hd (min x hd)
  rw [Fin.succAbove_castSucc_self] at this
  rw [this]
  exact simplex_fst_min x hd

variable {x}

include hx in
lemma strictMono_φ : StrictMono (φ x hd) := by
  have hx' := (prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i (min x hd)
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    rw [φ_of_lt _ _ _ (by grind), Fin.castPred_castSucc]
    rw [Fin.castSucc_lt_iff_succ_le] at hi
    obtain hi | hi :=  hi.lt_or_eq
    · rw [φ_of_lt _ _ _ (by grind)]
      exact hx' (Fin.lt_def.2 (by dsimp; grind))
    · rw [← Fin.castSucc_succ, hi, φ_castSucc]
      refine lt_of_le_of_ne ⟨?_, ?_⟩ ?_
      · dsimp
        rw [dsimp% objEquiv_apply_fst (x.cast hd).simplex,
          simplex_fst_le_castSucc_iff]
        grind
      · exact stdSimplex.monotone_apply _ (by dsimp; grind)
      · intro h
        rw [Prod.ext_iff] at h
        dsimp at h
        rw [dsimp% objEquiv_apply_fst (x.cast hd).simplex,
          dsimp% objEquiv_apply_snd (x.cast hd).simplex] at h
        obtain ⟨h₁, h₂⟩ := h
        apply hx _ hd i.succ
        rw [isIndex_succ]
        refine ⟨h₁, ?_, by aesop⟩
        have := φ_succAbove x hd (min x hd)
        rw [Fin.succAbove_castSucc_self] at this
        rw [← φ_succ_fst x hd, this, hi]
        rfl
  · exact Prod.lt_of_lt_of_le (by simp) (by simp)
  · rw [φ_of_gt _ _ _ (by grind), φ_of_gt _ _ _ (by grind)]
    exact hx' (by grind)

/-- The type (I) simplex reconstructed from a type (II) simplex. -/
noncomputable abbrev simplex : (Δ[m + 1] ⊗ Δ[n]) _⦋d + 1⦌ :=
  (objEquiv.{u}.symm ⟨φ x hd, (hx.strictMono_φ hd).monotone⟩)

@[simp]
lemma simplex_fst_apply (i : Fin (d + 2)) :
    (hx.simplex hd).1 i = (φ x hd i).1 := rfl

@[simp]
lemma simplex_snd_apply (i : Fin (d + 2)) :
    (hx.simplex hd).2 i = (φ x hd i).2 := rfl

lemma simplex_mem_nonDegenerate :
    hx.simplex hd ∈ (Δ[m + 1] ⊗ Δ[n]).nonDegenerate (d + 1) := by
  rw [nonDegenerate_iff_strictMono_objEquiv, Equiv.apply_symm_apply]
  exact hx.strictMono_φ hd

lemma δ_simplex :
    (Δ[m + 1] ⊗ Δ[n]).δ (min x hd).castSucc (hx.simplex hd) = (x.cast hd).simplex := by
  apply objEquiv.injective
  ext i : 2
  dsimp only [simplex]
  rw [objEquiv_δ_apply, Equiv.apply_symm_apply, OrderHom.coe_mk, φ_succAbove]
  dsimp
  rfl

lemma notMem_simplex :
    hx.simplex hd ∉ (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).obj _ := by
  refine fun h ↦ (x.cast hd).notMem ?_
  rw [← hx.δ_simplex hd]
  exact (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).map
    (SimplexCategory.δ (min x hd).castSucc).op h

set_option backward.isDefEq.respectTransparency false in
/-- The type (I) simplex reconstructed from a type (II) simplex. -/
@[simps]
noncomputable def type₁ : Type₁ k n where
  x :=
    Subcomplex.N.mk (hx.simplex hd) (hx.simplex_mem_nonDegenerate hd)
      (hx.notMem_simplex hd)
  d := d
  hd := rfl
  index := min x hd
  isIndex := by simp [isIndex_succ]

end IsType₂

namespace IsIndex

variable {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

set_option backward.isDefEq.respectTransparency false in
lemma min_δ : min hl.δ (show _ = d from rfl) = l := by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    (Finset.le_min' _ _ _ (fun y hy ↦ ?_))
  · simp only [mem_finset_iff]
    dsimp [δ, stdSimplex.δ_apply]
    rw [Fin.succAbove_castSucc_self, hl.simplex_fst_succ]
  · simp only [mem_finset_iff, S.cast_simplex_rfl, δ_simplex, Monoidal.tensorObj_obj,
      prod_δ_fst, stdSimplex.δ_apply] at hy
    by_contra!
    rw [Fin.succAbove_of_castSucc_lt _ _ (by grind)] at hy
    grind [(hl.succ_le_simplex_fst_iff y.castSucc).1 hy.symm.le]

set_option backward.isDefEq.respectTransparency false in
lemma isType₂_δ : IsType₂ hl.δ := by
  intro _ rfl t ht
  dsimp at t ht
  obtain ⟨t, rfl⟩ := Fin.eq_succ_of_ne_zero (i := t) (fun h ↦ by simp [h] at ht)
  obtain rfl : l = t.succ := by rw [← ht.min_eq, hl.min_δ]
  refine ((prodStdSimplex.nonDegenerate_iff_strictMono_objEquiv _).1
    (x.cast hd).nonDegenerate t.castSucc.castSucc_lt_succ).ne ?_
  simp only [isIndex_succ] at hl ht
  dsimp [stdSimplex.δ_apply] at hl ht ⊢
  aesop

set_option backward.isDefEq.respectTransparency false in
variable {x} in
lemma eq_of_isType₂_δ {u : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (hu : IsType₂ u) (i : Fin (d + 2))
    (hu' : S.mk u.simplex = S.mk (((Δ[m + 1] ⊗ Δ[n])).δ i (x.cast hd).simplex)) :
    i = l.castSucc ∨ i = l.succ := by
  obtain rfl : u.dim = d := congr_arg S.dim hu'
  rw [S.ext_iff] at hu'
  obtain hi | rfl | hi := lt_trichotomy i l.castSucc
  · obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := l) (by grind)
    refine (hu _ rfl l.succ ?_).elim
    rw [isIndex_succ]
    refine ⟨?_, ?_, ?_⟩ <;> dsimp <;>
      simp only [hu', Monoidal.tensorObj_obj, prod_δ_fst, prod_δ_snd,
        stdSimplex.δ_apply, Fin.succAbove_of_lt_succ i l.castSucc hi,
        Fin.succAbove_of_lt_succ i l.succ (by grind),
        hl.simplex_fst_succ]
    · exact hl.simplex_fst_castSucc
    · exact hl.simplex_snd_succ
  · exact Or.inl rfl
  · obtain rfl | hi := (Fin.castSucc_lt_iff_succ_le.1 hi).eq_or_lt
    · exact Or.inr rfl
    · obtain ⟨l, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := l) (by grind)
      refine (hu _ rfl l.succ ?_).elim
      simp [isIndex_succ, hu', stdSimplex.δ_apply,
        Fin.succAbove_of_castSucc_lt i l.castSucc (by grind),
        Fin.succAbove_of_castSucc_lt i l.succ (by grind),
        hl.simplex_fst_castSucc, hl.simplex_snd_succ, hl.simplex_fst_succ]

end IsIndex

lemma IsType₂.type₁_eq_of_δ_eq
    {t : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (ht : IsType₂ t) (s : Type₁.{u} k n) (hst : s.δ = t) {d : ℕ} (hd : t.dim = d) :
    ht.type₁ hd = s := by
  subst hst hd
  rw [Type₁.ext_iff, Subcomplex.N.ext_iff, N.ext_iff]
  rw [← s.x.toS.cast_eq_self s.hd, S.ext_iff']
  refine ⟨rfl, objEquiv.injective ?_⟩
  ext i : 2
  change φ s.δ rfl i = _
  let X : SSet.{u} := Δ[m + 1] ⊗ Δ[n]
  by_cases! hi : i = s.index.castSucc
  · subst hi
    conv_lhs => rw [← s.isIndex.min_δ]
    dsimp
    rw [φ_castSucc]
    ext : 1
    · exact s.isIndex.simplex_fst_castSucc.symm
    · change (s.x.cast s.hd).simplex.2
        (s.index.castSucc.succAbove (min s.δ rfl)) = _
      rw [s.isIndex.min_δ, Fin.succAbove_castSucc_self]
      exact s.isIndex.simplex_snd_succ
  · rw [← s.isIndex.min_δ] at hi
    rw [φ_of_ne _ rfl _ hi]
    change objEquiv (s.x.cast s.hd).simplex
      (s.index.castSucc.succAbove ((min s.δ rfl).predAbove i)) = _
    congr 1
    rw [← s.isIndex.min_δ]
    exact Fin.succAbove_predAbove hi

lemma Type₁.isType₂_δ (s : Type₁.{u} k n) : IsType₂ s.δ :=
  s.isIndex.isType₂_δ

variable {x} in
lemma IsIndex.δ_injective
    {d : ℕ} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)
    {y : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    {d' : ℕ} {hd' : y.dim = d' + 1} {l' : Fin (d' + 1)} (hl' : IsIndex y hd' l'.succ)
    (h : hl.δ = hl'.δ) :
    x = y := by
  have h₁ := hl.isType₂_δ.type₁_eq_of_δ_eq hl'.type₁ h.symm rfl
  have h₂ := hl.isType₂_δ.type₁_eq_of_δ_eq hl.type₁ rfl rfl
  exact congr_arg Type₁.x (h₂.symm.trans h₁)

end pairingCore

open pairingCore

/-- The underlying structure which gives a pairing for
`Subcomplex.unionProd Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`. -/
@[simps]
noncomputable def pairingCore {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).PairingCore where
  ι := Type₁.{u} k n
  dim s := s.d
  simplex s := (s.x.cast s.hd).simplex
  index s := s.index.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁' {s t} h := by
    rw [Type₁.ext_iff, Subcomplex.N.ext_iff, N.ext_iff]
    rwa [← s.x.toS.cast_eq_self s.hd, ← t.x.toS.cast_eq_self t.hd]
  injective_type₂' {s t} h := by
    replace h : s.δ = t.δ := by rwa [Subcomplex.N.ext_iff, N.ext_iff]
    generalize hs : s.δ = u
    have hu' : IsType₂ u := by simpa only [hs] using s.isType₂_δ
    rw [← hu'.type₁_eq_of_δ_eq _ hs rfl,
      hu'.type₁_eq_of_δ_eq _ (h.symm.trans hs) rfl]
  type₁_ne_type₂' s t hst := by
    replace hst : s.x = t.isIndex.δ := by
      rwa [Subcomplex.N.ext_iff, N.ext_iff, ← s.x.cast_eq_self s.hd]
    have := t.isIndex.isType₂_δ
    rw [← hst] at this
    exact this _ _ _ s.isIndex
  surjective' x := by
    by_cases hx : IsType₂ x
    · generalize hd : x.dim = d
      refine ⟨hx.type₁ hd, Or.inr ?_⟩
      rw [S.ext_iff']
      exact ⟨hd, (hx.δ_simplex hd).symm⟩
    · simp only [IsType₂, not_forall, not_not] at hx
      obtain ⟨d, hd, i, hx⟩ := hx
      obtain _ | d := d
      · fin_cases i
        simp at hx
      · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by rintro rfl; simp at hx)
        refine ⟨{
          x := x
          d := d
          hd := hd
          index := i
          isIndex := hx }, Or.inl ?_⟩
        dsimp
        rw [S.ext_iff']
        exact ⟨hd, rfl⟩

@[simp]
lemma type₁_pairingCore {m : ℕ} (k : Fin (m + 1)) {n : ℕ}
    (s : Type₁.{u} k n) :
    (pairingCore k n).type₁ s = s.x :=
  Subcomplex.N.cast_eq_self _ s.hd

set_option backward.isDefEq.respectTransparency false in
/-- A weak rank function for `pairingCore k n`. -/
noncomputable def weakRankFunction {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).WeakRankFunction ℕ where
  rank s := (finset s.x rfl).card
  lt := by
    intro ⟨s, d, hds, is, hs⟩ ⟨t, d', hdt, it, ht⟩ ⟨h₁, h₂⟩ h₃
    obtain ⟨ds, s, hs₁, hs₂, rfl⟩ := Subcomplex.N.mk_surjective s
    obtain ⟨dt, t, ht₁, ht₂, rfl⟩ := Subcomplex.N.mk_surjective t
    obtain rfl : d = d' := h₃
    obtain rfl : ds = d + 1 := hds
    obtain rfl : dt = d + 1 := hdt
    simp only [ne_eq, pairingCore_ι, Type₁.ext_iff] at h₁
    change N.mk ((Δ[m + 1] ⊗ Δ[n]).δ is.castSucc s) _ < N.mk t _ at h₂
    obtain ⟨f, hf, hδ⟩ := N.le_iff_exists_mono.1 h₂.le
    dsimp at f hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl | rfl := ht.eq_of_isType₂_δ hs.isType₂_δ i (by
      rw [S.ext_iff']
      exact ⟨rfl, hδ.symm⟩)
    · refine (h₁ (hs.δ_injective ht ?_)).elim
      rw [Subcomplex.N.ext_iff, N.ext_iff, S.ext_iff']
      exact ⟨rfl, hδ.symm⟩
    · let Ss := finset (Subcomplex.N.mk s hs₁ hs₂) rfl
      let St := finset (Subcomplex.N.mk t ht₁ ht₂) rfl
      let Sδ := finset hs.δ rfl
      replace hδ (i : Fin (d + 1)) :
          s.1 (is.castSucc.succAbove i) = t.1 (it.succ.succAbove i) :=
        DFunLike.congr_fun (congr_arg Prod.fst hδ.symm) i
      have hSs (i : Fin (d + 1)) : i ∈ Sδ ↔ is.castSucc.succAbove i ∈ Ss := by
        simp [Sδ, Ss, stdSimplex.δ_apply]
      have hSt (i : Fin (d + 1)) : i ∈ Sδ ↔ it.succ.succAbove i ∈ St := by
        simp [Sδ, St, stdSimplex.δ_apply, hδ]
      suffices Ss.card = Sδ.card ∧ St.card = Sδ.card + 1 by grind
      constructor
      · suffices Ss = Finset.image is.castSucc.succAbove Sδ by
          rw [this]
          exact Finset.card_image_of_injective _ Fin.succAbove_right_injective
        ext i
        obtain rfl | ⟨i, rfl⟩ := is.castSucc.eq_self_or_eq_succAbove i
        · have : is.castSucc ∉ Ss := fun h ↦ by
            have : s.1 is.castSucc ≤ k.castSucc := by
              simpa using (hs.simplex_fst_le_castSucc_iff is.castSucc).2 (by simp)
            simp only [Subcomplex.N.mk_dim, mem_finset_iff, S.cast_simplex_rfl,
              Subcomplex.N.mk_simplex, Ss] at h
            simp [h] at this
          simpa
        · simp [hSs]
      · suffices St = Finset.image it.succ.succAbove Sδ ∪ {it.succ} by
          rw [this, Finset.card_union_of_disjoint (by simp),
            Finset.card_image_of_injective _ Fin.succAbove_right_injective,
            Finset.card_singleton]
        ext i
        obtain rfl | ⟨i, rfl⟩ := it.succ.eq_self_or_eq_succAbove i
        · have : it.succ ∈ St := by
            simpa [St, mem_finset_iff] using ht.simplex_fst_succ
          simp [hSt, this]
        · simp [hSt]

instance {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).IsRegular :=
  (weakRankFunction.{u} k n).isRegular

set_option backward.isDefEq.respectTransparency false in
instance {m : ℕ} (k : Fin m) (n : ℕ) :
    (pairingCore.{u} k.succ n).IsInner where
  ne_zero (s : Type₁ k.succ n) h := by
    have : s.index = 0 := by rwa [← Fin.castSucc_eq_zero_iff]
    have hs : IsIndex s.x s.hd (Fin.succ 0) := by simpa [this] using s.isIndex
    obtain ⟨i, hi⟩ := mem_range_left s.x s.hd 0 (fun h ↦ by simp [Fin.ext_iff] at h)
    have := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.1 i.zero_le
    simp [dsimp% hs.simplex_fst_castSucc, dsimp% hi] at this
  ne_last := by simp

/-- A regular pairing for `Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]`
when `k : Fin (m + 1)` and `n : ℕ`. -/
noncomputable def pairing {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).Pairing :=
  if hk : k = Fin.last (m + 1) then
    (pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
      (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
        Functor.Monoidal.μIso opFunctor _ _) (by
          dsimp
          rw [hk, Subcomplex.preimage_comp,
            Subcomplex.preimage_op_unionProd,
            Subcomplex.preimage_unionProd,
            op_boundary, op_horn, Fin.rev_zero])
  else
    (pairingCore.{u} (k.castPred hk) n).pairing

lemma pairing_castSucc {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    pairing.{u} k.castSucc n = (pairingCore.{u} k n).pairing :=
  dif_neg (by grind)

set_option backward.isDefEq.respectTransparency false in
instance {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    (pairing.{u} k n).IsRegular := by
  by_cases! hk : k = Fin.last (m + 1)
  · subst hk
    dsimp [pairing]
    rw [dif_pos rfl]
    infer_instance
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [pairing_castSucc]
    infer_instance

instance {m : ℕ} (k : Fin m) (n : ℕ) :
    (pairing.{u} k.castSucc.succ n).IsInner := by
  simp only [← Fin.castSucc_succ, pairing_castSucc]
  infer_instance

end prodStdSimplex

end SSet
