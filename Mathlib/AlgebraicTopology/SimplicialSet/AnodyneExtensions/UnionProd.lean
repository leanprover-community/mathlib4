/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.WeaklyPolyhedralLike

/-!
# ...

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

variable {hd : x.dim = d} {l : Fin d} (hl : IsIndex x hd l.succ)

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

variable {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

@[simps]
noncomputable def δ :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N where
  dim := d
  simplex := (Δ[m + 1] ⊗ Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ _ (x.cast hd).nonDegenerate _
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

/-- Let `x` be a nondegenerate simplex of `Δ[m + 1] ⊗ Δ[n]` which
does not belong to `Λ[m + 1, k.castSucc].unionProd ∂Δ[n]`. This is
the property that `x` is a type (II) simplex for the pairing
`prodStdSimplex.pairingCore` that is constructed below. -/
def IsType₂ : Prop :=
  ∀ (d : ℕ) (hd : x.dim = d) (l : Fin (d + 1)), ¬ IsIndex x hd l

namespace IsType₂

variable (hx : IsType₂ x) {d : ℕ} (hd : x.dim = d)

noncomputable def φ (i : Fin (d + 1 + 1)) : Fin (m + 1 + 1) × Fin (n + 1) :=
  if i = (min x hd).castSucc
  then ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩
  else objEquiv (x.cast hd).simplex ((min x hd).predAbove i)

lemma φ_castSucc :
    φ x hd (min x hd).castSucc = ⟨k.castSucc, (x.cast hd).simplex.2 (min x hd)⟩ := by
  simp [φ]

lemma φ_succAbove (i : Fin (d + 1)) :
    φ x hd ((min x hd).castSucc.succAbove i) =
      objEquiv (x.cast hd).simplex i := by
  simp [φ]

lemma φ_succ_snd : (φ x hd (min x hd).succ).2 = (φ x hd (min x hd).castSucc).2 := by
  have := φ_succAbove x hd (min x hd)
  rw [Fin.succAbove_castSucc_self] at this
  rw [this, φ_castSucc]
  rfl

lemma φ_succ_fst : (φ x hd (min x hd).succ).1 = k.succ := by
  have := φ_succAbove x hd (min x hd)
  rw [Fin.succAbove_castSucc_self] at this
  rw [this]
  exact simplex_fst_min x hd

end IsType₂

namespace IsIndex

variable {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex x hd l.succ)

include hl

lemma isType₂_δ : IsType₂ hl.δ := sorry

end IsIndex

variable (k n) in
structure Type₁ where
  x : ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N
  d : ℕ
  hd : x.dim = d + 1
  index : Fin (d + 1)
  isIndex : IsIndex x hd index.succ

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

end Type₁

end pairingCore

open pairingCore

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
  injective_type₂' := sorry
  type₁_ne_type₂' s t hst := by
    replace hst : s.x = t.isIndex.δ := by
      rwa [Subcomplex.N.ext_iff, N.ext_iff, ← s.x.cast_eq_self s.hd]
    have := t.isIndex.isType₂_δ
    rw [← hst] at this
    exact this _ _ _ s.isIndex
  surjective' := sorry

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

end prodStdSimplex

end SSet
