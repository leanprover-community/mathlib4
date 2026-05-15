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

@[simps]
noncomputable def δ :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N where
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

end IsIndex

lemma IsType₂.type₁_eq_of_δ_eq
    {s : Type₁.{u} k n} {t : (Subcomplex.unionProd.{u} Λ[m + 1, k.castSucc] ∂Δ[n]).N}
    (ht : IsType₂ t) (hst : s.δ = t) {d : ℕ} (hd : t.dim = d) :
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

end pairingCore

open pairingCore

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
    rw [← hu'.type₁_eq_of_δ_eq hs rfl,
      hu'.type₁_eq_of_δ_eq (h.symm.trans hs) rfl]
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

instance {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).IsRegular := sorry

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
