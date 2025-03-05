/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Fintype
-- import Mathlib.Analysis.Analytic.Within
-- import Mathlib.Analysis.Calculus.FDeriv.Analytic
-- import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Faa di Bruno formula

The Faa di Bruno formula gives the iterated derivative of `g ∘ f` in terms of those of
`g` and `f`. It is expressed in terms of partitions `I` of `{0, ..., n-1}`. For such a
partition, denote by `k` its number of parts, write the parts as `I₀, ..., Iₖ₋₁` ordered so
that `max I₀ < ... < max Iₖ₋₁`, and let `iₘ` be the number of elements of `Iₘ`. Then
`D^n (g ∘ f) (x) (v₀, ..., vₙ₋₁) =
  ∑_{I partition of {0, ..., n-1}}
    D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))`
where by `v_{Iₘ}` we mean the vectors `vᵢ` with indices in `Iₘ`, i.e., the composition of `v`
with the increasing embedding of `Fin iₘ` into `Fin n` with range `Iₘ`.

For instance, for `n = 2`, there are 2 partitions of `{0, 1}`, given by `{0}, {1}` and `{0, 1}`,
and therefore
`D^2(g ∘ f) (x) (v₀, v₁) = D^2 g (f x) (Df (x) v₀, Df (x) v₁) + Dg (f x) (D^2f (x) (v₀, v₁))`.

The formula is straightforward to prove by induction, as differentiating
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` gives a sum
with `k + 1` terms where one differentiates either `D^k g (f x)`, or one of the `D^{iₘ} f (x)`,
amounting to adding to the partition `I` either a new atom `{-1}` to its left, or extending `Iₘ`
by adding `-1` to it. In this way, one obtains bijectively all partitions of `{-1, ..., n}`,
and the proof can go on (up to relabelling).

The main difficulty is to write things down in a precise language, namely to write
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` as a continuous multilinear
map of the `vᵢ`. For this, instead of working with partitions of `{0, ..., n-1}` and ordering their
parts, we work with partitions in which the ordering is part of the data -- this is equivalent,
but much more convenient to implement. We call these `OrderedFinpartition n`.

Note that the implementation of `OrderedFinpartition` is very specific to the Faa di Bruno formula:
as testified by the formula above, what matters is really the embedding of the parts in `Fin n`,
and moreover the parts have to be ordered by `max I₀ < ... < max Iₖ₋₁` for the formula to hold
in the general case where the iterated differential might not be symmetric. The defeqs with respect
to `Fin.cons` are also important when doing the induction. For this reason, we do not expect this
class to be useful beyond the Faa di Bruno formula, which is why it is in this file instead
of a dedicated file in the `Combinatorics` folder.

## Main results

Given `c : OrderedFinpartition n` and two formal multilinear series `q` and `p`, we
define `c.compAlongOrderedFinpartition q p` as an `n`-multilinear map given by the formula above,
i.e., `(v₁, ..., vₙ) ↦ qₖ (p_{i₁} (v_{I₁}), ..., p_{iₖ} (v_{Iₖ}))`.

Then, we define `q.taylorComp p` as a formal multilinear series whose `n`-th term is
the sum of `c.compAlongOrderedFinpartition q p` over all ordered finpartitions of size `n`.

Finally, we prove in `HasFTaylorSeriesUptoOn.comp` that, if two functions `g` and `f` have Taylor
series up to `n` given by `q` and `p`, then `g ∘ f` also has a Taylor series,
given by `q.taylorComp p`.

## Implementation

A first technical difficulty is to implement the extension process of `OrderedFinpartition`
corresponding to adding a new atom, or appending an atom to an existing part, and defining the
associated increasing parameterizations that show up in the definition
of `compAlongOrderedFinpartition`.

Then, one has to show that the ordered finpartitions thus
obtained give exactly all ordered finpartitions of order `n+1`. For this, we define the inverse
process (shrinking a finpartition of `n+1` by erasing `0`, either as an atom or from the part
that contains it), and we show that these processes are inverse to each other, yielding an
equivalence between `(c : OrderedFinpartition n) × Option (Fin c.length)`
and `OrderedFinpartition (n + 1)`. This equivalence shows up prominently in the inductive proof
of Faa di Bruno formula to identify the sums that show up.
-/

noncomputable section

open Set Fin Function -- Filter

namespace OrderedFinpartition

/-- A part of an ordered finpartition. It is a nonempty finite set in `Fin n`,
but we use sorted tuples instead, so that we can get nice definitional equalities
for the size and the embedding.  -/
@[ext]
structure Part (n : ℕ) where
  size : ℕ
  size_ne_zero : size ≠ 0
  toFun : Fin size → Fin n
  strictMono : StrictMono toFun
  deriving DecidableEq, Repr

namespace Part

variable {m n : ℕ}

initialize_simps_projections Part (toFun → apply)

instance size_neZero (p : Part n) : NeZero p.size := ⟨p.size_ne_zero⟩

attribute [simp] size_ne_zero

@[simp]
theorem size_pos (p : Part n) : 0 < p.size := Nat.pos_iff_ne_zero.mpr p.size_ne_zero

@[simp]
theorem one_le_size (p : Part n) : 1 ≤ p.size := p.size_pos

attribute [coe] toFun
instance : CoeFun (Part n) fun p ↦ Fin p.size → Fin n where coe := toFun

@[simp]
theorem lt_iff_lt (p : Part n) {i j : Fin p.size} : p i < p j ↔ i < j :=
  p.strictMono.lt_iff_lt

@[simp]
theorem le_iff_le (p : Part n) {i j : Fin p.size} : p i ≤ p j ↔ i ≤ j :=
  p.strictMono.le_iff_le

theorem injective (p : Part n) : Injective p := p.strictMono.injective

@[simp]
theorem apply_inj (p : Part n) {i j : Fin p.size} : p i = p j ↔ i = j :=
  p.injective.eq_iff

/-- The last (and the greatest) element of a part.
We introduce a definition instead of using `p ⊤`
to avoid dependent types. -/
def last (p : Part n) : Fin n := p ⊤

@[simp] lemma apply_top (p : Part n) : p ⊤ = p.last := rfl

/-!
### Equivalence to nonempty `Finset`s
-/

/-- Range of a `OrderedFinpartition.Part` as a `Finset`. -/
protected def range (p : Part n) : Finset (Fin n) :=
  Finset.univ.map ⟨p, p.strictMono.injective⟩

@[simp]
theorem coe_range (p : Part n) : (p.range : Set (Fin n)) = Set.range p := by
  simp [Part.range]

theorem mem_range (p : Part n) {i : Fin n} : i ∈ p.range ↔ ∃ j, p j = i := by
  simp [Part.range]

@[simp]
theorem card_range (p : Part n) : p.range.card = p.size := by simp [Part.range]

theorem range_nonempty (p : Part n) : p.range.Nonempty := by simp [← Finset.card_pos]

theorem range_injective : Injective (@Part.range n) := by
  intro p₁ p₂ h
  have h₁ : p₁.size = p₂.size := by simpa using congr(Finset.card $h)
  cases p₁; cases p₂
  subst h₁
  congr
  rw [← StrictMono.range_inj ‹_› ‹_›]
  simpa [Part.range, ← Finset.coe_inj] using h

@[simp]
lemma range_inj {p₁ p₂ : Part n} : p₁.range = p₂.range ↔ p₁ = p₂ := range_injective.eq_iff

/-- Define a `Part n` from a nonempty `Finset`. -/
@[simps]
def ofFinset (s : Finset (Fin n)) (hs : s.Nonempty) : Part n where
  size := s.card
  size_ne_zero := by simp [hs.ne_empty]
  toFun := s.orderEmbOfFin rfl
  strictMono := OrderEmbedding.strictMono _

@[simp]
theorem range_ofFinset (s : Finset (Fin n)) (hs : s.Nonempty) : (ofFinset s hs).range = s := by
  simp [Part.range, ← Finset.coe_inj]

@[simp]
theorem ofFinset_range (p : Part n) : ofFinset p.range p.range_nonempty = p := by
  simp [← range_inj]

/-- Equivalence between `Part n` and the set of nonempty finite sets in `Fin n`. -/
@[simps]
def equivFinset : Part n ≃ {s : Finset (Fin n) // s.Nonempty} where
  toFun p := ⟨p.range, p.range_nonempty⟩
  invFun s := ofFinset s.1 s.2
  left_inv := ofFinset_range
  right_inv _ := Subtype.eq <| range_ofFinset _ _

/-- Each `Fin n` has finitely many parts. -/
instance : Fintype (Part n) := .ofEquiv _ equivFinset.symm

@[simp]
theorem card_part : Fintype.card (Part n) = 2 ^ n - 1 := by
  simp [Fintype.card_congr equivFinset, Finset.nonempty_iff_ne_empty]

@[simp]
theorem size_le (p : Part n) : p.size ≤ n := by simpa using p.range.card_le_univ

theorem pos (p : Part n) : 0 < n := p.size_pos.trans_le p.size_le

theorem neZero (p : Part n) : NeZero n := .of_pos p.pos

/-- There are nonempty parts of `Fin 0`. -/
instance instIsEmpty : IsEmpty (Part 0) where
  false p := p.pos.ne rfl

@[simp]
theorem zero_mem_range (p : Part n) :
    haveI := p.neZero; 0 ∈ p.range ↔ p 0 = 0 := by
  haveI := p.neZero
  rw [p.mem_range]
  refine ⟨fun ⟨j, hj⟩ ↦ le_antisymm ?_ (Fin.zero_le' _), fun h ↦ ⟨0, h⟩⟩
  exact hj ▸ p.strictMono.monotone (Fin.zero_le' _)

theorem apply_ne_zero {p : Part n} :
    haveI := p.neZero; (∀ i, p i ≠ 0) ↔ p 0 ≠ 0 := by
  simp only [ne_eq, ← not_exists, ← mem_range, zero_mem_range]

/-- A part that contains a single element. -/
@[simps]
def atom (i : Fin n) : Part n where
  size := 1
  size_ne_zero := one_ne_zero
  toFun _ := i
  strictMono := Subsingleton.strictMono _

@[simp]
lemma atom_last (i : Fin n) : (atom i).last = i := rfl

@[simp]
theorem atom_range (i : Fin n) : (atom i).range = {i} := by simp [Part.range]

theorem atom_injective : (@atom n).Injective := LeftInverse.injective atom_last

@[simp]
lemma atom_inj {i j : Fin n} : atom i = atom j ↔ i = j := atom_injective.eq_iff

@[simp]
theorem range_eq_singleton {p : Part n} {i : Fin n} : p.range = {i} ↔ p = atom i :=
  range_injective.eq_iff' <| atom_range i

theorem size_eq_one {p : Part n} : p.size = 1 ↔ ∃ i, p = atom i := by
  rw [← card_range, Finset.card_eq_one]
  simp_rw [range_eq_singleton]

theorem one_lt_size_of_eq_of_ne_atom {p : Part n} {i j} (h₁ : p i = j) (h₂ : p ≠ atom j) :
    1 < p.size := by
  rw [p.one_le_size.gt_iff_ne, ne_eq, size_eq_one]
  rintro ⟨k, rfl⟩
  simp_all

@[simp]
lemma last_eq_zero {p : Part n} : haveI := p.neZero; p.last = 0 ↔ p = atom 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  suffices ∀ i, p i = p.last by
    rw [← range_eq_singleton, ← p.range_nonempty.subset_singleton_iff]
    simpa [Finset.subset_iff, Part.mem_range, h] using this
  exact fun i ↦ le_antisymm (p.strictMono.monotone le_top) <| h.symm ▸ Nat.zero_le _

@[simp]
lemma last_pos {p : Part n} : haveI := p.neZero; 0 < p.last ↔ p ≠ atom 0 := by
  haveI := p.neZero
  simp [pos_iff_ne_zero']

/-- If `n ≠ 0`, then `atom 0` is the default `Part n`. -/
instance instInhabited [NeZero n] : Inhabited (Part n) := ⟨atom 0⟩

/-- There is a unique part in `Fin 1`. -/
instance instUnique : Unique (Part 1) where
  uniq p := range_injective <| by simp only [(range_nonempty _).eq_univ]

/-- The part that contains the whole type. -/
@[simps]
def univ (n : ℕ) (h : n ≠ 0) : Part n where
  size := n
  size_ne_zero := h
  toFun := id
  strictMono := strictMono_id

/-- The embedding as a bundled `OrderEmbedding`. -/
@[simps! (config := .asFn)]
def emb (p : Part n) : Fin p.size ↪o Fin n :=
  .ofStrictMono p p.strictMono

/-- Map a `Part m` along an order embedding from `Fin m` to `Fin n`.

The two intended applications are:
- `f = Fin.succOrderEmb`;
- `f = q.emb` for `q : Part n` and `p : Part q.size`. -/
@[simps (config := .asFn)]
def map (p : Part m) (f : Fin m ↪o Fin n) : Part n where
  __ := p
  toFun := f ∘ p
  strictMono := f.strictMono.comp p.strictMono

@[simp]
theorem range_map (p : Part m) (f : Fin m ↪o Fin n) :
    (p.map f).range = p.range.map f.toEmbedding := by
  ext; simp [Part.mem_range]

@[simp]
theorem map_inj {p₁ p₂ : Part m} {f : Fin m ↪o Fin n} : p₁.map f = p₂.map f ↔ p₁ = p₂ := by
  simp [← range_inj]

@[simp]
theorem last_map (p : Part m) (f : Fin m ↪o Fin n) : (p.map f).last = f p.last :=
  rfl

@[simp]
theorem map_atom (f : Fin m ↪o Fin n) (i : Fin m) : (atom i).map f = atom (f i) := rfl

@[simp]
theorem map_eq_atom {p : Part m} {f : Fin m ↪o Fin n} {i : Fin n} :
    p.map f = atom i ↔ ∃ j, f j = i ∧ p = atom j := by
  refine ⟨fun h ↦ ?_, fun ⟨j, hji, hpj⟩ ↦ by simp [*]⟩
  obtain ⟨j, rfl⟩ : ∃ j, p = atom j := by
    rw [← size_eq_one, ← map_size, h, atom_size]
  use j, by simpa using h

/-- Map all elements of a part to `Fin (n + 1)` using `Fin.succ`,
then prepend zero. -/
@[simps size]
def extendZero (p : Part n) : Part (n + 1) where
  size := p.size + 1
  size_ne_zero := Nat.succ_ne_zero _
  toFun := Fin.cons 0 (.succ ∘ p)
  strictMono := by
    intro i j hlt
    rcases Fin.exists_succ_eq.mpr hlt.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using hlt

@[simp]
theorem extendZero_apply_zero (p : Part n) : p.extendZero 0 = 0 := rfl

@[simp]
theorem extendZero_apply_succ (p : Part n) (i : Fin p.size) : p.extendZero i.succ = (p i).succ := by
  simp [extendZero]

@[simp]
theorem extendZero_last (p : Part n) : p.extendZero.last = p.last.succ := by
  rw [last, last, ← extendZero_apply_succ, Fin.succ_top]

theorem range_extendZero_eq_cons (p : Part n) :
    p.extendZero.range = .cons 0 (p.range.map (Fin.succEmb n)) (by simp [Fin.succ_ne_zero]) := by
  ext
  simp [extendZero, Fin.exists_fin_succ, eq_comm (a := (0 : Fin _)), mem_range]

@[simp]
theorem extendZero_ne_atom (p : Part n) (i : Fin (n + 1)) : p.extendZero ≠ atom i :=
  ne_of_apply_ne size <| by simp

@[simps size, simps (config := .lemmasOnly) apply]
def mapPred (p : Part (n + 1)) (h : p 0 ≠ 0) : Part n where
  size := p.size
  size_ne_zero := p.size_ne_zero
  toFun i := (p i).pred <| apply_ne_zero.2 h i
  strictMono := Fin.strictMono_pred_comp _ p.strictMono

@[simp]
lemma mapPred_inj {p₁ p₂ : Part (n + 1)} {h₁ h₂} :
    p₁.mapPred h₁ = p₂.mapPred h₂ ↔ p₁ = p₂ := by
  simp +contextual [Part.ext_iff, Fin.heq_fun_iff, mapPred_apply]

@[simp]
theorem mapPred_last (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).last = p.last.pred (apply_ne_zero.2 h ⊤) :=
  rfl

theorem mapPred_range_eq_preimage (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).range = p.range.preimage Fin.succ (succ_injective _).injOn := by
  ext
  simp [Part.mem_range, pred_eq_iff_eq_succ, mapPred_apply]

@[simp]
theorem mapPred_map_succ (p : Part n) :
    (p.map (succOrderEmb n)).mapPred (Fin.succ_ne_zero _) = p := by
  cases p
  simp [map, mapPred]

@[simp]
theorem map_succ_mapPred (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.mapPred h).map (succOrderEmb n) = p := by
  rw [← mapPred_inj, mapPred_map_succ]

@[simps size, simps (config := .lemmasOnly) apply]
def eraseZero [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) : Part n where
  size := p.size - 1
  size_ne_zero := (Nat.sub_pos_of_lt <| one_lt_size_of_eq_of_ne_atom h₁ h₂).ne'
  toFun i := p <| i.succ.cast <| Nat.sub_add_cancel p.one_le_size
  strictMono i j hlt := by simpa [Fin.cast_lt_cast]

@[simp]
lemma eraseZero_last [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) :
    (p.eraseZero h₁ h₂).last = p.last := by
  rw [Part.last, eraseZero_apply]
  simp

lemma eraseZero_ne_zero [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0)
    (i : Fin (p.size - 1)) : p.eraseZero h₁ h₂ i ≠ 0 :=
  h₁ ▸ (p.strictMono <| Nat.succ_pos i).ne'

@[simp]
lemma eraseZero_range [NeZero n] (p : Part n) (h₁ : p 0 = 0) (h₂ : p ≠ atom 0) :
    (p.eraseZero h₁ h₂).range = p.range.erase 0 := by
  ext i
  by_cases hi : i = 0 <;> simp [Part.mem_range, eraseZero_apply, hi, p.injective.eq_iff' h₁,
    (finCongr <| Nat.sub_add_cancel p.one_le_size).surjective.exists, exists_fin_succ, h₁, Ne.symm]

def preimageSucc (p : Part (n + 1)) (h : p ≠ atom 0) : Part n :=
  if h₀ : p 0 = 0 then (p.eraseZero h₀ h).mapPred (p.eraseZero_ne_zero _ _ _) else p.mapPred h₀

@[simp]
theorem preimageSucc_last (p : Part (n + 1)) (h : p ≠ atom 0) :
    (p.preimageSucc h).last = p.last.pred (by simpa) := by
  unfold preimageSucc
  split_ifs <;> simp

@[simp]
theorem preimageSucc_range (p : Part (n + 1)) (h : p ≠ atom 0) :
    (p.preimageSucc h).range = p.range.preimage succ (succ_injective _).injOn := by
  simp [← Finset.coe_inj, preimageSucc, apply_dite Part.range, mapPred_range_eq_preimage,
    Set.disjoint_left, succ_ne_zero]

@[simp]
lemma preimageSucc_extendZero (p : Part n) :
    p.extendZero.preimageSucc (extendZero_ne_atom _ _) = p := by
  simp [Part.ext_iff, extendZero, preimageSucc, mapPred, eraseZero]

@[simp]
lemma preimageSucc_map_succ (p : Part n) :
    (p.map (succOrderEmb n)).preimageSucc (by simp [succ_ne_zero]) = p := by
  simp [Part.ext_iff, preimageSucc, succ_ne_zero]

lemma extendZero_preimageSucc (p : Part (n + 1)) (h₁ : p ≠ atom 0) (h₂ : p 0 = 0) :
    (p.preimageSucc h₁).extendZero = p := by
  simp [preimageSucc, h₂, Part.ext_iff, Fin.heq_fun_iff, forall_fin_succ, mapPred_apply,
    eraseZero_apply, Fin.cast]

lemma map_succ_preimageSucc (p : Part (n + 1)) (h : p 0 ≠ 0) :
    (p.preimageSucc <| ne_of_apply_ne (toFun · 0) h).map (succOrderEmb n) = p := by
  simp [Part.ext_iff, preimageSucc, h]

end Part

end OrderedFinpartition

/-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
parameterization of these subsets. We order the subsets by increasing greatest element.
This definition is tailored-made for the Faa di Bruno formula, and probably not useful elsewhere,
because of the specific parameterization by `Fin n` and the peculiar ordering. -/
@[ext]
structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  length : ℕ
  /-- The size of each part -/
  part : Fin length → OrderedFinpartition.Part n
  /-- The parts are ordered by increasing greatest element. -/
  part_last_strictMono : StrictMono fun m ↦ (part m).last
  /-- The parts are disjoint -/
  disjoint : Pairwise (Disjoint on fun m ↦ (part m).range)
  /-- The parts cover everything -/
  cover x : ∃ m, x ∈ (part m).range
  deriving DecidableEq

namespace OrderedFinpartition

/-! ### Basic API for ordered finpartitions -/

/-- The ordered finpartition of `Fin n` into singletons. -/
@[simps] def atomic (n : ℕ) : OrderedFinpartition n where
  length := n
  part i :=  .atom i
  part_last_strictMono := strictMono_id
  disjoint _ _ h := by simp [h.symm]
  cover m := by simp

variable {n : ℕ} (c : OrderedFinpartition n)

instance : Inhabited (OrderedFinpartition n) := ⟨atomic n⟩

@[simp]
lemma part_last_inj {i j : Fin c.length} : (c.part i).last = (c.part j).last ↔ i = j :=
  c.part_last_strictMono.injective.eq_iff

@[simp]
lemma part_last_lt_part_last {i j : Fin c.length} : (c.part i).last < (c.part j).last ↔ i < j :=
  c.part_last_strictMono.lt_iff_lt

@[simp]
lemma part_last_le_part_last {i j : Fin c.length} : (c.part i).last ≤ (c.part j).last ↔ i ≤ j :=
  c.part_last_strictMono.le_iff_le

lemma length_le : c.length ≤ n := by
  simpa only [Fintype.card_fin]
    using Fintype.card_le_of_injective _ c.part_last_strictMono.injective

@[deprecated Part.size_le (since := "2025-01-20")]
lemma partSize_le (m : Fin c.length) : (c.part m).size ≤ n := (c.part m).size_le

lemma part_injective : Injective c.part :=
  c.part_last_strictMono.injective.of_comp (f := Part.last)

@[simp]
lemma part_inj {i j} : c.part i = c.part j ↔ i = j := c.part_injective.eq_iff

lemma part_injective₂ :
    Injective fun x : (i : Fin c.length) × Fin (c.part i).size ↦ c.part x.1 x.2 := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  obtain rfl : i = j := by
    apply c.disjoint.eq
    have h : ∃ x y, c.part j y = c.part i x := ⟨x, y, h.symm⟩
    simpa [onFun, Finset.disjoint_left, Part.mem_range] using h
  simpa using (c.part i).injective h

@[deprecated (since := "2025-01-20")]
alias emb_injective := part_injective₂

theorem part_bijective₂ :
    Bijective fun x : (i : Fin c.length) × Fin (c.part i).size ↦ c.part x.1 x.2 :=
  ⟨c.part_injective₂, fun i ↦ by simpa [Part.mem_range] using c.cover i⟩

@[simp]
lemma part_inj₂ {i j i' j'} : c.part i j = c.part i' j' ↔ i = i' ∧ (j : ℕ) = j' := by
  simpa +contextual only [Sigma.mk.inj_iff, ← exists_prop, Fin.heq_ext_iff]
    using c.part_injective₂.eq_iff (a := ⟨i, j⟩) (b := ⟨i', j'⟩)

@[simp]
lemma part_mem_range {i j k} : c.part i j ∈ (c.part k).range ↔ i = k := by
  suffices i = k → ∃ (x : Fin (c.part k).size), (j : ℕ) = x by
    simpa [Part.mem_range, eq_comm] using this
  rintro rfl
  use j

/-- The finite set of all parts of an ordered finpartition. -/
def parts : Finset (Part n) :=
  Finset.univ.map ⟨c.part, c.part_injective⟩

@[simp]
lemma card_parts : c.parts.card = c.length := by simp [parts]

@[simp]
lemma coe_parts : c.parts.toSet = Set.range c.part := by simp [parts]

@[simp]
lemma mem_parts {p} : p ∈ c.parts ↔ ∃ i, c.part i = p := by simp [parts]

/-- An ordered finpartition is completely determined by the finite set of its parts. -/
theorem parts_injective : Injective (@parts n) := by
  intro c₁ c₂ h
  have h₁ : c₁.length = c₂.length := by simpa using congr($h |>.card)
  replace h : Set.range c₁.part = Set.range c₂.part := by
    simp only [← coe_parts, h]
  cases' c₁ with length₁ part₁ mono₁ disj₁ _
  cases' c₂ with length₂ part₂ mono₂ disj₂ _
  subst h₁
  suffices part₁ = part₂ by congr
  have h₂ : (part₁ · |>.last) = (part₂ · |>.last) := by
    rw [← mono₁.range_inj mono₂]
    simpa only [← Set.range_comp] using congr((fun p ↦ p ⊤) '' $h)
  ext1 i
  obtain ⟨j, hj⟩ : part₂ i ∈ Set.range part₁ := by simp [h]
  have h₃ : part₁ i ⊤ = part₁ j ⊤ := .trans congr($h₂ i) <| .symm congr($hj ⊤)
  rw [← hj, mono₁.injective h₃]

theorem disjoint_setRange {i j} (h : i ≠ j) : Disjoint (range (c.part i)) (range (c.part j)) := by
  simpa only [← Part.coe_range, Finset.disjoint_coe] using c.disjoint h

instance : Unique (OrderedFinpartition 0) :=
  have : Subsingleton (OrderedFinpartition 0) := parts_injective.subsingleton
  .mk' _

/-- An ordered finpartition gives an equivalence between `Fin n`
and the disjoint union of the parts, each of them parameterized by `Fin (c.part i).size`. -/
@[simps symm_apply]
def equivSigma : Fin n ≃ ((i : Fin c.length) × Fin (c.part i).size) where
  toFun := Fintype.bijInv c.part_bijective₂
  invFun x := c.part x.1 x.2
  left_inv := Fintype.rightInverse_bijInv _
  right_inv := Fintype.leftInverse_bijInv _

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
def index (j : Fin n) : Fin c.length :=
  (c.equivSigma j).1

/-- The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
def invEmbedding (j : Fin n) : Fin (c.part (c.index j)).size :=
  (c.equivSigma j).2

@[simp] lemma part_invEmbedding (j : Fin n) :
    c.part (c.index j) (c.invEmbedding j) = j :=
  c.equivSigma.symm_apply_apply j

@[simp]
lemma equivSigma_part (i j) : c.equivSigma (c.part i j) = ⟨i, j⟩ :=
  c.equivSigma.apply_symm_apply ⟨i, j⟩

@[simp]
lemma index_part (i j) : c.index (c.part i j) = i := by simp [index]

lemma index_eq_iff_mem_range {i j} : c.index i = j ↔ i ∈ (c.part j).range := by
  rcases c.equivSigma.symm.surjective i with ⟨⟨k, l⟩, rfl⟩
  simp

@[simp]
lemma mem_part_index_range (j : Fin n) : j ∈ (c.part (c.index j)).range :=
  (Part.mem_range _).mpr ⟨_, c.part_invEmbedding j⟩

@[to_additive] lemma prod_sigma_eq_prod {M : Type*} [CommMonoid M] (v : Fin n → M) :
    ∏ (m : Fin c.length), ∏ (r : Fin (c.part m).size), v (c.part m r) = ∏ i, v i := by
  rw [Finset.prod_sigma', Finset.univ_sigma_univ, ← c.equivSigma.symm.prod_comp]
  simp only [equivSigma_symm_apply]

@[simp]
theorem sum_part_size : ∑ i, (c.part i).size = n := by
  simpa using c.sum_sigma_eq_sum (1 : Fin n → ℕ)

@[simp]
lemma length_eq_zero : c.length = 0 ↔ n = 0 where
  mp h := by
    have : IsEmpty (Fin c.length) := by rw [h]; infer_instance
    rw [← c.sum_part_size, Finset.sum_of_isEmpty]
  mpr := by
    rintro rfl
    rw [Unique.eq_default c]
    rfl

@[simp]
lemma length_pos : 0 < c.length ↔ 0 < n := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, length_eq_zero]

@[simp]
lemma one_le_length : 1 ≤ c.length ↔ 1 ≤ n := c.length_pos

instance neZero_length [NeZero n] (c : OrderedFinpartition n) : NeZero c.length :=
  .of_pos <| c.length_pos.2 pos'

@[deprecated Part.size_neZero (since := "2025-01-20")]
lemma neZero_partSize (c : OrderedFinpartition n) (i : Fin c.length) : NeZero (c.part i).size :=
  inferInstance

@[simp]
lemma part_index_zero_zero [NeZero n] : c.part (c.index 0) 0 = 0 :=
  (Part.zero_mem_range _).mp <| c.mem_part_index_range 0

/-!
### Extending and shrinking ordered finpartitions

We show how an ordered finpartition can be extended to the left, either by adding a new atomic
part (in `extendLeft`) or adding the new element to an existing part (in `extendMiddle`).
Conversely, one can shrink a finpartition by deleting the element to the left, with a different
behavior if it was an atomic part (in `eraseLeft`, in which case the number of parts decreases by
one) or if it belonged to a non-atomic part (in `eraseMiddle`, in which case the number of parts
stays the same).

These operations are inverse to each other, giving rise to an equivalence between
`((c : OrderedFinpartition n) × Option (Fin c.length))` and `OrderedFinpartition (n + 1)`
called `OrderedFinPartition.extendEquiv`.
-/

/-- Extend an ordered partition of `n` entries, by adding a new singleton part to the left. -/
@[simps length]
def extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) where
  length := c.length + 1
  part := Fin.cons (.atom 0) fun i ↦ (c.part i).map (Fin.succOrderEmb n)
  part_last_strictMono i j hij := by
    rcases Fin.eq_succ_of_ne_zero hij.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp
    | succ => simpa using c.part_last_strictMono (Fin.succ_lt_succ_iff.mp hij)
  disjoint := by
    rw [pairwise_disjoint_on]
    intro i j hij
    rcases Fin.eq_succ_of_ne_zero hij.ne_bot with ⟨j, rfl⟩
    cases i using Fin.cases with
    | zero => simp [Fin.succ_ne_zero]
    | succ => simpa using c.disjoint (Fin.succ_lt_succ_iff.mp hij).ne
  cover i := by
    cases i using Fin.cases with
    | zero =>
      use 0
      simp
    | succ i =>
      use (c.index i).succ
      simp

@[simp]
theorem extendLeft_part_zero (c : OrderedFinpartition n) : c.extendLeft.part 0 = .atom 0 := rfl

@[simp]
theorem extendLeft_part_succ (c : OrderedFinpartition n) (i : Fin c.length) :
    c.extendLeft.part i.succ = (c.part i).map (Fin.succOrderEmb n) :=
  rfl

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
@[simps length, simps (config := .lemmasOnly) part]
def extendMiddle (c : OrderedFinpartition n) (k : Fin c.length) : OrderedFinpartition (n + 1) where
  length := c.length
  part := update (fun i ↦ (c.part i).map (Fin.succOrderEmb n)) k (c.part k).extendZero
  part_last_strictMono := by
    simpa [apply_update fun _ ↦ Part.last] using Fin.strictMono_succ.comp c.part_last_strictMono
  disjoint i j hne := by
    wlog hik : i ≠ k generalizing i j
    · obtain rfl : i = k := by push_neg at hik; exact hik
      exact this j i hne.symm hne.symm |>.symm
    rcases eq_or_ne j k with rfl | hjk <;>
      simpa [onFun, *, Part.range_extendZero_eq_cons, Fin.succ_ne_zero] using c.disjoint hne
  cover i := by
    cases i using Fin.cases with
    | zero =>
      use k
      simp
    | succ i =>
      use c.index i
      rcases eq_or_ne (c.index i) k with rfl | hne <;> simp [*, Part.range_extendZero_eq_cons]

@[simp]
theorem extendMiddle_part_self (c : OrderedFinpartition n) (k : Fin c.length) :
    (c.extendMiddle k).part k = (c.part k).extendZero := by
  simp [extendMiddle_part]

@[simp]
theorem extendMiddle_part_of_ne (c : OrderedFinpartition n) {i j : Fin c.length} (h : j ≠ i) :
    (c.extendMiddle i).part j = (c.part j).map (Fin.succOrderEmb n) := by
  simp [extendMiddle_part, h]

/-- If the first part of a partition is not `Part.atom 0`,
then none of the the parts is `Part.atom 0`. -/
theorem part_ne_atom_zero [NeZero n] (h : c.part 0 ≠ .atom 0) (i) : c.part i ≠ .atom 0 := by
  contrapose! h
  rw [← Part.last_eq_zero, ← (Fin.zero_le' _).le_iff_eq] at h ⊢
  exact (c.part_last_strictMono.monotone (Fin.zero_le' _)).trans h

@[simp]
theorem extendMiddle_part_ne_atom_zero (k : Fin c.length) :
    ∀ i, (c.extendMiddle k).part i ≠ .atom 0 := by
  intro i
  rcases eq_or_ne k i with rfl | hne <;>
    simp [extendMiddle_part, *, Ne.symm, succ_ne_zero]

/-- Extend an ordered partition of `n` entries, by adding singleton to the left
or appending it to one of the existing part. -/
def extend (c : OrderedFinpartition n) : Fin (c.length + 1) → OrderedFinpartition (n + 1) :=
  Fin.cons c.extendLeft c.extendMiddle

@[simp]
lemma extend_zero (c : OrderedFinpartition n) : c.extend 0 = c.extendLeft := rfl

@[simp]
lemma extend_succ (c : OrderedFinpartition n) (i : Fin c.length) :
    c.extend i.succ = c.extendMiddle i :=
  rfl

/-- Given an ordered finpartition of `n + 1`, with a leftmost part equal to `Part.atom 0`,
remove this atom to form an ordered finpartition of `n`. -/
@[simps length, simps (config := .lemmasOnly) part]
def eraseLeft (c : OrderedFinpartition (n + 1)) (hc : c.part 0 = .atom 0) :
    OrderedFinpartition n :=
  have eq : c.length - 1 + 1 = c.length := Nat.sub_add_cancel <| by simp
  { length := c.length - 1
    part i := (c.part <| i.succ.cast eq).mapPred <| by
      rw [ne_eq, ← Part.zero_mem_range]
      exact Finset.disjoint_left.mp (c.disjoint (i := 0) (by simp [Fin.ext_iff])) (by simp [hc])
    part_last_strictMono i j hlt := by simpa
    disjoint i j hne := by
      simp_rw [onFun, Part.mapPred_range_eq_preimage]
      simpa [← Finset.disjoint_coe] using (c.disjoint_setRange (by simpa)).preimage Fin.succ
    cover i := by
      simpa [Part.mapPred_range_eq_preimage, (finCongr eq).surjective.exists, exists_fin_succ, hc,
        succ_ne_zero] using c.cover i.succ }

@[simp]
theorem eraseLeft_extendLeft : c.extendLeft.eraseLeft rfl = c := by
  simp [eraseLeft, extendLeft, funext_iff]

theorem extendLeft_injective : Injective (@extendLeft n) := by
  intro c₁ c₂ h
  rw [← c₁.eraseLeft_extendLeft, ← c₂.eraseLeft_extendLeft]
  simp only [h]

@[simp]
lemma extendLeft_inj {c₁ c₂ : OrderedFinpartition n} :
    c₁.extendLeft = c₂.extendLeft ↔ c₁ = c₂ :=
  extendLeft_injective.eq_iff

@[simp]
theorem extendLeft_eraseLeft (c : OrderedFinpartition (n + 1)) (hc : c.part 0 = .atom 0) :
    (c.eraseLeft hc).extendLeft = c := by
  simp [OrderedFinpartition.ext_iff, eraseLeft, extendLeft, Fin.heq_fun_iff, forall_fin_succ, hc,
    ← Fin.val_inj]

/-- Given an ordered finpartition of `n+1`, with a leftmost atom different from `{0}`, remove `{0}`
from the atom that contains it, to form an ordered finpartition of `n`. -/
@[simps]
def eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : c.part 0 ≠ .atom 0) :
    OrderedFinpartition n where
  length := c.length
  part i := (c.part i).preimageSucc (c.part_ne_atom_zero hc i)
  part_last_strictMono i j hlt := by simpa
  disjoint i j hne := by
    simpa [onFun, ← Finset.disjoint_coe] using (c.disjoint_setRange hne).preimage succ
  cover i := by simpa using c.cover i.succ

@[simp]
theorem eraseMiddle_extendMiddle (i : Fin c.length) :
    (c.extendMiddle i).eraseMiddle (extendMiddle_part_ne_atom_zero c i 0) = c := by
  suffices ∀ j, ((c.extendMiddle i).part j).preimageSucc _ = c.part j by
    simpa [OrderedFinpartition.ext_iff, funext_iff]
  intro j
  rcases eq_or_ne i j with rfl | hne <;> simp [*, Ne.symm]

@[simp]
theorem extendMiddle_eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : c.part 0 ≠ .atom 0) :
    (c.eraseMiddle hc).extendMiddle (c.index 0) = c := by
  suffices ∀ j, ((c.eraseMiddle hc).extendMiddle (c.index 0)).part j = c.part j by
    simpa [OrderedFinpartition.ext_iff, funext_iff]
  intro j
  rcases eq_or_ne j (c.index 0) with rfl | hne
  · simp [Part.extendZero_preimageSucc]
  · have : c.part j 0 ≠ 0 := by
      simpa [index_eq_iff_mem_range] using hne.symm
    simp [*, Part.map_succ_preimageSucc]

/-- Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`. -/
def extendEquiv (n : ℕ) :
    ((c : OrderedFinpartition n) × Fin (c.length + 1)) ≃ OrderedFinpartition (n + 1) where
  toFun c := c.1.extend c.2
  invFun c := if h : c.part 0 = .atom 0 then ⟨c.eraseLeft h, 0⟩ else
    ⟨c.eraseMiddle h, .succ (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    cases o using Fin.cases with
    | zero =>
      simp
    | succ o =>
      simp [index_eq_iff_mem_range]
  right_inv c := by
    simp only
    rw [apply_dite (fun c : (c : OrderedFinpartition n) × Fin (c.length + 1) ↦ c.1.extend c.2)]
    split_ifs with h
    · simp
    · simp

/-! ### Applying ordered finpartitions to multilinear maps -/

/-- Given a formal multilinear series `p`, an ordered partition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyOrderedFinpartition c v i` for `v : Fin n → E` and `i : Fin c.k`. -/
def applyOrderedFinpartition (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) :
    (Fin n → E) → Fin c.length → F :=
  fun v m ↦ p m (v ∘ c.emb m)

lemma applyOrderedFinpartition_apply (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) :
  c.applyOrderedFinpartition p v = (fun m ↦ p m (v ∘ c.emb m)) := rfl

theorem norm_applyOrderedFinpartition_le (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) (m : Fin c.length) :
    ‖c.applyOrderedFinpartition p v m‖ ≤ ‖p m‖ * ∏ i : Fin (c.partSize m), ‖v (c.emb m i)‖ :=
  (p m).le_opNorm _

/-- Technical lemma stating how `c.applyOrderedFinpartition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyOrderedFinpartition` retain
multilinearity. -/
theorem applyOrderedFinpartition_update_right
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (j : Fin n) (v : Fin n → E) (z : E) :
    c.applyOrderedFinpartition p (update v j z) =
      update (c.applyOrderedFinpartition p v) (c.index j)
        (p (c.index j)
          (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_self]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_of_ne]
    congr
    apply Function.update_comp_eq_of_not_mem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j ∈ range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

theorem applyOrderedFinpartition_update_left (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F)
    (m : Fin c.length) (v : Fin n → E) (q : E[×c.partSize m]→L[𝕜] F) :
    c.applyOrderedFinpartition (update p m q) v
      = update (c.applyOrderedFinpartition p v) m (q (v ∘ c.emb m)) := by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

/-- Given a an ordered finite partition `c` of `n`, a continuous multilinear map `f` in `c.length`
variables, and for each `m` a continuous multilinear map `p m` in `c.partSize m` variables,
one can form a continuous multilinear map in `n`
variables by applying `p m` to each part of the partition, and then
applying `f` to the resulting vector. It is called `c.compAlongOrderedFinpartition f p`. -/
def compAlongOrderedFinpartition (f : F [×c.length]→L[𝕜] G) (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    E[×n]→L[𝕜] G where
  toFun v := f (c.applyOrderedFinpartition p v)
  map_update_add' v i x y := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update_right, ContinuousMultilinearMap.map_update_add]
  map_update_smul' v i c x := by
    cases Subsingleton.elim ‹_› (instDecidableEqFin _)
    simp only [applyOrderedFinpartition_update_right, ContinuousMultilinearMap.map_update_smul]
  cont := by
    apply f.cont.comp
    change Continuous (fun v m ↦ p m (v ∘ c.emb m))
    fun_prop

@[simp] lemma compAlongOrderFinpartition_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E[×c.partSize i]→L[𝕜] F) (v : Fin n → E) :
    c.compAlongOrderedFinpartition f p v = f (c.applyOrderedFinpartition p v) := rfl

theorem norm_compAlongOrderedFinpartition_le (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f p‖ ≤ ‖f‖ * ∏ i, ‖p i‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [compAlongOrderFinpartition_apply, mul_assoc, ← c.prod_sigma_eq_prod,
    ← Finset.prod_mul_distrib]
  exact f.le_opNorm_mul_prod_of_le <| c.norm_applyOrderedFinpartition_le _ _

/-- Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`. -/
@[simps apply_apply]
def compAlongOrderedFinpartitionₗ :
    (F [×c.length]→L[𝕜] G) →ₗ[𝕜]
      MultilinearMap 𝕜 (fun i : Fin c.length ↦ E[×c.partSize i]→L[𝕜] F) (E[×n]→L[𝕜] G) where
  toFun f :=
    { toFun := fun p ↦ c.compAlongOrderedFinpartition f p
      map_update_add' := by
        intro inst p m q q'
        cases Subsingleton.elim ‹_› (instDecidableEqFin _)
        ext v
        simp [applyOrderedFinpartition_update_left]
      map_update_smul' := by
        intro inst p m a q
        cases Subsingleton.elim ‹_› (instDecidableEqFin _)
        ext v
        simp [applyOrderedFinpartition_update_left] }
  map_add' _ _ := rfl
  map_smul' _ _ :=  rfl

variable (𝕜 E F G) in
/-- Bundled version of `compAlongOrderedFinpartition`, depending continuously linearly on `f`
and continuously multilinearly on `p`. -/
noncomputable def compAlongOrderedFinpartitionL :
    (F [×c.length]→L[𝕜] G) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i ↦ E[×c.partSize i]→L[𝕜] F) (E[×n]→L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p ↦ ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

@[simp] lemma compAlongOrderedFinpartitionL_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ (i : Fin c.length), E[×c.partSize i]→L[𝕜] F) :
    c.compAlongOrderedFinpartitionL 𝕜 E F G f p = c.compAlongOrderedFinpartition f p := rfl

theorem norm_compAlongOrderedFinpartitionL_le :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G‖ ≤ 1 :=
  MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

end OrderedFinpartition

/-! ### The Faa di Bruno formula -/

namespace FormalMultilinearSeries

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
def compAlongOrderedFinpartition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    E [×n]→L[𝕜] G :=
  c.compAlongOrderedFinpartition (q c.length) (fun m ↦ p (c.partSize m))

@[simp]
theorem compAlongOrderedFinpartition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p c) v =
      q c.length (c.applyOrderedFinpartition (fun m ↦ (p (c.partSize m))) v) :=
  rfl

/-- Taylor formal composition of two formal multilinear series. The `n`-th coefficient in the
composition is defined to be the sum of `q.compAlongOrderedFinpartition p c` over all
ordered partitions of `n`.
In other words, this term (as a multilinear function applied to `v₀, ..., vₙ₋₁`) is
`∑'_{k} ∑'_{I₀ ⊔ ... ⊔ Iₖ₋₁ = {0, ..., n-1}} qₖ (p_{i₀} (...), ..., p_{iₖ₋₁} (...))`, where
`iₘ` is the size of `Iₘ` and one puts all variables of `Iₘ` as arguments to `p_{iₘ}`, in
increasing order. The sets `I₀, ..., Iₖ₋₁` are ordered so that `max I₀ < max I₁ < ... < max Iₖ₋₁`.

This definition is chosen so that the `n`-th derivative of `g ∘ f` is the Taylor composition of
the iterated derivatives of `g` and of `f`.

Not to be confused with another notion of composition for formal multilinear series, called just
`FormalMultilinearSeries.comp`, appearing in the composition of analytic functions.
-/
protected noncomputable def taylorComp
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n ↦ ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

end FormalMultilinearSeries

theorem analyticOn_taylorComp
    (hq : ∀ (n : ℕ), AnalyticOn 𝕜 (fun x ↦ q x n) t)
    (hp : ∀ n, AnalyticOn 𝕜 (fun x ↦ p x n) s) {f : E → F}
    (hf : AnalyticOn 𝕜 f s) (h : MapsTo f s t) (n : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ (q (f x)).taylorComp (p x) n) s := by
  apply Finset.analyticOn_sum _ (fun c _ ↦ ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun m ↦ p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i ↦ hp _)

open OrderedFinpartition

/-- Composing two formal multilinear series `q` and `p` along an ordered partition extended by a
new atom to the left corresponds to applying `p 1` on the first coordinates, and the initial
ordered partition on the other coordinates.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
private lemma faaDiBruno_aux1 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) :
    (q.compAlongOrderedFinpartition p (c.extend none)).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear fun i ↦ p (c.partSize i)).comp
      ((q (c.length + 1)).curryLeft.comp ((continuousMultilinearCurryFin1 𝕜 E F) (p 1))) := by
  ext e v
  simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendLeft,
    ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
    ContinuousLinearMap.coe_comp', comp_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty, ContinuousLinearMap.flipMultilinear_apply_apply,
    compAlongOrderedFinpartitionL_apply, compAlongOrderFinpartition_apply]
  congr
  ext j
  exact Fin.cases rfl (fun i ↦ rfl) j

/-- Composing a formal multilinear series with an ordered partition extended by adding a left point
to an already existing atom of index `i` corresponds to updating the `i`th block,
using `p (c.partSize i + 1)` instead of `p (c.partSize i)` there.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
private lemma faaDiBruno_aux2 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) (i : Fin c.length) :
    (q.compAlongOrderedFinpartition p (c.extend (some i))).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun i ↦ p (c.partSize i)) i).comp (p (c.partSize i + 1)).curryLeft := by
  ext e v
  simp? [OrderedFinpartition.extend, extendMiddle, applyOrderedFinpartition_apply] says
    simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendMiddle,
      ContinuousMultilinearMap.curryLeft_apply,
      FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
      ContinuousLinearMap.coe_comp', comp_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, compAlongOrderedFinpartitionL_apply,
      compAlongOrderFinpartition_apply]
  congr
  ext j
  rcases eq_or_ne j i with rfl | hij
  · simp only [↓reduceDIte, update_self, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    match a with
    | 0 => simp
    | a + 1 => simp [cons]
  · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne]
    apply FormalMultilinearSeries.congr _ (by simp [hij])
    simp

/-- *Faa di Bruno* formula: If two functions `g` and `f` have Taylor series up to `n` given by
`q` and `p`, then `g ∘ f` also has a Taylor series, given by `q.taylorComp p`. -/
theorem HasFTaylorSeriesUpToOn.comp {n : WithTop ℕ∞} {g : F → G} {f : E → F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x ↦ (q (f x)).taylorComp (p x)) s := by
  /- One has to check that the `m+1`-th term is the derivative of the `m`-th term. The `m`-th term
  is a sum, that one can differentiate term by term. Each term is a linear map into continuous
  multilinear maps, applied to parts of `p` and `q`. One knows how to differentiate such a map,
  thanks to `HasFDerivWithinAt.linear_multilinear_comp`. The terms that show up are matched, using
  `faaDiBruno_aux1` and `faaDiBruno_aux2`, with terms of the same form at order `m+1`. Then, one
  needs to check that one gets each term once and exactly once, which is given by the bijection
  `OrderedFinpartition.extendEquiv m`. -/
  classical
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x ↦ (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y ↦ B (q (f y) c.length) (fun i ↦ p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x ↦ p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x ↦ q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt (le_trans (mod_cast Nat.le_add_left 1 m)
          (ENat.add_one_natCast_le_withTop_of_lt hm)) hx
      convert HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x ↦ (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.sum (fun c _ ↦ A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.add_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, ContinuousLinearMap.add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p ↦ rfl)
  · intro m hm
    apply continuousOn_finset_sum _ (fun c _ ↦ ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun i ↦ p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prod ?_ ?_)
    · have : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i ↦ ?_)
      have : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)
