/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Embeddings of `Fin n`

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file defines embeddings between `Fin n` and other types,

## Main definitions

* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.succEmb` : `Fin.succ` as an `Embedding`;
* `Fin.castLEEmb h` : `Fin.castLE` as an `Embedding`, embed `Fin n` into `Fin m`, `h : n ≤ m`;
* `finCongr` : `Fin.cast` as an `Equiv`, equivalence between `Fin n` and `Fin m` when `n = m`;
* `Fin.castAddEmb m` : `Fin.castAdd` as an `Embedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccEmb` : `Fin.castSucc` as an `Embedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatEmb m i` : `Fin.addNat` as an `Embedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddEmb n i` : `Fin.natAdd` as an `Embedding`, adds `n` on `i` on the left;

-/

assert_not_exists Monoid Finset

open Fin Nat Function

namespace Fin

variable {n m : ℕ}

section Order

/-!
### order
-/

/-- The inclusion map `Fin n → ℕ` is an embedding. -/
@[simps -fullyApplied apply]
def valEmbedding : Fin n ↪ ℕ :=
  ⟨val, val_injective⟩

@[simp]
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl

end Order

section Succ

/-!
### succ and casts into larger Fin types
-/

/-- `Fin.succ` as an `Embedding` -/
def succEmb (n : ℕ) : Fin n ↪ Fin (n + 1) where
  toFun := succ
  inj' := succ_injective _

@[simp]
theorem coe_succEmb : ⇑(succEmb n) = Fin.succ :=
  rfl

attribute [simp] castSucc_inj

/-- `Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps apply]
def castLEEmb (h : n ≤ m) : Fin n ↪ Fin m where
  toFun := castLE h
  inj' := castLE_injective _

@[simp, norm_cast] lemma coe_castLEEmb {m n} (hmn : m ≤ n) : castLEEmb hmn = castLE hmn := rfl

/- The next proof can be golfed a lot using `Fintype.card`.
It is written this way to define `ENat.card` and `Nat.card` without a `Fintype` dependency
(not done yet). -/
lemma nonempty_embedding_iff : Nonempty (Fin n ↪ Fin m) ↔ n ≤ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    obtain ⟨e⟩ := h
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
    refine Nat.succ_le_succ <| ihn ⟨?_⟩
    refine ⟨fun i ↦ (e.setValue 0 0 i.succ).pred (mt e.setValue_eq_iff.1 i.succ_ne_zero),
      fun i j h ↦ ?_⟩
    simpa only [pred_inj, EmbeddingLike.apply_eq_iff_eq, succ_inj] using h

lemma equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨e⟩ ↦ le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h ↦ h ▸ ⟨.refl _⟩⟩

/-- `Fin.castAdd` as an `Embedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
def castAddEmb (m) : Fin n ↪ Fin (n + m) := castLEEmb (le_add_right n m)

@[simp]
lemma coe_castAddEmb (m) : (castAddEmb m : Fin n → Fin (n + m)) = castAdd m := rfl

lemma castAddEmb_apply (m) (i : Fin n) : castAddEmb m i = castAdd m i := rfl

/-- `Fin.castSucc` as an `Embedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
def castSuccEmb : Fin n ↪ Fin (n + 1) := castAddEmb _

@[simp, norm_cast] lemma coe_castSuccEmb : (castSuccEmb : Fin n → Fin (n + 1)) = Fin.castSucc := rfl

lemma castSuccEmb_apply (i : Fin n) : castSuccEmb i = i.castSucc := rfl

/-- `Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply]
def addNatEmb (m) : Fin n ↪ Fin (n + m) where
  toFun := (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

/-- `Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply]
def natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where
  toFun := natAdd n
  inj' a b := by simp [Fin.ext_iff]

end Succ

section SuccAbove

variable {p : Fin (n + 1)}

/-- `Fin.succAbove p` as an `Embedding`. -/
@[simps!]
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1) := ⟨p.succAbove, succAbove_right_injective⟩

@[simp, norm_cast] lemma coe_succAboveEmb (p : Fin (n + 1)) : p.succAboveEmb = p.succAbove := rfl

/-- `Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, by appending the former
at the end of the latter.
`natAdd_castLEEmb m hmn i` maps `i : Fin m` to `i + (m - n) : Fin n` by adding `m - n` to `i` -/
@[simps!]
def natAdd_castLEEmb (hmn : n ≤ m) : Fin n ↪ Fin m :=
  (addNatEmb (m - n)).trans (finCongr (by omega)).toEmbedding

lemma range_natAdd_castLEEmb {n m : ℕ} (hmn : n ≤ m) :
    Set.range (natAdd_castLEEmb hmn) = {i | m - n ≤ i.1} := by
  simp only [natAdd_castLEEmb, Nat.sub_le_iff_le_add]
  ext y
  exact ⟨fun ⟨x, hx⟩ ↦ by simp [← hx]; omega,
    fun xin ↦ ⟨subNat (m - n) (y.cast (Nat.add_sub_of_le hmn).symm)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

end SuccAbove

end Fin
