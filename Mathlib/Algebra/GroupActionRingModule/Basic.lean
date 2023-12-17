/-
Copyright (c) 2023 Qi Ge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Modules over a ring, both under group action

In this file we define

*

## Implementation notes

## Tags

-/

class SemiActionModule (M R N : Type*)
    [Monoid M]
      [Semiring R] [MulSemiringAction M R]
        [AddCommMonoid N] [Module R N] [MulAction M N]
          where
  semilinear: ∀ m : M, ∀ r : R, ∀ n : N, m • (r • n) = (m • r) • (m • n)


variable (K : Type*) [Field K] [IsAlgClosed K] (l : ℕ) [Fact (Nat.Prime l)] (h : ringChar K ≠ l)

lemma HasPrimitiveRoot (n : ℕ+) : (primitiveRoots (l^(n:ℕ)) K).Nonempty := sorry

lemma HasCompatPrimitiveRoot (n : ℕ+) (ζ : primitiveRoots (l^(n:ℕ)) K) :
    ∃ ζ' ∈ primitiveRoots (l^((n:ℕ)+1)) K, (ζ')^l = ζ := sorry

lemma HasPrimitiveRootChain :
    ∃ ζ : (n : ℕ+) → primitiveRoots (l^(n : ℕ)) K, ∀ (n : ℕ+), (ζ n+1 : K)^l = ζ n := by
  constructor
  · sorry
  · intro n
    sorry

lemma some_lemma (n : ℕ+) : l^(n:ℕ) > 0 := Fin.size_pos'

lemma ChainInRoot (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) K)
    (n : ℕ+) :
      IsPrimitiveRoot (ζ n : K) (l^(n:ℕ)) := by
  apply (mem_primitiveRoots (some_lemma l n)).mp
  exact Finset.coe_mem (ζ n)

variable (L : Type*) [Field L]

-- @[simp]
noncomputable def seq' (g : Field.absoluteGaloisGroup L)
    (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L)) (n : ℕ+) : (ZMod (l^(n:ℕ)))ˣ :=
  -- IsPrimitiveRoot.autToPow L (ChainInRoot (AlgebraicClosure L) l ζ n) g
  @IsPrimitiveRoot.autToPow L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g

lemma divvv (n : ℕ) : l^n ∣ l^(n+1) := Dvd.intro l rfl

noncomputable def seq'_compat (g : Field.absoluteGaloisGroup L)
    (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L))
      (h : ∀ (n : ℕ+), (ζ (n+1) : (AlgebraicClosure L))^l = ζ n)
        (n : ℕ+) :
          ZMod.castHom (divvv l n) (ZMod (l^(n:ℕ))) (seq' l L g ζ (n+1)) = (seq' l L g ζ (n)) := by
  -- simp only [PNat.add_coe, PNat.one_coe, ZMod.cast_id', id_eq, ZMod.castHom_apply]
  -- rw [IsPrimitiveRoot.coe_autToPow_apply]
  simp only [PNat.add_coe, PNat.one_coe, seq', PNat.mk_coe, ZMod.cast_id', id_eq,
    ZMod.castHom_apply]
  simp only [IsPrimitiveRoot.autToPow]
  dsimp
  generalize_proofs h1 h2
  have h1' := h1.choose_spec
  have h2' := h2.choose_spec
  have hn := h n
  dsimp at *
  -- replace hn : ((ζ (n + 1) : AlgebraicClosure L)) ^ l = ζ n := hn
  replace h1' : g.toAlgHom (ζ (n + 1) : (AlgebraicClosure L)) = (ζ (n + 1) : (AlgebraicClosure L)) ^ Exists.choose h1 := h1'
  replace h2' : g.toAlgHom (ζ n : (AlgebraicClosure L)) = (ζ n : (AlgebraicClosure L)) ^ Exists.choose h2 := h2'
  rw [← hn] at h2'
  -- replace h2' : g.toAlgHom ((ζ (n + 1)) ^ l) = ((ζ (n + 1)) ^ l) ^ Exists.choose h2 := by rw [h]
  -- have h2'' : g.toAlgHom (ζ (n+1))^l = (ζ (n+1))^l ^ Exists.choose h2 := by rw [← h]
  -- have h1'' : g.toAlgHom (ζ (n + 1)) ^ l = (ζ (n + 1)) ^ Exists.choose h1 ^ l := by rw [h2'']

  -- have g (ζ n) = (ζ (n + 1)) ^ Exists.choose h1
  -- have h1'' : g.toAlgHom (ζ (n + 1)) = (ζ (n + 1)) ^ Exists.choose h1 := h1'
  -- have h2'' : g.toAlgHom (ζ n) = (ζ n) ^ Exists.choose h2 := h2'
  -- rw? at h1''

  -- rw [@IsPrimitiveRoot.coe_autToPow_apply L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g]
  -- rw [← @IsPrimitiveRoot.coe_autToPow_apply L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g]

-- def iscau (g : Field.absoluteGaloisGroup L)
    -- (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L)) : IsCauSeq (padicNorm l) (seq l L g ζ) := sorry

def cyclotomicChar:
      Field.absoluteGaloisGroup L →* ℤ_[l]ˣ where
        toFun := fun
          | .mk toEquiv map_mul' map_add' commutes' => {
            val := sorry -- PadicInt.ofIntSeq l (seq toEquiv
            inv := sorry
            val_inv := sorry
            inv_val := sorry
          }
        map_one' := sorry
        map_mul' := sorry
