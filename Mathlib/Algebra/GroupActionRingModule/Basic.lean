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
import Mathlib.FieldTheory.IsSepClosed

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


variable {K : Type*} [Field K] [IsSepClosed K] {l : ℕ} [Fact (Nat.Prime l)] (h : ringChar K ≠ l)

-- set_option maxHeartbeats 0
-- for a l^n th root we can take a l th root which is then primitive
theorem primitiveLift {n : ℕ} (h : 0 < n) (ζ : K) (hz: IsPrimitiveRoot ζ (l^n)) :
    ∃ ζ' : K,
      IsPrimitiveRoot ζ' (l^(n+1)) ∧ ζ'^l = (ζ : K) := by
  let f : Polynomial K := Polynomial.X^l - Polynomial.C (ζ : K)
  have l_pos : 0 < l := by exact Fin.size_pos'
  have l_neq_0 : (l : K) ≠ 0 := by sorry
  have zeta_neq_0 : (ζ : K) ≠ 0 := by sorry
  let hf : Polynomial.degree f ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C l_pos (ζ : K)]
    exact NeZero.natCast_ne l (WithBot ℕ)
  let hsep : Polynomial.Separable f := Polynomial.separable_X_pow_sub_C (ζ : K) l_neq_0 zeta_neq_0
  have hz := IsSepClosed.exists_root f hf hsep
  obtain ⟨ζ', h2⟩ := hz
  have hp : IsPrimitiveRoot ζ' (l^(n+1)) := sorry
  have hr : ζ' ^ l = (ζ : K) := sorry
  use ζ'

lemma pow_div (n : ℕ) : l^n ∣ l^(n+1) := Dvd.intro l rfl

lemma pow_gt_zero (n : ℕ) : l^n > 0 := Fin.size_pos'

variable (L : Type*) [Field L]

-- action of lifting is compatible
-- set_option maxRecDepth 99999
theorem liftCompat (n : ℕ) (h : 0 < n)
    (ζ : AlgebraicClosure L) (hz: IsPrimitiveRoot ζ (l^n))
      (g : Field.absoluteGaloisGroup L):
        ZMod.castHom (pow_div n) (ZMod (l^n))
          ((@IsPrimitiveRoot.autToPow L (AlgebraicClosure L) _ _ (Exists.choose (primitiveLift h ζ hz)) {val := l^(n+1), property := pow_gt_zero (n+1)} (Exists.choose_spec (primitiveLift h ζ hz)).left _ _) g : ZMod (l^(n+1)))
            = (@IsPrimitiveRoot.autToPow L (AlgebraicClosure L) _ _ ζ {val := l^n, property := pow_gt_zero n} hz _ _ g : ZMod (l^n)) := by
  simp only [PNat.mk_coe, ZMod.cast_id', id_eq, ZMod.castHom_apply, IsPrimitiveRoot.autToPow]
  dsimp
  generalize_proofs ζ' m₁ m₂
  have hζ' := ζ'.choose_spec
  obtain ⟨_, hh⟩ := hζ'
  have hm₁ := m₁.choose_spec
  have hm₂ := m₂.choose_spec
  dsimp at *
  -- simp_rw [← hh] at hm₂
  sorry

-- better way to do rcursion on PNat?
noncomputable def compatPrimitiveSeq (g : Field.absoluteGaloisGroup L) : (n : ℕ) → primitiveRoots (l^(n.toPNat' : ℕ)) (AlgebraicClosure L)
  -- := sorry
  | 0 => {
    val := 1
    property := sorry
  }
  | 1 => {
    val := 1
    property := sorry
  }
  | m+1 => {
    val := sorry
    -- val := liftCompat L m _ (compatPrimitiveSeq g m).val (((mem_primitiveRoots (show 0 < (l ^ (Nat.toPNat' m)) by sorry)).mp (compatPrimitiveSeq g m).property))
    property := sorry
  }

noncomputable def compatIntSeq (g : Field.absoluteGaloisGroup L) : (n : ℕ) → primitiveRoots (l^(n.toPNat' : ℕ)) (AlgebraicClosure L) := sorry

-- lemma HasPrimitiveRoot (n : ℕ+) : (primitiveRoots (l^(n:ℕ)) K).Nonempty := sorry

-- lemma HasCompatPrimitiveRoot (n : ℕ+) (ζ : primitiveRoots (l^(n:ℕ)) K) :
--     ∃ ζ' ∈ primitiveRoots (l^((n:ℕ)+1)) K, (ζ')^l = ζ := sorry

-- lemma HasPrimitiveRootChain :
--     ∃ ζ : (n : ℕ+) → primitiveRoots (l^(n : ℕ)) K, ∀ (n : ℕ+), (ζ n+1 : K)^l = ζ n := by
--   constructor
--   · sorry
--   · intro n
--     sorry

-- lemma ChainInRoot (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) K)
--     (n : ℕ+) :
--       IsPrimitiveRoot (ζ n : K) (l^(n:ℕ)) := by
--   apply (mem_primitiveRoots (some_lemma l n)).mp
--   exact Finset.coe_mem (ζ n)

-- -- @[simp]
-- noncomputable def seq' (g : Field.absoluteGaloisGroup L)
--     (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L)) (n : ℕ+) : (ZMod (l^(n:ℕ)))ˣ :=
--   -- IsPrimitiveRoot.autToPow L (ChainInRoot (AlgebraicClosure L) l ζ n) g
--   @IsPrimitiveRoot.autToPow L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g



-- noncomputable def seq'_compat (g : Field.absoluteGaloisGroup L)
--     (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L))
--       (h : ∀ (n : ℕ+), (ζ (n+1) : (AlgebraicClosure L))^l = ζ n)
--         (n : ℕ+) :
--           ZMod.castHom (divvv l n) (ZMod (l^(n:ℕ))) (seq' l L g ζ (n+1)) = (seq' l L g ζ (n)) := by
--   -- simp only [PNat.add_coe, PNat.one_coe, ZMod.cast_id', id_eq, ZMod.castHom_apply]
--   -- rw [IsPrimitiveRoot.coe_autToPow_apply]
--   simp only [PNat.add_coe, PNat.one_coe, seq', PNat.mk_coe, ZMod.cast_id', id_eq,
--     ZMod.castHom_apply]
--   simp only [IsPrimitiveRoot.autToPow]
--   dsimp
--   generalize_proofs h1 h2
--   have h1' := h1.choose_spec
--   have h2' := h2.choose_spec
--   have hn := h n
--   dsimp at *
--   -- replace hn : ((ζ (n + 1) : AlgebraicClosure L)) ^ l = ζ n := hn
--   replace h1' : g.toAlgHom (ζ (n + 1) : (AlgebraicClosure L)) = (ζ (n + 1) : (AlgebraicClosure L)) ^ Exists.choose h1 := h1'
--   replace h2' : g.toAlgHom (ζ n : (AlgebraicClosure L)) = (ζ n : (AlgebraicClosure L)) ^ Exists.choose h2 := h2'
--   -- simp_rw [hn] at h1'
--   simp_rw [← hn] at h2'
--   -- replace h2' : g.toAlgHom ((ζ (n + 1)) ^ l) = ((ζ (n + 1)) ^ l) ^ Exists.choose h2 := by rw [h]
--   -- have h2'' : g.toAlgHom (ζ (n+1))^l = (ζ (n+1))^l ^ Exists.choose h2 := by rw [← h]
--   -- have h1'' : g.toAlgHom (ζ (n + 1)) ^ l = (ζ (n + 1)) ^ Exists.choose h1 ^ l := by rw [h2'']

--   -- have g (ζ n) = (ζ (n + 1)) ^ Exists.choose h1
--   -- have h1'' : g.toAlgHom (ζ (n + 1)) = (ζ (n + 1)) ^ Exists.choose h1 := h1'
--   -- have h2'' : g.toAlgHom (ζ n) = (ζ n) ^ Exists.choose h2 := h2'
--   -- rw? at h1''

--   -- rw [@IsPrimitiveRoot.coe_autToPow_apply L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g]
--   -- rw [← @IsPrimitiveRoot.coe_autToPow_apply L (AlgebraicClosure L) _ _ (ζ n) {val := l^(n:ℕ), property := some_lemma l n} (ChainInRoot (AlgebraicClosure L) l ζ n) _ _ g]

-- -- def iscau (g : Field.absoluteGaloisGroup L)
--     -- (ζ : (n : ℕ+) → primitiveRoots (l^(n:ℕ)) (AlgebraicClosure L)) : IsCauSeq (padicNorm l) (seq l L g ζ) := sorry

-- def cyclotomicChar:
--       Field.absoluteGaloisGroup L →* ℤ_[l]ˣ where
--         toFun := fun
--           | .mk toEquiv map_mul' map_add' commutes' => {
--             val := sorry -- PadicInt.ofIntSeq l (seq toEquiv
--             inv := sorry
--             val_inv := sorry
--             inv_val := sorry
--           }
--         map_one' := sorry
--         map_mul' := sorry
