/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Field.AlgClosed
import Mathlib.Data.MvPolynomial.Basic

namespace FirstOrder

open MvPolynomial FreeCommRing

variable {ι : Type}

def genericPolyMap {ι : Type _} (mons : ι → Finset (ι →₀ ℕ)) :
    ι → FreeCommRing (ι ⊕ (Σ i : ι, mons i)) :=
  fun i => (mons i).attach.sum
    (fun m => FreeCommRing.of (Sum.inr ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inl j)^ n))

theorem lift_genericPolyMap {R : Type _} [CommRing R]
    {p : ι → MvPolynomial ι R} (x : ι → R) (i : ι) :
    FreeCommRing.lift
      (fun s : ι ⊕ (Σ i : ι, (p i).support) =>
        Sum.elim x (fun j => (p i).coeff j.2) s)
      (genericPolyMap (fun i => (p i).support) i) = MvPolynomial.eval x (p i) := by
  conv_rhs => rw [MvPolynomial.eval_eq, ← Finset.sum_attach]
  simp only [genericPolyMap, Finsupp.prod, map_sum, map_mul, lift_of, Sum.elim_inr,
    map_prod, map_pow, Sum.elim_inl]

end FirstOrder
