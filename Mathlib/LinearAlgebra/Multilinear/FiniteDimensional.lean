/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Multilinear.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Multilinear maps over finite dimensional spaces

The main results are that multilinear maps over finitely-generated, free modules are
finitely-generated and free.

* `Module.Finite.multilinearMap`
* `Module.Free.multilinearMap`

We do not put this in `LinearAlgebra.Multilinear.Basic` to avoid making the imports too large
there.
-/


namespace MultilinearMap

variable {ι R M₂ : Type*} {M₁ : ι → Type*}
variable [Finite ι]
variable [CommRing R] [AddCommGroup M₂] [Module R M₂]
variable [Module.Finite R M₂] [Module.Free R M₂]

variable [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
variable [∀ i, Module.Finite R (M₁ i)] [∀ i, Module.Free R (M₁ i)]

instance _root_.Module.Free.multilinearMap : Module.Free R (MultilinearMap R M₁ M₂) :=
  let ⟨_⟩ := nonempty_fintype ι
  let b := fun i => Module.Free.chooseBasis R (M₁ i)
  let b' := Module.Free.chooseBasis R M₂
  .of_basis <| b'.multilinearMap b

instance _root_.Module.Finite.multilinearMap : Module.Finite R (MultilinearMap R M₁ M₂) :=
  let ⟨_⟩ := nonempty_fintype ι
  let b := fun i => Module.Free.chooseBasis R (M₁ i)
  let b' := Module.Free.chooseBasis R M₂
  .of_basis <| b'.multilinearMap b

end MultilinearMap
