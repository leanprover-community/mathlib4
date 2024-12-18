/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Finitely generated submodules and bilinear maps

-/

open Function (Surjective)
open Finsupp

namespace Submodule

section Map₂

variable {R M N P : Type*}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]

theorem FG.map₂ (f : M →ₗ[R] N →ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
    (hq : q.FG) : (map₂ f p q).FG :=
  let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

end Map₂

end Submodule
