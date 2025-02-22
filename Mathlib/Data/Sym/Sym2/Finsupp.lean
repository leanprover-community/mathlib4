/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Sym.Sym2

/-!
# Finitely Supported Commutative multiplication
-/

section

variable {M N} {F : M → M → N} (h1 : ∀ a b : M, F a b = F b a)

def lift1 : Sym2 M → N := Sym2.lift ⟨F, h1⟩

@[simp]
lemma lift1_mk (xy : M × M) :
    lift1 h1 (Sym2.mk xy) = F xy.1 xy.2 := rfl

variable [Zero M] [Zero N] (h3 : ∀ (a : M), F a 0 = 0)

variable {α} [DecidableEq α] {f : α →₀ M}

noncomputable def lift2 : Sym2 α →₀ N := Finsupp.onFinset f.support.sym2 (lift1 h1 ∘ Sym2.map f) (by
  intro p
  obtain ⟨a, b⟩ := p
  intro h
  simp_all only [Function.comp_apply, Sym2.map_pair_eq, lift1_mk, ne_eq, Finset.mem_sym2_iff,
    Sym2.mem_iff, Finsupp.mem_support_iff, forall_eq_or_imp, forall_eq]
  apply And.intro
  · by_contra hn
    rw [h1, hn] at h
    exact h (h3 (f b))
  · by_contra hn
    rw [hn] at h
    exact h (h3 (f a)))

end
