/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Sym.Sym2

/-!
# Finitely Supported Commutative multiplication
-/

section

/--
Functions which are symmetrizable
-/
structure Symmetrizable (M N) [Zero M] [Zero N] where
  /-- The function -/
  toFun : M → M → N
  comm : ∀ a b : M, toFun a b = toFun b a
  right_zero : ∀ (a : M), toFun a 0 = 0

variable {M N} [Zero M] [Zero N]

/--
Lift a symmetrizable function to its sym
-/
def lift1 (F : Symmetrizable M N) : Sym2 M → N := Sym2.lift ⟨F.toFun, F.comm⟩

@[simp]
lemma lift1_mk (F : Symmetrizable M N) (xy : M × M) :
    lift1 F (Sym2.mk xy) = F.toFun xy.1 xy.2 := rfl

variable {α} [DecidableEq α]

/--
Lift a symmetrizable function composed with a finsupp
-/
noncomputable def lift2 (F : Symmetrizable M N) (f : α →₀ M) : Sym2 α →₀ N :=
    Finsupp.onFinset f.support.sym2 (lift1 F ∘ Sym2.map f) (by
  intro p h
  obtain ⟨a, b⟩ := p
  simp_all only [Function.comp_apply, Sym2.map_pair_eq, lift1_mk, ne_eq, Finset.mem_sym2_iff,
    Sym2.mem_iff, Finsupp.mem_support_iff, forall_eq_or_imp, forall_eq]
  apply And.intro
  · by_contra hn
    rw [F.comm, hn] at h
    exact h (F.right_zero (f b))
  · by_contra hn
    rw [hn] at h
    exact h (F.right_zero (f a)))

/--
The off-diagonal of a symmetrizable function composed with a finsupp
-/
def OffDiag (F : Symmetrizable M N) (f : α → M) : α → α → N :=
    fun a b => if a = b then (0 : N) else F.toFun (f a) (f b)

lemma offDiag_symm (F : Symmetrizable M N) (f : α → M) {a b : α} :
    OffDiag F f a b = OffDiag F f b a := by
  rw [OffDiag, OffDiag, F.comm]
  simp only [eq_comm]

/--
Lift the off-diagonal of a symmetrizable function composed with a finsupp
-/
def SymOffDiag (F : Symmetrizable M N) (f : α → M) : Sym2 α → N :=
    Sym2.lift ⟨OffDiag F f, fun a b => by
  rw [(offDiag_symm)] ⟩

@[simp]
lemma SymOffDiag_mk (F : Symmetrizable M N) (f : α → M) (xy : α × α) :
    SymOffDiag F f (Sym2.mk xy) = OffDiag F f xy.1 xy.2 := rfl

/--
The lift the off-diagonal of a symmetrizable function composed with a finsupp as a finsupp
-/
noncomputable def Finsupp.sym2OffDiag (F : Symmetrizable M N) (f : α →₀ M) : Sym2 α →₀ N :=
    Finsupp.onFinset f.support.sym2 (SymOffDiag F f) (by
      intro p h
      obtain ⟨a, b⟩ := p
      simp_all only [SymOffDiag_mk, ne_eq, Finset.mem_sym2_iff, Sym2.mem_iff, mem_support_iff,
        forall_eq_or_imp, forall_eq]
      apply And.intro
      · by_contra hn
        rw [offDiag_symm, OffDiag, hn, F.right_zero] at h
        simp_all only [ite_self, not_true_eq_false]
      · by_contra hn
        rw [offDiag_symm, OffDiag, hn, F.comm, F.right_zero] at h
        simp_all only [ite_self, not_true_eq_false])

@[simp]
lemma sym2OffDiag_mk (F : Symmetrizable M N) (f : α →₀ M) (xy : α × α) :
    Finsupp.sym2OffDiag F f (Sym2.mk xy) = if xy.1 = xy.2 then 0 else F.toFun (f xy.1) (f xy.2) :=
  rfl

lemma support_sym2OffDiag (F : Symmetrizable M N) (f : α →₀ M) :
    (Finsupp.sym2OffDiag F f).support ⊆ Finset.filter (fun ij ↦ ¬ij.IsDiag) f.support.sym2 := by
  intro p hp
  obtain ⟨a,b⟩ := p
  simp at hp
  simp
  obtain ⟨hp1,hp2⟩ := hp
  constructor
  · constructor
    · by_contra ha
      have e1 : F.toFun (f a) (f b) = 0 := by
        rw [ha, F.comm, F.right_zero]
      exact hp2 e1
    · by_contra hb
      have e1 : F.toFun (f a) (f b) = 0 := by
        rw [hb, F.right_zero]
      exact hp2 e1
  · exact hp1

end
