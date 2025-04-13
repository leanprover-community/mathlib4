/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Lattice

/-!
# Sorting the elements of `Sym2`

This files provides `Sym2.sortEquiv`, the forward direction of which is somewhat analogous to
`Multiset.sort`.
-/



namespace Sym2

variable {α}

/-- The supremum of the two elements. -/
def sup [SemilatticeSup α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊔ ·), sup_comm⟩ x

@[simp] theorem sup_mk [SemilatticeSup α] (a b : α) : s(a, b).sup = a ⊔ b := rfl

/-- The infimum of the two elements. -/
def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

@[simp] theorem inf_mk [SemilatticeInf α] (a b : α) : s(a, b).inf = a ⊓ b := rfl

protected theorem inf_le_sup [Lattice α] (s : Sym2 α) : s.inf ≤ s.sup := by
  cases s using Sym2.ind; simp [_root_.inf_le_sup]

/-- In a linear order, symmetric squares are canonically identified with ordered pairs. -/
@[simps!]
def sortEquiv [LinearOrder α] : Sym2 α ≃ { p : α × α // p.1 ≤ p.2 } where
  toFun s := ⟨(s.inf, s.sup), Sym2.inf_le_sup _⟩
  invFun p := Sym2.mk p
  left_inv := Sym2.ind fun a b => mk_eq_mk_iff.mpr <| by
    cases le_total a b with
    | inl h => simp [h]
    | inr h => simp [h]
  right_inv := Subtype.rec <| Prod.rec fun x y hxy =>
    Subtype.ext <| Prod.ext (by simp [hxy]) (by simp [hxy])

/-- In a linear order, two symmetric squares are equal if and only if
    they have the same infimum and supremum. -/
theorem eq_iff_inf_sup_eq [LinearOrder α] (s t : Sym2 (α)) :
  s = t ↔ (s.inf,s.sup) = (t.inf,t.sup) := by
  constructor
  · rw [@Sym2.ext_iff]
    intro h
    rw [@Prod.mk_inj]
    by_cases diag: IsDiag s
    · rw [Sym2.isDiag_iff_mem_range_diag] at diag
      simp [IsDiag] at diag
      obtain ⟨b,h'⟩ := diag
      have: diag b = t := by aesop
      aesop
    · let a := (Quot.out s).1
      have ainx:  a ∈ s := by exact out_fst_mem s
      let b := Sym2.Mem.other ainx
      have H:= Sym2.other_ne diag ainx
      have t': b ∈ s ∧ a ∈ s ↔ s = s(b, a) := Sym2.mem_and_mem_iff H
      observe binx: b ∈ s
      change  (Sym2.Mem.other ainx) ∈ s at binx
      have ainy: a ∈ t := by rwa [← h]
      have: b ∈ t ∧ a ∈ t ↔ t = s(b, a) := Sym2.mem_and_mem_iff H
      replace this:t = s(b,a) := by aesop
      simp [ainx,binx] at t'
      have: s = s(b,a) := by
        rw [← t']
        exact binx
      have: s = t := by exact Sym2.ext_iff.mpr h
      exact ⟨congrArg inf this, congrArg sup this⟩
  · let x1 := (Quot.out s).1
    let y1 := (Quot.out t).1
    let y2 := (Quot.out t).2

    by_cases diag: IsDiag s
    · rw [Sym2.isDiag_iff_mem_range_diag] at diag
      simp [IsDiag] at diag
      obtain ⟨b,h'⟩ := diag
      intro H
      simp at H
      obtain ⟨h1,h2⟩ := H
      simp [diag] at h'
      have: s.inf = b := by
        subst h'
        simp_all only [inf_mk, min_self, sup_mk, max_self]
      have: s.sup = b := by
        subst this
        simp_all only
        subst h'
        simp_all only [inf_mk, min_self, sup_mk, max_self]
      have yy: t.inf = b := by
        rename_i this_1
        subst this_1
        simp_all only
      have yy': t.sup = b := by
        rename_i this_1
        subst this_1
        simp_all only
      have: t.inf = t.sup := by rwa [yy']
      have sy1y2: s(y1,y2) = t := by  simp [Sym2,y1,y2]
      have yinfeq: t.inf = y1 ⊓ y2 := by
        rw [← sy1y2]
        simp only [inf_mk]
      rw [yy] at this
      have ysupeq: t.sup = y1 ⊔ y2 := by
        rw [← sy1y2]
        simp only [sup_mk]
      rw [yy'] at this
      have y1eqy2: y1 = y2 := by aesop
      have: y1 = b := by aesop
      rw [← y1eqy2,this] at sy1y2
      rwa [h'] at sy1y2
    · have x1inx:  x1 ∈ s := by exact out_fst_mem s
      let x2' := Sym2.Mem.other x1inx
      have H:= Sym2.other_ne diag x1inx
      have sx1x2': s(x1,x2') = s := by aesop
      have xinfeq: s.inf = x1 ⊓ x2' := by
        rw [← sx1x2']
        simp only [inf_mk]
      have xsupeq: s.sup = x1 ⊔ x2' := by
        rw [← sx1x2']
        simp only [sup_mk]
      rw [xinfeq,xsupeq]
      intro h
      simp at h
      obtain ⟨h1,h2⟩ := h

      have sy1y2: s(y1,y2) = t := by aesop
      have ndiagy: ¬ t.IsDiag := by
        have yinfeq: t.inf = y1 ⊓ y2 := by
          rw [← sy1y2]
          simp only [inf_mk]
        have ysupeq: t.sup = y1 ⊔ y2 := by
          rw [← sy1y2]
          simp only [sup_mk]
        by_contra!
        rw [Sym2.isDiag_iff_mem_range_diag] at this
        simp at this
        obtain ⟨b,hb⟩ := this
        rw [← sy1y2] at hb
        simp [Sym2.diag] at hb
        have: y1 = y2 := by aesop
        have t1: t.sup = b := by aesop
        have t2: t.inf = b := by aesop
        suffices x1 = x2' by
          dsimp [x2'] at this
          rw [← this] at H
          contradiction
        rw [t2] at h1
        rw [t1] at h2
        have: x1 ⊔ x2' = x1 ⊓  x2':= by aesop
        rwa [sup_eq_inf] at this

      have y1inx:  y1 ∈ t := by exact out_fst_mem t
      let y2' := Sym2.Mem.other y1inx
      have Hy:= Sym2.other_ne ndiagy y1inx

      have sy1y2: s(y1,y2') = t := by aesop
      have yinfeq: t.inf = y1 ⊓ y2' := by
        rw [← sy1y2]
        simp only [inf_mk]
      have ysupeq: t.sup = y1 ⊔ y2' := by
        rw [← sy1y2]
        simp only [sup_mk]

      obtain ⟨xy1,xy2⟩ : x1 ⊓ x2' = y1 ⊓ y2' ∧ x1 ⊔ x2' = y1 ⊔ y2' := by aesop

      obtain hx12 | hx12' : x1 < x2' ∨ x2' < x1 := lt_or_gt_of_ne (id (Ne.symm H)) <;>
      obtain hy12 | hy12' : y1 < y2' ∨ y2' < y1 := lt_or_gt_of_ne (id (Ne.symm Hy))
      · observe H1: x1 ⊓ x2' = x1
        observe H2: y1 ⊓ y2' = y1
        observe H3: x1 ⊔ x2' = x2'
        have H4: y1 ⊔ y2' = y2' := by aesop
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
      · observe H1: x1 ⊓ x2' = x1
        observe H2: y1 ⊓ y2' = y2'
        observe H3: x1 ⊔ x2' = x2'
        have H4: y1 ⊔ y2' = y1 := by aesop
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
        exact eq_swap
      · observe H1: x1 ⊓ x2' = x2'
        observe H2: y1 ⊓ y2' = y1
        observe H3: x1 ⊔ x2' = x1
        have H4: y1 ⊔ y2' = y2' := by
          simp
          exact le_of_lt hy12
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
        exact eq_swap
      · observe H1: x1 ⊓ x2' = x2'
        have H2: y1 ⊓ y2' = y2' := by
          simp
          exact le_of_lt hy12'
        observe H3: x1 ⊔ x2' = x1
        have H4: y1 ⊔ y2' = y1 := by
          simp
          exact le_of_lt hy12'
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]

end Sym2
