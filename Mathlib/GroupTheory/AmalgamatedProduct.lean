/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.QuotientGroup


variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] (H : Type*) [Group H]
  (φ : ∀ i, H →* G i) {K : Type*} [Group K]

open Monoid CoprodI Subgroup

def AmalgamatedProduct : Type _ :=
  CoprodI G ⧸ normalClosure
    (⋃ (i : ι) (j : ι), Set.range (fun g => of (φ i g) * (of (φ j g))⁻¹))

namespace AmalgamatedProduct

variable {G H φ}

instance : Group (AmalgamatedProduct G H φ) :=
  QuotientGroup.Quotient.group _

def of {i : ι} : G i →* AmalgamatedProduct G H φ :=
  (QuotientGroup.mk' _).comp CoprodI.of

def lift (f : ∀ i, G i →* K) (hf : ∀ i, (f i).comp (φ i) = 1) :
    AmalgamatedProduct G H φ →* K :=
  QuotientGroup.lift _ (CoprodI.lift f)
    (show normalClosure _ ≤ (CoprodI.lift f).ker
      from normalClosure_le_normal <| by
        simp only [FunLike.ext_iff, MonoidHom.coe_comp, Function.comp_apply,
          MonoidHom.one_apply] at hf
        simp [Set.iUnion_subset_iff, Set.range_subset_iff, SetLike.mem_coe, MonoidHom.mem_ker, hf])

@[simp]
theorem lift_of (f : ∀ i, G i →* K) (hf : ∀ i, (f i).comp (φ i) = 1) {i : ι} (g : G i) :
    (lift f hf) (of g : AmalgamatedProduct G H φ) = f i g := by
  delta AmalgamatedProduct
  simp [lift, of]

@[ext high]
theorem hom_ext {f g : AmalgamatedProduct G H φ →* K}
    (h : ∀ i, f.comp (of : G i →* _) = g.comp of) : f = g := by
  delta AmalgamatedProduct
  ext i x
  simp only [FunLike.ext_iff] at h
  exact h _ _

section Word

variable (G H φ) (n : ι)

structure Word extends CoprodI.Word G where
  normalized : ∀ x ∈ toList, x.2 ∈ (φ x.1).range → x.1 = n

variable {G H φ}

noncomputable def smulWord {i : ι} (g : G i) (w : Word G H φ n) : Word G H φ n :=
  letI := Classical.propDecidable
  if hg1 : g = 1 then w
  else if hg : (∃ x : H, φ i x = g) ∧ i ≠ n then
    have _ : 0 < if i = n then 0 else 1 := by simp [hg.2]
    smulWord (φ n (Classical.choose hg.1)) w
  else
    match w with
    | ⟨⟨[], _, _⟩,_⟩ =>
      ⟨⟨[⟨i, g⟩], by simp_all, by simp_all⟩, by
        simpa using hg⟩
    | ⟨⟨⟨j, h⟩::l, ne_one, chain_ne⟩, normalized⟩ =>
      if hij : i = j
      then smulWord (g * hij ▸ h)
        ⟨⟨l,
          fun x hx => ne_one x (List.mem_cons_of_mem _ hx),
          (List.chain'_cons'.1 chain_ne).2⟩,
          by simp_all; tauto⟩
      else ⟨⟨⟨i, g⟩ :: ⟨j, h⟩ :: l,
        by simp; simp at ne_one; tauto,
        by simp only [ne_eq, List.chain'_cons, hij,
            not_false_eq_true, chain_ne, and_self]⟩,
        by
          simp only [ne_eq, not_and, not_not, forall_exists_index] at hg
          simp only [List.find?, List.mem_cons, MonoidHom.mem_range,
            forall_exists_index, forall_eq_or_imp] at normalized ⊢
          exact ⟨hg, normalized⟩⟩
termination_by smulWord i g w => (w.toList.length,
  letI := Classical.decEq ι; if i = n then 0 else 1)

end Word

end AmalgamatedProduct
