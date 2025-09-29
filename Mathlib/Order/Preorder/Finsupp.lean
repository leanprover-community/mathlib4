/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
import Mathlib.Data.Finsupp.Defs

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `M` to `ι →₀ M`.
-/

assert_not_exists CompleteLattice

noncomputable section

open Finset

namespace Finsupp
variable {ι M : Type*} [Zero M]

section LE
variable [LE M] {f g : ι →₀ M}

instance instLE : LE (ι →₀ M) where le f g := ∀ i, f i ≤ g i

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := .rfl

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := .rfl

/-- The order on `Finsupp`s over a partial order embeds into the order on functions -/
@[simps]
def orderEmbeddingToFun : (ι →₀ M) ↪o (ι → M) where
  toFun f := f
  inj' := DFunLike.coe_injective
  map_rel_iff' := coe_le_coe

end LE

section Preorder
variable [Preorder M] {f g : ι →₀ M} {i : ι} {a b : M}

instance preorder : Preorder (ι →₀ M) where
  le_refl  _ _ := le_rfl
  le_trans _ _ _ hfg hgh i := (hfg i).trans (hgh i)

lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl

lemma coe_mono : Monotone (Finsupp.toFun : (ι →₀ M) → ι → M) := fun _ _ ↦ id

lemma coe_strictMono : Monotone (Finsupp.toFun : (ι →₀ M) → ι → M) := fun _ _ ↦ id

end Preorder

instance partialorder [PartialOrder M] : PartialOrder (ι →₀ M) where
  le_antisymm _f _g hfg hgf := ext fun i ↦ (hfg i).antisymm (hgf i)

section SemilatticeInf
variable [SemilatticeInf M]

instance semilatticeInf : SemilatticeInf (ι →₀ M) where
  inf := zipWith (· ⊓ ·) (inf_idem _)
  inf_le_left _f _g _i := inf_le_left
  inf_le_right _f _g _i := inf_le_right
  le_inf _f _g _i h1 h2 s := le_inf (h1 s) (h2 s)

@[simp] lemma inf_apply (f g : ι →₀ M) (i : ι) : (f ⊓ g) i = f i ⊓ g i := rfl

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup M]

instance semilatticeSup : SemilatticeSup (ι →₀ M) where
  sup := zipWith (· ⊔ ·) (sup_idem _)
  le_sup_left _f _g _i := le_sup_left
  le_sup_right _f _g _i := le_sup_right
  sup_le _f _g _h hf hg i := sup_le (hf i) (hg i)

@[simp]
lemma sup_apply (f g : ι →₀ M) (i : ι) : (f ⊔ g) i = f i ⊔ g i := rfl

end SemilatticeSup

section Lattice
variable [Lattice M] (f g : ι →₀ M)

instance lattice : Lattice (ι →₀ M) where
  __ := Finsupp.semilatticeInf
  __ := Finsupp.semilatticeSup

variable [DecidableEq ι]

lemma support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]

lemma support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice
end Finsupp
