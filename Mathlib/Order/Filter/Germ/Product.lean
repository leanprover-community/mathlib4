/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

import Mathlib.Order.Filter.Germ.Basic

/-!
# Bridge between Germ and Product

This file establishes an equivalence between `Filter.Germ l β` and
`Filter.Product l (fun _ => β)` for inhabited codomains.

The new `Filter.Product` is built from partial sections with filter-large domains.
To go from a product back to a germ, we totalize a representative section by
filling outside the domain with `default`.
-/

namespace Filter

variable {α β : Type*} {l : Filter α}

namespace Product

variable [Inhabited β]

/-- Totalize a partial section by using `default` outside its domain. -/
noncomputable def toTotal (s : Product.Section l (fun _ : α => β)) : α → β := by
  classical
  intro a
  exact if h : a ∈ s.dom then s.val ⟨a, h⟩ else default

end Product

namespace Germ

/-- Map a germ to the corresponding product class using full-domain sections. -/
def toProduct : Germ l β → Product l (fun _ : α => β) :=
  Quotient.map' (fun f => Product.ofTotal (l := l) f) (by
    intro f g hfg
    exact hfg.mono fun a ha => ⟨trivial, trivial, ha⟩)

/-- Map a product class back to a germ by totalizing a representative section. -/
noncomputable def Product.toGerm [Inhabited β] : Product l (fun _ : α => β) → Germ l β :=
  Quotient.lift (fun s => (Product.toTotal s : α → β)) (by
    intro s t hst
    refine Quotient.sound ?_
    exact Filter.mem_of_superset hst fun a ⟨hs, ht, hval⟩ =>
      by simp [Product.toTotal, hs, ht, hval])

/-- Equivalence between germs and products for constant families with inhabited codomain. -/
noncomputable def prodEquiv [Inhabited β] : Germ l β ≃ Product l (fun _ : α => β) where
  toFun := toProduct
  invFun := Product.toGerm (l := l)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro f
    apply Quotient.sound
    exact Eventually.of_forall (by intro a; simp [Product.toTotal, Product.ofTotal])
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    exact Filter.mem_of_superset s.dom_mem fun a ha =>
      ⟨trivial, ha, by simp [Product.toTotal, Product.ofTotal, ha]⟩

@[simp]
theorem prodEquiv_ofFun [Inhabited β] (f : α → β) :
    prodEquiv (Filter.Germ.ofFun f : Germ l β) =
      (f : Product l (fun _ : α => β)) := rfl

@[simp]
theorem prodEquiv_coe [Inhabited β] (f : α → β) :
    prodEquiv (f : Germ l β) = (f : Product l (fun _ : α => β)) := rfl

end Germ

end Filter
