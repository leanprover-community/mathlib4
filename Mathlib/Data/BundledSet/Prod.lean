import Mathlib.Data.BundledSet.Weaken
import Mathlib.Data.BundledSet.Lattice
import Mathlib.Data.Set.Prod

namespace BundledSet

section Prod

class ProdPred (α β : Type*) (p : Set α → Prop) (q : Set β → Prop)
    (r : outParam <| Set (α × β) → Prop) : Prop where
  prod {s t} : p s → q t → r (s ×ˢ t)

variable {α β : Type*} {p : Set α → Prop} {q : Set β → Prop} {r : outParam <| Set (α × β) → Prop}
  [ProdPred α β p q r] {s : BundledSet α p} {t : BundledSet β q}

instance : SProd (BundledSet α p) (BundledSet β q) (BundledSet (α × β) r) where
  sprod s t := ⟨s.1 ×ˢ t.1, ProdPred.prod s.2 t.2⟩

@[simp] lemma mem_prod {x : α × β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t := .rfl

variable (s t) in
@[simp] lemma carrier_prod : (s ×ˢ t).1 = s.1 ×ˢ t.1 := rfl

lemma mk_mem_prod {x : α} {y : β} (hx : x ∈ s) (hy : y ∈ t) : (x, y) ∈ s ×ˢ t := ⟨hx, hy⟩

@[gcongr]
lemma prod_mono {s' t'} (hs : s ≤ s') (ht : t ≤ t') : s ×ˢ t ≤ s' ×ˢ t' :=
  Set.prod_mono hs ht

@[gcongr]
lemma prod_mono_left {s'} (hs : s ≤ s') : s ×ˢ t ≤ s' ×ˢ t := prod_mono hs le_rfl

@[gcongr]
lemma prod_mono_right {t'} (ht : t ≤ t') : s ×ˢ t ≤ s ×ˢ t' := prod_mono le_rfl ht

@[simp]
lemma top_prod_top [UnivPred α p] [UnivPred β q] [UnivPred (α × β) r] :
    (⊤ : BundledSet α p) ×ˢ (⊤ : BundledSet β q) = ⊤ :=
  carrier_injective Set.univ_prod_univ

lemma inf_prod [InterPred α p] [InterPred (α × β) r] (s s' : BundledSet α p) (t : BundledSet β q) :
    (s ⊓ s') ×ˢ t = (s ×ˢ t) ⊓ (s' ×ˢ t) :=
  carrier_injective Set.inter_prod

lemma prod_inf [InterPred β q] [InterPred (α × β) r] (s : BundledSet α p) (t t' : BundledSet β q) :
    s ×ˢ (t ⊓ t') = (s ×ˢ t) ⊓ (s ×ˢ t') :=
  carrier_injective Set.prod_inter

lemma prod_inf_prod [InterPred α p] [InterPred β q] [InterPred (α × β) r]
    (s s' : BundledSet α p) (t t' : BundledSet β q) :
    (s ×ˢ t) ⊓ (s' ×ˢ t') = (s ⊓ s') ×ˢ (t ⊓ t') :=
  carrier_injective Set.prod_inter_prod

end Prod

end BundledSet
