import Mathlib.Data.BundledSet.Basic

namespace BundledSet

variable {p q r : Set α → Prop}

class Implies (p q : Set α → Prop) : Prop where
  implies : ∀ s, p s → q s

instance : Implies p p := ⟨fun _ ↦ id⟩

theorem Implies.comp (p q r : Set α → Prop) [Implies p q] [Implies q r] : Implies p r where
  implies s hs := implies s (implies s hs : q s)

@[coe, simps]
def weaken [Implies p q] (s : BundledSet α p) : BundledSet α q := ⟨s, Implies.implies _ s.2⟩

attribute [norm_cast] weaken_carrier

instance [Implies p q] : CoeHTCT (BundledSet α p) (BundledSet α q) := ⟨weaken⟩

@[simp] theorem weaken_self (s : BundledSet α p) : weaken s = s := rfl

@[simp] theorem mem_weaken [Implies p q] {s : BundledSet α p} {x : α} :
    x ∈ (s : BundledSet α q) ↔ x ∈ s :=
  Iff.rfl

@[simp, norm_cast]
theorem weaken_weaken [Implies p q] [Implies q r] (s : BundledSet α p) :
    ((s : BundledSet α q) : BundledSet α r) = haveI := Implies.comp p q r; ↑s :=
  rfl

end BundledSet
