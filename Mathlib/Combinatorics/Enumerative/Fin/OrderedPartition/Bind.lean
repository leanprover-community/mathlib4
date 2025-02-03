import Mathlib.Combinatorics.Enumerative.Fin.OrderedPartition.Basic

namespace Fin

namespace OrderedPartition

variable {n : ℕ}

theorem ofParts.isAntisymm_aux (s : Finset (Part n)) (hd : s.toSet.PairwiseDisjoint Part.range) :
    IsAntisymm ((fun p : s ↦ p.1.last) ⁻¹'o (· ≤ ·)) :=
  Order.Preimage.isAntisymm _

def ofParts (s : Finset (Part n)) (hd : s.toSet.PairwiseDisjoint Part.range)
    (hU : s.biUnion Part.range = .univ) : OrderedPartition n where
  length := s.card
  part i := (s.attach.sort ((fun p : s ↦ p.1.last) ⁻¹'o (· ≤ ·)))[i]'(_)
  part_last_strictMono := _
  disjoint := _
  cover := _

def bind (c : OrderedPartition n) (cs : ∀ i, OrderedPartition (c.part i).size) :
    OrderedPartition n :=
  ofParts (Finset.univ.biUnion fun i ↦ (cs i).parts.map (Part.mapEmb (c.part i).emb)) _ _

end OrderedPartition

end Fin
