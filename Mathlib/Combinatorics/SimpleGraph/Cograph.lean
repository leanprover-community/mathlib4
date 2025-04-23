import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hasse

universe u

variable {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
open Sum

/-- Binary disjoint union of graphs -/
@[simps]
def SimpleGraph.Sum {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) :
  SimpleGraph (V ⊕ W) where
    Adj := LiftRel G.Adj H.Adj
    symm := fun
      | _, _, .inl h => .inl (G.symm h)
      | _, _, .inr h => .inr (H.symm h)
    loopless := fun
      | _, .inl h => G.loopless _ h
      | _, .inr h => H.loopless _ h

inductive SimpleGraph.SigmaAux {ι : Type u} {V : ι → Type u} (G : (i : ι) → V i → V i → Prop) :
  ((i : ι) × V i) → ((i : ι) × V i) → Prop
| mk {i : ι} {v w : V i} (h : G i v w) : SigmaAux G ⟨i, v⟩ ⟨i, w⟩

/-- Disjoint union of graphs -/
def SimpleGraph.Sigma {ι : Type u} {V : ι → Type u} (G : (i : ι) → SimpleGraph (V i)) :
  SimpleGraph (Σ i, V i) where
    Adj := SigmaAux (fun i => (G i).Adj)
    symm := fun | _, _, .mk h => .mk ((G _).symm h)
    loopless := fun | _, .mk h => (G _).loopless _ h

/-- Binary join of graphs -/
@[simps]
def SimpleGraph.Join {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) :
  SimpleGraph (V ⊕ W) where
    Adj
    | inl i, inl j => G.Adj i j
    | inr i, inr j => H.Adj i j
    | _, _ => True
    symm
    | inl _, inl _, h | inr _, inr _, h => h.symm
    | inl _, inr _, _ | inr _, inl _, _ => ⟨⟩
    loopless i := by aesop
    -- | inl _, h => G.irrefl h
    -- | inr _, h => H.irrefl h

lemma Join_eq {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) :
    G.Join H = (Gᶜ.Sum Hᶜ)ᶜ := by aesop

#exit

inductive is_cograph : (V : Type u) → SimpleGraph V → Prop
| basic : is_cograph PUnit ⊤
| compl {V : Type u} (G : SimpleGraph V) : is_cograph V G → is_cograph V Gᶜ
| disj_union {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) :
    is_cograph V G → is_cograph W H → is_cograph (V ⊕ W) (G.Sum H)
| equiv {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) : is_cograph V G → G ≃g H →
    is_cograph W H

#check is_cograph.rec

-- #check is_cograph

def SimpleGraph_PEmpty_equiv {G : SimpleGraph PEmpty} : G ≃g (⊤ : SimpleGraph PEmpty) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by simp

def SimpleGraph_PUnit_equiv {G : SimpleGraph PUnit} : G ≃g (⊤ : SimpleGraph PUnit) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by simp

-- lemma is_cograph_punit {V : Type u} {G : SimpleGraph PUnit} : is_cograph PUnit G

-- lemma complete_graph_is_cograph
