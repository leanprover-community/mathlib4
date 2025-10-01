import Mathlib.GroupTheory.FreeGroup.Reduce

variable {α X G : Type*} [Group G] [MulAction G X] [DecidableEq α]

/--
The orbit of the point `x` under the action of the set `s` is the set of all points `g • x`
for `g ∈ s`.
-/
def Orbit (s : Set G) (x : X) := {g • x | g ∈ s}

namespace FreeGroup

/--
All Elements of the free Group that start with a certain letter.
-/
def startsWith (w : α × Bool) := {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

theorem startsWith.ne_one {w : α × Bool} (g : FreeGroup α) (h : g ∈ FreeGroup.startsWith w) :
    g ≠ 1 := by
  intro h1
  simp [h1, startsWith, FreeGroup.toWord_one] at h

variable [MulAction (FreeGroup α) X]

--theorem Orbit_rot (x : X) (w : α × Bool) : {(FreeGroup.mk [w])⁻¹ • y | y ∈ Orbit x w} =
--      ⋃ v ∈ {z : α × Bool | z ≠ (w.1, !w.2)}, Orbit x v := by
theorem Orbit.duplicate (x : X) (w : α × Bool) :
    {(mk [w])⁻¹ • y | y ∈ Orbit (startsWith w) x} =
      ⋃ v ∈ {z : α × Bool | z ≠ (w.1, !w.2)}, Orbit (startsWith v) x := by
  ext i
  simp only [Orbit, startsWith, Set.mem_setOf_eq, inv_mk, exists_exists_and_eq_and, ne_eq,
    Set.mem_iUnion, exists_prop, Prod.exists, Prod.mk.injEq, not_and, Bool.not_eq_not,
    Bool.exists_bool, Bool.false_eq, Bool.true_eq]
  constructor
  .
    rintro ⟨g, ⟨h1,h2⟩⟩
    have h : g.toWord[0]'(by grind) = w := by grind
    subst h2
    by_cases hC : g.toWord.length > 1
    . use (g.toWord[1]'hC).1
      cases hg3 : (g.toWord[1]'hC).2
      . left
        constructor
        . intro h
          have h5 := List.IsChain.getElem (isReduced_toWord : IsReduced g.toWord) 0 (by grind)
                        (by grind) -- des isches
          grind
        . use mk g.toWord.tail
          have h4 : reduce g.toWord.tail = g.toWord.tail := by
              have h6 : IsReduced g.toWord.tail :=
                IsReduced.infix g.isReduced_toWord
                            (by rw [List.IsInfix]; use [g.toWord.head (by grind)]; use []; simp)
              rw [IsReduced.reduce_eq h6]
          constructor
          . grind [toWord_mk, zero_add]
          . rw [← mul_smul]
            congr 1
            rw [show g = mk (g.toWord) by exact Eq.symm mk_toWord, mul_mk]
            refine reduce.exact ?_
            simp only [toWord_mk, reduce_toWord, invRev, List.map_cons, List.map_nil,
              List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, reduce.cons,
              Bool.not_eq_eq_eq_not, Bool.not_not]
            rw [show g.toWord = g.toWord.head (by grind) :: g.toWord.tail by grind]
            grind

      . sorry







    . sorry
