section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] Vector.Perm.isSetoid

private def fromVector : Vector α 2 → α × α
  | ⟨[a, b], _⟩ => (a, b)

private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .inr ⟨h₁, h₂⟩ => by
          rw [h₁, h₂]
          first | done | apply List.Perm.swap'; rfl }

/-- The symmetric square is equivalent to length-2 vectors up to permutations. -/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2)
    where
  toFun :=
    Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        cases' x with _ x; · simp at hx
        cases' x with _ x; · simp at hx
        cases' x with _ x; swap
        · exfalso
          simp at hx
        cases' y with _ y; · simp at hy
        cases' y with _ y; · simp at hy
        cases' y with _ y; swap
        · exfalso
          simp at hy
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · constructor
        apply Sym2.Rel.swap)
  left_inv := by apply Sym2.ind; aesop (add norm unfold [Sym2.fromVector])
  right_inv x := by
    refine' x.recOnSubsingleton fun x => _
    · cases' x with x hx
      cases' x with _ x
      · simp at hx
      cases' x with _ x
      · simp at hx
      cases' x with _ x
      swap
      · exfalso
        simp at hx
      rfl
#align sym2.sym2_equiv_sym' Sym2.sym2EquivSym'

/-- The symmetric square is equivalent to the second symmetric power. -/
def equivSym (α : Type*) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm
#align sym2.equiv_sym Sym2.equivSym

/-- The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equivSym`, but it's provided
in case the definition for `Sym` changes.) -/
def equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s = 2 } :=
  equivSym α
#align sym2.equiv_multiset Sym2.equivMultiset

end SymEquiv

