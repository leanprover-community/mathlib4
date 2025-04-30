import Mathlib

open Lean Elab Meta Tactic

section

attribute [- instance] List.decidableChain List.decidableChain'

instance List.decidableChain₁ {α : Type*} {R : α → α → Prop} [DecidableRel R] (a : α) (l : List α) :
    Decidable (Chain R a l) := by
  induction l generalizing a with
  | nil => exact decidable_of_decidable_of_iff (p := True) (by simp)
  | cons b as ih =>
    haveI := ih; exact decidable_of_decidable_of_iff (p := (R a b ∧ Chain R b as)) (by simp)

instance List.decidableChain₂ {α : Type*} {R : α → α → Prop} [DecidableRel R] (l : List α) :
    Decidable (Chain' R l) := by
  cases l
  · exact inferInstanceAs (Decidable True)
  · exact inferInstanceAs (Decidable (Chain _ _ _))

example : (List.range 3000).Chain' (· ≠ ·) := by decide+kernel

end

def List.bitUnion (l : List ℕ) : ℕ := l.foldr (1 <<< · ||| ·) 0

lemma List.mem_of_shiftRight_foldr_and_one
    {l : List ℕ} (i : ℕ) (h : l.bitUnion >>> i &&& 1 = 1) :
    i ∈ l := by
  induction l with
  | nil => simp [bitUnion] at h
  | cons head tail ih =>
    simp only [List.foldr_cons, ne_eq, Nat.shiftRight_or_distrib,
      Nat.and_one_is_mod, Nat.or_mod_two_eq_one, bitUnion] at h
    rcases h with h | h
    · rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq_mul_pow, one_mul] at h
      by_cases hi : head < i
      · rw [Nat.div_eq_zero_iff.mpr (.inr (by gcongr; simp))] at h
        aesop
      obtain ⟨j, rfl⟩ := exists_add_of_le (le_of_not_lt hi)
      · rw [add_comm, pow_add, Nat.mul_div_cancel _ (by positivity)] at h
        cases j <;> simp at *
    · simp [ih (Nat.and_one_is_mod _ ▸ h)]

lemma Nat.sub_shiftLeft_distrib (a b c : ℕ) :
    (a - b) <<< c = a <<< c - b <<< c := by
  simp [Nat.shiftLeft_eq_mul_pow, Nat.sub_mul]

lemma Nat.shiftLeft_mono (a : ℕ) {b c : ℕ} (h : b ≤ c) :
    a <<< b ≤ a <<< c := by
  simp only [Nat.shiftLeft_eq_mul_pow]
  gcongr
  simp

@[simp]
lemma sub_one_div_self (n : ℕ) : (n - 1) / n = 0 := by
  cases n <;> simp

lemma List.perm_range_of_bitUnion_eq_length_eq {n : ℕ} {l : List ℕ} (h : l.bitUnion = 1 <<< n - 1)
    (hl : l.length = n) : l.Perm (List.range n) := by
  rw [← Multiset.coe_eq_coe, Multiset.coe_range]
  refine .symm (Multiset.eq_of_le_of_card_le ?_ ?_)
  · rw [Multiset.le_iff_subset (Multiset.nodup_range n)]
    simp only [Multiset.subset_iff, Multiset.mem_range, Multiset.mem_coe]
    refine fun i hi ↦ List.mem_of_shiftRight_foldr_and_one _ ?_
    rw [h]
    obtain ⟨j, rfl⟩ := exists_add_of_le hi.le
    trans ((1 <<< j - 1) <<< i + (1 <<< i - 1)) >>> i &&& 1
    · congr 2
      rw [Nat.sub_shiftLeft_distrib, ← Nat.shiftLeft_add, ← Nat.add_sub_assoc,
        Nat.sub_add_cancel, add_comm]
      · exact Nat.shiftLeft_mono _ (by simp)
      · exact Nat.le_shiftLeft
    · rw [Nat.shiftRight_eq_div_pow, Nat.add_div_eq_of_add_mod_lt]
      · cases j <;> simp [Nat.shiftLeft_eq_mul_pow] at *
      · simp [Nat.shiftLeft_eq_mul_pow]
  · simp [hl]

def provePerm (lhsE : Expr) (n : Nat) : TacticM Expr := do
  let goal₁ ← mkEq (← mkAppM ``List.bitUnion #[lhsE]) (mkNatLit (1 <<< n - 1))
  let goal₂ ← mkEq (← mkAppM ``List.length #[lhsE]) (mkNatLit n)
  let pf₁ ← evalDecideCore.doKernel `decide goal₁
  let pf₂ ← evalDecideCore.doKernel `decide goal₂
  return mkApp4 (mkConst ``List.perm_range_of_bitUnion_eq_length_eq) (mkNatLit n) lhsE pf₁ pf₂

elab "prove_perm" : tactic => do
  let goal ← getMainGoal
  let g := (← goal.getType'').consumeMData
  let some (tyE, lhsE, rhsE) := g.app3? ``List.Perm      | throwError "not a List.Perm"
  unless tyE.isConstOf ``Nat                            do throwError "not a nat perm"
  let some nE := rhsE.app1? ``List.range                 | throwError "not a List.range"
  let some n := nE.nat?                                  | throwError "not a literal nat"
  goal.assign (← provePerm lhsE n)

example : List.Perm [1, 2, 3, 0] (List.range 4) := by prove_perm
example : List.Perm (List.range 3) (List.range 3) := by prove_perm

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option pp.deepTerms true

lemma test2 : List.Perm [0, 1, 2] (List.range 3) := by prove_perm

section DisjointCert

universe u
variable {X : Type u} [LinearOrder X] {n₁ n₂ : ℕ} {f g : ℕ → X}

abbrev DisjointCert.ListAll (l : List (X × (ℕ ⊕ ℕ))) : Prop :=
  l.all fun p ↦ p.2.elim (p.1 == f ·) (p.1 == g ·)

abbrev DisjointCert.Chain'Fst (l : List (X × (ℕ ⊕ ℕ))) : Prop :=
  (l.map Prod.fst).Chain' (· < ·)

abbrev DisjointCert.mapInl (l : List (X × (ℕ ⊕ ℕ))) : List ℕ :=
  l.filterMap fun p ↦ p.2.elim .some fun _ ↦ .none

abbrev DisjointCert.mapInr (l : List (X × (ℕ ⊕ ℕ))) : List ℕ :=
  l.filterMap fun p ↦ p.2.elim (fun _ ↦ .none) .some

variable (n₁ n₂ f g) in
structure DisjointCert where
  list : List (X × (ℕ ⊕ ℕ))
  list_all : list.all fun p ↦ p.2.elim (p.1 == f ·) (p.1 == g ·)
  chain_fst : (list.map Prod.fst).Chain' (· < ·)
  perm_inl : (list.filterMap fun p ↦ p.2.elim .some fun _ ↦ .none).Perm (List.range n₁)
  perm_inr : (list.filterMap fun p ↦ p.2.elim (fun _ ↦ .none) .some).Perm (List.range n₂)

lemma DisjointCert.eq_of_inl_mem (cert : DisjointCert n₁ n₂ f g) {x n}
    (hx : (x, .inl n) ∈ cert.list) : x = f n :=
  beq_iff_eq.mp (List.all_eq_true.mp cert.list_all _ hx)

lemma DisjointCert.eq_of_inr_mem (cert : DisjointCert n₁ n₂ f g) {x n}
    (hx : (x, .inr n) ∈ cert.list) : x = g n :=
  beq_iff_eq.mp (List.all_eq_true.mp cert.list_all _ hx)

lemma DisjointCert.filter_isLeft_perm (cert : DisjointCert n₁ n₂ f g) :
    (cert.list.filter (·.2.isLeft)).Perm ((List.range n₁).map fun i ↦ (f i, .inl i)) := by
  refine .trans (.of_eq ?_) (.map _ cert.perm_inl)
  rw [← List.filterMap_eq_map, List.filterMap_filterMap, ← List.filterMap_eq_filter]
  apply List.filterMap_congr
  rintro ⟨x, n | n⟩ hx
  · simp [cert.eq_of_inl_mem hx]
  · simp

lemma DisjointCert.map_inl_range_subPerm (cert : DisjointCert n₁ n₂ f g) :
    ((List.range n₁).map fun i ↦ (f i, .inl i)).Subperm cert.list :=
  cert.filter_isLeft_perm.symm.subperm.trans List.filter_sublist.subperm

lemma DisjointCert.filter_isRight_perm (cert : DisjointCert n₁ n₂ f g) :
    (cert.list.filter (·.2.isRight)).Perm ((List.range n₂).map fun i ↦ (g i, .inr i)) := by
  refine .trans (.of_eq ?_) (.map _ cert.perm_inr)
  rw [← List.filterMap_eq_map, List.filterMap_filterMap, ← List.filterMap_eq_filter]
  apply List.filterMap_congr
  rintro ⟨x, n | n⟩ hx
  · simp
  · simp [cert.eq_of_inr_mem hx]

lemma DisjointCert.map_inr_range_subPerm (cert : DisjointCert n₁ n₂ f g) :
    ((List.range n₂).map fun i ↦ (g i, .inr i)).Subperm cert.list :=
  cert.filter_isRight_perm.symm.subperm.trans List.filter_sublist.subperm

lemma DisjointCert.forall_ne (cert : DisjointCert n₁ n₂ f g) :
    ∀ a₁ < n₁, ∀ a₂ < n₂, f a₁ ≠ g a₂ := by
  intros a₁ ha₁ a₂ ha₂
  have h₁ := cert.map_inl_range_subPerm.subset (List.mem_map_of_mem (List.mem_range.mpr ha₁))
  have h₂ := cert.map_inr_range_subPerm.subset (List.mem_map_of_mem (List.mem_range.mpr ha₂))
  have := (List.chain'_iff_pairwise.mp cert.chain_fst).nodup
  rw [List.Nodup, List.pairwise_map] at this
  exact this.forall (fun _ _ ↦ Ne.symm) h₁ h₂ (by simp)

lemma DisjointCert.disjoint_list (cert : DisjointCert n₁ n₂ f g) :
    ((List.range n₁).map f).Disjoint ((List.range n₂).map g) := by
  simpa [List.disjoint_iff_ne] using cert.forall_ne

lemma DisjointCert.disjoint (cert : DisjointCert n₁ n₂ f g) :
    Disjoint (f '' Set.Iio n₁) (g '' Set.Iio n₂) := by
  simpa [Set.disjoint_iff_forall_ne] using cert.forall_ne

universe v

instance {α : Type u} {β : Type v} [ToExpr α] [ToExpr β] [ToLevel.{u}] [ToLevel.{v}] :
    ToExpr (α ⊕ β) where
  toExpr
  | .inl a => mkApp3 (mkConst ``Sum.inl [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (toTypeExpr β) (toExpr a)
  | .inr b => mkApp3 (mkConst ``Sum.inr [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (toTypeExpr β) (toExpr b)
  toTypeExpr := mkApp2 (mkConst ``Sum [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (toTypeExpr β)

instance {α : Type u} {β : Type v} [ToExpr α] [ToExpr β] [ToLevel.{u}] [ToLevel.{v}] :
    ToExpr (α × β) where
  toExpr
  | (a, b) => mkApp4 (mkConst ``Prod.mk [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (toTypeExpr β) (toExpr a) (toExpr b)
  toTypeExpr := mkApp2 (mkConst ``Prod [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (toTypeExpr β)

-- set_option trace.Meta.synthInstance true in
variable (n₁ n₂ f g) in
def DisjointCert.mkExpr (instexpr : Expr) (fexpr : Expr) (gexpr : Expr) [ToLevel.{u}] [ToExpr X] :
    TacticM Expr := do
  let l : List (X × (ℕ ⊕ ℕ)) := ((List.range n₁).map (fun i ↦ (f i, Sum.inl i)) ++
    (List.range n₂).map (fun i ↦ (g i, Sum.inr i))).mergeSort (fun a b ↦ a.1 ≤ b.1)
  let lE := toExpr l
  let listAllType := mkAppN (mkConst ``ListAll [ToLevel.toLevel.{u}])
    #[toTypeExpr X, instexpr, fexpr, gexpr, lE]
  let listAll ← evalDecideCore.doKernel `decide listAllType
  let chain'FstType := mkAppN (mkConst ``Chain'Fst [ToLevel.toLevel.{u}])
    #[toTypeExpr X, instexpr, lE]
  let chain'Fst ← evalDecideCore.doKernel `decide chain'FstType
  let permInl ← provePerm (mkApp2 (mkConst ``mapInl [ToLevel.toLevel.{u}]) (toTypeExpr X) lE) n₁
  let permInr ← provePerm (mkApp2 (mkConst ``mapInr [ToLevel.toLevel.{u}]) (toTypeExpr X) lE) n₂
  return mkAppN (mkConst ``mk [ToLevel.toLevel.{u}])
    #[toTypeExpr X, instexpr, mkNatLit n₁, mkNatLit n₂, fexpr, gexpr,
      lE, listAll, chain'Fst, permInl, permInr]

elab "mk_disjoint_cert" : tactic => do
  let goal ← getMainGoal
  let g := (← goal.getType'').consumeMData
  if ! g.isAppOfArity ``DisjointCert 6 then throwError "not a DisjointCert"
  let arg := g.getAppArgs
  let some n₁ := arg[2]!.nat? | throwError s!"{arg[2]!} is not a literal nat"
  let some n₂ := arg[3]!.nat? | throwError s!"{arg[3]!} is not a literal nat"
  let ret ← DisjointCert.mkExpr n₁ n₂ (2 * ·) (2 * · + 1) arg[1]!
    arg[4]! arg[5]!
  goal.assign ret

example : Disjoint ((2 * ·) '' Set.Iio 1000) ((2 * · + 1) '' Set.Iio 1000) := by
  apply DisjointCert.disjoint
  mk_disjoint_cert

end DisjointCert
