import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicGeometry.EllipticCurve.Schoof.Decidable
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.Data.Nat.Size
import Mathlib.Order.CompletePartialOrder
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

universe u

variable {M : Type u} [AddCancelMonoid M] {a bl br d : M}

def NotNMultipleWithin (a bl br : M) (l r : Nat) : Prop :=
  ∀ i ∈ Set.Ico l r, i • a + bl ≠ br

lemma NotNMultipleWithin.trans {l m r : ℕ}
    (h₁ : NotNMultipleWithin a bl br l m) (h₂ : NotNMultipleWithin a bl br m r) :
    NotNMultipleWithin a bl br l r :=
  fun i ⟨hli, hir⟩ ↦ (lt_or_ge i m).elim (h₁ _ ⟨hli, ·⟩) (h₂ _ ⟨·, hir⟩)

lemma NotNMultipleWithin.add {l r : ℕ} :
    NotNMultipleWithin a (bl + d) (br + d) l r ↔ NotNMultipleWithin a bl br l r := by
  simp [NotNMultipleWithin, ← add_assoc]

lemma NotNMultipleWithin.add' {l r d : ℕ} :
    NotNMultipleWithin a bl br (l + d) (r + d) ↔
      NotNMultipleWithin a (d • a + bl) br l r := by
  simp [NotNMultipleWithin, ← Set.image_add_const_Ico, forall_comm (β := (_ : ℕ) = _),
    forall_comm (α := ℕ), add_nsmul, add_assoc]

lemma NotNMultipleWithin.of_lt {l r : ℕ} (h : r ≤ l) :
    NotNMultipleWithin a bl br l r := by
  simp only [NotNMultipleWithin,Set.Ico_eq_empty (not_lt_of_le h),
    Set.mem_empty_iff_false, ne_eq, IsEmpty.forall_iff, implies_true]

lemma NotNMultipleWithin.self {l : ℕ} :
    NotNMultipleWithin a bl br l l :=
  .of_lt le_rfl

lemma NotNMultipleWithin.iff_sub {l r : ℕ} :
    NotNMultipleWithin a bl br l r ↔ NotNMultipleWithin a (l • a + bl) br 0 (r - l) := by
  by_cases hlr : l ≤ r
  · rw [← add', zero_add, Nat.sub_add_cancel hlr]
  · simp [of_lt (lt_of_not_le hlr).le, Nat.sub_eq_zero_iff_le.mpr (lt_of_not_le hlr).le, self]

lemma NotNMultipleWithin.mul {n k : ℕ} :
    NotNMultipleWithin a bl br 0 (n * k + 1) ↔
      bl ≠ br ∧
        Disjoint ((fun i ↦ ((i + 1) * k) • a + bl) '' Set.Iio n) ((· • a + br) '' Set.Iio k) := by
  simp only [Set.disjoint_iff_forall_ne, Set.mem_image, Set.mem_Iio, ne_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · refine fun H ↦ ⟨?_, fun i hin j hjk e ↦ H ((i + 1) * k - j) ?_ ?_⟩
    · simpa using H 0 (by simp)
    · simp only [Set.mem_Ico, zero_le, true_and, Nat.lt_succ]
      exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right _ (Nat.succ_le.mpr hin))
    · refine add_right_injective (j • a) (.trans ?_ e)
      simp only [← add_assoc, ← add_nsmul]
      rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      exact hjk.le.trans (by rw [Nat.succ_mul]; exact k.le_add_left _)
  · rintro ⟨hlr, H⟩ i ⟨-, hi⟩ heq
    by_cases hk : k = 0
    · simp [show i = 0 by simpa [hk] using hi, hlr] at heq
    by_cases hi' : k ∣ i
    · obtain ⟨_ | i, rfl⟩ := hi'
      · simp [hlr] at heq
      · refine H i ?_ 0 (Nat.pos_iff_ne_zero.mpr hk) (by simpa [mul_comm _ k])
        apply Nat.lt_of_mul_lt_mul_right (a := k)
        apply Nat.lt_of_add_lt_add_right (n := 1)
        refine lt_of_le_of_lt ?_ hi
        rwa [mul_comm, Nat.mul_succ, Nat.add_le_add_iff_left, Nat.one_le_iff_ne_zero]
    refine H (i / k) ?_ (k - i % k) ?_ ?_
    · by_contra! hin
      have : i = n * k := (Nat.lt_succ_iff.mp hi).antisymm
        ((Nat.mul_le_mul_right k hin).trans (Nat.div_mul_le_self i k))
      exact hi' ⟨_, this.trans (mul_comm _ _)⟩
    · simp [Nat.pos_iff_ne_zero, ← Nat.dvd_iff_mod_eq_zero, hi', hk]
    · rw [← heq, ← add_assoc, ← add_nsmul]
      congr 2
      apply Nat.add_left_cancel (n := i % k)
      rw [Nat.succ_mul, ← add_assoc, Nat.mod_add_div', ← add_assoc, ← Nat.add_sub_assoc,
        Nat.add_sub_cancel_left, add_comm]
      exact (Nat.mod_lt _ (Nat.pos_iff_ne_zero.mpr hk)).le

variable (a bl) in
abbrev NotNMultipleWithin.fun₁ (k l : ℕ) := fun i ↦ ((i + 1) * k) • a + (l • a + bl)

variable (a br) in
abbrev NotNMultipleWithin.fun₂ := fun x : ℕ ↦ x • a + br

lemma NotNMultipleWithin.iff_forall_lt {l r : ℕ} :
    NotNMultipleWithin a bl br l r ↔ ∀ i < r - l, (i + l) • a + bl ≠ br := by
  rw [iff_sub]
  simp [NotNMultipleWithin, Fin.forall_iff, add_nsmul, add_assoc]

lemma NotNMultipleWithin.of_cond
      (k l r : ℕ)
      (h₁ : l • a + bl ≠ br)
      (h₂ : Disjoint (fun₁ a bl k l '' Set.Iio ((r - l) / k)) (fun₂ a br '' Set.Iio k))
      (h₃ : ∀ i < (r - l) % k - 1, (i + ((r - l) / k * k + 1)) • a + (l • a + bl) ≠ br) :
    NotNMultipleWithin a bl br l r := by
  refine NotNMultipleWithin.iff_sub.mpr ?_
  refine ((mul (n := (r - l) / k) (k := k)).mpr ⟨h₁, h₂⟩).trans ?_
  rw [iff_forall_lt]
  simpa only [← Nat.sub_sub, ← Nat.mod_eq_sub_div_mul]

open Qq
-- #check assumeInstancesCommute

-- set_option trace.Meta.synthInstance true in
open NotNMultipleWithin in
def mkNotNMultipleWithin [LinearOrder M]
    [ToLevel.{u}] [ToExpr M] (a bl br : M) (l r : Nat) : TacticM Expr := do
  have u : Level := ToLevel.toLevel.{u}
  have ME : Q(Type u) := toTypeExpr M
  let instAddCancelMonoid : Q(AddCancelMonoid $ME) ← synthInstanceQ q(AddCancelMonoid $ME)
  let instLinearOrder : Q(LinearOrder $ME) ← synthInstanceQ q(LinearOrder $ME)
  let k := (r - l).sqrt
  have kE : Q(Nat) := mkNatLit k
  have aE : Q($ME) := toExpr a
  have blE : Q($ME) := toExpr bl
  have brE : Q($ME) := toExpr br
  let h₁ : Q($l • $aE + $blE ≠ $brE) ← evalDecideCore.doKernel `decide q($l • $aE + $blE ≠ $brE)
  let d₁ := (r - l) / k
  have d₁E : Q(Nat) := mkNatLit d₁
  have : $d₁E =Q ($r - $l) / $kE := ⟨⟩
  let disj : Q(DisjointCert $d₁E $kE (fun₁ $aE $blE $kE $l) (fun₂ $aE $brE)) ←
    DisjointCert.mkExpr d₁ k (fun₁ a bl k l) (fun₂ a br) instLinearOrder
      q(fun₁ $aE $blE $kE $l) q(fun₂ $aE $brE)
  let h₂ := q(DisjointCert.disjoint $disj)
  let x₁ := (r - l) % k - 1
  let x₂ := (r - l) / k * k + 1
  have : $d₁E =Q ($r - $l) / $kE := ⟨⟩
  have x₁E : Q(Nat) := mkNatLit x₁
  have x₂E : Q(Nat) := mkNatLit x₂
  have : $x₁E =Q ($r - $l) % $kE - 1 := ⟨⟩
  have : $x₂E =Q ($r - $l) / $kE * $kE + 1 := ⟨⟩
  let h₃ : Q(∀ i < $x₁E, (i + $x₂E) • $aE + ($l • $aE + $blE) ≠ $brE) ←
    evalDecideCore.doKernel `decide q(∀ i < $x₁E, (i + $x₂E) • $aE + ($l • $aE + $blE) ≠ $brE)
  have ret : Q(@NotNMultipleWithin $ME $instAddCancelMonoid $aE $blE $brE $l $r) :=
    q(NotNMultipleWithin.of_cond $kE $l $r $h₁ $h₂ $h₃)
  return ret

#check Nat.Prime
elab "prove_NotNMultipleWithin" : tactic => do
  let goal ← getMainGoal
  let g := (← goal.getType'').consumeMData
  if ! g.isAppOfArity ``NotNMultipleWithin 7 then throwError "not a NotNMultipleWithin"
  let arg := g.getAppArgs
  let some pE := arg[0]!.app1? ``ZMod      | throwError "not `ZMod"
  let some p := pE.nat?                    | throwError s!"{pE} is not a literal nat"
  let some a := pE.o


  let a := evalExpr M arg[2]!
  let some n₁ := arg[2]!.nat? | throwError s!"{arg[2]!} is not a literal nat"
  let some n₂ := arg[3]!.nat? | throwError s!"{arg[3]!} is not a literal nat"
  let ret ← DisjointCert.mkExpr n₁ n₂ (2 * ·) (2 * · + 1) arg[1]!
    arg[4]! arg[5]!
  goal.assign ret

open Qq in
def Lean.Expr.weierstrassCurvePointNat?
      (e : Expr) {R : Type*} [CommRing R] [DecidableEq R] (E : WeierstrassCurve.Affine R) :
    Option E.Point := do
  if e.isAppOfArity ``WeierstrassCurve.Affine.Point.some 6 then
    let arg := e.getAppArgs
    let some x := arg[3]!.nat? | failure
    let some y := arg[4]!.nat? | failure
    if h : E.Nonsingular x y then
      return .some h
    else failure
  else if e.isAppOfArity ``WeierstrassCurve.Affine.Point.zero 3 then
    return 0
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    let some (E, n, _) := e.app3? ``OfNat.ofNat | failure
    let some n := n.nat? | failure
    if n = 0 then
      return 0
    else failure
  else failure

open Qq in
def Lean.Expr.weierstrassCurveNat?
      (e : Expr) (R : Type*) [Semiring R] :
    Option (WeierstrassCurve.Affine R) := do
  if e.isAppOfArity ``WeierstrassCurve.mk 6 then
    let arg := e.getAppArgs
    let some a₁ := arg[1]!.nat? | failure
    let some a₂ := arg[2]!.nat? | failure
    let some a₃ := arg[3]!.nat? | failure
    let some a₄ := arg[4]!.nat? | failure
    let some a₆ := arg[5]!.nat? | failure
    return ⟨a₁, a₂, a₃, a₄, a₆⟩
  else
    failure

open Qq in
def Lean.Expr.weierstrassCurveAffineNat?
      (e : Expr) (R : Type*) [Semiring R] :
    Option (WeierstrassCurve.Affine R) := .map WeierstrassCurve.toAffine <| do
  let some (_, e') := e.app2? ``WeierstrassCurve.toAffine | e.weierstrassCurveNat? R
  e'.weierstrassCurveNat? R

deriving instance Repr for WeierstrassCurve.Affine.Point

instance {R : Type*} [CommRing R] [ToString R] (E : WeierstrassCurve.Affine R) :
    ToString E.Point where
  toString
  | .zero => "0"
  | .some (x := x) (y := y) _ => s!"({x}, {y})"

instance : ∀ (p : ℕ), ToString (ZMod p)
  | 0 => inferInstanceAs (ToString Int)
  | n + 1 => inferInstanceAs (ToString (Fin (n + 1)))

instance : ∀ (p : ℕ), DecidableEq (ZMod p)
  | 0 => inferInstanceAs (DecidableEq Int)
  | n + 1 => inferInstanceAs (DecidableEq (Fin (n + 1)))

def E : WeierstrassCurve (ZMod 37) :=
  ⟨0, -1, 0, 27, -81⟩

elab "test" t:term : tactic => do
  let t ← elabTerm t .none
  -- dbg_trace s!"{t}"
  dbg_trace s!"{t.weierstrassCurvePointNat? E}"

instance : Fact (Nat.Prime 37) := ⟨by decide⟩
#synth Field (ZMod 37)
instance : E.IsElliptic := by decide

#synth AddCommGroup E.toAffine.Point

#eval toString (((.some (x := 10) (y := 33) (by decide) : E.toAffine.Point) +
  (.some (x := 10) (y := 33) (by decide) : E.toAffine.Point)))

#reduce [1, 4, 5, 3, 7, 2].mergeSort

example :
    NotNMultipleWithin (.some (x := 10) (y := 33) (by decide) : E.toAffine.Point) 0 0 10 20 := by
  test (.some (x := 10) (y := 33) (by decide) : E.toAffine.Point)
  sorry
#min_imports
