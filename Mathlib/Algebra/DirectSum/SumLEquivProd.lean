import Mathlib.Algebra.DirectSum.Module
universe v w u

set_option autoImplicit false
variable {ια ιβ k : Type*} [CommRing k] {α : (i : ια) → Type u}
    {β : (i : ιβ) → Type u}

namespace Sum
variable [Zero ια] [Zero ιβ]

instance instZero [∀ (i : ια), Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (i : ια ⊕ ιβ) : Zero (Sum.elim α β i) :=
  match i with
  | Sum.inl i => inferInstanceAs (Zero (α i))
  | Sum.inr i => inferInstanceAs (Zero (β i))

instance instAdd [∀ (i : ια), Add (α i)]
    [∀ i : ιβ, Add (β i)] (i : ια ⊕ ιβ) : Add (Sum.elim α β i) :=
  match i with
  | Sum.inl i => inferInstanceAs (Add (α i))
  | Sum.inr i => inferInstanceAs (Add (β i))

-- is there a slicker way to do this?
instance instAddZeroClass [∀ (i : ια), AddZeroClass (α i)]
    [∀ i : ιβ, AddZeroClass (β i)] (i : ια ⊕ ιβ) : AddZeroClass (Sum.elim α β i) :=
  { zero_add := fun _ => match i with
    | Sum.inl i => zero_add (M := α i) _
    | Sum.inr i => zero_add (M := β i) _
    add_zero := fun _ => match i with
    | Sum.inl i => add_zero (M := α i) _
    | Sum.inr i => add_zero (M := β i) _ }

instance instAddSemigroup [∀ (i : ια), AddSemigroup (α i)]
    [∀ i : ιβ, AddSemigroup (β i)] (i : ια ⊕ ιβ) : AddSemigroup (Sum.elim α β i) :=
  { add_assoc := fun _ _ _ => match i with
    | Sum.inl i => add_assoc (G := α i) _ _ _
    | Sum.inr i => add_assoc (G := β i) _ _ _ }

instance instAddCommSemigroup [∀ (i : ια), AddCommSemigroup (α i)]
    [∀ i : ιβ, AddCommSemigroup (β i)] (i : ια ⊕ ιβ) : AddCommSemigroup (Sum.elim α β i) :=
  { add_comm := fun _ _ => match i with
    | Sum.inl i => add_comm (G := α i) _ _
    | Sum.inr i => add_comm (G := β i) _ _ }

instance instSMul {γ : Type*} [∀ i : ια, SMul γ (α i)]
    [∀ i : ιβ, SMul γ (β i)] (i : ια ⊕ ιβ) :
    SMul γ (Sum.elim α β i) :=
  match i with
  | Sum.inl i => inferInstanceAs (SMul γ (α i))
  | Sum.inr i => inferInstanceAs (SMul γ (β i))

instance instAddMonoid [∀ (i : ια), AddMonoid (α i)]
    [∀ i : ιβ, AddMonoid (β i)] (i : ια ⊕ ιβ) : AddMonoid (Sum.elim α β i) :=
  { instAddSemigroup i, instAddZeroClass i with
    nsmul := nsmulRec }

instance instAddCommMonoid [∀ (i : ια), AddCommMonoid (α i)]
    [∀ i : ιβ, AddCommMonoid (β i)] (i : ια ⊕ ιβ) : AddCommMonoid (Sum.elim α β i) :=
  { add_comm := AddCommSemigroup.add_comm }

instance instNeg [∀ (i : ια), Neg (α i)]
    [∀ i : ιβ, Neg (β i)] (i : ια ⊕ ιβ) : Neg (Sum.elim α β i) :=
  match i with
  | Sum.inl i => inferInstanceAs (Neg (α i))
  | Sum.inr i => inferInstanceAs (Neg (β i))

instance instSub [∀ (i : ια), Sub (α i)]
    [∀ i : ιβ, Sub (β i)] (i : ια ⊕ ιβ) : Sub (Sum.elim α β i) :=
  match i with
  | Sum.inl i => inferInstanceAs (Sub (α i))
  | Sum.inr i => inferInstanceAs (Sub (β i))

instance instSubNegMonoid [∀ (i : ια), SubNegMonoid (α i)]
    [∀ i : ιβ, SubNegMonoid (β i)] (i : ια ⊕ ιβ) : SubNegMonoid (Sum.elim α β i) :=
  { sub_eq_add_neg := fun _ _ => match i with
    | Sum.inl i => sub_eq_add_neg (G := α i) _ _
    | Sum.inr i => sub_eq_add_neg (G := β i) _ _
    zsmul := zsmulRec }

instance instAddGroup [∀ (i : ια), AddGroup (α i)]
    [∀ i : ιβ, AddGroup (β i)] (i : ια ⊕ ιβ) : AddGroup (Sum.elim α β i) :=
  { add_left_neg := fun _ => match i with
    | Sum.inl i => add_left_neg (G := α i) _
    | Sum.inr i => add_left_neg (G := β i) _ }

-- why do I keep having to specify `add_comm`?
instance instAddCommGroup [∀ (i : ια), AddCommGroup (α i)]
    [∀ i : ιβ, AddCommGroup (β i)] (i : ια ⊕ ιβ) : AddCommGroup (Sum.elim α β i) :=
  { add_comm := fun _ _ => match i with
    | Sum.inl i => add_comm (G := α i) _ _
    | Sum.inr i => add_comm (G := β i) _ _ }

instance instMulAction {γ : Type*} [Monoid γ] [∀ (i : ια), MulAction γ (α i)]
    [∀ i : ιβ, MulAction γ (β i)] (i : ια ⊕ ιβ) : MulAction γ (Sum.elim α β i) :=
  { one_smul := fun _ => match i with
    | Sum.inl i => one_smul γ (α := α i) _
    | Sum.inr i => one_smul γ (α := β i) _
    mul_smul := fun _ _ _ => match i with
    | Sum.inl i => mul_smul (β := α i) _ _ _
    | Sum.inr i => mul_smul (β := β i) _ _ _ }

instance instDistribMulAction {γ : Type*} [Monoid γ]
    [∀ (i : ια), AddMonoid (α i)] [∀ i : ιβ, AddMonoid (β i)]
    [∀ (i : ια), DistribMulAction γ (α i)]
    [∀ i : ιβ, DistribMulAction γ (β i)] (i : ια ⊕ ιβ) : DistribMulAction γ (Sum.elim α β i) :=
  { smul_zero := fun _ => match i with
    | Sum.inl i => smul_zero (A := α i) _
    | Sum.inr i => smul_zero (A := β i) _
    smul_add := fun _ _ _ => match i with
    | Sum.inl i => smul_add (A := α i) _ _ _
    | Sum.inr i => smul_add (A := β i) _ _ _ }

instance instModule {k : Type*} [Semiring k]
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    [∀ (i : ια), Module k (α i)] [∀ i : ιβ, Module k (β i)] (i : ια ⊕ ιβ) :
    Module k (Sum.elim α β i) :=
  { add_smul := fun _ _ _ => match i with
    | Sum.inl i => add_smul (M := α i) _ _ _
    | Sum.inr i => add_smul (M := β i) _ _ _
    zero_smul := fun _ => match i with
    | Sum.inl i => zero_smul (M := α i) _ _
    | Sum.inr i => zero_smul (M := β i) _ _ }

end Sum

namespace DFinsupp

def onFinset {ι : Type*} {α : (i : ι) → Type v} [∀ (i : ι), Zero (α i)]
    (s : Finset ι) (f : (i : ι) → α i) (hf : ∀ a, f a ≠ 0 → a ∈ s) : Π₀ i : ι, α i where
  toFun := f
  support' := Trunc.mk ⟨s.1, fun i => by by_cases h : f i = 0 <;> tauto⟩

@[simp]
theorem onFinset_apply {ι : Type*} {α : (i : ι) → Type v} [∀ (i : ι), Zero (α i)]
    {s : Finset ι} {f : (i : ι) → α i} {hf a} : onFinset s f hf a = f a :=
  rfl

noncomputable def sumElim
    [∀ i : ια, Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i, α i) (g : Π₀ i, β i) :
    Π₀ (i : ια ⊕ ιβ), Sum.elim α β i := by
  classical
  exact onFinset (Finset.disjSum (support f) (support g))
    (fun i => match i with
    | Sum.inl i => f i
    | Sum.inr i => g i)
    fun i => match i with
    | Sum.inl i => fun h => by simp_all
    | Sum.inr i => fun h => by simp_all

@[simp] lemma sumElim_apply_inl
    [∀ (i : ια), Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i, α i) (g : Π₀ i, β i) (i : ια) :
  sumElim f g (Sum.inl i) = f i := rfl

@[simp] lemma sumElim_apply_inr
    [∀ (i : ια), Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i, α i) (g : Π₀ i, β i) (i : ιβ) :
  sumElim f g (Sum.inr i) = g i := rfl

variable [DecidableEq ια] [DecidableEq ιβ] (α β)

noncomputable def sumFinsuppEquivProdFinsupp
    [∀ i : ια, Zero (α i)] [∀ i : ιβ, Zero (β i)] :
    (Π₀ i : ια ⊕ ιβ, Sum.elim α β i) ≃ (Π₀ i : ια, α i) × (Π₀ i : ιβ, β i) where
  toFun := fun f => ⟨comapDomain Sum.inl Sum.inl_injective f,
    comapDomain Sum.inr Sum.inr_injective f⟩
  invFun := fun ⟨f, g⟩ => sumElim f g
  left_inv := fun _ => ext fun j => match j with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl
  right_inv := fun ⟨_, _⟩ => Prod.ext (ext fun _ => rfl) (ext fun _ => rfl)

variable {α β}

@[simp] lemma sumFinsuppEquivProdFinsupp_apply_inl
    [∀ i : ια, Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i : ια ⊕ ιβ, Sum.elim α β i) (i : ια) :
    (sumFinsuppEquivProdFinsupp α β f).1 i = f (Sum.inl i) := rfl

@[simp] lemma sumFinsuppEquivProdFinsupp_apply_inr
    [∀ i : ια, Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i : ια ⊕ ιβ, Sum.elim α β i) (i : ιβ) :
    (sumFinsuppEquivProdFinsupp α β f).2 i = f (Sum.inr i) := rfl

@[simp] lemma sumFinsuppEquivProdFinsupp_symm_apply
    [∀ i : ια, Zero (α i)] [∀ i : ιβ, Zero (β i)]
    (f : Π₀ i : ια, α i) (g : Π₀ i : ιβ, β i) :
    (sumFinsuppEquivProdFinsupp α β).symm (f, g) = sumElim f g := rfl

end DFinsupp
namespace DirectSum
variable (α β) [DecidableEq ια] [DecidableEq ιβ]
open scoped DirectSum

noncomputable def sumAddEquivProd
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)] :
    (⨁ (i : ια ⊕ ιβ), Sum.elim α β i) ≃+ (⨁ i : ια, α i) × (⨁ i : ιβ, β i) :=
  { DFinsupp.sumFinsuppEquivProdFinsupp α β with
    map_add' := fun _ _ => Prod.ext (DFinsupp.ext fun _ => rfl) (DFinsupp.ext fun _ => rfl) }

variable {α β}

-- not really thought about whether these are the right simp lemmas

@[simp] lemma sumAddEquivProd_inl_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    (i : ια) (x : ⨁ (i : ια ⊕ ιβ), Sum.elim α β i) :
    (sumAddEquivProd α β x).1 i = x (Sum.inl i) := rfl

@[simp] lemma sumAddEquivProd_inr_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    (i : ιβ) (x : ⨁ (i : ια ⊕ ιβ), Sum.elim α β i) :
    (sumAddEquivProd α β x).2 i = x (Sum.inr i) := rfl

@[simp] lemma sumAddEquivProd_symm_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    (x : ⨁ (i : ια), α i) (y : ⨁ (i : ιβ), β i) :
    (sumAddEquivProd α β).symm (x, y) = DFinsupp.sumElim x y := rfl

variable (k α β)

noncomputable def sumLEquivProd
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    [∀ (i : ια), Module k (α i)] [∀ i : ιβ, Module k (β i)] :
    (⨁ (i : ια ⊕ ιβ), Sum.elim α β i) ≃ₗ[k] (⨁ i : ια, α i) × (⨁ i : ιβ, β i) :=
  { sumAddEquivProd α β with
    map_smul' := fun _ _ => Prod.ext (DFinsupp.ext fun _ => rfl) (DFinsupp.ext fun _ => rfl) }

variable {α β}

@[simp] lemma sumLEquivProd_inl_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    [∀ (i : ια), Module k (α i)] [∀ i : ιβ, Module k (β i)]
    (i : ια) (x : ⨁ (i : ια ⊕ ιβ), Sum.elim α β i) :
    (sumLEquivProd k α β x).1 i = x (Sum.inl i) := rfl

@[simp] lemma sumLEquivProd_inr_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    [∀ (i : ια), Module k (α i)] [∀ i : ιβ, Module k (β i)]
    (i : ιβ) (x : ⨁ (i : ια ⊕ ιβ), Sum.elim α β i) :
    (sumLEquivProd k α β x).2 i = x (Sum.inr i) := rfl

@[simp] lemma sumLEquivProd_symm_apply
    [∀ (i : ια), AddCommMonoid (α i)] [∀ i : ιβ, AddCommMonoid (β i)]
    [∀ (i : ια), Module k (α i)] [∀ i : ιβ, Module k (β i)]
    (x : ⨁ (i : ια), α i) (y : ⨁ (i : ιβ), β i) :
    (sumLEquivProd k α β).symm (x, y) = DFinsupp.sumElim x y := rfl
