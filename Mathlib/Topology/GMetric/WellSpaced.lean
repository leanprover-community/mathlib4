import Mathlib.Topology.GMetric.GInfSep

namespace Set

variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]
variable (gdist : α → α → γ)

section discrete
def WeakDiscreteGDistWith (d:γ) :Prop := ∀ x y, x ≠ y → d ≤ gdist x y

def WeakDiscreteGDist : Prop := ∃ d:γ, WeakDiscreteGDistWith gdist d

def DiscreteGDistWith (d:γ) : Prop := ∀ x y, x ≠ y → d < gdist x y

def DiscreteGDist : Prop := ∃ d:γ, DiscreteGDistWith gdist d
end discrete

section bounded
def WeakBoundedGDistWith (d:γ):Prop := ∀ x y, gdist x y ≤ d

def WeakBoundedGDist :Prop := ∃ d, WeakBoundedGDistWith gdist d

def BoundedGDistWith (d:γ):Prop := ∀ x y, gdist x y < d

def BoundedGDist : Prop := ∃ d, BoundedGDistWith gdist d

end bounded


variable {T:Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] (gdist:T) (s:Set α)
open GMetric

section packing

def IsOpenPackingWith (r:γ) : Prop := s.PairwiseDisjoint (ball gdist . r)

def IsPackingWith (r:γ) : Prop := s.PairwiseDisjoint (closedBall gdist . r)

-- CovariantClass (Set α) (Set α) (.∩.) (.⊆.)

lemma isOpenPacking_of_isPacking
    ⦃δ: γ⦄ (hpack:IsPackingWith gdist s δ): IsOpenPackingWith gdist s δ :=
  hpack.mono_on (fun _ _ => ball_subset_closedBall gdist)

lemma isPacking_of_isOpenPacking_of_lt
    ⦃δ₁ δ₂: γ⦄ (hlt: δ₁<δ₂) (hsep: IsOpenPackingWith gdist s δ₂) : IsPackingWith gdist s δ₁ := by
  exact hsep.mono_on (fun _ _ => closedBall_subset_ball gdist hlt)

-- is close to golfed prolly
lemma not_separates_sup_sep_gdist
    (y:α) {a b:α} {ha:a∈s} {hb:b∈ s} (hpack: a ≠ b) : ¬IsPackingWith gdist s (gdist y a ⊔ gdist y b) := by
  contrapose! hpack
  apply hpack.elim' ha hb
  rw [closedBall,closedBall,bot_eq_empty]
  push_neg
  use y
  simp

-- maybe can be golfed
theorem isOpenPackingWith_iff
    (δ₁:γ) : IsOpenPackingWith gdist s δ₁ ↔ ∀ δ₂, (δ₂<δ₁) → IsPackingWith gdist s δ₂:= by
  constructor
  . exact fun hwsep δ₂ hδ₂ => isPacking_of_isOpenPacking_of_lt gdist s hδ₂ hwsep
  . simp_rw [IsOpenPackingWith,IsPackingWith]
    intro hltsep
    by_contra hcontra
    obtain ⟨x,⟨hx,⟨y,⟨hy,⟨hne,⟨z,hz⟩⟩⟩⟩⟩⟩ := exists_ne_mem_inter_of_not_pairwiseDisjoint hcontra
    have hlt: gdist z x ⊔ gdist z y < δ₁ := by
      rw [sup_lt_iff,← mem_ball,← mem_ball,← mem_inter_iff]
      exact hz
    obtain fin := @hltsep _ hlt _ hx _ hy hne
    -- z is in the intersection, hence a contradiction
    apply @fin {z} _ _ z _ <;> simp

lemma isPackingWith_of_le_of_isPackingWith
    ⦃δ₁ δ₂:γ⦄ (hle:δ₁≤δ₂) (hsep:IsPackingWith gdist s δ₂) : IsPackingWith gdist s δ₁ := by
  apply hsep.mono_on (fun _ _ => closedBall_subset_closedBall gdist hle)

-- can probably be golfed
lemma dist_le_dist_mems_of_isPackingWith_dist {x y : α} {hx:x∈ s} {hy:y∈ s} (hneq : ¬x = y)
  (x' : s) (y' : α) (hsep : IsPackingWith gdist s (gdist x' y')) :
  gdist x' y' ≤ gdist x y := by
  rw [IsPackingWith] at hsep
  have h_inter_empty: (Disjoint on fun x ↦ closedBall gdist x (gdist (↑x') y')) x y := by
    exact hsep hx hy hneq
  contrapose! h_inter_empty
  rw [Function.onFun,Disjoint]
  push_neg
  use {y}
  simp only [le_eq_subset, singleton_subset_iff, mem_closedBall, gdist_self, bot_eq_empty,
    mem_empty_iff_false, not_false_eq_true, and_true]
  rw [comm']
  use h_inter_empty.le
  exact gdist_nonneg gdist

-- do i rather want ` sSup fun d => IsPackingWith gdist s d`? i don't think so...
def packing_radius : γ :=
  ⨆ (x ∈ s) (y:α) (_ : IsPackingWith gdist s (gdist (x:α) y)), gdist (x:α) y

local notation "rₚ" => packing_radius gdist s
def packing_radius_closed: Prop := IsPackingWith gdist s rₚ

@[simp]
lemma lt_packingradius_iff
    (δ₂:γ) : δ₂ < rₚ ↔ ∃ x∈ s, ∃ (y:α), IsPackingWith gdist s (gdist x y) ∧ δ₂ < gdist x y := by
  simp_rw [packing_radius,lt_iSup_iff]
  simp

lemma isOpenPackingWith_packingradius : IsOpenPackingWith gdist s rₚ := by
  rw [isOpenPackingWith_iff]
  simp only [lt_packingradius_iff, forall_exists_index, and_imp]
  intro _ _ _ _ hsep hlt
  exact isPackingWith_of_le_of_isPackingWith gdist s hlt.le hsep

lemma separates_of_mem_ball_packingradius
    {x':α} {z:α} (hz:z ∈ball gdist x' rₚ) : IsPackingWith gdist s (gdist x' z) := by
  rw [comm']
  exact isPacking_of_isOpenPacking_of_lt gdist s ((mem_ball gdist).mp hz)
    (isOpenPackingWith_packingradius gdist s)

structure UniformlyDiscreteWith (δ:γ) : Prop :=
  isOpenPackingWith : IsOpenPackingWith gdist s δ
  positive_radius : 0 < δ

def Uniformlydiscrete : Prop := ∃ (δ:γ), UniformlyDiscreteWith gdist s δ

end packing

section covering

-- is false when s is empty but α is not.
-- is true when s is empty and β is empty.
def IsClosedCoveringWith (R:γ):Prop := ⋃ (x∈ s), (closedBall gdist x R) = univ

def IsCoveringWith (R:γ):Prop := ⋃ (x∈ s), (ball gdist x R) = univ

lemma isClosedCoveringWith_of_isCoveringWith
    ⦃δ:γ⦄ (hcov:IsCoveringWith gdist s δ): IsClosedCoveringWith gdist s δ := by
  rw [IsClosedCoveringWith]
  rw [IsCoveringWith] at hcov
  have hsubset: ⋃ x∈ s, ball gdist x δ ⊆ ⋃ x∈ s, closedBall gdist x δ := by
    exact Set.iUnion_mono (fun x => Set.iUnion_mono (fun _ => ball_subset_closedBall gdist))
  simp_all only [univ_subset_iff]

lemma isCoveringWith_of_lt_of_isClosedCoveringWith
    ⦃δ₁ δ₂:γ⦄ (hlt:δ₁<δ₂) (hccov: IsClosedCoveringWith gdist s δ₁) : IsCoveringWith gdist s δ₂ := by
  rw [IsCoveringWith,← univ_subset_iff,← hccov]
  exact Set.iUnion_mono (fun x => Set.iUnion_mono (fun _ => closedBall_subset_ball gdist hlt))

lemma covers_of_le_of_covers
    (δ₁ δ₂:γ) (hle:δ₁≤ δ₂) (hcov: IsCoveringWith gdist s δ₁) : IsCoveringWith gdist s δ₂ := by
  rw [IsCoveringWith] at hcov ⊢
  rw [← univ_subset_iff,← hcov]
  exact Set.iUnion_mono (fun x => Set.iUnion_mono (fun _ => ball_subset_ball gdist hle))

def closest_distance (y:α): γ := ⨅ (x ∈ s), (gdist x y)

lemma not_covers_closest_distance (y:α): ¬ IsCoveringWith gdist s (closest_distance gdist s y) := by
  rw [IsCoveringWith,closest_distance]
  push_neg
  rw [ne_univ_iff_exists_not_mem]
  use y
  simp_rw [mem_iUnion, mem_ball, exists_prop, not_exists, not_and, not_lt, iInf_le_iff,
    le_iInf_iff, comm']
  exact (fun x hx δ₁ hδ₁ => hδ₁ x hx)


def covering_radius: γ := ⨅ (R:γ) (_:IsCoveringWith gdist s R), R
def covering_radius' : γ := ⨆ (y:α), closest_distance gdist s y

example : s.covering_radius' gdist ≤ s.covering_radius gdist := by
  simp_rw [covering_radius,covering_radius',le_iInf_iff]
  simp_rw [IsCoveringWith,closest_distance,iSup_le_iff,iInf_le_iff]
  intro b hcov y c hc
  simp at hc
  have hy: y ∈ univ := trivial
  rw [← hcov] at hy
  simp at hy
  obtain ⟨x,⟨hx,hx'⟩⟩ := hy
  obtain hz := hc x hx
  rw [comm'] at hx'
  exact hz.trans hx'.le

structure RelativelyDenseWith (δ:γ) : Prop :=
  isClosedCoveringWith : IsClosedCoveringWith gdist s δ
  not_top : δ < ⊤

def RelativelyDense : Prop := ∃ (δ:γ), RelativelyDenseWith gdist s δ

end covering

section net_delone

-- technically this defines a 2ε-net, but we can't define an ε-net because there is no division.
structure IsNetWith (ε:γ) :Prop :=
  isOpenPacking : IsOpenPackingWith gdist s ε
  isClosedCoveringWith: IsClosedCoveringWith gdist s (2•ε)

structure GMetric.IsDeloneWith (r R:γ):Prop :=
  isOpenPacking : IsOpenPackingWith gdist s r
  isClosedCoveringWith: IsClosedCoveringWith gdist s R

class GMetric.IsDelone : Prop :=
  isDeloneWith: ∃ (r R :γ),IsDeloneWith gdist s r R

end net_delone

end Set
