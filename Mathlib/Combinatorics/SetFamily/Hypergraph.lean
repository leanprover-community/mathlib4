
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Finset.Slice
import Mathlib.Combinatorics.SimpleGraph.Basic
universe u
open Function Set
section FamHom
variable {α β γ : Type*}
variable {ι : Sort*}
variable {𝒜 : Set (Finset α)} {ℬ : Set (Finset β)} {𝒞 : Set (Finset γ)}
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]


/-- A set homomorphism with respect to a given pair of sets of sets
is a function `f : α → β` such that `A ∈ 𝒜 → f(A) ∈ ℬ`. -/
structure FamHom {α β : Type*} [DecidableEq α] [DecidableEq β]
    (𝒜 : Set (Finset α)) (ℬ : Set (Finset β)) where
  /-- The underlying function of a `FamHom` -/
  toFun : α → β
  /-- A `FamHom` sends members of 𝒜 to members of ℬ -/
  map_mem' : ∀ {A}, A ∈ 𝒜 → A.image toFun ∈ ℬ


/-- A family homomorphism with respect to a given pair of sets `𝒜` and `ℬ`
is a function `f : α → β` such that `A ∈ 𝒜 → toFun '' A  ∈ B`. -/
infixl:25 " →s " => FamHom

section
/-- `FamHomClass F 𝒜 ℬ` asserts that `F` is a type of functions such that all `f : F`
satisfy `A ∈ 𝒜 → toFun '' A  ∈ B`.

The sets `𝒜` and `ℬ` are `outParam`s since figuring them out from a goal is a higher-order
matching problem that Lean usually can't do unaided.
-/
class FamHomClass (F : Type*) {α β : outParam Type*} [DecidableEq α] [DecidableEq β]
(𝒜 : outParam <| Set (Finset α))  (ℬ : outParam <| Set (Finset β)) [FunLike F α β] : Prop where
  /-- A `FamHomClass` sends related elements to related elements -/
  map_mem : ∀ (f : F) {A}, A ∈ 𝒜 → A.image f  ∈ ℬ

end

namespace FamHom

instance : FunLike (𝒜 →s ℬ) α β where
  coe o := o.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr

instance : FamHomClass (𝒜 →s ℬ) 𝒜 ℬ where
  map_mem := map_mem'

initialize_simps_projections FamHom (toFun → apply)

protected theorem map_mem (f : 𝒜 →s ℬ) {A} : A ∈ 𝒜 → A.image f  ∈ ℬ :=
  f.map_mem'

@[simp]
theorem coe_fn_toFun (f : 𝒜 →s ℬ) : f.toFun = (f : α → β) :=
  rfl

/-- The map `coe_fn : (𝒜 →s ℬ) → (α → β)` is injective. -/
theorem coe_fn_injective : Injective fun (f : 𝒜 →s ℬ) => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : 𝒜 →s ℬ⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Identity map is a Set homomorphism. -/
@[refl, simps]
protected def id (𝒜: Set (Finset α)) : 𝒜 →s 𝒜  :=
  ⟨fun x => x, by simp⟩

/-- Composition of two Set homomorphisms is a Set homomorphism. -/
@[simps]
protected def comp (g : ℬ →s 𝒞) (f : 𝒜 →s ℬ) : 𝒜 →s 𝒞 :=
  ⟨fun x => g (f x), by
    intro A hA; convert g.map_mem <| f.map_mem hA
    ext; simp⟩

end FamHom


/-- A FamInjHom with respect to a given pair of sets of sets `𝒜` and `ℬ`
is an embedding `f : α ↪ β` such that `A ∈ 𝓐 → f '' A  ∈ ℬ`. -/
structure FamInjHom {α β : Type*} [DecidableEq α] [DecidableEq β]
    (𝒜 : Set (Finset α)) (ℬ : Set (Finset β)) extends α ↪ β where
  map_mem' : ∀ {A}, A ∈ 𝒜 → A.map toEmbedding ∈ ℬ

-- /-- A set embedding with respect to a given pair of sets of sets `𝒜` and `ℬ`
-- is an embedding `f : α ↪ β` such that `A ∈ 𝓐 ↔ toFun '' A  ∈ ℬ`. -/
-- structure SetEmbedding {α β : Type*}
--     (𝒜 : Set (Finset α)) (ℬ : Set (Finset β)) extends α ↪ β where
--   /-- Elements are related iff they are related after apply a `SetEmbedding` -/
--   map_mem_iff' : ∀ {A}, toEmbedding '' A ∈ ℬ ↔ A ∈ 𝒜

/-- A set embedding with respect to a given pair of sets `𝒜` and `ℬ`
is an embedding `f : α ↪ β` such that `A ∈ 𝒜 ↔ toFun '' A  ∈ ℬ`. -/
infixl:25 " ↪s " => FamInjHom

-- theorem preimage_equivalence {α β} (f : α → β) {ℬ : Set (Finset β)} (hs : Equivalence ℬ) :
--     Equivalence (f ⁻¹'o ℬ) :=
--   ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩

namespace FamInjHom
#check Finset.map_eq_image
/-- A set embedding is also a set homomorphism -/
def toFamHom (f : 𝒜 ↪s ℬ) : 𝒜 →s ℬ where
  toFun := f.toEmbedding.toFun
  map_mem' := by
    intro A hA
    have :=f.map_mem' hA
    rwa [Finset.map_eq_image] at this;

instance : Coe (𝒜 ↪s ℬ) (𝒜 →s ℬ) :=
  ⟨toFamHom⟩

instance : FunLike (𝒜 ↪s ℬ) α β where
  coe x := x.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr

instance : FamHomClass (𝒜 ↪s ℬ) 𝒜 ℬ where
  map_mem f _ h :=by
    have :=f.map_mem' h
    rwa [Finset.map_eq_image] at this;

initialize_simps_projections FamInjHom (toFun → apply)

instance : EmbeddingLike (𝒜 ↪s ℬ) α β where
  injective' f := f.inj'

@[simp]
theorem coe_toEmbedding {f : 𝒜 ↪s ℬ} : ((f : 𝒜 ↪s ℬ).toEmbedding : α → β) = f :=
  rfl

@[simp]
theorem coe_toFamHom {f : 𝒜 ↪s ℬ} : ((f : 𝒜 ↪s ℬ).toFamHom : α → β) = f :=
  rfl

theorem toEmbedding_injective : Injective (toEmbedding : 𝒜 ↪s ℬ → (α ↪ β)) := by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]
theorem toEmbedding_inj {f g : 𝒜 ↪s ℬ} : f.toEmbedding = g.toEmbedding ↔ f = g :=
  toEmbedding_injective.eq_iff

theorem injective (f : 𝒜 ↪s ℬ) : Injective f :=
  f.inj'

theorem inj (f : 𝒜 ↪s ℬ) {a b} : f a = f b ↔ a = b := f.injective.eq_iff

theorem map_mem (f : 𝒜 ↪s ℬ) {A} : A ∈ 𝒜 → A.map f.toEmbedding ∈ ℬ :=
  f.map_mem'

@[simp]
theorem coe_mk {f} {h} : ⇑(⟨f, h⟩ : 𝒜 ↪s ℬ) = f :=
  rfl

/-- The map `coe_fn : (𝒜 ↪s ℬ) → (α → β)` is injective. -/
theorem coe_fn_injective : Injective fun f : 𝒜 ↪s ℬ => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : 𝒜 ↪s ℬ⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Identity map is a FamInjHom. -/
@[refl, simps!]
protected def refl (𝒜 : Set (Finset α)) : 𝒜 ↪s 𝒜 :=
  ⟨Embedding.refl _, by
  intro A hA; simp_rw [Finset.map_eq_image]
  convert hA; ext; simp⟩


/-- Composition of two set embeddings is a set embedding. -/
protected def trans (f : 𝒜 ↪s ℬ) (g : ℬ ↪s 𝒞) : 𝒜 ↪s 𝒞 :=
  ⟨f.1.trans g.1, by
    intro A hA; convert g.map_mem <| f.map_mem' hA;
    ext; simp⟩

instance (𝒜 : Set (Finset α)) : Inhabited (𝒜 ↪s 𝒜) :=
  ⟨FamInjHom.refl _⟩

theorem trans_apply (f : 𝒜 ↪s ℬ) (g : ℬ ↪s 𝒞) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
theorem coe_trans (f : 𝒜 ↪s ℬ) (g : ℬ ↪s 𝒞) : (f.trans g) = g ∘ f :=
  rfl

end FamInjHom

end FamHom
variable {ι : Sort*}
@[ext]
structure HyperGraph (r : ℕ) (V : Type u)  where
  /-- The edges of an r uniform hypergraph. -/
  Edges : Set (Finset V)
  Sized : Edges.Sized r


instance HyperGraph.setLike (r : ℕ) (V : Type u) : SetLike (HyperGraph r V) (Finset V) where
  coe s := s.Edges
  coe_injective' := by
    rintro ⟨s, _⟩ ⟨t, _⟩ h
    congr

@[simp]
lemma mem_iff {r : ℕ} {V : Type u } {G : HyperGraph r V} {e : Finset V} : e ∈ G.Edges ↔ e ∈ G :=
    by rfl

/-- Constructor for hypergraphs using a boolean predicate on r-sets. -/
@[simps]
def HyperGraph.mk' {r : ℕ} {V : Type u} :
    {edges : Finset V → Bool // ∀ e, edges e → e.card = r} ↪ HyperGraph r V  where
  toFun x := ⟨fun e ↦ x.1 e, fun v  ↦ by
     intro hv; apply x.2; simpa⟩
  inj' := by
    rintro ⟨edges, _⟩ ⟨edges', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext e
    simpa [Bool.coe_iff_coe] using congr_fun h e

@[simp]
lemma mk'_edges {r : ℕ} {V : Type u} (edges : Finset V → Bool) (e : Finset V)
(h : ∀ e, edges e → e.card = r) : e ∈ (HyperGraph.mk' ⟨edges, h⟩) ↔ edges e = true :=
  Iff.rfl


/-- We can enumerate r-hypergraphs on a Fintype by enumerating all families of r-set -/
instance {r : ℕ} {V : Type u} [Fintype V] [DecidableEq V] : Fintype (HyperGraph r V) where
  elems := Finset.univ.map HyperGraph.mk'
  complete := by
    classical
    rintro ⟨edges, hr⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    refine ⟨fun e  ↦ e ∈ edges,?_,?_⟩
    · simp only [decide_eq_true_eq]
      apply hr
    · ext e
      simp;



/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def HyperGraph.fromSet {V : Type u} (r : ℕ) (s : Set (Finset V)) : HyperGraph r V where
  Edges := {e ∈ s | e.card = r}
  Sized := fun _ he ↦ he.2

@[simp]
theorem HyperGraph.fromSet_mem {V : Type u} (r : ℕ) (s : Set (Finset V)) (e : Finset V) :
    e ∈ HyperGraph.fromSet r s ↔ e ∈ s ∧ e.card = r := Iff.rfl

/-- The complete hypergraph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
def completeHyperGraph (r : ℕ) (V : Type u)  : HyperGraph r V where
  Edges := { e | e.card = r }
  Sized := fun _ he ↦ he

/-- The hypergraph with no edges on a given vertex type `V`. `Mathlib` prefers the notation `⊥`. -/
def emptyHyperGraph (r : ℕ) (V : Type u) : HyperGraph r V where
  Edges := ∅
  Sized := sized_empty

namespace HyperGraph
variable {V : Type u} {r : ℕ}
theorem edges_injective : Injective (Edges : HyperGraph r V → Set (Finset V))
    := fun _ _ => HyperGraph.ext

@[simp]
theorem edges_inj {G H : HyperGraph r V} : G.Edges = H.Edges ↔ G = H :=
  edges_injective.eq_iff


/-- The relation that one `HyperGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubHyperGraph (G H : HyperGraph r V) : Prop :=
  ∀ ⦃e : Finset V⦄, e ∈ G → e ∈ H

instance : LE (HyperGraph r V) :=
  ⟨IsSubHyperGraph⟩


@[simp]
theorem isSubHyperGraph_eq_le : (IsSubHyperGraph : HyperGraph r V → HyperGraph r V → Prop) =
 (· ≤ ·) := rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (HyperGraph r V) where
  max x y :=
    { Edges := x.Edges ⊔ y.Edges
      Sized := sized.union ⟨x.Sized, y.Sized⟩ }

@[simp]
theorem mem_sup_iff (x y : HyperGraph r V) (e : Finset V) : e ∈ (x ⊔ y) ↔  e ∈ x ∨ e ∈ y :=
  Iff.rfl

/-- The infimum of two hypergraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (HyperGraph r V) where
  min x y :=
    { Edges := x.Edges ⊓ y.Edges
      Sized := x.Sized.mono inter_subset_left }

@[simp]
theorem mem_inf_iff (x y : HyperGraph r V) (e : Finset V) : e ∈ (x ⊓ y) ↔ e ∈ x ∧ e ∈ y :=
  Iff.rfl

/-- We define `Gᶜ` to be the `HyperGraph r V` containing all r-sets not in G . -/
instance hasCompl : HasCompl (HyperGraph r V) where
  compl G :=
    { Edges := { e | e.card = r ∧ e ∉ G }
      Sized := fun _ he => he.1 }

@[simp]
theorem mem_compl_iff (G : HyperGraph r V) (e : Finset V) : e ∈ Gᶜ ↔ e.card = r ∧ ¬ e ∈ G :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (HyperGraph r V) where
  sdiff x y :=
    { Edges := x.Edges \ y.Edges
      Sized := by
        intro e he; apply x.Sized he.1}

@[simp]
theorem mem_sdiff_iff (x y : HyperGraph r V) (e : Finset V) : e ∈ (x \ y) ↔ e ∈ x ∧ ¬ e ∈ y :=
  Iff.rfl

instance supSet : SupSet (HyperGraph r V) where
  sSup s :=
    { Edges := {e | ∃ G ∈ s, e ∈ G}
      Sized := fun _ ⟨G, _, h2⟩ ↦ G.Sized h2 }

instance infSet : InfSet (HyperGraph r V) where
  sInf s :=
    { Edges := {e | (∀ G ∈ s, e ∈ G) ∧ e.card = r}
      Sized := fun _ he ↦ he.2}

variable {e : Finset V}
@[simp]
theorem mem_sSup_iff {s : Set (HyperGraph r V)}  : e ∈ (sSup s) ↔ ∃ G ∈ s, e ∈ G :=
  Iff.rfl

@[simp]
theorem mem_sInf_iff {s : Set (HyperGraph r V)} : e ∈ (sInf s) ↔  (∀ G ∈ s, e ∈ G) ∧ e.card = r
    :=Iff.rfl

@[simp]
theorem mem_iSup_iff {f : ι → HyperGraph r V} : e ∈  (⨆ i, f i) ↔ ∃ i, e ∈ (f i):= by simp [iSup]

@[simp]
theorem mem_iInf_iff {f : ι → HyperGraph r V} : e ∈ (⨅ i, f i) ↔ (∀ i, e ∈ (f i)) ∧ e.card = r := by
  simp [iInf]

theorem mem_sInf_of_nonempty {s : Set (HyperGraph r V)} (hs : s.Nonempty) :
    e ∈ (sInf s) ↔ ∀ G ∈ s, e ∈ G :=
  mem_sInf_iff.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      intro h; apply G.Sized <| h _ hG

theorem mem_iInf_of_nonempty [Nonempty ι] {f : ι → HyperGraph r V} :
   e ∈ (⨅ i, f i) ↔ ∀ i, e ∈ (f i) := by
  rw [iInf, mem_sInf_of_nonempty (Set.range_nonempty _), Set.forall_mem_range]

/-- For r-uniform hypergraphs `G`, `H`, `G ≤ H` iff `∀ e ∈ G → e ∈ H`. -/
instance distribLattice : DistribLattice (HyperGraph r V) :=
  { show DistribLattice (HyperGraph r V) from
      edges_injective.distribLattice _ (fun _ _ => rfl) fun _ _ => rfl with
    le := fun G H => ∀ ⦃e⦄, e ∈ G → e ∈ H}

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (HyperGraph r V) :=
  { HyperGraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := completeHyperGraph r V
    bot := emptyHyperGraph r V
    le_top := fun x _  h => x.Sized h
    bot_le := fun _ _  h => h.elim
    sdiff_eq := fun x y => by
      ext e;
      refine ⟨fun h => ⟨h.1, ⟨?_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      apply x.Sized h.1
    inf_compl_le_bot := fun G => by
      intro e he; rw [mem_inf_iff,mem_compl_iff] at he; apply absurd he.1 he.2.2
    top_le_sup_compl := fun G => by
      intro e he
      by_cases h : e ∈ G
      · exact Or.inl h
      · exact Or.inr ⟨he, h⟩
    sSup := sSup
    le_sSup := fun _ G hs e he ↦ ⟨G,hs,he⟩
    sSup_le := fun s G hG e ⟨H,hH,h2⟩ ↦ hG _ hH h2
    sInf := sInf
    sInf_le := fun s G hs e he ↦ he.1 _ hs
    le_sInf := fun s G hs e he ↦ ⟨fun H hH ↦ hs _ hH he, G.Sized he⟩
    iInf_iSup_eq := by
      intro ι f g
      ext e; simp only [mem_iff, mem_iInf_iff, mem_iSup_iff, exists_and_right, and_congr_left_iff]
      intro hr
      constructor <;> intro h
      · exact ⟨_, fun i ↦ (h i).choose_spec⟩
      · intro i
        obtain ⟨x, hx⟩:=h
        use (x i)
        apply hx }

@[simp]
theorem mem_top (e : Finset V) : e ∈ (⊤ : HyperGraph r V) ↔ e.card = r :=
  Iff.rfl

@[simp]
theorem mem_bot (e : Finset V) : e ∈ (⊥ : HyperGraph r V) ↔ False :=
  Iff.rfl

@[simp]
theorem completeHyperGraph_eq_top (r : ℕ) (V : Type u) : completeHyperGraph r V = ⊤ :=
  rfl

@[simp]
theorem emptyGraph_eq_bot (r : ℕ) (V : Type u) : emptyHyperGraph r V = ⊥ :=
  rfl

@[simps]
instance (r : ℕ) (V : Type u) : Inhabited (HyperGraph r V) :=
  ⟨⊥⟩

instance [IsEmpty V] (hr : 0 < r) : Unique (HyperGraph r V) where
   default := ⊥
   uniq G := by
    ext e;
    simp only [mem_iff, mem_bot, iff_false]
    intro he;
    have : 0 < e.card := (G.Sized he) ▸ hr;
    obtain ⟨a,ha⟩:=Finset.card_pos.1 this
    exact IsEmpty.false a

-- instance [Nonempty V] (r : ℕ): Nontrivial (HyperGraph r V) :=
--   ⟨⟨⊥, ⊤, by
--     intro hf

--     sorry⟩⟩

section Decidable

variable (V) (G H : HyperGraph r V) [DecidablePred (· ∈ G)] [DecidablePred (· ∈ H)]
instance Bot.memDecidable : DecidablePred (· ∈  (⊥ : HyperGraph r V)):=
  inferInstanceAs <| DecidablePred fun  _ => False

instance Sup.memDecidable : DecidablePred (· ∈ G ⊔ H) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G ∨ e ∈ H

instance Inf.memDecidable : DecidablePred (· ∈ G ⊓ H) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G ∧ e ∈ H

instance Sdiff.adjDecidable : DecidablePred (· ∈ G \ H) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G ∧ ¬ e ∈ H

variable [DecidableEq V]

instance Top.memDecidable : DecidablePred (· ∈ (⊤ : HyperGraph r V)) :=
  inferInstanceAs <| DecidablePred fun (e : Finset V) => e.card = r

instance Compl.adjDecidable : DecidablePred (· ∈ Gᶜ) :=
  inferInstanceAs <| DecidablePred fun (e : Finset V) => e.card = r ∧ e ∉ G

end Decidable
variable (G : HyperGraph r V)
/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : Set V := {v | ∃ e ∈ G, v ∈ e}

theorem mem_support {v : V} : v ∈ G.support ↔ ∃ e ∈ G, v ∈ e :=
  Iff.rfl

theorem support_mono {G G' : HyperGraph r V} (h : G ≤ G') : G.support ⊆ G'.support :=
   fun _ ⟨e, he⟩ ↦ ⟨e, (h he.1), he.2⟩

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def neighborHyperGraph [DecidableEq V] (G : HyperGraph r V) (v : V) : HyperGraph (r - 1) V where
  Edges := (fun e => e.erase v) '' {e | e ∈ G ∧ v ∈ e}
  Sized := by
    intro f hf; simp only [mem_image, mem_setOf_eq] at hf
    obtain ⟨e,he,he2⟩:= hf
    rw [← he2]; exact G.Sized he.1 ▸ Finset.card_erase_of_mem he.2

lemma mem_neighborHyperGraph_iff [DecidableEq V] {G : HyperGraph r V} {v : V} {e : Finset V} :
 e ∈ G.neighborHyperGraph v ↔ insert v e ∈ G ∧ e.card = r - 1 ∧ v ∉ e := by
  constructor <;> intro h
  · change  e ∈ (fun e => e.erase v) '' {e | e ∈ G ∧ v ∈ e} at h
    simp only [mem_image, mem_setOf_eq] at h
    obtain ⟨f,h1,h2⟩:= h
    rw [← h2]; rw [Finset.insert_erase h1.2, Finset.card_erase_of_mem h1.2,G.Sized h1.1]
    use h1.1,rfl
    exact Finset.not_mem_erase v f
  · use (insert v e),⟨h.1, Finset.mem_insert_self v e⟩
    simp only [Finset.erase_insert_eq_erase, Finset.erase_eq_self]
    exact h.2.2

instance neighborHyperGraph.memDecidable [DecidableEq V] (G : HyperGraph r V)(v : V)
[DecidablePred (· ∈ G)] : DecidablePred (· ∈ G.neighborHyperGraph v) := by
  intro e; simp_rw [mem_neighborHyperGraph_iff]
  infer_instance

lemma neighborHyperGraph_le_of_le [DecidableEq V] {G H : HyperGraph r V} (v : V) (hle : G ≤ H) :
    G.neighborHyperGraph v ≤ H.neighborHyperGraph v :=by
  intro e he
  rw [mem_neighborHyperGraph_iff] at *
  use (hle he.1), he.2.1, he.2.2

def incidenceHyperGraph [DecidableEq V] (G : HyperGraph r V) (v : V) : HyperGraph r V where
  Edges := {e | e ∈ G ∧ v ∈ e}
  Sized := fun _ he ↦ G.Sized he.1

lemma mem_incidenceHyperGraph_iff [DecidableEq V] {G : HyperGraph r V} {v : V} {e : Finset V} :
 e ∈ G.incidenceHyperGraph v ↔ e ∈ G ∧ v ∈ e := by rfl

lemma incidenceHyperGraph_le_of_le [DecidableEq V] {G H : HyperGraph r V} (v : V) (hle : G ≤ H) :
    G.incidenceHyperGraph v ≤ H.incidenceHyperGraph v :=by
  intro e he
  rw [mem_incidenceHyperGraph_iff] at *
  use (hle he.1), he.2

instance incidenceHyperGraph.memDecidable [DecidableEq V] (G : HyperGraph r V)(v : V)
[DecidablePred (· ∈ G)] : DecidablePred (· ∈ G.incidenceHyperGraph v) := by
  intro e; simp_rw [mem_incidenceHyperGraph_iff]
  infer_instance

def linkHyperGraph [DecidableEq V] (G : HyperGraph r V) (e : Finset V) : HyperGraph (r - e.card) V
    where
  Edges := (fun f => f \ e) '' {f | f ∈ G ∧ e ⊆ f}
  Sized := by
    intro f hf; simp only [mem_image, mem_setOf_eq] at hf
    obtain ⟨e,he,he2⟩:= hf
    rw [← he2]; exact G.Sized he.1 ▸ Finset.card_sdiff he.2

lemma mem_linkHyperGraph_iff [DecidableEq V] {G : HyperGraph r V} {e f : Finset V} :
 f ∈ G.linkHyperGraph e ↔ Disjoint e f ∧ e ∪ f ∈ G ∧ f.card = r - e.card := by
  constructor <;> intro h
  · change f ∈ (fun f => f \ e) '' {f | f ∈ G ∧ e ⊆ f} at h
    simp only [mem_image, mem_setOf_eq] at h
    obtain ⟨g,h1,h2⟩:= h
    rw [← h2];
    rw [Finset.union_sdiff_of_subset h1.2]
    use Finset.disjoint_sdiff, h1.1
    rw [Finset.card_sdiff h1.2,G.Sized h1.1]
  · use (e ∪ f), ⟨h.2.1, Finset.subset_union_left⟩, Finset.union_sdiff_cancel_left h.1

def toGraph [DecidableEq V] (G : HyperGraph r V) [DecidablePred (· ∈ G)] : SimpleGraph V where
  Adj := fun v w ↦ ∃ e ∈ G, v ∈ e ∧ w ∈ e ∧ v ≠ w
  symm := by aesop_graph
  loopless := by aesop_graph



end HyperGraph

-- /-- A set isomorphism is an equivalence that is also a set embedding. -/
-- structure SetIso {α β : Type*}
--     (𝒜 : Set (Finset α)) (ℬ : Set (Finset β)) extends α ≃ β where
--   /-- Elements are related iff they are related after apply a `SetIso` -/
--   map_mem_iff' : ∀ {A}, A.map toEquiv  ∈ ℬ ↔ A ∈ 𝒜

-- /-- A set isomorphism is an equivalence that is also a set embedding. -/
-- infixl:25 " ≃s " => SetIso

-- namespace SetIso

-- /-- Convert a `SetIso` to a `FamInjHom`. This function is also available as a coercion
-- but often it is easier to write `f.toFamInjHom` than to write explicitly `𝒜` and `𝓑`
-- in the target type. -/
-- def toFamInjHom (f : 𝒜 ≃s ℬ) : 𝒜 ↪s ℬ :=
--   ⟨f.toEquiv.toEmbedding, fun hA ↦ f.map_mem_iff'.mpr hA ⟩

-- theorem toEquiv_injective : Injective (toEquiv : 𝒜 ≃s ℬ → α ≃ β)
--   | ⟨e₁, o₁⟩, ⟨e₂, _⟩, h => by congr

-- instance : CoeOut (𝒜  ≃s ℬ) (𝒜  ↪s ℬ) :=
--   ⟨toFamInjHom⟩

-- instance : FunLike (𝒜  ≃s ℬ) α β where
--   coe x := x
--   coe_injective' := Equiv.coe_fn_injective.comp toEquiv_injective

-- instance : FamHomClass (𝒜  ≃s ℬ) 𝒜 ℬ where
--   map_mem f _ h := Iff.mpr (map_mem_iff' f) h

-- instance : EquivLike (𝒜 ≃s ℬ) α β where
--   coe f := f
--   inv f := f.toEquiv.symm
--   left_inv f := f.left_inv
--   right_inv f := f.right_inv
--   coe_injective' _ _ hf _ := DFunLike.ext' hf

-- @[simp]
-- theorem coe_toFamInjHom (f : 𝒜 ≃s ℬ) : (f.toFamInjHom : α → β) = f :=
--   rfl

-- @[simp]
-- theorem coe_toEmbedding (f : 𝒜 ≃s ℬ) : (f.toEmbedding : α → β) = f :=
--   rfl

-- theorem map_mem_iff (f : 𝒜 ≃s ℬ) {A} : f '' A  ∈ ℬ ↔ A ∈ 𝒜 := f.map_mem_iff'

-- @[simp]
-- theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃A⦄, f '' A  ∈ ℬ ↔ A ∈ 𝒜) :
--     (SetIso.mk f @o : α → β) = f :=
--   rfl

-- @[simp]
-- theorem coe_fn_toEquiv (f : 𝒜 ≃s ℬ) : (f.toEquiv : α → β) = f :=
--   rfl

-- /-- The map `DFunLike.coe : (𝒜  ≃s ℬ) → (α → β)` is injective. -/
-- theorem coe_fn_injective : Injective fun f : 𝒜 ≃s ℬ => (f : α → β) :=
--   DFunLike.coe_injective

-- @[ext]
-- theorem ext ⦃f g : 𝒜 ≃s ℬ⦄ (h : ∀ x, f x = g x) : f = g :=
--   DFunLike.ext f g h

-- /-- Inverse map of a set isomorphism is a set isomorphism. -/
-- protected def symm (f : 𝒜 ≃s ℬ) : ℬ ≃s 𝒜 :=
--   ⟨f.toEquiv.symm, by intro B; rw [← f.map_mem_iff, ← coe_fn_toEquiv, f.1.image_symm_image]⟩

-- /-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
--   because `SetIso` defines custom coercions other than the ones given by `DFunLike`. -/
-- def Simps.apply (h : 𝒜 ≃s ℬ) : α → β :=
--   h

-- /-- See Note [custom simps projection]. -/
-- def Simps.symm_apply (h : 𝒜 ≃s ℬ) : β → α :=
--   h.symm

-- initialize_simps_projections SetIso (toFun → apply, invFun → symm_apply)

-- /-- Identity map is a set isomorphism. -/
-- @[refl, simps! apply]
-- protected def refl (𝒜 : Set (Finset α)) : 𝒜 ≃s 𝒜 :=
--   ⟨Equiv.refl _, by simp⟩

-- /-- Composition of two set isomorphisms is a set isomorphism. -/
-- @[simps! apply]
-- protected def trans (f₁ : 𝒜 ≃s ℬ) (f₂ : ℬ ≃s 𝒞) : 𝒜 ≃s 𝒞 :=
--   ⟨f₁.toEquiv.trans f₂.toEquiv, by
--     intro A;  rw [← f₁.map_mem_iff, ← f₂.map_mem_iff]; congr!; ext; simp⟩

-- instance (𝒜 : Set (Finset α)) : Inhabited (𝒜  ≃s 𝒜) :=
--   ⟨SetIso.refl _⟩

-- @[simp]
-- theorem default_def (𝒜 : Set (Finset α)) : default = SetIso.refl 𝒜 :=
--   rfl

-- /-- A set isomorphism between equal sets on equal types. -/
-- @[simps! toEquiv apply]
-- protected def cast {α β : Type u} {𝒜 : Set (Finset α)} {ℬ : Set (Finset β)} (h₁ : α = β) (h₂ : HEq 𝒜 ℬ) :
--     𝒜 ≃s ℬ :=
--   ⟨Equiv.cast h₁, @fun A => by
--     subst h₁
--     rw [eq_of_heq h₂]
--     simp⟩

-- @[simp]
-- protected theorem cast_symm {α β : Type u} {𝒜 : Set (Finset α)} {ℬ : Set (Finset β)} (h₁ : α = β)
--     (h₂ : HEq 𝒜 ℬ) : (SetIso.cast h₁ h₂).symm = SetIso.cast h₁.symm h₂.symm := rfl

-- @[simp]
-- protected theorem cast_refl {α : Type u} {𝒜 : Set (Finset α)} (h₁ : α = α := rfl)
--     (h₂ : HEq 𝒜 𝒜 := HEq.rfl) : SetIso.cast h₁ h₂ = SetIso.refl 𝒜 := rfl

-- @[simp]
-- protected theorem cast_trans {α β γ : Type u} {𝒜 : Set (Finset α)} {ℬ : Set (Finset β)} {𝒞 : Set (Finset γ)}
--   (h₁ : α = β) (h₁' : β = γ) (h₂ : HEq 𝒜 ℬ) (h₂' : HEq ℬ 𝒞) :
--     (SetIso.cast h₁ h₂).trans (SetIso.cast h₁' h₂') = SetIso.cast (h₁.trans h₁') (h₂.trans h₂') :=
--   ext fun x => by subst h₁; rfl

-- /-- A set isomorphism is also a set isomorphism between complemented sets. -/
-- @[simps!]
-- protected def compl (f : 𝒜 ≃s ℬ) : 𝒜ᶜ ≃s ℬᶜ :=
--   ⟨f, f.map_mem_iff.not⟩

-- @[simp]
-- theorem coe_fn_symm_mk (f o) : ((@SetIso.mk _ _ 𝒜 ℬ f @o).symm : β → α) = f.symm :=
--   rfl

-- @[simp]
-- theorem apply_symm_apply (e : 𝒜 ≃s ℬ) (x : β) : e (e.symm x) = x :=
--   e.toEquiv.apply_symm_apply x

-- @[simp]
-- theorem symm_apply_apply (e : 𝒜 ≃s ℬ) (x : α) : e.symm (e x) = x :=
--   e.toEquiv.symm_apply_apply x

-- theorem mem_symm_apply (e : 𝒜 ≃s ℬ) {B} : e.symm '' B ∈ 𝒜  ↔ B ∈ ℬ  := by
--   rw [← e.map_mem_iff]
--   congr!
--   ext; simp

-- @[simp]
-- theorem self_trans_symm (e : 𝒜 ≃s ℬ) : e.trans e.symm = SetIso.refl 𝒜 :=
--   ext e.symm_apply_apply

-- @[simp]
-- theorem symm_trans_self (e : 𝒜 ≃s ℬ) : e.symm.trans e = SetIso.refl ℬ :=
--   ext e.apply_symm_apply

-- protected theorem bijective (e : 𝒜 ≃s ℬ) : Bijective e :=
--   e.toEquiv.bijective

-- protected theorem injective (e : 𝒜 ≃s ℬ) : Injective e :=
--   e.toEquiv.injective

-- protected theorem surjective (e : 𝒜 ≃s ℬ) : Surjective e :=
--   e.toEquiv.surjective

-- theorem eq_iff_eq (f : 𝒜 ≃s ℬ) {a b} : f a = f b ↔ a = b :=
--   f.injective.eq_iff

-- /-- A surjective surjective FamInjHom is a set isomorphism. -/
-- @[simps! apply]
-- noncomputable def ofSurjective (f : 𝒜 ↪s ℬ) (H : Surjective f) (hsurj : ∀ {B}, B ∈ ℬ → ∃ A ∈ 𝒜,
--   f '' A = B) : 𝒜 ≃s ℬ :=
--   ⟨Equiv.ofBijective f ⟨f.injective, H⟩, by
--   intro A
--   constructor <;> intro h
--   · obtain ⟨A',hA⟩:= hsurj  h
--     convert hA.1
--     simp only [Equiv.ofBijective_apply] at hA
--     apply (image_eq_image f.injective).1
--     rw [hA.2]
--   · exact f.map_mem h⟩

-- end SetIso
