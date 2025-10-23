/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Data.ULift
import Mathlib.Util.Delaborators
import Mathlib.Util.AssertExists

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerosity
(i.e., existence of a bijection).

## Main definitions

* `Cardinal` is the type of cardinal numbers (in a given universe).
* `Cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `Cardinal`.
* Addition `c₁ + c₂` is defined by `Cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `Cardinal.mul_def : #α * #β = #(α × β)`.
* Exponentiation `c₁ ^ c₂` is defined by `Cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `Cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `Cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `Cardinal.aleph0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `Cardinal.aleph0.{u} : Cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `Cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `Cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `Mathlib/SetTheory/Cardinal/Ordinal.lean`.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Monoid

open List Function Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

/-! ### Definition of cardinals -/

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoid (Type u) where
  r α β := Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
@[pp_with_univ]
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent

namespace Cardinal

/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]
theorem inductionOn {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p #α) : p c :=
  Quotient.inductionOn c h

@[elab_as_elim]
theorem inductionOn₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (h : ∀ α β, p #α #β) : p c₁ c₂ :=
  Quotient.inductionOn₂ c₁ c₂ h

@[elab_as_elim]
theorem inductionOn₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (c₃ : Cardinal) (h : ∀ α β γ, p #α #β #γ) : p c₁ c₂ c₃ :=
  Quotient.inductionOn₃ c₁ c₂ c₃ h

theorem induction_on_pi {ι : Type u} {p : (ι → Cardinal.{v}) → Prop}
    (f : ι → Cardinal.{v}) (h : ∀ f : ι → Type v, p fun i ↦ #(f i)) : p f :=
  Quotient.induction_on_pi f h

protected theorem eq : #α = #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'

@[simp]
theorem mk_out (c : Cardinal) : #c.out = c :=
  Quotient.out_eq _

/-- The representative of the cardinal of a type is equivalent to the original type. -/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)

theorem mk_congr (e : α ≃ β) : #α = #β :=
  Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

/-- Lift a function between `Type*`s to a function between `Cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf #α = #(f α) :=
  rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `Cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-! ### Lifting cardinals to a higher universe -/

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}` -/
@[pp_with_univ]
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]
theorem mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α :=
  rfl

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't work. -/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

/-- A cardinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work. -/
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun _ => mk_congr Equiv.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
theorem lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

theorem out_lift_equiv (a : Cardinal.{u}) : Nonempty ((lift.{v} a).out ≃ a.out) := by
  rw [← mk_out a, ← mk_uLift, mk_out]
  exact ⟨outMkEquiv.trans Equiv.ulift⟩

theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans <| f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
      ⟨Equiv.ulift.trans <| f.trans Equiv.ulift.symm⟩⟩

/-- A variant of `Cardinal.lift_mk_eq` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}

theorem mk_congr_lift {α : Type u} {β : Type v} (e : α ≃ β) : lift.{v} #α = lift.{u} #β :=
  lift_mk_eq'.2 ⟨e⟩

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift

/-! ### Basic cardinals -/

instance : Zero Cardinal.{u} :=
  -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

@[simp]
theorem mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0 :=
  (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]
theorem lift_zero : lift 0 = 0 := mk_eq_zero _

theorem mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : #α ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›

instance : One Cardinal.{u} :=
  -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

theorem mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1 :=
  let ⟨_⟩ := nonempty_unique α; (Equiv.ofUnique α (ULift (Fin 1))).cardinal_eq

instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) :=
  rfl

instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

@[simp]
theorem mk_sum (α : Type u) (β : Type v) : #(α ⊕ β) = lift.{v, u} #α + lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]
theorem mk_option {α : Type u} : #(Option α) = #α + 1 := by
  rw [(Equiv.optionEquivSumPUnit.{u, u} α).cardinal_eq, mk_sum, mk_eq_one PUnit, lift_id, lift_id]

@[simp]
theorem mk_psum (α : Type u) (β : Type v) : #(α ⊕' β) = lift.{v} #α + lift.{u} #β :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)

instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

theorem mul_def (α β : Type u) : #α * #β = #(α × β) :=
  rfl

@[simp]
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance instPowCardinal : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

theorem power_def (α β : Type u) : #α ^ #β = #(β → α) :=
  rfl

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = (lift.{u} #β^lift.{v} #α) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]
theorem lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]
theorem power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
theorem power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = a :=
  inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

theorem power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b * a ^ c :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumArrowEquivProdArrow β γ α

@[simp]
theorem one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0 : Cardinal) ^ a = 0 :=
  inductionOn a fun _ heq =>
    mk_eq_zero_iff.2 <|
      isEmpty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩

theorem power_ne_zero {a : Cardinal} (b : Cardinal) : a ≠ 0 → a ^ b ≠ 0 :=
  inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

theorem mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
  inductionOn₃ a b c fun _ _ γ => mk_congr <| Equiv.arrowProdEquivProdArrow γ _ _

@[simp]
theorem lift_one : lift 1 = 1 := mk_eq_one _

@[simp]
theorem lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

/-! ### Indexed cardinal `sum` -/

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σ i, (f i).out)

@[simp]
theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum fun i => #(f i) :=
  mk_congr <| Equiv.sigmaCongrRight fun _ => outMkEquiv.symm

theorem mk_sigma_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i) :=
  Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.lift_mk_eq'.1 (h i)⟩

theorem mk_sigma_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
  mk_congr <| Equiv.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

/-- Similar to `mk_sigma_congr` with indexing types in different universes. This is not a strict
generalization. -/
theorem mk_sigma_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
  mk_congr <| Equiv.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_sigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ i, f i) = #(Σ i, g i) :=
  mk_sigma_congr (Equiv.refl ι) h

theorem mk_psigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_psigma_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_sigma_arrow {ι} (α : Type*) (f : ι → Type*) :
    #(Sigma f → α) = #(Π i, f i → α) := mk_congr <| Equiv.piCurry fun _ _ ↦ α

@[simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a :=
  inductionOn a fun α =>
    mk_congr <|
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)

theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a := by simp

@[simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equiv.cardinal_eq <|
    Equiv.ulift.trans <|
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
        Nonempty.some <| by rw [← lift_mk_eq.{_,_,v}, mk_out, mk_out, lift_lift]

theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

/-! ### Indexed cardinal `prod` -/

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #(Π i, (f i).out)

@[simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : #(Π i, α i) = prod fun i => #(α i) :=
  mk_congr <| Equiv.piCongrRight fun _ => outMkEquiv.symm

theorem mk_pi_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i) :=
  Cardinal.lift_mk_eq'.2 ⟨.piCongr e fun i ↦ Classical.choice <| Cardinal.lift_mk_eq'.1 (h i)⟩

theorem mk_pi_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_pi_congr_prop {ι ι' : Prop} {f : ι → Type v} {g : ι' → Type v} (e : ι ↔ ι')
    (h : ∀ i, #(f i) = #(g (e.mp i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr (.ofIff e) fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

/-- Similar to `mk_pi_congr` with indexing types in different universes. This is not a strict
generalization. -/
theorem mk_pi_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_pi_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr (Equiv.refl ι) h

theorem mk_pi_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr_prop Iff.rfl h

@[simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι :=
  inductionOn a fun _ =>
    mk_congr <| Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm

theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ #ι :=
  inductionOn a fun _ => (mk_pi _).symm

@[simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 := by
  lift f to ι → Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]

theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by simp [prod_eq_zero]

theorem lift_power_sum {ι : Type u} (a : Cardinal.{v}) (f : ι → Cardinal.{v}) :
    lift.{u, v} a ^ sum f = prod fun i ↦ a ^ f i := by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [← mk_uLift, prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => ULift α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv Equiv.ulift).trans ?_
  exact outMkEquiv.symm

theorem power_sum {ι : Type u} (a : Cardinal.{max u v}) (f : ι → Cardinal.{max u v}) :
    a ^ sum f = prod fun i ↦ a ^ f i := by
  simpa [← lift_umax] using lift_power_sum a f

@[simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

/-! ### The first infinite cardinal `aleph0` -/

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift #ℕ

@[inherit_doc]
scoped notation "ℵ₀" => Cardinal.aleph0

theorem mk_nat : #ℕ = ℵ₀ :=
  (lift_id _).symm

theorem aleph0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _

@[simp]
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _

theorem lift_mk_fin (n : ℕ) : lift #(Fin n) = n := rfl

/-! ### Cardinalities of basic sets and types -/

theorem mk_empty : #Empty = 0 :=
  mk_eq_zero _

theorem mk_pempty : #PEmpty = 0 :=
  mk_eq_zero _

theorem mk_punit : #PUnit = 1 :=
  mk_eq_one PUnit

theorem mk_unit : #Unit = 1 :=
  mk_punit

theorem mk_plift_true : #(PLift True) = 1 :=
  mk_eq_one _

theorem mk_plift_false : #(PLift False) = 0 :=
  mk_eq_zero _

theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    #{ a : α // p (e a) } = #{ b : β // p b } :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)

end Cardinal

-- namespace Tactic

-- open Cardinal Positivity

-- Porting note: Meta code, do not port directly
-- /-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is
--  positive. -/
-- @[positivity]
-- unsafe def positivity_cardinal_pow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` power_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Cardinal`
--     _ =>
--     failed

-- end Tactic
