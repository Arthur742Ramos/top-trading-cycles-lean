module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic

namespace TTC

-- A housing market: an endowment bijection plus a profile of strict preference
-- rankings (each a permutation, read least-to-greatest rank).  This is a
-- plain product type rather than a `structure` so that the Palomar
-- comparator sees a genuine `def` (`defnInfo`); the `endow` / `rank` / `mk`
-- accessors below keep the usual dot notation working.  It is an `abbrev`
-- (reducible) so that the `Prod` projections typecheck.
public abbrev HousingMarket (n : Nat) : Type :=
  (Fin n ≃ Fin n) × (Fin n → Fin n ≃ Fin n)

namespace HousingMarket

/-- Which house each agent owns. -/
@[expose] public def endow {n : Nat} (M : HousingMarket n) : Fin n ≃ Fin n := M.1

/-- The strict preference ranking of each agent. -/
@[expose] public def rank {n : Nat} (M : HousingMarket n) : Fin n → Fin n ≃ Fin n := M.2

/-- Build a market from an endowment and a preference profile. -/
@[expose] public def mk {n : Nat} (w : Fin n ≃ Fin n)
    (r : Fin n → Fin n ≃ Fin n) : HousingMarket n := (w, r)

end HousingMarket

public def prefLT {n : Nat} (M : HousingMarket n) (i a b : Fin n) : Prop :=
  (M.rank i).symm a < (M.rank i).symm b

-- Unfolding lemma for `prefLT`, proved here where the definition is in-memory.
public theorem prefLT_unfold {n : Nat} (M : HousingMarket n) (i a b : Fin n) :
    prefLT M i a b ↔ (M.rank i).symm a < (M.rank i).symm b := Iff.rfl

public def prefLE {n : Nat} (M : HousingMarket n) (i a b : Fin n) : Prop :=
  (M.rank i).symm a ≤ (M.rank i).symm b

public def Core {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
    S.Nonempty ∧
    Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
    ∀ i ∈ S, prefLT M i (y i) (x i)

-- Unfolding lemma for `Core`, proved here where the definition is still
-- in-memory (it is opaque when imported).
public theorem Core_unfold {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) :
    Core M x ↔ ¬∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
      S.Nonempty ∧
      Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
      ∀ i ∈ S, prefLT M i (y i) (x i) := Iff.rfl

/-- The strict core: no coalition can *weakly* block, i.e. reallocate its
members' endowed houses so that every member is weakly better off and at
least one is strictly better off.  This is the notion for which the TTC
allocation is the unique (bijective) element (Roth–Postlewaite 1977); the
strong `Core` above can contain other allocations. -/
public def StrictCore {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
    S.Nonempty ∧
    Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
    (∀ i ∈ S, prefLE M i (x i) (y i)) ∧
    (∃ i ∈ S, prefLT M i (x i) (y i))

-- Unfolding lemma for `StrictCore`, proved here where the definition is in-memory.
public theorem StrictCore_unfold {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) :
    StrictCore M x ↔ ¬∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
      S.Nonempty ∧
      Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
      (∀ i ∈ S, prefLE M i (x i) (y i)) ∧
      (∃ i ∈ S, prefLT M i (x i) (y i)) := Iff.rfl

public def ParetoOptimal {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (z : Fin n → Fin n),
    Function.Bijective z ∧
    (∀ i, prefLE M i (x i) (z i)) ∧
    (∃ i, prefLT M i (x i) (z i))

public def IndividuallyRational {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) : Prop :=
  ∀ i, prefLE M i (M.endow i) (x i)

end TTC
