module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic

namespace TTC

public structure HousingMarket (n : Nat) where
  endow : Fin n ≃ Fin n
  rank : Fin n → (Fin n ≃ Fin n)

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

public def ParetoOptimal {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (z : Fin n → Fin n),
    Function.Bijective z ∧
    (∀ i, prefLE M i (x i) (z i)) ∧
    (∃ i, prefLT M i (x i) (z i))

public def IndividuallyRational {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) : Prop :=
  ∀ i, prefLE M i (M.endow i) (x i)

end TTC
