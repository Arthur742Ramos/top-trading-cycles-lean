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

public def prefLE {n : Nat} (M : HousingMarket n) (i a b : Fin n) : Prop :=
  (M.rank i).symm a ≤ (M.rank i).symm b

public def Core {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
    S.Nonempty ∧
    Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
    ∀ i ∈ S, prefLT M i (y i) (x i)

public def ParetoOptimal {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (z : Fin n → Fin n),
    Function.Bijective z ∧
    (∀ i, prefLE M i (x i) (z i)) ∧
    (∃ i, prefLT M i (x i) (z i))

public def IndividuallyRational {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) : Prop :=
  ∀ i, prefLE M i (M.endow i) (x i)

-- M1b will replace this body with the TTC allocation.
public def ttcMechanism (n : Nat) (w : Fin n ≃ Fin n)
    (r : Fin n → (Fin n ≃ Fin n)) : Fin n → Fin n :=
  fun i => w i

public def Strategyproof (n : Nat) (w : Fin n ≃ Fin n) : Prop :=
  ∀ (r : Fin n → (Fin n ≃ Fin n)) (i : Fin n) (rNew : Fin n ≃ Fin n),
    let x := ttcMechanism n w r
    let xNew := ttcMechanism n w (Function.update r i rNew)
    prefLE (HousingMarket.mk w r) i (xNew i) (x i)

end TTC
