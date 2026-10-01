module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat

/-
Statement surface for the Top Trading Cycles formalization.

This module contains the comparator definitions (HousingMarket, ttcAllocation,
Core, StrictCore) with their real bodies, copied from the TTC library, and the
three comparator theorems as deliberate placeholder sorries per the Palomar
statement-surface format. The Solution module proves these theorems from the
library.
-/

namespace TTC

open scoped Classical

-- A housing market: an endowment bijection plus a profile of strict preference
-- rankings (each a permutation, read least-to-greatest rank).
public abbrev HousingMarket (n : Nat) : Type :=
  (Fin n ≃ Fin n) × (Fin n → Fin n ≃ Fin n)

namespace HousingMarket

/-- Which house each agent owns. -/
public def endow {n : Nat} (M : HousingMarket n) : Fin n ≃ Fin n := M.1

/-- The strict preference ranking of each agent. -/
public def rank {n : Nat} (M : HousingMarket n) : Fin n → Fin n ≃ Fin n := M.2

/-- Build a market from an endowment and a preference profile. -/
public def mk {n : Nat} (w : Fin n ≃ Fin n)
    (r : Fin n → Fin n ≃ Fin n) : HousingMarket n := (w, r)

end HousingMarket

public def prefLT {n : Nat} (M : HousingMarket n) (i a b : Fin n) : Prop :=
  (M.rank i).symm a < (M.rank i).symm b

public def prefLE {n : Nat} (M : HousingMarket n) (i a b : Fin n) : Prop :=
  (M.rank i).symm a ≤ (M.rank i).symm b

/-- The core: no coalition can reallocate its own endowments so that every
member strictly prefers the deviation. -/
public def Core {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
    S.Nonempty ∧
    Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
    ∀ i ∈ S, prefLT M i (y i) (x i)

/-- The strict core: no coalition can weakly block (every member weakly better
off, at least one strictly), reallocating its members' endowed houses. The TTC
allocation is the unique bijective strict-core allocation (Roth-Postlewaite
1977). -/
public def StrictCore {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n) : Prop :=
  ¬ ∃ (S : Finset (Fin n)) (y : Fin n → Fin n),
    S.Nonempty ∧
    Set.BijOn y (S : Set (Fin n)) (M.endow '' (S : Set (Fin n))) ∧
    (∀ i ∈ S, prefLE M i (y i) (x i)) ∧
    (∃ i ∈ S, prefLT M i (y i) (x i))

private theorem favRanks_nonempty {n : Nat} (M : HousingMarket n)
    (H : Finset (Fin n)) (hne : H.Nonempty) (a : Fin n) :
    (Finset.univ.filter (fun k : Fin n => (M.rank a) k ∈ H)).Nonempty := by
  obtain ⟨h, hh⟩ := hne
  obtain ⟨k, hk⟩ := (M.rank a).surjective h
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩⟩
  simpa only [hk] using hh

public noncomputable def favHouse {n : Nat} (M : HousingMarket n)
    (H : Finset (Fin n)) (hne : H.Nonempty) (a : Fin n) : Fin n :=
  let S := Finset.univ.filter (fun k : Fin n => (M.rank a) k ∈ H)
  have hS : S.Nonempty := favRanks_nonempty M H hne a
  (M.rank a) (S.min' hS)

public theorem exists_simple_cycle {n : Nat} (f : Fin n → Fin n) (a : Fin n) :
    ∃ i j : Nat, i < j ∧ f^[j] a = f^[i] a ∧
      (∀ k₁ k₂, i ≤ k₁ → k₁ < j → i ≤ k₂ → k₂ < j →
        f^[k₁] a = f^[k₂] a → k₁ = k₂) := by
  have hnot : ¬ Function.Injective (fun k : Fin (n + 1) => f^[k.val] a) :=
    Fintype.not_injective_of_card_lt _ (by simp)
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hnot
  have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
  have hex : ∃ j : Nat, ∃ i : Nat, i < j ∧ f^[j] a = f^[i] a := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · exact ⟨v.val, u.val, hlt, huv.symm⟩
    · exact ⟨u.val, v.val, hgt, huv⟩
  let j := Nat.find hex
  obtain ⟨i, hij, hclose⟩ := Nat.find_spec hex
  refine ⟨i, j, hij, hclose, ?_⟩
  intro k₁ k₂ _ hk₁ _ hk₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (Nat.find_min hex hk₂) ⟨k₁, hlt, heq.symm⟩
  · exact (Nat.find_min hex hk₁) ⟨k₂, hgt, heq⟩

-- The chosen witness keeps the cycle bounds and distinctness proof together.
private structure SimpleCycle {n : Nat} (f : Fin n → Fin n) (a : Fin n) where
  first : Nat
  last : Nat
  lt : first < last
  closes : f^[last] a = f^[first] a
  distinct : ∀ k₁ k₂, first ≤ k₁ → k₁ < last → first ≤ k₂ → k₂ < last →
    f^[k₁] a = f^[k₂] a → k₁ = k₂

private noncomputable def chooseCycle {n : Nat} (f : Fin n → Fin n) (a : Fin n) :
    SimpleCycle f a :=
  Classical.choice (by
    obtain ⟨i, j, hij, hclose, hdistinct⟩ := exists_simple_cycle f a
    exact ⟨⟨i, j, hij, hclose, hdistinct⟩⟩)

private def cycleAgents {n : Nat} {f : Fin n → Fin n} {a : Fin n}
    (cycle : SimpleCycle f a) : Finset (Fin n) :=
  (Finset.Ico cycle.first cycle.last).image (fun k => f^[k] a)

private noncomputable def roundPoint {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (hne : A.Nonempty) : Fin n → Fin n :=
  fun a => if a ∈ A then
    M.endow.symm (favHouse M (A.image M.endow) (hne.image M.endow) a) else a

public noncomputable def ttcRound {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (hne : A.Nonempty) : Finset (Fin n) × (Fin n → Fin n) :=
  let H := A.image M.endow
  have hH : H.Nonempty := hne.image M.endow
  let f := roundPoint M A hne
  let a₀ : Fin n := Classical.choose hne
  let cycle := chooseCycle f a₀
  let C := (Finset.Ico cycle.first cycle.last).image (fun k => f^[k] a₀)
  let assign : Fin n → Fin n := fun c => if c ∈ C then favHouse M H hH c else c
  (C, assign)

public noncomputable def ttcIter {n : Nat} (M : HousingMarket n) :
    Nat → Finset (Fin n) → (Fin n → Fin n) → Finset (Fin n) × (Fin n → Fin n) :=
  fun fuel =>
    Nat.rec (motive := fun _ => Finset (Fin n) → (Fin n → Fin n) →
        Finset (Fin n) × (Fin n → Fin n))
      (fun A x => (A, x))
      (fun _ ih A x =>
        if h : A.Nonempty then
          let (C, assign) := ttcRound M A h
          ih (A \ C) (fun i => if i ∈ C then assign i else x i)
        else (A, x))
      fuel

/-- The allocation produced by Gale's top trading cycles algorithm, in
one-cycle-at-a-time form: each agent points to the owner of their favourite
remaining house, houses point to their owners, and the single directed cycle
reachable from a chosen remaining agent trades and leaves; repeated until
nobody remains. This computes the same allocation as the simultaneous version
(see the remark in README.md). -/
public noncomputable def ttcAllocation {n : Nat} (M : HousingMarket n) : Fin n → Fin n :=
  (ttcIter M n Finset.univ id).2

namespace Palomar

/-- The TTC procedure removes every agent within `n` rounds: iterating the
round function `n` times leaves the empty set of remaining agents. -/
public theorem ttcTerminates {n : Nat} (M : HousingMarket n) :
    (ttcIter M n Finset.univ id).1 = ∅ :=
  sorry

/-- The TTC allocation is in the core: no coalition can reallocate its own
endowments to make every member strictly better off. -/
public theorem ttcInCore {n : Nat} (M : HousingMarket n) :
    Core M (ttcAllocation M) :=
  sorry

/-- Strict-core uniqueness: the TTC allocation is the unique bijective
allocation that no coalition can weakly block. -/
public theorem ttcUniqueStrictCore {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) (hxb : Function.Bijective x)
    (hx : StrictCore M x) : x = ttcAllocation M :=
  sorry

end Palomar

end TTC
