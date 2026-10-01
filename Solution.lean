module

public import TTC.Main

/-
Solution proofs for the Top Trading Cycles formalization.

This module restates the three comparator theorem names under `TTC.Palomar`
(with statements defeq to those in Challenge.lean) and proves them by applying
the library theorems from `TTC.Main`. The library proofs live in the `TTC`
namespace; the `Palomar` namespace here matches the Challenge statement surface.
-/

namespace TTC

namespace Palomar

/-- The TTC procedure removes every agent within `n` rounds. -/
public theorem ttcTerminates {n : Nat} (M : HousingMarket n) :
    (ttcIter M n Finset.univ id).1 = ∅ :=
  TTC.ttcIter_univ_empty M

/-- The TTC allocation is in the core. -/
public theorem ttcInCore {n : Nat} (M : HousingMarket n) :
    Core M (ttcAllocation M) :=
  TTC.ttcInCore M

/-- Strict-core uniqueness: the TTC allocation is the unique bijective
allocation that no coalition can weakly block. -/
public theorem ttcUniqueStrictCore {n : Nat} (M : HousingMarket n)
    (x : Fin n → Fin n) (hxb : Function.Bijective x)
    (hx : StrictCore M x) : x = ttcAllocation M :=
  TTC.ttcUniqueStrictCore M x hxb hx

end Palomar

end TTC
