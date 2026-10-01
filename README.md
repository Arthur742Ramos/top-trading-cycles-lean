# Top Trading Cycles — Lean 4 formalization

A Lean 4 + Mathlib formalization of **Gale's top trading cycles (TTC) algorithm
(1974)** for the **Shapley-Scarf housing market** (Shapley and Scarf, 1974).

## The mathematics

A housing market has `n` agents and `n` houses. Each agent owns exactly one
house (the endowment is a bijection), and each agent has a **strict** preference
order over houses.

**The TTC algorithm** (due to David Gale). Repeat the following rounds until no
agents remain:

1. Each remaining agent points to the owner of their favourite *remaining*
   house; each remaining house points to its owner.
2. Every node has out-degree exactly 1, so the resulting directed graph contains
   directed cycles. Every agent in a cycle receives the house they pointed to;
   those agents and houses leave the market.

**Theorems on the comparator surface** (checked by the Palomar verifier
against `Challenge.lean`).

- `TTC.Palomar.ttcTerminates` — the procedure ends: each round removes at least
  one nonempty directed cycle, so after at most `n` rounds nobody remains.
- `TTC.Palomar.ttcInCore` — the TTC allocation is in the (ordinary) **core**:
  no coalition can reallocate its own endowments so that every member is
  strictly better off. (Proof idea: look at the first round in which some
  coalition member trades; they receive their top choice among the houses
  still present, which include everything the coalition could offer them.)
- `TTC.Palomar.ttcUniqueStrictCore` — **strict-core uniqueness**: the TTC
  allocation is the unique *bijective* allocation that no coalition can
  *weakly* block (every member weakly better off, at least one strictly).
  Concretely, for `(x : Fin n → Fin n)` with `(hxb : Function.Bijective x)`
  and `(hx : StrictCore M x)`, the theorem concludes `x = ttcAllocation M`.
  This is uniqueness in the strict core, not a singleton claim about the
  ordinary core.

**Further results in the library** (`TTC/`, not on the comparator surface).

- `TTC.ttcPareto` — the TTC allocation is Pareto optimal.
- `TTC.ttcIR` — the TTC allocation is individually rational: every agent
  weakly prefers their TTC house to their endowment.
- `TTC.ttcInStrictCore` — the TTC allocation is in the strict core
  (Shapley-Scarf, 1974): no coalition can weakly block it.
- `TTC.ttcStrategyproof` — **strategyproofness** (Roth, 1982): for every
  endowment `w`, preference profile `r`, agent `i`, and misreport `rNew`,
  the truthful TTC outcome is weakly preferred (under `i`'s true preferences)
  to the outcome when `i` alone reports `rNew`. The proof goes through
  strict-core membership: a profitable deviator cannot belong to the first
  truthful cycle where the allocations differ, so that cycle would weakly
  block the reported-profile outcome.
- `TTC.ttc_preferred_house_removed` — a house strictly preferred to an
  agent's TTC assignment leaves the market (with its owner) in a strictly
  earlier round than the agent.

Preference convention: `(rank i).symm h` is the rank of house `h` for agent
`i`, smaller is better; `prefLE M i a b` means `a` is weakly preferred to `b`.

## Repository layout

- `TTC/` — the proof library (`TTC/Main.lean` is the root).
- `Challenge.lean` — the small auditable statement surface: the comparator
  definitions with real bodies and the comparator theorems as deliberate
  placeholders. Imports only Lean/Mathlib, never project modules.
- `Solution.lean` — restates the comparator theorem names and proves them from
  the library (kept under `TTC.Palomar.Implementation`).
- `comparator.json` — the Palomar comparator configuration.
- `formalization.yaml` — registry metadata.
- `scripts/verify-palomar.sh` — the local replica of the registry's checks:
  module headers, comparator names elaborating in `Challenge` with the right
  declaration kinds (`def`s are `defnInfo`, never structures), zero sorries in
  proofs, the axiom audit, and the official `lake comparator` stage.

## Building

Requires the pinned Lean/Mathlib `v4.35.0-rc2` toolchain (see `lean-toolchain`).

```bash
./scripts/verify-palomar.sh
```

## References

- L. S. Shapley and H. Scarf, "On cores and indivisibility", *Journal of
  Mathematical Economics* 1(1), 23-37, 1974.
- A. E. Roth and A. Postlewaite, "Weak versus strong domination in a market
  with indivisible goods", *Journal of Mathematical Economics* 4(2), 131-137,
  1977.
- A. E. Roth, "Incentive compatibility in a market with indivisible goods",
  *Economics Letters* 9(2), 127-132, 1982.

## License

BSD-3-Clause. See `LICENSE`.
