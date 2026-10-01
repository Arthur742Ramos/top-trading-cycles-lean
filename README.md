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

**Theorems formalized.**

- `TTC.Palomar.ttcTerminates` — the procedure ends: each round removes at least
  one nonempty directed cycle, so after at most `n` rounds nobody remains.
- `TTC.Palomar.ttcInCore` — the TTC allocation is in the **core**: no coalition
  can reallocate its own endowments so that every member is strictly better
  off. (Proof idea: look at the first round in which some coalition member
  trades; they receive their top choice among the houses still present, which
  include everything the coalition could offer them.)
- `TTC.Palomar.ttcUniqueCore` — the core is a **singleton**: the TTC allocation
  is the only core allocation (Roth and Postlewaite, 1977). Same first-leaver
  argument applied to an arbitrary core allocation.

The library additionally proves the TTC allocation is **Pareto optimal** (a
Pareto improvement by the grand coalition would be a blocking deviation),
**individually rational** (every agent weakly prefers their TTC house to their
endowment, since their own house stays available until they trade), and
**strategyproof** (Roth, 1982: no agent can profit by misreporting preferences).

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
