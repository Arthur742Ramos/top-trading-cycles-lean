module

public import TTC.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat

namespace TTC

open Function
open scoped Classical

noncomputable section

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

public theorem favHouse_mem {n : Nat} (M : HousingMarket n)
    {H : Finset (Fin n)} (hne : H.Nonempty) (a : Fin n) :
    favHouse M H hne a ∈ H := by
  let S := Finset.univ.filter (fun k : Fin n => (M.rank a) k ∈ H)
  have hS : S.Nonempty := favRanks_nonempty M H hne a
  change (M.rank a) (S.min' hS) ∈ H
  exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2

public theorem favHouse_best {n : Nat} (M : HousingMarket n)
    {H : Finset (Fin n)} (hne : H.Nonempty) (a : Fin n)
    {h : Fin n} (hh : h ∈ H) :
    (M.rank a).symm (favHouse M H hne a) ≤ (M.rank a).symm h := by
  let S := Finset.univ.filter (fun k : Fin n => (M.rank a) k ∈ H)
  have hS : S.Nonempty := favRanks_nonempty M H hne a
  change (M.rank a).symm ((M.rank a) (S.min' hS)) ≤ (M.rank a).symm h
  rw [Equiv.symm_apply_apply]
  apply Finset.min'_le S
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simpa only [Equiv.apply_symm_apply] using hh⟩

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

private theorem cycleAgents_nonempty {n : Nat} {f : Fin n → Fin n} {a : Fin n}
    (cycle : SimpleCycle f a) : (cycleAgents cycle).Nonempty := by
  refine ⟨f^[cycle.first] a, Finset.mem_image.mpr ⟨cycle.first, ?_, rfl⟩⟩
  exact Finset.mem_Ico.mpr ⟨le_rfl, cycle.lt⟩

private theorem cycleAgents_closed {n : Nat} {f : Fin n → Fin n} {a : Fin n}
    (cycle : SimpleCycle f a) {c : Fin n} (hc : c ∈ cycleAgents cycle) :
    f c ∈ cycleAgents cycle := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hik, hkj⟩ := Finset.mem_Ico.mp hk
  by_cases hnext : k + 1 < cycle.last
  · refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, hnext⟩, ?_⟩
    exact Function.iterate_succ_apply' f k a
  · have hwrap : k + 1 = cycle.last := by omega
    refine Finset.mem_image.mpr
      ⟨cycle.first, Finset.mem_Ico.mpr ⟨le_rfl, cycle.lt⟩, ?_⟩
    calc
      f^[cycle.first] a = f^[cycle.last] a := cycle.closes.symm
      _ = f^[k + 1] a := by rw [hwrap]
      _ = f (f^[k] a) := Function.iterate_succ_apply' f k a

private theorem cycleAgents_predecessor {n : Nat} {f : Fin n → Fin n} {a : Fin n}
    (cycle : SimpleCycle f a) {d : Fin n} (hd : d ∈ cycleAgents cycle) :
    ∃ c ∈ cycleAgents cycle, f c = d := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hik, hkj⟩ := Finset.mem_Ico.mp hk
  by_cases hfirst : cycle.first < k
  · have hsucc : (k - 1).succ = k := by omega
    refine ⟨f^[k - 1] a, Finset.mem_image.mpr
      ⟨k - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
    have h := (Function.iterate_succ_apply' f (k - 1) a).symm
    rw [hsucc] at h
    exact h
  · have hkfirst : k = cycle.first := by omega
    have hij := cycle.lt
    have hsucc : (cycle.last - 1).succ = cycle.last := by omega
    refine ⟨f^[cycle.last - 1] a, Finset.mem_image.mpr
      ⟨cycle.last - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
    have h := (Function.iterate_succ_apply' f (cycle.last - 1) a).symm
    rw [hsucc, cycle.closes, ← hkfirst] at h
    exact h

private theorem cycleAgents_inj {n : Nat} {f : Fin n → Fin n} {a : Fin n}
    (cycle : SimpleCycle f a) : Set.InjOn f ↑(cycleAgents cycle) := by
  let next : Nat → Nat := fun k => if k + 1 < cycle.last then k + 1 else cycle.first
  have hij := cycle.lt
  have next_bounds (k : Nat) (hik : cycle.first ≤ k) (hkj : k < cycle.last) :
      cycle.first ≤ next k ∧ next k < cycle.last := by
    dsimp only [next]
    split_ifs <;> omega
  have next_apply (k : Nat) (hik : cycle.first ≤ k) (hkj : k < cycle.last) :
      f^[next k] a = f (f^[k] a) := by
    dsimp only [next]
    split_ifs with hnext
    · exact Function.iterate_succ_apply' f k a
    · have hwrap : k + 1 = cycle.last := by omega
      calc
        f^[cycle.first] a = f^[cycle.last] a := cycle.closes.symm
        _ = f^[k + 1] a := by rw [hwrap]
        _ = f (f^[k] a) := Function.iterate_succ_apply' f k a
  intro c₁ hc₁ c₂ hc₂ heq
  obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.mp hc₁
  obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hc₂
  obtain ⟨hi₁, hj₁⟩ := Finset.mem_Ico.mp hk₁
  obtain ⟨hi₂, hj₂⟩ := Finset.mem_Ico.mp hk₂
  have hn₁ := next_bounds k₁ hi₁ hj₁
  have hn₂ := next_bounds k₂ hi₂ hj₂
  have hnext : next k₁ = next k₂ :=
    cycle.distinct _ _ hn₁.1 hn₁.2 hn₂.1 hn₂.2 (by
      rw [next_apply k₁ hi₁ hj₁, next_apply k₂ hi₂ hj₂]
      exact heq)
  have hk : k₁ = k₂ := by
    dsimp only [next] at hnext
    split_ifs at hnext <;> omega
  exact congrArg (fun k => f^[k] a) hk

private noncomputable def roundPoint {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (hne : A.Nonempty) : Fin n → Fin n :=
  fun a => if a ∈ A then
    M.endow.symm (favHouse M (A.image M.endow) (hne.image M.endow) a) else a

private theorem roundPoint_mem {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {a : Fin n} (ha : a ∈ A) :
    roundPoint M A hne a ∈ A := by
  have hh := favHouse_mem M (hne.image M.endow) a
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hh
  change (if a ∈ A then
    M.endow.symm (favHouse M (A.image M.endow) (hne.image M.endow) a) else a) ∈ A
  rw [ite_eq_left ha, ← heq, Equiv.symm_apply_apply]
  exact hb

private theorem roundPoint_endow {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {a : Fin n} (ha : a ∈ A) :
    M.endow (roundPoint M A hne a) =
      favHouse M (A.image M.endow) (hne.image M.endow) a := by
  change M.endow (if a ∈ A then
    M.endow.symm (favHouse M (A.image M.endow) (hne.image M.endow) a) else a) = _
  rw [ite_eq_left ha, Equiv.apply_symm_apply]

private theorem roundIter_mem {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) (k : Nat) :
    (roundPoint M A hne)^[k] (Classical.choose hne) ∈ A := by
  induction k with
  | zero => exact Classical.choose_spec hne
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact roundPoint_mem M hne ih

private noncomputable def roundCycle {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (hne : A.Nonempty) :
    SimpleCycle (roundPoint M A hne) (Classical.choose hne) :=
  chooseCycle (roundPoint M A hne) (Classical.choose hne)

private noncomputable def roundAgents {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (hne : A.Nonempty) : Finset (Fin n) :=
  cycleAgents (roundCycle M A hne)

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

public theorem ttcRound_nonempty {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) : (ttcRound M A hne).1.Nonempty := by
  exact cycleAgents_nonempty (roundCycle M A hne)

-- Congruence for ttcRound when the set is rewritten. Proved here where
-- ttcRound is in-memory.
public theorem ttcRound_fst_congr {n : Nat} (M : HousingMarket n)
    {A A' : Finset (Fin n)} (hAA' : A = A')
    (h : A.Nonempty) (h' : A'.Nonempty) :
    (ttcRound M A h).1 = (ttcRound M A' h').1 := by
  cases hAA'
  rfl

public theorem ttcRound_snd_congr {n : Nat} (M : HousingMarket n)
    {A A' : Finset (Fin n)} (hAA' : A = A')
    (h : A.Nonempty) (h' : A'.Nonempty) (i : Fin n) :
    (ttcRound M A h).2 i = (ttcRound M A' h').2 i := by
  cases hAA'
  rfl

public theorem ttcRound_sub {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) : (ttcRound M A hne).1 ⊆ A := by
  intro c hc
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  exact roundIter_mem M hne k

private theorem ttcRound_assign_eq {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {c : Fin n}
    (hc : c ∈ (ttcRound M A hne).1) :
    (ttcRound M A hne).2 c =
      favHouse M (A.image M.endow) (hne.image M.endow) c := by
  change c ∈ roundAgents M A hne at hc
  change (if c ∈ roundAgents M A hne then
    favHouse M (A.image M.endow) (hne.image M.endow) c else c) = _
  rw [ite_eq_left hc]

public theorem ttcRound_assign_mem {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {c : Fin n}
    (hc : c ∈ (ttcRound M A hne).1) :
    (ttcRound M A hne).2 c ∈ A.image M.endow := by
  rw [ttcRound_assign_eq M hne hc]
  exact favHouse_mem M (hne.image M.endow) c

public theorem ttcRound_assign_best {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {c : Fin n}
    (hc : c ∈ (ttcRound M A hne).1) {h : Fin n} (hh : h ∈ A.image M.endow) :
    (M.rank c).symm ((ttcRound M A hne).2 c) ≤ (M.rank c).symm h := by
  rw [ttcRound_assign_eq M hne hc]
  exact favHouse_best M (hne.image M.endow) c hh

private theorem ttcRound_assign_endow {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) {c : Fin n}
    (hc : c ∈ (ttcRound M A hne).1) :
    (ttcRound M A hne).2 c = M.endow (roundPoint M A hne c) := by
  rw [ttcRound_assign_eq M hne hc]
  exact (roundPoint_endow M hne (ttcRound_sub M hne hc)).symm

public theorem ttcRound_image_eq {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) :
    (ttcRound M A hne).1.image (ttcRound M A hne).2 =
      (ttcRound M A hne).1.image (⇑M.endow) := by
  ext h
  constructor
  · intro hh
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hh
    have hnext : roundPoint M A hne c ∈ (ttcRound M A hne).1 :=
      cycleAgents_closed (roundCycle M A hne) hc
    refine Finset.mem_image.mpr ⟨roundPoint M A hne c, hnext, ?_⟩
    exact (ttcRound_assign_endow M hne hc).symm
  · intro hh
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨c, hc, hcd⟩ := cycleAgents_predecessor (roundCycle M A hne) hd
    refine Finset.mem_image.mpr ⟨c, hc, ?_⟩
    rw [ttcRound_assign_endow M hne hc, hcd]

public theorem ttcRound_assign_inj {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) :
    Set.InjOn (ttcRound M A hne).2 ↑((ttcRound M A hne).1) := by
  intro c₁ hc₁ c₂ hc₂ heq
  have hpoint : roundPoint M A hne c₁ = roundPoint M A hne c₂ :=
    M.endow.injective (by
      rw [← ttcRound_assign_endow M hne hc₁, ← ttcRound_assign_endow M hne hc₂]
      exact heq)
  exact cycleAgents_inj (roundCycle M A hne) hc₁ hc₂ hpoint

public theorem ttcRound_card_lt {n : Nat} (M : HousingMarket n)
    {A : Finset (Fin n)} (hne : A.Nonempty) :
    (A \ (ttcRound M A hne).1).card < A.card := by
  rw [Finset.card_sdiff_of_subset (ttcRound_sub M hne)]
  have hC := Finset.card_pos.mpr (ttcRound_nonempty M hne)
  have hA := Finset.card_pos.mpr hne
  omega

public noncomputable def ttcIter {n : Nat} (M : HousingMarket n) :
    Nat → Finset (Fin n) → (Fin n → Fin n) → Finset (Fin n) × (Fin n → Fin n)
  | 0, A, x => (A, x)
  | fuel + 1, A, x =>
      if h : A.Nonempty then
        let (C, assign) := ttcRound M A h
        ttcIter M fuel (A \ C) (fun i => if i ∈ C then assign i else x i)
      else (A, x)

public noncomputable def ttcAllocation {n : Nat} (M : HousingMarket n) : Fin n → Fin n :=
  (ttcIter M n Finset.univ id).2

-- Unfolding lemma for `ttcAllocation`, proved here where `ttcIter` is still
-- in-memory (its definition is opaque when imported). Private to avoid
-- export requirements.
private theorem ttcAllocation_eq_private {n : Nat} (M : HousingMarket n) :
    ttcAllocation M = (ttcIter M n Finset.univ id).2 := rfl

-- Helper to convert injectivity from ttcIter form to ttcAllocation form,
-- proved here where the defeq is available.
public theorem ttcAllocation_inj_of_iter_inj {n : Nat} (M : HousingMarket n)
    (h : Function.Injective (ttcIter M n Finset.univ id).2) :
    Function.Injective (ttcAllocation M) := h

-- Application unfolding for `ttcAllocation`, proved here where `ttcIter`
-- is in-memory. Private to avoid export requirements.
private theorem ttcAllocation_apply_private {n : Nat} (M : HousingMarket n) (i : Fin n) :
    ttcAllocation M i = (ttcIter M n Finset.univ id).2 i := rfl

-- Public version via the private one (the private rfl works, public needs help).
public theorem ttcAllocation_apply {n : Nat} (M : HousingMarket n) (i : Fin n) :
    ttcAllocation M i = (ttcIter M n Finset.univ id).2 i :=
  ttcAllocation_apply_private M i

-- Unfolding equations for `ttcIter`, exported as theorems because the
-- auto-generated equation lemmas do not persist in the olean.
public theorem ttcIter_zero {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) (x : Fin n → Fin n) :
    ttcIter M 0 A x = (A, x) :=
  ttcIter.eq_1 M A x

public theorem ttcIter_succ {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) :
    ttcIter M (fuel + 1) A x =
      if h : A.Nonempty then
        ttcIter M fuel (A \ (ttcRound M A h).1)
          (fun i => if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i)
      else (A, x) := by
  have e1 : fuel + 1 = fuel.succ := rfl
  rw [e1, ttcIter.eq_2]

public def ttcMechanism (n : Nat) (w : Fin n ≃ Fin n)
    (r : Fin n → (Fin n ≃ Fin n)) : Fin n → Fin n :=
  ttcAllocation ⟨w, r⟩

public def Strategyproof (n : Nat) (w : Fin n ≃ Fin n) : Prop :=
  ∀ (r : Fin n → (Fin n ≃ Fin n)) (i : Fin n) (rNew : Fin n ≃ Fin n),
    let x := ttcMechanism n w r
    let xNew := ttcMechanism n w (Function.update r i rNew)
    prefLE (HousingMarket.mk w r) i (xNew i) (x i)

end

end TTC
