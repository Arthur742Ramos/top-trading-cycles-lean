module

public import TTC.Defs
public import TTC.Algorithm

namespace TTC

open scoped Classical

-- Remaining agents after a given number of rounds.
private noncomputable def rounds {n : Nat} (M : HousingMarket n) :
    Nat → Finset (Fin n) → Finset (Fin n)
  | 0, A => A
  | k + 1, A =>
      if h : A.Nonempty then rounds M k (A \ (ttcRound M A h).1) else A

private theorem rounds_succ {n : Nat} (M : HousingMarket n) (k : Nat)
    (A : Finset (Fin n)) (h : A.Nonempty) :
    rounds M (k + 1) A = rounds M k (A \ (ttcRound M A h).1) := by
  show rounds M k.succ A = _
  rw [rounds.eq_2, dite_eq_left h]

private theorem rounds_empty {n : Nat} (M : HousingMarket n) (k : Nat) :
    rounds M k ∅ = ∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show rounds M k.succ ∅ = _
      rw [rounds.eq_2, dite_eq_right Finset.not_nonempty_empty]

private theorem rounds_subset {n : Nat} (M : HousingMarket n) (k : Nat)
    (A : Finset (Fin n)) : rounds M (k + 1) A ⊆ rounds M k A := by
  induction k generalizing A with
  | zero =>
      by_cases h : A.Nonempty
      · rw [rounds_succ M 0 A h]
        exact Finset.sdiff_subset
      · have e : rounds M 1 A = A := by
          show rounds M (Nat.succ 0) A = _
          rw [rounds.eq_2, dite_eq_right h]
        rw [e]
        exact fun _ hi => hi
  | succ k ih =>
      by_cases h : A.Nonempty
      · rw [rounds_succ M (k + 1) A h, rounds_succ M k A h]
        exact ih _
      · have e1 : rounds M (k + 2) A = A := by
          rw [rounds.eq_2, dite_eq_right h]
        have e2 : rounds M (k + 1) A = A := by
          rw [rounds.eq_2, dite_eq_right h]
        rw [e1, e2]

private theorem ttcIter_step_fst {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) (h : A.Nonempty) :
    (ttcIter M (fuel + 1) A x).1 =
      (ttcIter M fuel (A \ (ttcRound M A h).1)
        (fun i => if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i)).1 := by
  have e1 : fuel + 1 = fuel.succ := rfl
  rw [ttcIter_succ M fuel A x, dite_eq_left h]

private theorem ttcIter_step_snd {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) (h : A.Nonempty) :
    (ttcIter M (fuel + 1) A x).2 =
      (ttcIter M fuel (A \ (ttcRound M A h).1)
        (fun i => if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i)).2 := by
  have e1 : fuel + 1 = fuel.succ := rfl
  rw [ttcIter_succ M fuel A x, dite_eq_left h]

private theorem ttcIter_fst_eq_rounds {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) :
    (ttcIter M fuel A x).1 = rounds M fuel A := by
  induction fuel generalizing A x with
  | zero => simp [ttcIter_zero, rounds]
  | succ fuel ih =>
      by_cases h : A.Nonempty
      · rw [ttcIter_step_fst M fuel A x h, rounds_succ M fuel A h]
        exact ih _ _
      · rw [ttcIter_succ M fuel A x, dite_eq_right h]
        have e1 : fuel + 1 = fuel.succ := rfl
        rw [e1, rounds.eq_2, dite_eq_right h]

private theorem iter_empties {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) :
    A.card ≤ fuel → (ttcIter M fuel A x).1 = ∅ := by
  induction fuel generalizing A x with
  | zero =>
      intro hle
      rw [ttcIter_zero]
      exact Finset.card_eq_zero.mp (by omega : A.card = 0)
  | succ fuel ih =>
      intro hle
      by_cases h : A.Nonempty
      · rw [ttcIter_step_fst M fuel A x h]
        exact ih _ _ (by
          have hlt := ttcRound_card_lt M h
          omega)
      · have e1 : fuel + 1 = fuel.succ := rfl
        rw [ttcIter_succ M fuel A x, dite_eq_right h]
        exact Finset.not_nonempty_iff_eq_empty.mp h

private theorem iter_preserves {n : Nat} (M : HousingMarket n) (fuel : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) (i : Fin n) :
    i ∉ A → (ttcIter M fuel A x).2 i = x i := by
  induction fuel generalizing A x with
  | zero =>
      intro hi
      rw [ttcIter_zero]
  | succ fuel ih =>
      intro hi
      by_cases h : A.Nonempty
      · have hiC : i ∉ (ttcRound M A h).1 :=
          fun hc => hi (ttcRound_sub M h hc)
        have hiA : i ∉ A \ (ttcRound M A h).1 :=
          fun hm => hi (Finset.mem_sdiff.mp hm).1
        rw [ttcIter_step_snd M fuel A x h, ih _ _ hiA]
        show (if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i) = x i
        rw [ite_eq_right hiC]
      · have e1 : fuel + 1 = fuel.succ := rfl
        rw [ttcIter_succ M fuel A x, dite_eq_right h]

private theorem mem_diff_exists {n : Nat} (M : HousingMarket n) (i : Fin n)
    {A : Finset (Fin n)} {fuel : Nat} :
    i ∈ A → A.card ≤ fuel →
      ∃ k, k < fuel ∧ i ∈ rounds M k A \ rounds M (k + 1) A := by
  classical
  intro hi hle
  have hempty : rounds M fuel A = ∅ := by
    rw [← ttcIter_fst_eq_rounds M fuel A id]
    exact iter_empties M fuel A id hle
  have hex : ∃ k, i ∉ rounds M k A := ⟨fuel, by rw [hempty]; exact Finset.notMem_empty i⟩
  let k₀ := Nat.find hex
  have hle_prime : k₀ ≤ fuel := Nat.find_min' hex (by
    rw [hempty]
    exact Finset.notMem_empty i)
  have hpos : 0 < k₀ := by
    by_contra hcon
    have hk0 : k₀ = 0 := by omega
    have hspec : i ∉ rounds M k₀ A := Nat.find_spec hex
    rw [hk0] at hspec
    exact hspec hi
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  refine ⟨k, by omega, ?_⟩
  have h1 : i ∈ rounds M k A := by
    by_contra hcon
    have hle2 : k₀ ≤ k := Nat.find_min' hex hcon
    omega
  have h2 : i ∉ rounds M (k + 1) A := by
    show i ∉ rounds M k.succ A
    rw [← hk]
    exact Nat.find_spec hex
  exact Finset.mem_sdiff.mpr ⟨h1, h2⟩

-- An agent's assignment at its leaving round survives every later round.
private theorem assign_of_mem_diff {n : Nat} (M : HousingMarket n) (k m : Nat)
    (A : Finset (Fin n)) (x : Fin n → Fin n) (i : Fin n) :
    (h : (rounds M k A).Nonempty) →
      i ∈ rounds M k A \ rounds M (k + 1) A →
      i ∈ (ttcRound M (rounds M k A) h).1 ∧
        (ttcIter M ((k + 1) + m) A x).2 i =
          (ttcRound M (rounds M k A) h).2 i := by
  induction k generalizing m A x with
  | zero =>
      intro h hmem
      have hfuel : (0 + 1) + m = (0 + m) + 1 := by omega
      rw [hfuel]
      by_cases h_prime : A.Nonempty
      · have hr1 : rounds M (0 + 1) A = A \ (ttcRound M A h_prime).1 := by
          rw [rounds_succ M 0 A h_prime, rounds.eq_1]
        have hr0 : rounds M 0 A = A := rfl
        rw [hr0, hr1] at hmem
        obtain ⟨hiA, hnot⟩ := Finset.mem_sdiff.mp hmem
        have hiC : i ∈ (ttcRound M A h_prime).1 := by
          by_contra hc
          exact hnot (Finset.mem_sdiff.mpr ⟨hiA, hc⟩)
        constructor
        · change i ∈ (ttcRound M A h).1
          exact hiC
        · rw [ttcIter_step_snd M (0 + m) A x h_prime,
            iter_preserves M (0 + m) _ _ i hnot]
          change (if i ∈ (ttcRound M A h_prime).1 then
            (ttcRound M A h_prime).2 i else x i) = (ttcRound M A h).2 i
          rw [ite_eq_left hiC]
      · exact (h_prime h).elim
  | succ k ih =>
      intro h hmem
      have hfuel : ((k + 1) + 1) + m = ((k + 1) + m) + 1 := by omega
      rw [hfuel]
      by_cases h_prime : A.Nonempty
      · rw [rounds_succ M k A h_prime, rounds_succ M (k + 1) A h_prime] at hmem
        have h2 : (rounds M k (A \ (ttcRound M A h_prime).1)).Nonempty :=
          ⟨_, (Finset.mem_sdiff.mp hmem).1⟩
        have ih_prime := ih m (A \ (ttcRound M A h_prime).1)
          (fun j => if j ∈ (ttcRound M A h_prime).1 then
            (ttcRound M A h_prime).2 j else x j) h2 hmem
        constructor
        · have hset : rounds M (k + 1) A =
              rounds M k (A \ (ttcRound M A h_prime).1) :=
            rounds_succ M k A h_prime
          have heqC : (ttcRound M (rounds M k (A \ (ttcRound M A h_prime).1)) h2).1 =
              (ttcRound M (rounds M (k + 1) A) h).1 :=
            ttcRound_fst_congr M hset.symm h2 h
          rw [← heqC]
          exact ih_prime.1
        · calc
            (ttcIter M (((k + 1) + m) + 1) A x).2 i =
                (ttcIter M ((k + 1) + m) (A \ (ttcRound M A h_prime).1)
                  (fun j => if j ∈ (ttcRound M A h_prime).1 then
                    (ttcRound M A h_prime).2 j else x j)).2 i := by
                      rw [ttcIter_step_snd M ((k + 1) + m) A x h_prime]
            _ = (ttcRound M (rounds M k (A \ (ttcRound M A h_prime).1)) h2).2 i :=
              ih_prime.2
            _ = (ttcRound M (rounds M (k + 1) A) h).2 i := by
              have hset : rounds M (k + 1) A =
                  rounds M k (A \ (ttcRound M A h_prime).1) :=
                rounds_succ M k A h_prime
              exact ttcRound_snd_congr M hset.symm h2 h i
      · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_prime
        have hr : rounds M (k + 1) A = ∅ := by
          rw [hA]
          exact rounds_empty M (k + 1)
        have hiempty : i ∈ (∅ : Finset (Fin n)) := by
          have hi := (Finset.mem_sdiff.mp hmem).1
          rwa [hr] at hi
        exact (Finset.notMem_empty i hiempty).elim

/-- No coalition can strictly improve every member using its own endowed houses. -/
public theorem ttcInCore {n : Nat} (M : HousingMarket n) :
    Core M (ttcAllocation M) := by
  classical
  rw [Core_unfold]
  intro h
  obtain ⟨S, y, hSne, hBij, hAll⟩ := h
  have hempty : rounds M n Finset.univ = ∅ := by
    rw [← ttcIter_fst_eq_rounds M n Finset.univ id]
    exact iter_empties M n _ _ (by rw [Finset.card_univ, Fintype.card_fin])
  have hexk2 : ∃ k, k < n ∧
      ((rounds M k Finset.univ \ rounds M (k + 1) Finset.univ) ∩ S).Nonempty := by
    obtain ⟨i₀, hi₀S⟩ := hSne
    obtain ⟨k, hkk, hkmem⟩ := mem_diff_exists M i₀ (Finset.mem_univ i₀)
      (by rw [Finset.card_univ, Fintype.card_fin])
    exact ⟨k, hkk, ⟨_, Finset.mem_inter.mpr ⟨hkmem, hi₀S⟩⟩⟩
  let kstar := Nat.find hexk2
  have hspec : kstar < n ∧
      ((rounds M kstar Finset.univ \ rounds M (kstar + 1) Finset.univ) ∩ S).Nonempty :=
    Nat.find_spec hexk2
  obtain ⟨hkstar_lt, hkstar_ne⟩ := hspec
  obtain ⟨i, hi⟩ := hkstar_ne
  obtain ⟨hikmem, hiS⟩ := Finset.mem_inter.mp hi
  have hstar : (rounds M kstar Finset.univ).Nonempty :=
    ⟨_, (Finset.mem_sdiff.mp hikmem).1⟩
  have hsub : S ⊆ rounds M kstar Finset.univ := by
    intro j hjS
    by_contra hjnot
    have hexj : ∃ k, j ∉ rounds M k Finset.univ := ⟨n, by
      rw [hempty]
      exact Finset.notMem_empty j⟩
    let kj := Nat.find hexj
    have hspecj : j ∉ rounds M kj Finset.univ := Nat.find_spec hexj
    have hkj_le : kj ≤ kstar := Nat.find_min' hexj hjnot
    have hkj_pos : 0 < kj := by
      rcases Nat.eq_zero_or_pos kj with h0 | hpos
      · exfalso
        rw [h0] at hspecj
        exact hspecj (Finset.mem_univ j)
      · exact hpos
    obtain ⟨k_prime, hk_prime⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hkj_pos)
    have h1 : j ∈ rounds M k_prime Finset.univ := by
      by_contra hcon
      have hle2 : kj ≤ k_prime := Nat.find_min' hexj hcon
      omega
    have h2 : j ∉ rounds M (k_prime + 1) Finset.univ := by
      show j ∉ rounds M k_prime.succ Finset.univ
      rw [← hk_prime]
      exact hspecj
    have hmem_prime : j ∈
        rounds M k_prime Finset.univ \ rounds M (k_prime + 1) Finset.univ :=
      Finset.mem_sdiff.mpr ⟨h1, h2⟩
    have hlt : k_prime < kstar := by omega
    have hq :
        ((rounds M k_prime Finset.univ \ rounds M (k_prime + 1) Finset.univ) ∩ S).Nonempty :=
      ⟨_, Finset.mem_inter.mpr ⟨hmem_prime, hjS⟩⟩
    have hle3 : kstar ≤ k_prime := Nat.find_min' hexk2 ⟨by omega, hq⟩
    omega
  have hyi : y i ∈ (rounds M kstar Finset.univ).image ⇑M.endow := by
    have h1 : y i ∈ M.endow '' ↑S := hBij.1 (Finset.mem_coe.mpr hiS)
    have h2 : M.endow '' ↑S ⊆ M.endow '' ↑(rounds M kstar Finset.univ) :=
      Set.image_mono (Finset.coe_subset.mpr hsub)
    have h3 := h2 h1
    rwa [← Finset.coe_image, Finset.mem_coe] at h3
  have hassign := assign_of_mem_diff M kstar (n - kstar - 1) Finset.univ id i hstar hikmem
  have hfuel : (kstar + 1) + (n - kstar - 1) = n := by omega
  rw [hfuel] at hassign
  have hbest := ttcRound_assign_best M hstar hassign.1 hyi
  have hlt := hAll i hiS
  rw [prefLT_unfold] at hlt
  have heq : ttcAllocation M i = (ttcIter M n Finset.univ id).2 i :=
    ttcAllocation_apply M i
  rw [heq] at hlt
  rw [← hassign.2] at hbest
  omega

-- Monotonicity across arbitrarily many rounds.
private theorem rounds_subset_of_le {n : Nat} (M : HousingMarket n)
    (A : Finset (Fin n)) {k l : Nat} (hkl : k ≤ l) :
    rounds M l A ⊆ rounds M k A := by
  induction l, hkl using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ l _ ih => exact Finset.Subset.trans (rounds_subset M l A) ih

-- Express the next round using the agents currently remaining.
private theorem rounds_next {n : Nat} (M : HousingMarket n) (k : Nat)
    (A : Finset (Fin n)) (h : (rounds M k A).Nonempty) :
    rounds M (k + 1) A = rounds M k A \ (ttcRound M (rounds M k A) h).1 := by
  induction k generalizing A with
  | zero => exact rounds_succ M 0 A h
  | succ k ih =>
      have hA : A.Nonempty := by
        obtain ⟨i, hi⟩ := h
        exact ⟨i, rounds_subset_of_le M A (Nat.zero_le _) hi⟩
      have hs := rounds_succ M k A hA
      have h2 : (rounds M k (A \ (ttcRound M A hA).1)).Nonempty := hs ▸ h
      calc
        _ = rounds M (k + 1) (A \ (ttcRound M A hA).1) :=
          rounds_succ M (k + 1) A hA
        _ = rounds M k (A \ (ttcRound M A hA).1) \
            (ttcRound M (rounds M k (A \ (ttcRound M A hA).1)) h2).1 := ih _ h2
        _ = _ := congrArg₂ (fun B C : Finset (Fin n) => B \ C) hs.symm
          (ttcRound_fst_congr M hs.symm h2 h)

private theorem allocation_eq_round {n : Nat} (M : HousingMarket n)
    (k : Nat) (hk : k < n) (h : (rounds M k Finset.univ).Nonempty)
    {c : Fin n} (hc : c ∈ (ttcRound M (rounds M k Finset.univ) h).1) :
    ttcAllocation M c = (ttcRound M (rounds M k Finset.univ) h).2 c := by
  have hmem : c ∈ rounds M k Finset.univ \ rounds M (k + 1) Finset.univ := by
    rw [rounds_next M k Finset.univ h]
    exact Finset.mem_sdiff.mpr ⟨ttcRound_sub M h hc, by
      intro hm
      exact (Finset.mem_sdiff.mp hm).2 hc⟩
  have ha := (assign_of_mem_diff M k (n - k - 1) Finset.univ id c h hmem).2
  have hfuel : (k + 1) + (n - k - 1) = n := by omega
  rw [hfuel] at ha
  exact (ttcAllocation_apply M c).trans ha

-- Every completed round permutes exactly the endowed houses of its agents.
private theorem removed_image_eq {n : Nat} (M : HousingMarket n) (k : Nat)
    (hk : k ≤ n) :
    (Finset.univ \ rounds M k Finset.univ).image (ttcAllocation M) =
      (Finset.univ \ rounds M k Finset.univ).image (⇑M.endow) := by
  classical
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
      have hklt : k < n := by omega
      have ih := ih (by omega)
      by_cases h : (rounds M k Finset.univ).Nonempty
      · have hsplit : Finset.univ \ rounds M (k + 1) Finset.univ =
            (Finset.univ \ rounds M k Finset.univ) ∪
              (ttcRound M (rounds M k Finset.univ) h).1 := by
          rw [rounds_next M k Finset.univ h]
          ext c
          have hsub := ttcRound_sub M h (x := c)
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
          tauto
        have hcycle : (ttcRound M (rounds M k Finset.univ) h).1.image
              (ttcAllocation M) =
            (ttcRound M (rounds M k Finset.univ) h).1.image (⇑M.endow) := by
          calc
            _ = (ttcRound M (rounds M k Finset.univ) h).1.image
                (ttcRound M (rounds M k Finset.univ) h).2 :=
              Finset.image_congr (fun c hc => allocation_eq_round M k hklt h hc)
            _ = _ := ttcRound_image_eq M h
        rw [hsplit, Finset.image_union, Finset.image_union, ih, hcycle]
      · have he : rounds M k Finset.univ = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp h
        have he1 : rounds M (k + 1) Finset.univ = ∅ :=
          Finset.eq_empty_iff_forall_notMem.mpr (fun c hc => by
            have hc0 := rounds_subset M k Finset.univ hc
            rw [he] at hc0
            exact Finset.notMem_empty c hc0)
        simpa only [he, he1] using ih

/-- Every bijective strict-core allocation equals the TTC allocation. -/
public theorem ttcUniqueStrictCore {n : Nat} (M : HousingMarket n) (x : Fin n → Fin n)
    (hxb : Function.Bijective x) (hx : StrictCore M x) :
    x = ttcAllocation M := by
  classical
  by_contra hne
  let D := Finset.univ.filter (fun i => x i ≠ ttcAllocation M i)
  have hD : D.Nonempty := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hex : ∃ k, k < n ∧
      ((rounds M k Finset.univ \ rounds M (k + 1) Finset.univ) ∩ D).Nonempty := by
    obtain ⟨i, hiD⟩ := hD
    obtain ⟨k, hk, hi⟩ := mem_diff_exists M i (Finset.mem_univ i)
      (by rw [Finset.card_univ, Fintype.card_fin])
    exact ⟨k, hk, i, Finset.mem_inter.mpr ⟨hi, hiD⟩⟩
  let kstar := Nat.find hex
  obtain ⟨hkstar, i, hi⟩ := Nat.find_spec hex
  obtain ⟨himem, hiD⟩ := Finset.mem_inter.mp hi
  have hR : (rounds M kstar Finset.univ).Nonempty :=
    ⟨i, (Finset.mem_sdiff.mp himem).1⟩
  have hagree : ∀ j, j ∉ rounds M kstar Finset.univ →
      x j = ttcAllocation M j := by
    intro j hj
    by_contra hdiff
    obtain ⟨k, hk, hjmem⟩ := mem_diff_exists M j (Finset.mem_univ j)
      (by rw [Finset.card_univ, Fintype.card_fin])
    have hklt : k < kstar := by
      by_contra h
      exact hj (rounds_subset_of_le M Finset.univ (by omega)
        (Finset.mem_sdiff.mp hjmem).1)
    have hmin : kstar ≤ k := Nat.find_min' hex ⟨hk, j,
      Finset.mem_inter.mpr ⟨hjmem, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hdiff⟩⟩⟩
    omega
  have hremaining : ∀ c ∈ rounds M kstar Finset.univ,
      x c ∈ (rounds M kstar Finset.univ).image (⇑M.endow) := by
    intro c hc
    by_contra hnot
    obtain ⟨j, hj⟩ := M.endow.surjective (x c)
    have hjnot : j ∉ rounds M kstar Finset.univ := by
      intro hjmem
      exact hnot (Finset.mem_image.mpr ⟨j, hjmem, hj⟩)
    have hout : x c ∈ (Finset.univ \ rounds M kstar Finset.univ).image
        (⇑M.endow) :=
      Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjnot⟩, hj⟩
    rw [← removed_image_eq M kstar (Nat.le_of_lt hkstar)] at hout
    obtain ⟨j2, hj2, heq⟩ := Finset.mem_image.mp hout
    have hj2not := (Finset.mem_sdiff.mp hj2).2
    have hcj : c = j2 := hxb.1 (by rw [hagree j2 hj2not]; exact heq.symm)
    exact hj2not (hcj ▸ hc)
  let C := (ttcRound M (rounds M kstar Finset.univ) hR).1
  have hiC : i ∈ C :=
    (assign_of_mem_diff M kstar (n - kstar - 1) Finset.univ id i hR himem).1
  have heq : ∀ c ∈ C, ttcAllocation M c =
      (ttcRound M (rounds M kstar Finset.univ) hR).2 c :=
    fun c hc => allocation_eq_round M kstar hkstar hR hc
  have himage : C.image (ttcAllocation M) = C.image (⇑M.endow) := by
    calc
      _ = C.image (ttcRound M (rounds M kstar Finset.univ) hR).2 :=
        Finset.image_congr heq
      _ = _ := ttcRound_image_eq M hR
  have hBij : Set.BijOn (ttcAllocation M) (↑C) (M.endow '' ↑C) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      have hh : ttcAllocation M c ∈ C.image (⇑M.endow) := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
      rwa [Finset.mem_image] at hh
    · intro c hc d hd hcd
      apply ttcRound_assign_inj M hR hc hd
      rw [← heq c hc, ← heq d hd]
      exact hcd
    · intro house hh
      have hhfin : house ∈ C.image (⇑M.endow) := by
        rwa [← Finset.coe_image, Finset.mem_coe] at hh
      rw [← himage] at hhfin
      exact Finset.mem_image.mp hhfin
  have hweak : ∀ c ∈ C, prefLE M c (ttcAllocation M c) (x c) := by
    intro c hc
    have hbest := ttcRound_assign_best M hR hc
      (hremaining c (ttcRound_sub M hR hc))
    rw [← heq c hc] at hbest
    exact (prefLE_unfold M c _ _).mpr hbest
  have hstrict : prefLT M i (ttcAllocation M i) (x i) := by
    rw [prefLT_unfold]
    have hle := hweak i hiC
    rw [prefLE_unfold] at hle
    have hdiff : x i ≠ ttcAllocation M i := (Finset.mem_filter.mp hiD).2
    have hne_rank : (M.rank i).symm (ttcAllocation M i) ≠ (M.rank i).symm (x i) :=
      fun h => hdiff ((M.rank i).symm.injective h).symm
    exact lt_of_le_of_ne hle hne_rank
  exact (StrictCore_unfold M x).mp hx
    ⟨C, ttcAllocation M, ttcRound_nonempty M hR, hBij, hweak, i, hiC, hstrict⟩

end TTC
