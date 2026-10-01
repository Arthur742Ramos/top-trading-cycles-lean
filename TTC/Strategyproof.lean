module

public import TTC.Core
public import TTC.Termination

namespace TTC

open scoped Classical

/-- A house strictly preferred to an agent's TTC assignment has already left
when that agent exits. Houses leave with their endowed owners. -/
public theorem ttc_preferred_house_removed {n : Nat} (M : HousingMarket n)
    (i h : Fin n) (k : Nat) (hk : k < n)
    (hi : i ∈ rounds M k Finset.univ \ rounds M (k + 1) Finset.univ)
    (hbetter : prefLT M i h (ttcAllocation M i)) :
    ∃ l, l < k ∧ M.endow.symm h ∈
      rounds M l Finset.univ \ rounds M (l + 1) Finset.univ := by
  have hR : (rounds M k Finset.univ).Nonempty :=
    ⟨i, (Finset.mem_sdiff.mp hi).1⟩
  have hiC := (assign_of_mem_diff M k (n - k - 1) Finset.univ id i hR hi).1
  have hnot : M.endow.symm h ∉ rounds M k Finset.univ := by
    intro hh
    have hbest := ttcRound_assign_best M hR hiC
      (Finset.mem_image.mpr ⟨M.endow.symm h, hh, M.endow.apply_symm_apply h⟩)
    rw [← allocation_eq_round M k hk hR hiC] at hbest
    have hlt := (prefLT_unfold M i _ _).mp hbetter
    exact (not_lt_of_ge hbest) hlt
  obtain ⟨l, hl, hmem⟩ := mem_diff_exists M (M.endow.symm h) (fuel := n)
    (Finset.mem_univ _) (by simp)
  refine ⟨l, ?_, hmem⟩
  by_contra hle
  exact hnot (rounds_subset_of_le M Finset.univ (by omega)
    (Finset.mem_sdiff.mp hmem).1)

-- Induction over the actual cycle deletions. A weakly blocking coalition
-- that meets a cycle must contain the whole cycle, and agree with all its
-- assignments. Delete that cycle from the coalition and continue.
private theorem iter_no_weak_block {n : Nat} (M : HousingMarket n) (fuel : Nat) :
    ∀ (A : Finset (Fin n)) (x : Fin n → Fin n) (S : Finset (Fin n))
      (y : Fin n → Fin n), A.card ≤ fuel → S ⊆ A →
      Set.BijOn y (↑S) (M.endow '' ↑S) →
      (∀ c ∈ S, prefLE M c (y c) ((ttcIter M fuel A x).2 c)) →
      (∃ c ∈ S, prefLT M c (y c) ((ttcIter M fuel A x).2 c)) → False := by
  induction fuel with
  | zero =>
      intro A x S y hcard hSA hbij hweak hstrict
      have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      obtain ⟨c, hc, _⟩ := hstrict
      have hcA := hSA hc
      rw [hA] at hcA
      exact Finset.notMem_empty c hcA
  | succ fuel ih =>
      intro A x S y hcard hSA hbij hweak hstrict
      obtain ⟨j, hjS, hjstrict⟩ := hstrict
      have hA : A.Nonempty := ⟨j, hSA hjS⟩
      let C := (ttcRound M A hA).1
      let asgn := (ttcRound M A hA).2
      let z := fun c => if c ∈ C then asgn c else x c
      have hstep : ttcIter M (fuel + 1) A x = ttcIter M fuel (A \ C) z := by
        rw [ttcIter_succ, dite_eq_left hA]
      rw [hstep] at hweak hjstrict
      have hassign : ∀ c ∈ C, (ttcIter M fuel (A \ C) z).2 c = asgn c := by
        intro c hc
        rw [ttcIter_preserves M fuel (A \ C) z c (by
          intro hm; exact (Finset.mem_sdiff.mp hm).2 hc)]
        exact ite_eq_left hc
      have hequal : ∀ c ∈ C, c ∈ S → y c = asgn c := by
        intro c hcC hcS
        have hy : y c ∈ A.image M.endow := by
          obtain ⟨d, hdS, hd⟩ := hbij.1 hcS
          exact Finset.mem_image.mpr ⟨d, hSA hdS, hd⟩
        have hbest := ttcRound_assign_best M hA hcC hy
        have hw := (prefLE_unfold M c _ _).mp (hweak c hcS)
        rw [hassign c hcC] at hw
        exact (M.rank c).symm.injective (le_antisymm hw hbest)
      have hclosed : ∀ c ∈ C, c ∈ S → M.endow.symm (asgn c) ∈ S := by
        intro c hcC hcS
        obtain ⟨d, hdS, hd⟩ := hbij.1 hcS
        rw [hequal c hcC hcS] at hd
        rw [← hd, Equiv.symm_apply_apply]
        exact hdS
      have hwhole : ∀ c ∈ C, c ∈ S → C ⊆ S := by
        intro c hcC hcS
        exact ttcRound_subset_of_closed M hA S ⟨c, hcC, hcS⟩ hclosed
      have himage : C.image asgn = C.image (⇑M.endow) := ttcRound_image_eq M hA
      have hbij2 : Set.BijOn y (↑(S \ C)) (M.endow '' ↑(S \ C)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          obtain ⟨hcS, hcC⟩ := Finset.mem_sdiff.mp hc
          obtain ⟨d, hdS, hd⟩ := hbij.1 hcS
          refine ⟨d, Finset.mem_sdiff.mpr ⟨hdS, ?_⟩, hd⟩
          intro hdC
          have hdimg : y c ∈ C.image (⇑M.endow) :=
            Finset.mem_image.mpr ⟨d, hdC, hd⟩
          rw [← himage] at hdimg
          obtain ⟨c2, hc2C, hc2⟩ := Finset.mem_image.mp hdimg
          have hc2S := hwhole d hdC hdS hc2C
          have hc2eq : y c2 = y c := (hequal c2 hc2C hc2S).trans hc2
          have hcc : c2 = c := hbij.2.1 hc2S hcS hc2eq
          exact hcC (hcc ▸ hc2C)
        · intro c hc d hd heq
          exact hbij.2.1 (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hd).1 heq
        · intro house hh
          obtain ⟨d, hd, rfl⟩ := hh
          obtain ⟨hdS, hdC⟩ := Finset.mem_sdiff.mp hd
          obtain ⟨c, hcS, hc⟩ := hbij.2.2 ⟨d, hdS, rfl⟩
          refine ⟨c, Finset.mem_sdiff.mpr ⟨hcS, ?_⟩, hc⟩
          intro hcC
          have hmem : M.endow d ∈ C.image asgn :=
            Finset.mem_image.mpr ⟨c, hcC, (hequal c hcC hcS).symm.trans hc⟩
          rw [himage] at hmem
          obtain ⟨d2, hd2, he⟩ := Finset.mem_image.mp hmem
          exact hdC (M.endow.injective he ▸ hd2)
      have hjC : j ∉ C := by
        intro hj
        rw [hassign j hj, hequal j hj hjS, prefLT_unfold] at hjstrict
        exact (lt_irrefl _) hjstrict
      apply ih (A \ C) z (S \ C) y
      · have hlt := ttcRound_card_lt M hA
        change (A \ C).card < A.card at hlt
        omega
      · intro c hc
        exact Finset.mem_sdiff.mpr ⟨hSA (Finset.mem_sdiff.mp hc).1,
          (Finset.mem_sdiff.mp hc).2⟩
      · exact hbij2
      · intro c hc
        exact hweak c (Finset.mem_sdiff.mp hc).1
      · exact ⟨j, Finset.mem_sdiff.mpr ⟨hjS, hjC⟩, hjstrict⟩

/-- No coalition can weakly improve every member, with one strict improvement,
using its own endowed houses. -/
public theorem ttcInStrictCore {n : Nat} (M : HousingMarket n) :
    StrictCore M (ttcAllocation M) := by
  rw [StrictCore_unfold]
  rintro ⟨S, y, _, hbij, hweak, hstrict⟩
  simp only [ttcAllocation_apply] at hweak hstrict
  exact iter_no_weak_block M n Finset.univ id S y (by simp)
    (Finset.subset_univ S) hbij hweak hstrict

/-- Truthful reporting weakly dominates every unilateral misreport. The proof
uses the first truthful cycle where the allocations differ: earlier agreement
keeps the alternative allocation inside the remaining endowed houses. A
profitable deviator cannot lie in that cycle, so the cycle would weakly block
its reported-profile TTC allocation, contradicting strict-core membership. -/
public theorem ttcStrategyproof (n : Nat) (w : Fin n ≃ Fin n) :
    Strategyproof n w := by
  rw [Strategyproof_unfold]
  intro r i rNew
  let M := HousingMarket.mk w r
  let Mnew := HousingMarket.mk w (Function.update r i rNew)
  change prefLE M i (ttcAllocation M i) (ttcAllocation Mnew i)
  rw [prefLE_unfold]
  by_contra h
  have hgain : (M.rank i).symm (ttcAllocation Mnew i) <
      (M.rank i).symm (ttcAllocation M i) := lt_of_not_ge h
  let y := ttcAllocation Mnew
  have hyb : Function.Bijective y := ttcAllocation_bijective Mnew
  have hycore : StrictCore Mnew y := ttcInStrictCore Mnew
  let D := Finset.univ.filter (fun c => y c ≠ ttcAllocation M c)
  have hiD : i ∈ D := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    intro heq
    change (M.rank i).symm (y i) < (M.rank i).symm (ttcAllocation M i) at hgain
    rw [heq] at hgain
    exact (lt_irrefl _) hgain
  have hex : ∃ k, k < n ∧
      ((rounds M k Finset.univ \ rounds M (k + 1) Finset.univ) ∩ D).Nonempty := by
    obtain ⟨k, hk, hi⟩ := mem_diff_exists M i (Finset.mem_univ i)
      (fuel := n) (by simp)
    exact ⟨k, hk, i, Finset.mem_inter.mpr ⟨hi, hiD⟩⟩
  let kstar := Nat.find hex
  obtain ⟨hkstar, c, hc⟩ := Nat.find_spec hex
  obtain ⟨hcmem, hcD⟩ := Finset.mem_inter.mp hc
  have hR : (rounds M kstar Finset.univ).Nonempty :=
    ⟨c, (Finset.mem_sdiff.mp hcmem).1⟩
  have hagree : ∀ d, d ∉ rounds M kstar Finset.univ →
      y d = ttcAllocation M d := by
    intro d hd
    by_contra hdiff
    obtain ⟨k, hk, hdmem⟩ := mem_diff_exists M d (Finset.mem_univ d)
      (fuel := n) (by simp)
    have hklt : k < kstar := by
      by_contra hle
      exact hd (rounds_subset_of_le M Finset.univ (by omega)
        (Finset.mem_sdiff.mp hdmem).1)
    have hmin : kstar ≤ k := Nat.find_min' hex ⟨hk, d,
      Finset.mem_inter.mpr ⟨hdmem, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hdiff⟩⟩⟩
    omega
  have hremaining : ∀ d ∈ rounds M kstar Finset.univ,
      y d ∈ (rounds M kstar Finset.univ).image (⇑M.endow) := by
    intro d hd
    by_contra hnot
    obtain ⟨owner, howner⟩ := M.endow.surjective (y d)
    have houtside : owner ∉ rounds M kstar Finset.univ := by
      intro hmem
      exact hnot (Finset.mem_image.mpr ⟨owner, hmem, howner⟩)
    have hout : y d ∈ (Finset.univ \ rounds M kstar Finset.univ).image
        (⇑M.endow) := Finset.mem_image.mpr
      ⟨owner, Finset.mem_sdiff.mpr ⟨Finset.mem_univ owner, houtside⟩, howner⟩
    rw [← removed_image_eq M kstar (Nat.le_of_lt hkstar)] at hout
    obtain ⟨d2, hd2, heq⟩ := Finset.mem_image.mp hout
    have hd2not := (Finset.mem_sdiff.mp hd2).2
    have hdd2 : d = d2 := hyb.1 (by rw [hagree d2 hd2not]; exact heq.symm)
    exact hd2not (hdd2 ▸ hd)
  let C := (ttcRound M (rounds M kstar Finset.univ) hR).1
  have hcC : c ∈ C :=
    (assign_of_mem_diff M kstar (n - kstar - 1) Finset.univ id c hR hcmem).1
  have heq : ∀ d ∈ C, ttcAllocation M d =
      (ttcRound M (rounds M kstar Finset.univ) hR).2 d :=
    fun d hd => allocation_eq_round M kstar hkstar hR hd
  have hbest : ∀ d ∈ C, (M.rank d).symm (ttcAllocation M d) ≤
      (M.rank d).symm (y d) := by
    intro d hd
    rw [heq d hd]
    exact ttcRound_assign_best M hR hd (hremaining d (ttcRound_sub M hR hd))
  have hne : ∀ d ∈ C, d ≠ i := by
    intro d hd hdi
    subst d
    exact (not_lt_of_ge (hbest i hd)) hgain
  have hrank : ∀ d, d ≠ i → Mnew.rank d = M.rank d := by
    intro d hd
    exact Function.update_of_ne hd rNew r
  have himage : C.image (ttcAllocation M) = C.image (⇑Mnew.endow) := by
    calc
      _ = C.image (ttcRound M (rounds M kstar Finset.univ) hR).2 :=
        Finset.image_congr heq
      _ = C.image (⇑M.endow) := ttcRound_image_eq M hR
      _ = _ := rfl
  have hBij : Set.BijOn (ttcAllocation M) (↑C) (Mnew.endow '' ↑C) := by
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      have hh : ttcAllocation M d ∈ C.image (⇑Mnew.endow) := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
      rwa [Finset.mem_image] at hh
    · intro d hd e he hde
      apply ttcRound_assign_inj M hR hd he
      rw [← heq d hd, ← heq e he]
      exact hde
    · intro house hh
      have hhfin : house ∈ C.image (⇑Mnew.endow) := by
        rwa [← Finset.coe_image, Finset.mem_coe] at hh
      rw [← himage] at hhfin
      exact Finset.mem_image.mp hhfin
  have hweak : ∀ d ∈ C, prefLE Mnew d (ttcAllocation M d) (y d) := by
    intro d hd
    rw [prefLE_unfold, hrank d (hne d hd)]
    exact hbest d hd
  have hstrict : prefLT Mnew c (ttcAllocation M c) (y c) := by
    rw [prefLT_unfold, hrank c (hne c hcC)]
    have hdiff : y c ≠ ttcAllocation M c := (Finset.mem_filter.mp hcD).2
    have hneq : (M.rank c).symm (ttcAllocation M c) ≠ (M.rank c).symm (y c) :=
      fun he => hdiff ((M.rank c).symm.injective he).symm
    exact lt_of_le_of_ne (hbest c hcC) hneq
  exact (StrictCore_unfold Mnew y).mp hycore
    ⟨C, ttcAllocation M, ttcRound_nonempty M hR, hBij, hweak, c, hcC, hstrict⟩

end TTC
