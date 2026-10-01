module

public import TTC.Defs
public import TTC.Algorithm

namespace TTC

open scoped Classical

private theorem ttcIter_step {n : Nat} (M : HousingMarket n) :
    ∀ (fuel : Nat) (A : Finset (Fin n)) (x : Fin n → Fin n) (h : A.Nonempty),
      ttcIter M (fuel + 1) A x =
        ttcIter M fuel (A \ (ttcRound M A h).1)
          (fun i => if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i) := by
  intro fuel A x h
  rw [ttcIter_succ M fuel A x, dite_eq_left h]

public theorem ttcIter_empties {n : Nat} (M : HousingMarket n) :
    ∀ (fuel : Nat) (A : Finset (Fin n)) (x : Fin n → Fin n),
      A.card ≤ fuel → (ttcIter M fuel A x).1 = ∅ := by
  intro fuel
  induction fuel with
  | zero =>
      intro A x hle
      have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [ttcIter_zero]
      exact hA
  | succ fuel ih =>
      intro A x hle
      by_cases h : A.Nonempty
      · rw [ttcIter_step M fuel A x h]
        exact ih _ _ (by
          have hlt := ttcRound_card_lt M h
          omega)
      · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        rw [ttcIter_succ M fuel A x, dite_eq_right h, hA]

public theorem ttcIter_univ_empty {n : Nat} (M : HousingMarket n) :
    (ttcIter M n Finset.univ id).1 = ∅ :=
  ttcIter_empties M n _ _ (by rw [Finset.card_univ, Fintype.card_fin])

public theorem ttcIter_preserves {n : Nat} (M : HousingMarket n) :
    ∀ (fuel : Nat) (A : Finset (Fin n)) (x : Fin n → Fin n) (i : Fin n),
      i ∉ A → (ttcIter M fuel A x).2 i = x i := by
  intro fuel
  induction fuel with
  | zero =>
      intro A x i hi
      rw [ttcIter_zero]
  | succ fuel ih =>
      intro A x i hi
      by_cases h : A.Nonempty
      · have hiC : i ∉ (ttcRound M A h).1 :=
          fun hc => hi (ttcRound_sub M h hc)
        have hiA : i ∉ A \ (ttcRound M A h).1 := by
          simp [Finset.mem_sdiff, hi]
        rw [ttcIter_step M fuel A x h, ih _ _ _ hiA]
        show (if i ∈ (ttcRound M A h).1 then (ttcRound M A h).2 i else x i) = x i
        rw [ite_eq_right hiC]
      · rw [ttcIter_succ M fuel A x, dite_eq_right h]

public theorem ttcIter_inj {n : Nat} (M : HousingMarket n) :
    ∀ (fuel : Nat) (A : Finset (Fin n)) (x : Fin n → Fin n),
      Set.InjOn x ↑(Finset.univ \ A) →
      Disjoint (x '' ↑(Finset.univ \ A)) (M.endow '' ↑A) →
      Set.InjOn (ttcIter M fuel A x).2
        ↑(Finset.univ \ (ttcIter M fuel A x).1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro A x hinj hdisj
      rw [ttcIter_zero]
      exact hinj
  | succ fuel ih =>
      intro A x hinj hdisj
      by_cases h : A.Nonempty
      · set C := (ttcRound M A h).1 with hCdef
        set as := (ttcRound M A h).2 with hasdef
        have hsub : C ⊆ A := by
          simpa only [hCdef] using ttcRound_sub M h
        have hinjC : Set.InjOn as ↑C := by
          simpa only [hCdef, hasdef] using ttcRound_assign_inj M h
        have himg : C.image as = C.image (⇑M.endow) := by
          simpa only [hCdef, hasdef] using ttcRound_image_eq M h
        have has_mem (i : Fin n) (hi : i ∈ C) :
            as i ∈ M.endow '' (C : Set (Fin n)) := by
          have hm : as i ∈ C.image as :=
            Finset.mem_image.mpr ⟨i, hi, rfl⟩
          rw [himg] at hm
          obtain ⟨d, hdC, hdeq⟩ := Finset.mem_image.mp hm
          exact ⟨d, Finset.mem_coe.mpr hdC, hdeq⟩
        have has_mem_A (i : Fin n) (hi : i ∈ C) :
            as i ∈ M.endow '' (A : Set (Fin n)) :=
          (Set.image_mono (Finset.coe_subset.mpr hsub)) (has_mem i hi)
        have hunion : (↑(Finset.univ \ (A \ C)) : Set (Fin n)) =
            ↑(Finset.univ \ A) ∪ ↑C := by
          ext i
          simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_sdiff,
            Set.mem_univ, true_and, Set.mem_union, Finset.mem_coe]
          tauto
        have hInj : Set.InjOn (fun i => if i ∈ C then as i else x i)
            (↑(Finset.univ \ A) ∪ ↑C) := by
          intro i hi j hj heq
          by_cases hiC : i ∈ C <;> by_cases hjC : j ∈ C
          · simp only [hiC, hjC, ite_true] at heq
            exact hinjC (Finset.mem_coe.mpr hiC) (Finset.mem_coe.mpr hjC) heq
          · simp only [hiC, hjC, ite_true, ite_false] at heq
            have hjA : j ∈ (↑(Finset.univ \ A) : Set (Fin n)) :=
              ((Set.mem_union _ _ _).mp hj).resolve_right
                (fun hc => hjC (Finset.mem_coe.mp hc))
            have hxj : x j ∈ x '' (↑(Finset.univ \ A) : Set (Fin n)) :=
              ⟨j, hjA, rfl⟩
            have hasi : as i ∈ M.endow '' (A : Set (Fin n)) := has_mem_A i hiC
            have hxjA : x j ∈ M.endow '' (A : Set (Fin n)) := heq ▸ hasi
            exact False.elim ((Set.disjoint_left.mp hdisj hxj) hxjA)
          · simp only [hiC, hjC, ite_true, ite_false] at heq
            have hiA : i ∈ (↑(Finset.univ \ A) : Set (Fin n)) :=
              ((Set.mem_union _ _ _).mp hi).resolve_right
                (fun hc => hiC (Finset.mem_coe.mp hc))
            have hxi : x i ∈ x '' (↑(Finset.univ \ A) : Set (Fin n)) :=
              ⟨i, hiA, rfl⟩
            have hasj : as j ∈ M.endow '' (A : Set (Fin n)) := has_mem_A j hjC
            have hxiA : x i ∈ M.endow '' (A : Set (Fin n)) := heq.symm ▸ hasj
            exact False.elim ((Set.disjoint_left.mp hdisj hxi) hxiA)
          · simp only [hiC, hjC, ite_false] at heq
            have hiA : i ∈ (↑(Finset.univ \ A) : Set (Fin n)) :=
              ((Set.mem_union _ _ _).mp hi).resolve_right
                (fun hc => hiC (Finset.mem_coe.mp hc))
            have hjA : j ∈ (↑(Finset.univ \ A) : Set (Fin n)) :=
              ((Set.mem_union _ _ _).mp hj).resolve_right
                (fun hc => hjC (Finset.mem_coe.mp hc))
            exact hinj hiA hjA heq
        have hDisj :
            Disjoint ((fun i => if i ∈ C then as i else x i) ''
              (↑(Finset.univ \ A) ∪ ↑C)) (M.endow '' ↑(A \ C)) := by
          rw [Set.image_union, Set.disjoint_union_left]
          constructor
          · have eimg : (fun i => if i ∈ C then as i else x i) ''
                (↑(Finset.univ \ A) : Set (Fin n)) =
                x '' ↑(Finset.univ \ A) := by
              apply Set.image_congr
              intro i hi
              have hiA : i ∉ A := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hi)).2
              have hiC : i ∉ C := fun hc => hiA (hsub hc)
              exact ite_eq_right hiC
            rw [eimg]
            have hrem : (↑(A \ C) : Set (Fin n)) ⊆ ↑A :=
              Finset.coe_subset.mpr Finset.sdiff_subset
            exact Disjoint.mono_right (Set.image_mono hrem) hdisj
          · have eimg2 : (fun i => if i ∈ C then as i else x i) ''
                (C : Set (Fin n)) = as '' ↑C :=
              Set.image_congr (fun i hi => ite_eq_left (Finset.mem_coe.mp hi))
            rw [eimg2, Set.disjoint_left]
            intro y hy1 hy2
            obtain ⟨c, hcC, rfl⟩ := hy1
            obtain ⟨d, hdAC, hdeq⟩ := hy2
            obtain ⟨c', hc'C, hceq⟩ := has_mem c (Finset.mem_coe.mp hcC)
            have hcd : c' = d := M.endow.injective (hceq.trans hdeq.symm)
            have hdC : d ∈ C := by
              rw [← hcd]
              exact Finset.mem_coe.mp hc'C
            exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp hdAC)).2 hdC
        have hstep := ttcIter_step M fuel A x h
        rw [← hCdef, ← hasdef] at hstep
        rw [hstep]
        exact ih (A \ C) (fun i => if i ∈ C then as i else x i)
          (by rw [hunion]; exact hInj) (by rw [hunion]; exact hDisj)
      · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        rw [ttcIter_succ M fuel A x, dite_eq_right h]
        subst hA
        simpa using hinj

public theorem ttcAllocation_bijective {n : Nat} (M : HousingMarket n) :
    Function.Bijective (ttcAllocation M) := by
  have h1 : Set.InjOn id ((((Finset.univ : Finset (Fin n)) \ Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rw [Finset.sdiff_self, Finset.coe_empty]
    exact Set.injOn_empty id
  have h2 : Disjoint (id '' ((((Finset.univ : Finset (Fin n)) \ Finset.univ : Finset (Fin n)) : Set (Fin n))))
      (M.endow '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rw [Finset.sdiff_self, Finset.coe_empty, Set.image_empty]
    exact disjoint_bot_left
  have hinjT := ttcIter_inj M n Finset.univ id h1 h2
  rw [ttcIter_univ_empty M] at hinjT
  rw [Finset.sdiff_empty, Finset.coe_univ] at hinjT
  have hI : Function.Injective (ttcIter M n Finset.univ id).2 :=
    Set.injOn_univ.mp hinjT
  have hI' : Function.Injective (ttcAllocation M) :=
    ttcAllocation_inj_of_iter_inj M hI
  exact Function.Injective.bijective_of_finite hI'

end TTC
