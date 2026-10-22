import LRX.ActualTwoComponentPeakGeometry

namespace LRX.FiniteWindow
open scoped BigOperators
variable {n : ℕ}

theorem window_square_sum_le_total_square (As : List (FillingWindow n)) :
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ ((As.map (fun A => (A.size : ℤ))).sum)^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin As.length => ((As.get i).size : ℤ))
    (fun i _ => Int.natCast_nonneg _)
  rw [sum_window_indices As (fun A => (A.size : ℤ)^2),
    sum_window_indices As (fun A => (A.size : ℤ))] at h
  exact h
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The total size of the actual suffix-window family is precisely v. -/
theorem suffix_component_family_size_sum (p : State n) (L : ℕ) :
    ((suffixComponentFamily p L).map (fun A => A.size)).sum =
      ∑ C ∈ nontrivialSuffixComponents p L, C.card := by
  classical
  let S := nontrivialSuffixComponents p L
  calc
    _ = (S.attach.toList.map (fun C => C.val.card)).sum := by
      simp only [suffixComponentFamily,List.map_map,Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro C _
      exact (suffix_component_filling_spec p L C).1
    _ = ∑ C ∈ S, C.card := by
      simpa only [Finset.toList_toFinset,Finset.sum_attach] using
        (List.sum_toFinset (fun C : {C // C ∈ S} => C.val.card) (Finset.nodup_toList S.attach)).symm

/-- Keeping the internal and exterior families separate improves the square
bound when the exterior has small total size. -/
theorem area_window_split_square_cap (p : State n) (L : ℕ) :
    let V : ℤ := ((areaWindowFamily p L).map (fun A => (A.size : ℤ))).sum
    let v : ℤ := ∑ C ∈ nontrivialSuffixComponents p L, (C.card : ℤ)
    ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum ≤ (V-v)^2+v^2 := by
  have hi := window_square_sum_le_total_square (positiveSourceFamily p L)
  have he := window_square_sum_le_total_square (suffixComponentFamily p L)
  have hs := congrArg (fun x : ℕ => (x : ℤ)) (suffix_component_family_size_sum p L)
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_sum] at hs
  dsimp only
  simp only [areaWindowFamily,List.map_append,List.sum_append]
  rw [hs] at he ⊢
  nlinarith only [hi,he]

/-- The split-square bound with exactly the R,a,v parameters of C9/C10. -/
theorem prefix_component_split_square_cap (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    let L := (componentSet p 0).card
    let r : ℤ := (prefixSourceCore p).card+((singletonSuffixComponents p L).card : ℤ)
    let v : ℤ := ∑ C ∈ nontrivialSuffixComponents p L, (C.card : ℤ)
    ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum ≤ ((n : ℤ)-r-v)^2+v^2 := by
  have hpart := congrArg (fun x : ℕ => (x : ℤ)) (area_core_size_partition p hc hproper)
  simp only [Nat.cast_add,Nat.cast_list_sum,List.map_map,Function.comp_def] at hpart
  have h := area_window_split_square_cap p (componentSet p 0).card
  dsimp only at h ⊢
  have hV : ((areaWindowFamily p (componentSet p 0).card).map (fun A => (A.size : ℤ))).sum =
      (n : ℤ)-((prefixSourceCore p).card+((singletonSuffixComponents p (componentSet p 0).card).card : ℤ)) := by
    omega
  rwa [hV] at h

#print axioms suffix_component_family_size_sum
#print axioms prefix_component_split_square_cap
end LRX.FiniteCuts
