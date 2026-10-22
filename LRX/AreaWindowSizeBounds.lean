import LRX.LargeSourceCoreSize

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Every actual C5 interval has size at most floor(n/2)-1. -/
theorem area_window_size_cap (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    ∀ A ∈ areaWindowFamily p (componentSet p 0).card, A.size ≤ n/2-1 := by
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  intro A hA
  rcases List.mem_append.mp hA with hA | hA
  · obtain ⟨hm,_,_,hb⟩ := positive_source_family_spec p L
    obtain ⟨r,hr,hpos⟩ := hb A hA
    have hw := positive_boundary_window_width A.window p.symm A.filling (hm A hA)
      (FiniteWindow.majorized_short (canonical_lift p.symm) hmaj) r hr hpos
    omega
  · have hb := (suffix_component_family_spec p L hproper.le hcut).2.2 A hA
    have hf := A.window.fits
    dsimp only [L] at hb
    omega

/-- C5's total-size cap uses the four original core vertices and exact partition. -/
theorem area_window_total_size_cap (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    ((areaWindowFamily p (componentSet p 0).card).map (fun A => A.size)).sum ≤ 2*(n/2-1) := by
  have hn := NeZero.pos n
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hpart := area_core_size_partition p hc hproper
  have hcore := large_prefix_source_core_card p hmaj hlarge hproper
  omega

/-- Every exterior component contributes an interval of size at least two. -/
theorem suffix_family_sizes_nontrivial (p : State n) (L : ℕ) :
    ∀ A ∈ suffixComponentFamily p L, 2 ≤ A.size := by
  intro A hA
  obtain ⟨C,_,rfl⟩ := List.mem_map.mp hA
  rw [(suffix_component_filling_spec p L C).1]
  exact (Finset.mem_filter.mp C.property).2

/-- At least t entries of the actual C5 interval family have size at least two. -/
theorem area_family_nontrivial_count (p : State n) (L : ℕ) :
    (nontrivialSuffixComponents p L).card ≤
      ((areaWindowFamily p L).filter (fun A => decide (2 ≤ A.size))).length := by
  classical
  have hf : (suffixComponentFamily p L).filter (fun A => decide (2 ≤ A.size)) =
      suffixComponentFamily p L := by
    apply List.filter_eq_self.mpr
    intro A hA
    simpa only [decide_eq_true_eq] using suffix_family_sizes_nontrivial p L A hA
  have hlen : (suffixComponentFamily p L).length = (nontrivialSuffixComponents p L).card := by
    simp only [suffixComponentFamily,List.length_map,Finset.length_toList,Finset.card_attach]
  rw [areaWindowFamily,List.filter_append,List.length_append,hf,hlen]
  omega

/-- The selected intervals contain all t actual nontrivial exterior components. -/
theorem area_window_total_size_lower (p : State n) (L : ℕ) :
    2*(nontrivialSuffixComponents p L).card ≤
      ((areaWindowFamily p L).map (fun A => A.size)).sum := by
  have hsum (xs : List (FillingWindow n)) (hx : ∀ A ∈ xs, 2 ≤ A.size) :
      2*xs.length ≤ (xs.map (fun A => A.size)).sum := by
    induction xs with
    | nil => simp
    | cons A xs ih =>
      have ha := hx A (by simp)
      have ht := ih (fun B hB => hx B (by simp [hB]))
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  have hh := hsum (suffixComponentFamily p L) (suffix_family_sizes_nontrivial p L)
  have hlen : (suffixComponentFamily p L).length = (nontrivialSuffixComponents p L).card := by
    simp only [suffixComponentFamily,List.length_map,Finset.length_toList,Finset.card_attach]
  rw [hlen] at hh
  simp only [areaWindowFamily,List.map_append,List.sum_append]
  omega

/-- The linear square-sum bound used with C10 in the absolute-size argument. -/
theorem area_window_square_sum_cap (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    let As := areaWindowFamily p (componentSet p 0).card
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      ((n/2-1 : ℕ) : ℤ)*((As.map (fun A => A.size)).sum : ℤ) := by
  have main (xs : List (FillingWindow n)) (hx : ∀ A ∈ xs, A.size ≤ n/2-1) :
      (xs.map (fun A => (A.size : ℤ)^2)).sum ≤
        ((n/2-1 : ℕ) : ℤ)*((xs.map (fun A => A.size)).sum : ℤ) := by
    induction xs with
    | nil => simp
    | cons A xs ih =>
      have ha : (A.size : ℤ) ≤ ((n/2-1 : ℕ) : ℤ) := by exact_mod_cast hx A (by simp)
      have ht := ih (fun B hB => hx B (by simp [hB]))
      have hp := mul_nonneg (show (0 : ℤ) ≤ (A.size : ℤ) by positivity)
        (show (0 : ℤ) ≤ ((n/2-1 : ℕ) : ℤ)-(A.size : ℤ) by omega)
      simp only [List.map_cons,List.sum_cons,Nat.cast_add]
      nlinarith
  exact main _ (area_window_size_cap p hmaj hlarge hproper)

#print axioms area_window_total_size_lower
#print axioms area_window_square_sum_cap
#print axioms area_window_size_cap
#print axioms area_window_total_size_cap
#print axioms area_family_nontrivial_count
end LRX.FiniteCuts
