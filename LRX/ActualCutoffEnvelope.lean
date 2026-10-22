import LRX.ThirdAreaWindow

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The common refined envelope required by cutoff_of_unpaid_peak, for the
actual C9/C10 family. Only the epsilon and U prebounds remain as inputs. -/
theorem actual_cutoff_window_envelope (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : 2 ≤ (nontrivialSuffixComponents p (componentSet p 0).card).card)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤
      3*((nontrivialSuffixComponents p (componentSet p 0).card).card : ℤ)+6)
    (hU : (sourceHalfPeak p : ℤ) ≤ 3*((nontrivialSuffixComponents p (componentSet p 0).card).card : ℤ)+1) :
    let As := areaWindowFamily p (componentSet p 0).card
    let t : ℤ := (nontrivialSuffixComponents p (componentSet p 0).card).card
    let m : ℤ := (n/2 : ℕ)
    let parity : ℤ := (n%2 : ℕ)
    let r : ℤ := (prefixSourceCore p).card+
      ((singletonSuffixComponents p (componentSet p 0).card).card : ℤ)
    3 ≤ t ∨ 200 ≤ m →
      (As.map (fun A => (A.size : ℤ)^2)).sum ≤
        (m-1)^2+(m+1-(r-parity)-CoupledPeakCutoff.width t)^2+(CoupledPeakCutoff.width t)^2 := by
  let As := areaWindowFamily p (componentSet p 0).card
  let t : ℤ := (nontrivialSuffixComponents p (componentSet p 0).card).card
  let m : ℤ := (n/2 : ℕ)
  let parity : ℤ := (n%2 : ℕ)
  let r : ℤ := (prefixSourceCore p).card+
    ((singletonSuffixComponents p (componentSet p 0).card).card : ℤ)
  let V : ℤ := (As.map (fun A => (A.size : ℤ))).sum
  have hnpos := NeZero.pos n
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hpart := area_core_size_partition p hc hproper
  have hpart' := congrArg (fun x : ℕ => (x : ℤ)) hpart
  simp only [Nat.cast_add,Nat.cast_list_sum,List.map_map,Function.comp_def] at hpart'
  have hVR : V+r=(n : ℤ) := by
    dsimp only [V,As,r]
    linarith
  have hn : (n : ℤ)=2*m+parity := by dsimp [m,parity]; omega
  have hv : V=2*m+parity-r := by omega
  change 3 ≤ t ∨ 200 ≤ m → _
  intro hg
  by_cases ht2 : (nontrivialSuffixComponents p (componentSet p 0).card).card=2
  · have ht' : t=2 := by dsimp [t]; rw [ht2]; norm_num
    have hm : 200 ≤ n/2 := by dsimp [m] at hg; omega
    have he' : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 12 := by
      rw [ht2] at he
      norm_num only [Nat.cast_ofNat] at he
      linarith
    have hU' : sourceHalfPeak p ≤ 7 := by rw [ht2] at hU; norm_num at hU; omega
    have hthree := two_component_three_nonempty_windows p hmaj hlarge hproper ht2 hm he' hU'
    have h := actual_three_window_envelope p hmaj hlarge hproper hthree
    change (As.map (fun A => (A.size : ℤ)^2)).sum ≤ (m-1)^2+(V-m)^2+1 at h
    change (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      (m-1)^2+(m+1-(r-parity)-CoupledPeakCutoff.width t)^2+(CoupledPeakCutoff.width t)^2
    rw [ht']
    norm_num [CoupledPeakCutoff.width]
    rw [hv] at h
    nlinarith
  · have ht3 : 3 ≤ (nontrivialSuffixComponents p (componentSet p 0).card).card := by omega
    have h := actual_many_window_envelope p hmaj hlarge hproper ht3
    change (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      (m-1)^2+(V-m+1-2*(t-2))^2+(2*(t-2))^2 at h
    change (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      (m-1)^2+(m+1-(r-parity)-CoupledPeakCutoff.width t)^2+(CoupledPeakCutoff.width t)^2
    have ht' : t ≠ 2 := by dsimp [t]; omega
    simp only [CoupledPeakCutoff.width,if_neg ht']
    rw [hv] at h
    nlinarith

#print axioms actual_cutoff_window_envelope
end LRX.FiniteCuts
