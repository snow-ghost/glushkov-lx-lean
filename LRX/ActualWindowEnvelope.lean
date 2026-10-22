import LRX.IndexedWindowProfile

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The exact common square envelope for at least three exterior components. -/
theorem actual_many_window_envelope (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : 3 ≤ (nontrivialSuffixComponents p (componentSet p 0).card).card) :
    let As := areaWindowFamily p (componentSet p 0).card
    let t : ℤ := (nontrivialSuffixComponents p (componentSet p 0).card).card
    let m : ℤ := (n/2 : ℕ)
    let V : ℤ := (As.map (fun A => (A.size : ℤ))).sum
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤
      (m-1)^2+(V-m+1-2*(t-2))^2+(2*(t-2))^2 := by
  let As := areaWindowFamily p (componentSet p 0).card
  let t := (nontrivialSuffixComponents p (componentSet p 0).card).card
  let M : ℤ := ((n/2-1 : ℕ) : ℤ)
  have hcap (A : FillingWindow n) (hA : A ∈ As) : (A.size : ℤ) ≤ M := by
    dsimp only [M]
    exact_mod_cast area_window_size_cap p hmaj hlarge hproper A hA
  have hv : (As.map (fun A => (A.size : ℤ))).sum ≤ 2*M := by
    have hh : (((As.map (fun A => A.size)).sum : ℕ) : ℤ) ≤ 2*M := by
      dsimp only [As,M]
      exact_mod_cast area_window_total_size_cap p hmaj hlarge hproper
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have h := window_profile_envelope As 2 t M (by dsimp [t]; omega)
    (area_family_nontrivial_count p _) (by dsimp [M]; positivity) hcap hv
  have hM : M=((n/2 : ℕ) : ℤ)-1 := by
    have hn := NeZero.pos n
    dsimp [M]
    omega
  have ht' : 3 ≤ (t : ℤ) := by exact_mod_cast ht
  have hh := mul_nonneg (show (0 : ℤ) ≤ (t : ℤ)-2 by omega)
    (show (0 : ℤ) ≤ (t : ℤ)-3 by omega)
  dsimp only at h ⊢
  rw [hM] at h
  change (As.map (fun A => (A.size : ℤ)^2)).sum ≤
    (((n/2 : ℕ) : ℤ)-1)^2+
      ((As.map (fun A => (A.size : ℤ))).sum-((n/2 : ℕ) : ℤ)+1-2*((t : ℤ)-2))^2+
      (2*((t : ℤ)-2))^2
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

/-- The w=1 envelope requires only three actual nonempty intervals. -/
theorem actual_three_window_envelope (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (hthree : 3 ≤ ((areaWindowFamily p (componentSet p 0).card).filter
      (fun A => decide (1 ≤ A.size))).length) :
    let As := areaWindowFamily p (componentSet p 0).card
    let m : ℤ := (n/2 : ℕ)
    let V : ℤ := (As.map (fun A => (A.size : ℤ))).sum
    (As.map (fun A => (A.size : ℤ)^2)).sum ≤ (m-1)^2+(V-m)^2+1 := by
  let As := areaWindowFamily p (componentSet p 0).card
  let M : ℤ := ((n/2-1 : ℕ) : ℤ)
  have hcap (A : FillingWindow n) (hA : A ∈ As) : (A.size : ℤ) ≤ M := by
    dsimp only [M]
    exact_mod_cast area_window_size_cap p hmaj hlarge hproper A hA
  have hv : (As.map (fun A => (A.size : ℤ))).sum ≤ 2*M := by
    have hh : (((As.map (fun A => A.size)).sum : ℕ) : ℤ) ≤ 2*M := by
      dsimp only [As,M]
      exact_mod_cast area_window_total_size_cap p hmaj hlarge hproper
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh
  have h := window_profile_envelope As 1 3 M (by omega) hthree (by dsimp [M]; positivity) hcap hv
  have hM : M=((n/2 : ℕ) : ℤ)-1 := by
    have hn := NeZero.pos n
    dsimp [M]
    omega
  rw [hM] at h
  dsimp only at ⊢
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1 <;> ring

#print axioms actual_many_window_envelope
#print axioms actual_three_window_envelope
end LRX.FiniteCuts
