import LX.MinimumEnergyPhases
import LX.DepthCrowding
import LX.CrowdedDeadline

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A controlled additive loss in the subset inequalities. Unlike full
majorization, this permits the slightly more expensive phases needed by LX. -/
def NearMajorized (d : Fin n → ℤ) (K : ℕ) : Prop :=
  ∀ S : Finset (Fin n),2*(∑ i ∈ S,d i) ≤ (S.card : ℤ)*((n : ℤ)-S.card)+K

theorem near_majorized_of_energy_allowance {p : State n} {c₀ c : ℤ}
    {d₀ d : Fin n → ℤ} (hd₀ : IsLift p c₀ d₀)
    (hmin : ∀ c' d',IsLift p c' d' → energy d₀ ≤ energy d')
    (hd : IsLift p c d) (K : ℕ)
    (henergy : (energy d : ℤ) ≤ energy d₀+(n : ℤ)*K) : NearMajorized d K := by
  intro S
  have hm := hmin _ _ (shift_lift hd S)
  have hm' : (energy d₀ : ℤ) ≤ energy (phaseShift d S) := by exact_mod_cast hm
  have he := shift_energy d S hd.1
  have hprod : 0 ≤ (n : ℤ)*((S.card : ℤ)*((n : ℤ)-S.card)-2*(∑ i ∈ S,d i)+K) := by
    nlinarith
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hb := nonneg_of_mul_nonneg_right hprod hn
  linarith

theorem near_majorized_neg {d : Fin n → ℤ} (hb : ∑ i,d i=0) {K : ℕ}
    (hm : NearMajorized d K) : NearMajorized (fun i => -d i) K := by
  intro S
  have hs := Finset.sum_add_sum_compl S d
  rw [hb] at hs
  have hc : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hh := hm Sᶜ
  simp only [Finset.card_compl,Finset.card_univ,Fintype.card_fin,Nat.cast_sub hc] at hh
  rw [Finset.sum_neg_distrib]
  nlinarith

/-- Width n is sufficient here; a tied endpoint split across the seam is
allowed, as in raiseMinimum. -/
theorem crossing_unit_of_width (d : Fin n → ℤ)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (i j : Fin n) : |crossing d i j| ≤ 1 := by
  have hhi := hwidth j i
  have hlo := hwidth i j
  have hv := (j-i).isLt
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hnumlo : -(n : ℤ) ≤ crossingNumerator d i j := by unfold crossingNumerator; omega
  have hnumhi : crossingNumerator d i j < 2*(n : ℤ) := by unfold crossingNumerator; omega
  have hqlo := (Int.le_ediv_iff_mul_le hn).mpr (show (-1 : ℤ)*n ≤ crossingNumerator d i j by omega)
  have hqhi := (Int.ediv_lt_iff_lt_mul hn).mpr (show crossingNumerator d i j < (2 : ℤ)*n by omega)
  rw [abs_le]
  unfold crossing
  omega

theorem displacement_depth_width_bound {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (hwidth : ∀ i j,d i-d j ≤ (n : ℤ))
    (k : ℕ) (i : Fin n) (hk : k ≤ backwardDepth d i) :
    d i+(backwardDepth d i : ℤ) ≤ depthCount d (k+1) := by
  rw [displacement_add_depth hd]
  have hterm (j : Fin n) : ((crossing d i j).toNat : ℤ) ≤
      if k+1 ≤ backwardDepth d j then 1 else 0 := by
    have hc := crossing_unit_of_width d hwidth i j
    by_cases hp : 0 < crossing d i j
    · have hh := crossing_pos_depth_lt d i j hp
      rw [ite_eq_left (by omega : k+1 ≤ backwardDepth d j)]
      have hab := le_abs_self (crossing d i j)
      omega
    · have hz : (crossing d i j).toNat=0 := by omega
      rw [hz,Nat.cast_zero]
      split_ifs <;> norm_num
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hterm j)
  simpa [depthCount] using hh

theorem near_depth_count_quadratic {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) {K : ℕ} (hm : NearMajorized d K)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (k : ℕ) :
    (depthCount d k : ℤ)*((depthCount d k : ℤ)-(n : ℤ)+2*k-2*depthCount d (k+1)) ≤ K := by
  let S := Finset.univ.filter (fun i => k ≤ backwardDepth d i)
  have hsum : (S.card : ℤ)*((k : ℤ)-depthCount d (k+1)) ≤ ∑ i ∈ S,-d i := by
    calc
      _ = ∑ _i ∈ S,((k : ℤ)-depthCount d (k+1)) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by
        have hh := (Finset.mem_filter.mp hi).2
        have hc := displacement_depth_width_bound hd hwidth k i hh
        omega)
  have hmaj := near_majorized_neg hd.1 hm S
  change (depthCount d k : ℤ)*((k : ℤ)-depthCount d (k+1)) ≤ _ at hsum
  change 2*(∑ i ∈ S,-d i) ≤ (depthCount d k : ℤ)*((n : ℤ)-depthCount d k)+K at hmaj
  nlinarith

theorem near_depth_count_recurrence {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) {K : ℕ} (hm : NearMajorized d K)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (k : ℕ) (hk : 2*k ≤ n) :
    (depthCount d k : ℤ) ≤ (n : ℤ)-2*k+2*depthCount d (k+1)+K := by
  have hq := near_depth_count_quadratic hd hm hwidth k
  by_contra hnot
  have hs : (1 : ℤ) ≤ depthCount d k := by omega
  have hb : (0 : ℤ) ≤ (depthCount d k : ℤ)-(n : ℤ)+2*k-2*depthCount d (k+1) := by omega
  have hp := mul_nonneg (show (0 : ℤ) ≤ (depthCount d k : ℤ)-1 by omega) hb
  nlinarith

theorem near_top_depth_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) {K : ℕ} (hm : NearMajorized d K)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (h : ℕ) (hh : 2*h ≤ n)
    (hmax : ∀ i,backwardDepth d i ≤ h) :
    (depthCount d h : ℤ) ≤ (n : ℤ)-2*h+K := by
  have hz : depthCount d (h+1)=0 := by
    unfold depthCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have := hmax i
    omega
  have hc := near_depth_count_recurrence hd hm hwidth h hh
  simpa only [hz,Nat.cast_zero,mul_zero,add_zero] using hc

theorem near_next_depth_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) {K : ℕ} (hm : NearMajorized d K)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (h : ℕ) (hpos : 0 < h) (hh : 2*h ≤ n)
    (hmax : ∀ i,backwardDepth d i ≤ h) :
    (depthCount d (h-1) : ℤ) ≤ 3*((n : ℤ)-2*h)+2+3*K := by
  have hc := near_depth_count_recurrence hd hm hwidth (h-1) (by omega)
  have ht := near_top_depth_count hd hm hwidth h hh hmax
  rw [Nat.sub_add_cancel hpos] at hc
  have he : ((h-1 : ℕ) : ℤ)=(h : ℤ)-1 := by omega
  rw [he] at hc
  linarith

#print axioms near_majorized_of_energy_allowance
#print axioms near_depth_count_quadratic
#print axioms near_next_depth_count

/-- A bounded exchange penalty changes only the constant prefix allowance.
The positions of maximum-depth tokens remain an explicit geometric premise. -/
theorem near_majorized_scan_deadline {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hn : 2 ≤ n) (hd : IsLift p c d) {K : ℕ} (hm : NearMajorized d K)
    (hwidth : ∀ i j,d i-d j ≤ (n : ℤ)) (hi : Function.Injective (labels d))
    (h M : ℕ) (hpos : 2 ≤ h) (hh : 2*h ≤ n)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i,backwardDepth d i=h → i.val ≤ M) :
    scanDeadline d ≤ (h-1)*(n-1)+max M (3*(n-2*h)+2+3*K)-1 := by
  apply scan_deadline_of_crowding hn d hi h M (3*(n-2*h)+2+3*K)
    hpos hmax hhead hpositions
  have hc := near_next_depth_count hd hm hwidth h (by omega) hh hmax
  omega

#print axioms near_majorized_scan_deadline
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- An actual anchor with K extra exchanges has the required weakened subset
inequalities. The energy allowance is derived, rather than added as a premise. -/
theorem near_majorized_of_exchange_allowance {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (b : Fin n) (K : ℕ)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K) :
    NearMajorized (displacement p b) K := by
  apply near_majorized_of_energy_allowance (is_lift p a) ha (is_lift p b) K
  have he := anchor_energy_inversion_invariant p a b
  have hx' : (inversions (displacement p b) : ℤ) ≤ inversions (displacement p a)+K := by
    exact_mod_cast hx
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- Transfer the certified near-minimum phase to a literal LX word. The final
residue is retained; it is not bounded by an entire extra lap. -/
theorem near_minimum_phase_word {p : State n} {a : Fin n}
    (hn : 2 ≤ n) (ha : GlobalMinimum p a) (b : Fin n) (K M : ℕ)
    (hx : inversions (displacement p b) ≤ inversions (displacement p a)+K)
    (hpos : 2 ≤ height p b) (hh : 2*height p b ≤ n)
    (hhead : backwardDepth (displacement p b) 0 < height p b)
    (hpositions : ∀ i,backwardDepth (displacement p b) i=height p b → i.val ≤ M) :
    let T := (height p b-1)*(n-1)+max M (3*(n-2*height p b)+2+3*K)-1
    ∃ w : List Letter,p*eval w=1 ∧
      w.length ≤ inversions (displacement p a)+K+T+
        ((phase p b : Fin n)-(T : Fin n)).val := by
  intro T
  have hd := is_lift p b
  have hl (i : Fin n) : labels (displacement p b) i=p i+(phase p b : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels (displacement p b)) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have hwidth (i j : Fin n) : displacement p b i-displacement p b j ≤ (n : ℤ) := by
    have hi := displacement_band p b i
    have hj := displacement_band p b j
    omega
  have htime := near_majorized_scan_deadline hn hd
    (near_majorized_of_exchange_allowance ha b K hx) hwidth hi (height p b) M hpos hh
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i) hhead hpositions
  obtain ⟨w,ht,_⟩ := candidate_sorting_word hn p b
  obtain ⟨v,hv,hlen⟩ := ht.word_at_cursor hn p (phase p b : Fin n) hd.1 hi hl T
    ((ht.rotations_le_deadline hn hd.1 hi).trans htime)
  exact ⟨v,hv,by omega⟩

#print axioms near_majorized_of_exchange_allowance
#print axioms near_minimum_phase_word
end LX.AnchoredPhases
