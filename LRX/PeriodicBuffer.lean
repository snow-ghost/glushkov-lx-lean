import Mathlib

/-! Integer coordinate identities for the corrected periodic buffer service.
No cycle coverage or global sorting cost is assumed or asserted here. -/
namespace LRX.PeriodicBuffer

def passive (M H y : ℤ) : ℤ := y + 1 + (y-H)/M

def buffer (M H y : ℤ) : ℤ := H + (M+1)*((y-H)/M)

def contract (n x : ℤ) : ℤ := x + (-x)/n

theorem quotient_eq_of_bounds {M x q : ℤ} (hM : 0 < M)
    (hlo : q*M ≤ x) (hhi : x < (q+1)*M) : x/M = q := by
  have ha := (Int.le_ediv_iff_mul_le hM).mpr hlo
  have hb := (Int.ediv_lt_iff_lt_mul hM).mpr hhi
  omega

theorem quotient_sub_one {M : ℤ} (hM : 0 < M) (x : ℤ) :
    (x-1)/M = x/M - if x%M=0 then 1 else 0 := by
  have hdiv := Int.ediv_mul_add_emod x M
  have hr0 := Int.emod_nonneg x (ne_of_gt hM)
  have hr1 := Int.emod_lt_of_pos x hM
  split_ifs with hr
  · apply quotient_eq_of_bounds hM <;> nlinarith
  · have hrpos : 1 ≤ x%M := by omega
    apply quotient_eq_of_bounds hM <;> nlinarith

theorem quotient_add_one {M : ℤ} (hM : 0 < M) (x : ℤ) :
    (x+1)/M = x/M + if (x+1)%M=0 then 1 else 0 := by
  have h := quotient_sub_one hM (x+1)
  simp only [add_sub_cancel_right] at h
  omega

/-- At a logical head class, the passive token is exactly one physical step ahead. -/
theorem head_gap {M H y : ℤ} (hhead : (y-H)%M=0) :
    passive M H y = buffer M H y + 1 := by
  have h := Int.ediv_mul_add_emod (y-H) M
  rw [hhead] at h
  dsimp [passive, buffer]
  nlinarith

theorem buffer_forward (M H y : ℤ) :
    buffer M (H+1) (y+1) = buffer M H y + 1 := by
  have h : y+1-(H+1)=y-H := by ring
  simp only [buffer, h]
  ring

theorem buffer_backward (M H y : ℤ) :
    buffer M (H-1) (y-1) = buffer M H y - 1 := by
  have h : y-1-(H-1)=y-H := by ring
  simp only [buffer, h]
  ring

theorem passive_forward {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    passive M (H+1) y = passive M H y - if (y-H)%M=0 then 1 else 0 := by
  have h : y-(H+1)=(y-H)-1 := by ring
  rw [passive, h, quotient_sub_one hM]
  unfold passive
  ring

theorem passive_backward {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    passive M (H-1) y = passive M H y + if (y-(H-1))%M=0 then 1 else 0 := by
  have h : y-(H-1)=(y-H)+1 := by ring
  rw [passive, h, quotient_add_one hM]
  unfold passive
  ring

theorem passive_period {M : ℤ} (hM : M ≠ 0) (H y k : ℤ) :
    passive M H (y+k*M) = passive M H y + k*(M+1) := by
  have h : y+k*M-H=(y-H)+k*M := by ring
  simp only [passive, h, Int.add_mul_ediv_right _ _ hM]
  ring

theorem buffer_period {M : ℤ} (hM : M ≠ 0) (H y k : ℤ) :
    buffer M H (y+k*M) = buffer M H y + k*(M+1) := by
  have h : y+k*M-H=(y-H)+k*M := by ring
  simp only [buffer, h, Int.add_mul_ediv_right _ _ hM]
  ring

theorem contract_period {n : ℤ} (hn : n ≠ 0) (x k : ℤ) :
    contract n (x+k*n) = contract n x + k*(n-1) := by
  have h : -(x+k*n)=-x+(-k)*n := by ring
  simp only [contract, h, Int.add_mul_ediv_right _ _ hn]
  ring

theorem contract_step {n : ℤ} (hn : 0 < n) (x : ℤ) :
    contract n (x+1) - contract n x = 1 - if (-x)%n=0 then 1 else 0 := by
  have h : -(x+1)=(-x)-1 := by ring
  simp only [contract, h, quotient_sub_one hn]
  ring

theorem contract_monotone {n : ℤ} (hn : 0 < n) : Monotone (contract n) := by
  apply monotone_int_of_le_succ
  intro x
  have h := contract_step hn x
  split_ifs at h <;> omega


theorem passive_mod {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    (passive M H y-H)%(M+1) = (y-H)%M+1 := by
  have hr0 := Int.emod_nonneg (y-H) (ne_of_gt hM)
  have hr1 := Int.emod_lt_of_pos (y-H) hM
  have hd := Int.ediv_mul_add_emod (y-H) M
  have he : passive M H y-H = (M+1)*((y-H)/M) + ((y-H)%M+1) := by
    dsimp [passive]; nlinarith
  calc
    _ = ((y-H)%M+1)%(M+1) := by rw [he]; simp
    _ = (y-H)%M+1 := Int.emod_eq_of_lt (by omega) (by omega)

theorem buffer_at_cursor (M H y : ℤ) : Int.ModEq (M+1) (buffer M H y) H := by
  simp [buffer, Int.ModEq, Int.add_emod]

theorem passive_not_cursor {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    ¬ Int.ModEq (M+1) (passive M H y) H := by
  intro h
  have hh := h.sub_right H
  change (passive M H y-H)%(M+1) = (H-H)%(M+1) at hh
  rw [passive_mod hM] at hh
  have hr := Int.emod_nonneg (y-H) (ne_of_gt hM)
  simp only [sub_self, Int.zero_emod] at hh
  omega

theorem passive_next_iff {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    Int.ModEq (M+1) (passive M H y) (H+1) ↔ (y-H)%M=0 := by
  have h1 : (1 : ℤ)%(M+1)=1 := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · intro h
    have hh := h.sub_right H
    change (passive M H y-H)%(M+1) = (H+1-H)%(M+1) at hh
    rw [passive_mod hM, add_sub_cancel_left, h1] at hh
    omega
  · intro h
    have hh : Int.ModEq (M+1) (passive M H y-H) 1 := by
      change (passive M H y-H)%(M+1) = 1%(M+1)
      rw [passive_mod hM, h, h1]; omega
    have hnew := hh.add_right H
    rw [sub_add_cancel, add_comm 1 H] at hnew
    exact hnew

theorem passive_prev_iff {M : ℤ} (hM : 0 < M) (H y : ℤ) :
    Int.ModEq (M+1) (passive M H y) (H-1) ↔ (y-(H-1))%M=0 := by
  have hd := passive_backward hM H y
  constructor
  · intro h
    by_contra hc
    rw [ite_eq_right hc, add_zero] at hd
    exact passive_not_cursor hM (H-1) y (hd.symm ▸ h)
  · intro hc
    rw [ite_eq_left hc] at hd
    have hh := ((passive_next_iff hM (H-1) y).mpr hc).sub_right 1
    simpa only [hd, add_sub_cancel_right] using hh

def edgePassages (n a b : ℤ) : ℤ := |(-b)/n-(-a)/n|

theorem contract_distance {n : ℤ} (hn : 0 < n) (a b : ℤ) :
    |contract n b-contract n a| = |b-a| - edgePassages n a b := by
  rcases le_total a b with hab | hba
  · have hf := contract_monotone hn hab
    have hg := Int.ediv_le_ediv hn (by omega : -b ≤ -a)
    rw [abs_of_nonneg (by omega : 0 ≤ contract n b-contract n a),
      abs_of_nonneg (by omega : 0 ≤ b-a)]
    unfold edgePassages
    rw [abs_of_nonpos (by omega : (-b)/n-(-a)/n ≤ 0)]
    unfold contract
    ring
  · have hf := contract_monotone hn hba
    have hg := Int.ediv_le_ediv hn (by omega : -a ≤ -b)
    rw [abs_of_nonpos (by omega : contract n b-contract n a ≤ 0),
      abs_of_nonpos (by omega : b-a ≤ 0)]
    unfold edgePassages
    rw [abs_of_nonneg (by omega : 0 ≤ (-b)/n-(-a)/n)]
    unfold contract
    ring

open scoped BigOperators in
theorem rotation_price {ι : Type*} (s : Finset ι) {n : ℤ} (hn : 0 < n)
    (start target : ι → ℤ) :
    (∑ i ∈ s, |contract n (target i)-contract n (start i)|) =
      (∑ i ∈ s, |target i-start i|) - ∑ i ∈ s, edgePassages n (start i) (target i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => contract_distance hn (start i) (target i))


theorem contract_between {n x : ℤ} (hx : 0 < x) (hxn : x < n) :
    contract n x = x-1 := by
  have hn : 0 < n := by omega
  have hd : (-x)/n = -1 := quotient_eq_of_bounds hn (by nlinarith) (by nlinarith)
  simp [contract, hd, sub_eq_add_neg]

/-- Contracting congruent lifted endpoints preserves their logical class. -/
theorem contract_modEq {n a b : ℤ} (hn : n ≠ 0) (h : Int.ModEq n a b) :
    Int.ModEq (n-1) (contract n a) (contract n b) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp h
  rw [hk, mul_comm n k, contract_period hn]
  simp [Int.ModEq, Int.add_emod]

/-- The contracted target reconstructs its exact integer position, including turns. -/
theorem reconstruct_buffer {M : ℤ} (hM : 0 < M) (x : ℤ) (hx : x%(M+1)=0) :
    buffer M 0 (contract (M+1) x) = x := by
  have hxform : x = 0 + (x/(M+1))*(M+1) := by
    have hh := Int.ediv_mul_add_emod x (M+1)
    rw [hx] at hh
    omega
  have hf : contract (M+1) x = 0 + (x/(M+1))*M := by
    conv_lhs => rw [hxform]
    rw [contract_period (by omega : M+1 ≠ 0)]
    simp [contract]
  rw [hf, buffer_period (ne_of_gt hM)]
  simp only [buffer, sub_self, Int.zero_ediv, mul_zero, add_zero, zero_add]
  simpa only [zero_add] using hxform.symm

theorem reconstruct_passive {M : ℤ} (hM : 0 < M) (x : ℤ) (hx : x%(M+1)≠0) :
    passive M 0 (contract (M+1) x) = x := by
  have hn : 0 < M+1 := by omega
  have hr0 := Int.emod_nonneg x (ne_of_gt hn)
  have hr1 := Int.emod_lt_of_pos x hn
  have hr : 0 < x%(M+1) := by omega
  have hxform : x = x%(M+1) + (x/(M+1))*(M+1) := (Int.emod_add_ediv_mul _ _).symm
  have hf : contract (M+1) x = (x%(M+1)-1) + (x/(M+1))*M := by
    conv_lhs => rw [hxform]
    rw [contract_period (ne_of_gt hn), contract_between hr hr1]
    ring
  have hq : (x%(M+1)-1)/M=0 := quotient_eq_of_bounds hM (by nlinarith) (by nlinarith)
  rw [hf, passive_period (ne_of_gt hM)]
  simp only [passive, sub_zero, hq, add_zero]
  nlinarith [hxform]

#print axioms head_gap
#print axioms passive_forward
#print axioms passive_backward
#print axioms contract_monotone
#print axioms passive_next_iff
#print axioms passive_prev_iff
#print axioms rotation_price
#print axioms contract_modEq
#print axioms reconstruct_buffer
#print axioms reconstruct_passive
end LRX.PeriodicBuffer
