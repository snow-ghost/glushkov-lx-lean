import LX.DepthQueue
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Minimum of the original depths at positions 0 through k. -/
def prefixMinimum (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => b 0
  | k+1 => min (prefixMinimum b k) (b (k+1))

theorem prefix_minimum_le_iff (b : ℕ → ℕ) (k x : ℕ) :
    x ≤ prefixMinimum b k ↔ ∀ j ≤ k, x ≤ b j := by
  induction k with
  | zero => simp [prefixMinimum]
  | succ k ih =>
    rw [prefixMinimum,le_min_iff,ih]
    constructor
    · rintro ⟨hh,hx⟩ j hj
      by_cases he : j=k+1
      · simpa only [he] using hx
      · exact hh j (by omega)
    · intro hh
      exact ⟨fun j hj => hh j (by omega),hh (k+1) (by omega)⟩

theorem sweep_prefix_head_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (k : ℕ) (hk : k < n) :
    backwardDepth (sweep d k) 0=prefixMinimum (atDepth d) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sweep,sweep_step_head_depth hn _ (sweep_injective hn d hi k),
      ih (by omega),prefixMinimum]
    have hh := (sweep_prefix_depth hn d hi k (by omega)).2 1 (by omega) (by omega)
    change backwardDepth (sweep d k) 1=atDepth d (1+k) at hh
    simpa only [Nat.add_comm 1 k] using congrArg (min (prefixMinimum (atDepth d) k)) hh

/-- The first output of a lap is only transported after it leaves the head. -/
theorem sweep_emitted_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) :
    atDepth (sweep d k) (n-k)=backwardDepth (compareHead d) 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k=0
    · subst k
      change atDepth (rotate (compareHead d)) (n-1)=backwardDepth (compareHead d) 0
      rw [at_depth_rotate hn,Nat.sub_add_cancel (by omega : 1 ≤ n)]
      simp only [atDepth,Fin.natCast_self]
    · rw [sweep,sweepStep,at_depth_rotate hn]
      have he : n-(k+1)+1=n-k := by omega
      rw [he,compare_head_tail_depth hn _ (n-k) (by omega) (by omega)]
      exact ih (by omega) (by omega)

/-- All quantities in this expression belong to the original input lift. -/
def emittedDepth (d : Fin n → ℤ) (j : ℕ) : ℕ :=
  if ∃ i : Fin j, atTarget d j < atTarget d i.val
  then atDepth d j-1 else prefixMinimum (atDepth d) (j-1)

theorem comparison_at_prefix (hn : 2 ≤ n) (d : Fin n → ℤ)
    (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    (sweep d (j-1)) 1+1 < (sweep d (j-1)) 0 ↔
      ∃ i : Fin j, atTarget d j < atTarget d i.val := by
  have hv := sweep_prefix_values hn d (j-1) (by omega)
  have ht := hv.2 1 (by omega) (by omega)
  have he : 1+(j-1)=j := by omega
  rw [he] at ht
  have hhead := hv.1
  simp only [atTarget,Nat.cast_zero,Nat.cast_one,zero_add] at ht hhead
  have hh : (sweep d (j-1)) 1+1 < (sweep d (j-1)) 0 ↔
      atTarget d j < ForwardCarrier.sweepPrefix (atTarget d) (j-1) (j-1) := by
    dsimp only [atTarget]
    omega
  rw [hh,ForwardCarrier.lt_carrier_iff]
  constructor
  · rintro ⟨i,hi,hlt⟩
    exact ⟨⟨i,by omega⟩,hlt⟩
  · rintro ⟨i,hi⟩
    exact ⟨i.val,by have := i.isLt; omega,hi⟩

theorem compare_prefix_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    backwardDepth (compareHead (sweep d (j-1))) 0=emittedDepth d j := by
  have he := comparison_at_prefix hn d j hj hjn
  have ht := (sweep_prefix_depth hn d hi (j-1) (by omega)).2 1 (by omega) (by omega)
  have hadd : 1+(j-1)=j := by omega
  rw [hadd] at ht
  change backwardDepth (sweep d (j-1)) 1=atDepth d j at ht
  unfold compareHead emittedDepth
  split_ifs with hs hp hp
  · have hh := exchange_backward_depth hn (sweep d (j-1)) hs
    omega
  · exact False.elim (hp (he.mp hs))
  · exact False.elim (hs (he.mpr hp))
  · exact sweep_prefix_head_depth hn d hi (j-1) (by omega)

/-- The entire post-lap queue is a closed expression in the original depths
and the original prefix records; no scan state remains on the right. -/
theorem first_lap_depth_formula (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (i : Fin n) :
    backwardDepth (sweep d (n-1)) i = if i=0 then 0 else emittedDepth d i.val := by
  by_cases hi0 : i=0
  · subst i
    simp only [ite_true]
    exact sweep_head_zero hn d hi
  · rw [ite_eq_right hi0]
    have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
    have hlt := i.isLt
    have hh := sweep_emitted_depth hn (sweep d (i.val-1)) (n-i.val) (by omega) (by omega)
    have ha : i.val-1+(n-i.val)=n-1 := by omega
    have hb : n-(n-i.val)=i.val := by omega
    rw [← sweep_add,ha,hb] at hh
    simp only [atDepth,Fin.cast_val_eq_self] at hh
    rw [hh,compare_prefix_depth hn d hi i.val hip hlt]

/-- A deadline expressed solely through the original affine permutation. -/
def sourceDeadline (d : Fin n → ℤ) : ℕ :=
  (n-1)+(Finset.univ.sup fun i : Fin n =>
    let b := if i=0 then 0 else emittedDepth d i.val
    if b=0 then 0 else (n-1)*(b-1)+i.val)-1


#print axioms first_lap_depth_formula
end LX.AffineScan
