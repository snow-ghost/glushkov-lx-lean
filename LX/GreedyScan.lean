import LX.AffineScan
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The forward scan stops immediately at zero and exchanges exactly at descents. -/
inductive ScanTrace : (Fin n → ℤ) → List Letter → Prop
  | done {d} (hz : ∀ i, d i = 0) : ScanTrace d []
  | left {d w} (hz : ¬ ∀ i, d i = 0) (hle : d 0 ≤ d 1 + 1)
      (tail : ScanTrace (rotate d) w) : ScanTrace d (.l :: w)
  | swap {d w} (hdesc : d 1 + 1 < d 0)
      (tail : ScanTrace (exchange d) w) : ScanTrace d (.x :: w)

theorem ScanTrace.run_zero {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w) :
    ∀ i, run w d i = 0 := by
  induction ht with
  | done hz => exact hz
  | left _ _ _ ih => exact ih
  | swap _ _ ih => exact ih

theorem ScanTrace.unique {d : Fin n → ℤ} {u v : List Letter}
    (hu : ScanTrace d u) (hv : ScanTrace d v) : u = v := by
  induction hu generalizing v with
  | done hz =>
    cases hv with
    | done => rfl
    | left hz' _ _ => exact False.elim (hz' hz)
    | swap hd _ => have h0 := hz 0; have h1 := hz 1; omega
  | left hz hle ht ih =>
    cases hv with
    | done hz' => exact False.elim (hz hz')
    | left _ _ ht' => exact congrArg (List.cons Letter.l) (ih ht')
    | swap hd _ => omega
  | swap hd ht ih =>
    cases hv with
    | done hz => have h0 := hz 0; have h1 := hz 1; omega
    | left _ hle _ => omega
    | swap _ ht' => exact congrArg (List.cons Letter.x) (ih ht')

theorem run_left_zero_iff (k : ℕ) (d : Fin n → ℤ) :
    (∀ i, run (List.replicate k .l) d i = 0) ↔ ∀ i, d i = 0 := by
  simp only [run_left_apply]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := ((LX.Core.L n)^k).surjective i
    exact h j
  · intro h i
    exact h _

theorem ScanTrace.prepend_left (k : ℕ) (d : Fin n → ℤ) (w : List Letter)
    (hz : ¬ ∀ i, d i = 0)
    (hskip : ∀ j < k, run (List.replicate j .l) d 0 ≤ run (List.replicate j .l) d 1 + 1)
    (ht : ScanTrace (run (List.replicate k .l) d) w) :
    ScanTrace d (List.replicate k .l ++ w) := by
  induction k generalizing d with
  | zero => exact ht
  | succ k ih =>
    apply ScanTrace.left hz (hskip 0 (by omega))
    apply ih
    · intro h
      apply hz
      exact (run_left_zero_iff 1 d).mp h
    · intro j hj
      exact hskip (j + 1) (by omega)
    · exact ht

/-- Every valid balanced board admits the actual greedy forward scan. -/
theorem exists_scan_trace (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d)) :
    ∃ w : List Letter, ScanTrace d w := by
  generalize he : LX.Core.AffineLift.energy d = E
  induction E using Nat.strong_induction_on generalizing d with
  | h E ih =>
    by_cases hz : ∀ i, d i = 0
    · exact ⟨[], ScanTrace.done hz⟩
    have hex : ∃ k : ℕ, ∃ hk : k < n,
        d (finRotate n ⟨k, hk⟩) + 1 < d ⟨k, hk⟩ := by
      obtain ⟨i, hdesc⟩ := exists_descent hn d hb hi hz
      exact ⟨i.val, i.isLt, hdesc⟩
    let k := Nat.find hex
    obtain ⟨hk, hdesc⟩ := Nat.find_spec hex
    have hcast : (k : Fin n) = ⟨k, hk⟩ := by
      apply Fin.ext
      change k % n = k
      exact Nat.mod_eq_of_lt hk
    let u : List Letter := List.replicate k .l
    let e := run u d
    have he0 : e 0 = d ⟨k, hk⟩ := by
      simp [e, u, run_left_apply, LX.Core.AffineLift.rotation_power_apply, hcast]
    have he1 : e 1 = d (finRotate n ⟨k, hk⟩) := by
      simp only [e, u, run_left_apply, LX.Core.AffineLift.rotation_power_apply, finRotate_apply, hcast]
      congr 1
      abel
    have hdesce : e 1 + 1 < e 0 := by simpa only [he0, he1] using hdesc
    have henergy : LX.Core.AffineLift.energy e = E := (run_left_energy k d).trans he
    have hlt : LX.Core.AffineLift.energy (exchange e) < E := by
      rw [← henergy]
      exact exchange_energy_lt hn e hdesce
    have hb' : ∑ j, exchange e j = 0 := by rw [exchange_sum, run_sum, hb]
    have hi' : Function.Injective (labels (exchange e)) :=
      exchange_injective hn e (run_injective hn u d hi)
    obtain ⟨v, hv⟩ := ih _ hlt (exchange e) hb' hi' rfl
    refine ⟨u ++ .x :: v, ScanTrace.prepend_left k d (.x :: v) hz ?_ (ScanTrace.swap hdesce hv)⟩
    intro j hj
    have hjn : j < n := lt_trans hj hk
    have hnot := Nat.find_min hex hj
    have hh : d ⟨j, hjn⟩ ≤ d (finRotate n ⟨j, hjn⟩) + 1 := by
      by_contra h
      exact hnot ⟨hjn, by omega⟩
    have hjcast : (j : Fin n) = ⟨j, hjn⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hjn]
    simpa only [run_left_apply, LX.Core.AffineLift.rotation_power_apply, zero_add,
      finRotate_apply, hjcast, add_comm, add_zero] using hh

/-- The unique forward scan acts on the actual permutation in its exact orientation. -/
theorem exists_realized_scan (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : LX.Core.AffineLift.IsLift p.symm c d) :
    ∃ w : List Letter, ScanTrace d w ∧
      p * eval (w ++ List.replicate ((c : Fin n) - (w.count .l : Fin n)).val .l) = 1 := by
  have hlabels (i : Fin n) : labels d i = p i + (c : Fin n) := by
    simpa only [labels, Equiv.symm_symm] using LX.Core.AffineLift.lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hlabels, hlabels] at hij
    exact p.injective (add_right_cancel hij)
  obtain ⟨w, hw⟩ := exists_scan_trace hn d hd.1 hi
  exact ⟨w, hw, sorting_word_of_zero hn p (c : Fin n) d hlabels w hw.run_zero⟩

#print axioms ScanTrace.run_zero
#print axioms ScanTrace.unique
#print axioms exists_scan_trace
#print axioms exists_realized_scan
end LX.AffineScan
