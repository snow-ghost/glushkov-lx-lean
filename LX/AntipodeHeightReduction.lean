import LX.AntipodeCandidates
import LX.ExceptionalPriceLower

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A displacement below -h forces at least h full inter-token intervals
of cursor motion, regardless of the chosen sequence of exchanges. -/
theorem displacement_rotation_lower (hn : 2 ≤ n) (d : Fin n → ℤ)
    (w : List Letter) (hw : ∀ i,run w d i=0) (h : ℕ) (i : Fin n)
    (hi : d i ≤ -(h : ℤ)-1) : h*(n-1) ≤ w.count .l := by
  have ht := DirectedTokenLower.word_cursor_lower hn w i
  rw [LiftedScan.exact_positions_of_zero hn d w hw i,
    DirectedTokenLower.cursor_eq_left_count] at ht
  have hn' : (2 : ℤ) ≤ n := by omega
  have hp := mul_le_mul_of_nonneg_left hi (show (0 : ℤ) ≤ (n : ℤ)-1 by omega)
  have hgoal : (h : ℤ)*((n : ℤ)-1) ≤ (w.count .l : ℤ) := by
    by_cases hz : i.val=0
    · simp only [hz,Nat.zero_sub,Nat.cast_zero,mul_zero,zero_add,zero_sub] at ht
      nlinarith
    · have he : ((i.val-1 : ℕ) : ℤ)=(i : ℤ)-1 := by omega
      rw [he] at ht
      nlinarith
  have hnsub : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
  exact_mod_cast (show (h : ℤ)*((n-1 : ℕ) : ℤ) ≤ (w.count .l : ℤ) by rw [hnsub]; exact hgoal)

end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem even_large_height_paid (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) (hi : d i < -(m : ℤ)) :
    3*m^2-4*m+3 ≤ inversions d+paidRotations c g := by
  have hI := even_lift_inversions_lower m hm hn hd
  have hL := displacement_rotation_lower (by omega : 2 ≤ n) d g hg.run_zero m i (by omega)
  have hpad : g.count .l ≤ paidRotations c g := by simp only [paidRotations]; omega
  have hn1 : n-1+1=n := by omega
  have hm1 : m-1+1=m := by omega
  have hsub := Nat.sub_add_cancel (show 4*m ≤ 3*m^2 by nlinarith)
  nlinarith

theorem odd_large_height_paid (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) (hi : d i < -(m : ℤ)) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  have hI := odd_lift_inversions_lower m hm hn hd
  have hL := displacement_rotation_lower (by omega : 2 ≤ n) d g hg.run_zero m i (by omega)
  have hpad : g.count .l ≤ paidRotations c g := by simp only [paidRotations]; omega
  have hn1 : n-1+1=n := by omega
  have hm1 : m-1+1=m := by omega
  have hsub := Nat.sub_add_cancel (show m ≤ 3*m^2 by nlinarith)
  nlinarith

/-- Every potentially shorter lift of the even candidate is in this
lower strip; this removes all larger heights for every size. -/
theorem even_unpaid_lower_strip (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-4*m+3) :
    ∀ i,-(m : ℤ) ≤ d i := by
  intro i
  by_contra hi
  have hh := even_large_height_paid m hm hn hd hg i (by omega)
  omega

theorem odd_unpaid_lower_strip (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-m+1) :
    ∀ i,-(m : ℤ) ≤ d i := by
  intro i
  by_contra hi
  have hh := odd_large_height_paid m hm hn hd hg i (by omega)
  omega

#print axioms even_unpaid_lower_strip
#print axioms odd_unpaid_lower_strip
end LX.Antipode
