import LRX.TwoBlockCenterCover
import LRX.PortRoute

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The literal shortest rotation price agrees with the integer circular distance. -/
theorem short_move_eq_lee (s t : Fin n) :
    ((min (t-s).val (n-(t-s).val) : ℕ) : ℤ)=BalancedTwoBlockPorts.lee (n : ℤ) (s : ℤ) (t : ℤ) := by
  have hs := s.isLt
  have ht := t.isLt
  by_cases h : s.val ≤ t.val
  · rw [Fin.sub_val_of_le h]
    have hd : t.val-s.val ≤ n := by omega
    simp only [Nat.cast_min,Nat.cast_sub h,Nat.cast_sub hd,BalancedTwoBlockPorts.lee]
    rw [abs_of_nonpos (by omega : (s : ℤ)-(t : ℤ) ≤ 0)]
    congr 1 <;> omega
  · have hts : t < s := by change t.val < s.val; omega
    rw [Fin.coe_sub_iff_lt.mpr hts]
    have hlow : s.val ≤ n+t.val := by omega
    have hhigh : n+t.val-s.val ≤ n := by omega
    simp only [Nat.cast_min,Nat.cast_sub hhigh,Nat.cast_sub hlow,Nat.cast_add,BalancedTwoBlockPorts.lee]
    rw [abs_of_nonneg (by omega : 0 ≤ (s : ℤ)-(t : ℤ))]
    omega

theorem lee_symm (s t : ℤ) : BalancedTwoBlockPorts.lee (n : ℤ) s t=BalancedTwoBlockPorts.lee (n : ℤ) t s := by
  simp only [BalancedTwoBlockPorts.lee,abs_sub_comm]

/-- Add actual shortest-rotation words to a normalized internal route. -/
theorem approach_word (p : State n) (s t start finish : Fin n) (w : List Letter)
    (he : eval w=(rotation s)⁻¹*p*rotation t) :
    ∃ v : List Letter, eval v=(rotation start)⁻¹*p*rotation finish ∧
      (v.length : ℤ)=(w.length : ℤ)+
        BalancedTwoBlockPorts.lee (n : ℤ) (start : ℤ) (s : ℤ)+
        BalancedTwoBlockPorts.lee (n : ℤ) (finish : ℤ) (t : ℤ) := by
  let v := toPort (s-start)++w++toPort (finish-t)
  refine ⟨v,?_,?_⟩
  · simp only [v,eval_append,toPort_eval_rotation,he,rotation_sub]
    group
  · simp only [v,List.length_append,toPort_length,Nat.cast_add]
    rw [short_move_eq_lee,short_move_eq_lee,lee_symm (t : ℤ) (finish : ℤ)]
    ring

#print axioms short_move_eq_lee
#print axioms approach_word
end LRX.RotationWords
