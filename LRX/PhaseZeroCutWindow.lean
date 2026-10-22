import LRX.CanonicalMultiComponentRoutes
import LRX.TwoArcPacketSymmetry
import LRX.ZeroLoadCut

namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A zero port of an arbitrary phase lift supplies the exact canonical finite
window after moving the origin just past that port. -/
theorem phase_zero_cut_canonical {p : State n} {d : Fin n → ℤ} (c z : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) (hz : portLoad d z=0) :
    localDisplacement d (z+1)=FiniteCuts.displacement (localTarget p c (z+1)).symm := by
  let last : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  have hlast : last.val+1=n := by dsimp [last]; have := NeZero.pos n; omega
  have hlastadd : last+1=0 := by
    apply Fin.ext
    rw [Fin.val_zero]
    change (n-1+(1 : ℕ)%n)%n=(0 : ℕ)
    have hn := NeZero.pos n
    by_cases he : n=1
    · subst n; norm_num
    · rw [Nat.mod_eq_of_lt (show 1 < n by omega),show n-1+1=n by omega,Nat.mod_self]
  have hshift : last+(z+1)=z := by linear_combination hlastadd
  have hzero : portLoad (localDisplacement d (z+1)) last=0 := by
    rw [port_load_recenter,hshift,hz]
  funext i
  exact CycleFootprint.zero_last_cut_canonical (recentered_lift c (z+1) hd) last hlast hzero i

theorem phase_local_word_target (p : State n) (c r : Fin n) :
    (rotation (-r))⁻¹*localTarget p c r*rotation (c-r)=p := by
  have hneg : rotation (-r)=(rotation r)⁻¹ := by
    have h := rotation_sub r 0
    simpa only [zero_sub,rotation,Fin.val_zero,pow_zero,mul_one] using h
  rw [hneg,inv_inv]
  unfold localTarget rotation
  group

theorem phase_zero_cut_majorized {p : State n} {d : Fin n → ℤ} (c z : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) (hm : AffineLift.Majorized d) (hz : portLoad d z=0) :
    AffineLift.Majorized (FiniteCuts.displacement (localTarget p c (z+1)).symm) := by
  rw [← phase_zero_cut_canonical c z hd hz]
  exact majorized_recenter hm (z+1)

#print axioms phase_zero_cut_canonical
#print axioms phase_local_word_target
#print axioms phase_zero_cut_majorized
end LRX.RotationWords
