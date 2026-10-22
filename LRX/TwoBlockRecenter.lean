import LRX.InvariantCutRecenter

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Moving the cut past the first block exchanges the two blocks and preserves I. -/
theorem invariant_cut_recenter_blocks (p : State n) (a : ℕ) (ha : 0<a) (han : a<n)
    (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    let r : Fin n := ⟨a,han⟩
    (∀ i : Fin n, (localTarget p 0 r i).val < n-a ↔ i.val < n-a) ∧
      inversionNumber (localTarget p 0 r)=inversionNumber p := by
  let r : Fin n := ⟨a,han⟩
  let z : Fin n := ⟨a-1,by omega⟩
  let t : Fin n := ⟨n-a-1,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hr : z+1=r := by
    apply Fin.ext
    change (a-1+1%n)%n=a
    rw [Nat.mod_eq_of_lt (by omega : 1<n)]
    have he : a-1+1=a := by omega
    rw [he,Nat.mod_eq_of_lt han]
  have ht : t+r=last := by
    apply Fin.ext
    change (n-a-1+a)%n=n-1
    have he : n-a-1+a=n-1 := by omega
    rw [he,Nat.mod_eq_of_lt (by omega : n-1<n)]
  have hz : portLoad (displacement p.symm) z=0 := invariant_cut_port_zero p a ha (by omega) hcut
  have hlast : portLoad (displacement p.symm) last=0 := by
    rw [port_load_eq_twice_half]
    have hv : last.val+1=n := by dsimp [last]; omega
    rw [hv,half_load_end]
    simp
  have htz := zero_cut_target_load p z t hz
  rw [hr,ht,hlast] at htz
  have hc := zero_port_invariant_cut (localTarget p 0 r) t htz
  have htval : t.val+1=n-a := by dsimp [t]; omega
  rw [htval] at hc
  have hi := inversion_number_zero_recenter p z hz
  rw [hr] at hi
  exact ⟨hc,hi⟩

#print axioms invariant_cut_recenter_blocks
end LRX.FiniteCuts
