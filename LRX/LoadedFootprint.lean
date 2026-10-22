import LRX.GeometricPacket
import LRX.PortLoadMass

/-! Every edge of positive load belongs to the footprint of a moving cycle. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

theorem passage_interval {N a b : ℤ} (hN : 0 < N)
    (hpos : 0 < PeriodicBuffer.edgePassages N a b) :
    ∃ k : ℤ, min a b ≤ k*N ∧ k*N+1 ≤ max a b := by
  have hne : (-b)/N ≠ (-a)/N := by
    intro h
    simp [PeriodicBuffer.edgePassages,h] at hpos
  by_cases hab : a ≤ b
  · have hle := Int.ediv_le_ediv hN (show -b ≤ -a by omega)
    have hlt : (-b)/N < (-a)/N := by omega
    have hupper := (Int.ediv_lt_iff_lt_mul hN).mp hlt
    have hlower := Int.ediv_mul_le (-a) (ne_of_gt hN)
    refine ⟨-((-a)/N),?_,?_⟩ <;> simp only [min_eq_left hab,max_eq_right hab] <;> nlinarith
  · have hle := Int.ediv_le_ediv hN (show -a ≤ -b by omega)
    have hlt : (-a)/N < (-b)/N := by omega
    have hupper := (Int.ediv_lt_iff_lt_mul hN).mp hlt
    have hlower := Int.ediv_mul_le (-b) (ne_of_gt hN)
    refine ⟨-((-b)/N),?_,?_⟩ <;> simp only [min_eq_right (le_of_not_ge hab),max_eq_left (le_of_not_ge hab)] <;> nlinarith

variable {n : ℕ} [NeZero n]

theorem positive_load_footprint {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (r : Fin n) (hpos : 0 < RotationWords.portLoad d r) :
    ∃ a : Active p, r ∈ activeFootprint p d a ∧ r+1 ∈ activeFootprint p d a := by
  classical
  rw [RotationWords.port_load_original] at hpos
  have hw : ∃ i : Fin n, 0 < PeriodicBuffer.edgePassages (n : ℤ)
      ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i) := by
    by_contra h
    push Not at h
    have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    omega
  obtain ⟨i,hi⟩ := hw
  have hdi : d i ≠ 0 := by intro hz; simp [PeriodicBuffer.edgePassages,hz] at hi
  have hmi : p⁻¹ i ≠ i := fun hf => hdi (BufferProgram.fixed_short_displacement hd i (hshort i) hf)
  obtain ⟨k,hlo,hhi⟩ := passage_interval (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) hi
  have hrange : min (i : ℤ) ((i : ℤ)+d i) ≤ (r : ℤ)+k*(n : ℤ) ∧
      (r : ℤ)+k*(n : ℤ)+1 ≤ max (i : ℤ) ((i : ℤ)+d i) := by
    omega
  have hm := BufferProgram.mem_own_orbit p i hmi
  refine ⟨⟨i,hmi⟩,?_,?_⟩
  · exact (mem_footprint p d i r).mpr ⟨i,hm,k,hrange.1,by omega⟩
  · have hp := arrow_point_mem p d i i hm ((r : ℤ)+k*(n : ℤ)+1) ⟨by omega,hrange.2⟩
    have he : (((r : ℤ)+k*(n : ℤ)+1 : ℤ) : Fin n)=r+1 := by
      rw [Int.cast_add,copy_cast,Int.cast_one]
    simpa only [he,activeFootprint] using hp

def LoadedStep (d : Fin n → ℤ) (x y : Fin n) : Prop :=
  (y=x+1 ∧ 0 < RotationWords.portLoad d x) ∨ (x=y+1 ∧ 0 < RotationWords.portLoad d y)

theorem loaded_step_footprint {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    {x y : Fin n} (h : LoadedStep d x y) :
    ∃ a : Active p, x ∈ activeFootprint p d a ∧ y ∈ activeFootprint p d a := by
  rcases h with ⟨rfl,hp⟩ | ⟨rfl,hp⟩
  · exact positive_load_footprint hd hshort x hp
  · obtain ⟨a,ha,hb⟩ := positive_load_footprint hd hshort y hp
    exact ⟨a,hb,ha⟩

#print axioms passage_interval
#print axioms positive_load_footprint
end LRX.CycleFootprint
