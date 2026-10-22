import LRX.PacketPartitionWidths
import LRX.ArrowLoadPaths
import LRX.PortLoadBalance

/-! Every nonempty internal gap has a positive, hence at least two, load at
its left boundary port in the original balanced lift. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem internal_boundary_crossing {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : Internal p d a) :
    ∃ s : Fin n, ∃ k : ℤ,
      min (s : ℤ) ((s : ℤ)+d s) ≤ (a : ℤ)+k*(n : ℤ) ∧
      (a : ℤ)+k*(n : ℤ)+1 ≤ max (s : ℤ) ((s : ℤ)+d s) := by
  obtain ⟨s,x,hs,hx,k,hlo,hhi⟩ := ha
  have hscore := (PrunedLift.mem_core p d 0 s).mp hs
  have htcore := PrunedLift.in_core_same_cycle p d 0 hscore (Equiv.Perm.SameCycle.refl _ _).apply_right
  have hs' : (((s : ℤ)-k*(n : ℤ) : ℤ) : Fin n)=s := by simp
  have ht' : (((s : ℤ)+d s-k*(n : ℤ) : ℤ) : Fin n)=p.symm s := by
    calc
      _ = (((s : ℤ)+d s : ℤ) : Fin n) := by simp
      _ = p.symm s := by simpa using AffineLift.lift_residue hd s
  have hstart := core_copy_outside_partition_gap p d a ((s : ℤ)-k*(n : ℤ)) (by simpa only [hs'] using hs)
  have hfinish := core_copy_outside_partition_gap p d a ((s : ℤ)+d s-k*(n : ℤ))
    (by simpa only [ht'] using (PrunedLift.mem_core p d 0 (p.symm s)).mpr htcore)
  have hx' := (mem_positions (PrunedLift.core p d 0) a x).mp hx
  refine ⟨s,k,?_⟩
  rcases hstart with hstart | hstart <;> rcases hfinish with hfinish | hfinish <;> constructor <;> omega

theorem internal_load_positive {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : Internal p d a) :
    0 < RotationWords.portLoad d a := by
  obtain ⟨s,k,hlo,hhi⟩ := internal_boundary_crossing hd a ha
  have hp := CycleFootprint.passage_positive_of_interval
    (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) k
    (a := (s : ℤ)-(a : ℤ)) (b := (s : ℤ)-(a : ℤ)+d s) (by omega) (by omega)
  rw [RotationWords.port_load_original]
  apply lt_of_lt_of_le hp
  exact Finset.single_le_sum (f := fun i : Fin n => PeriodicBuffer.edgePassages (n : ℤ)
    ((i : ℤ)-(a : ℤ)) ((i : ℤ)-(a : ℤ)+d i)) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

theorem internal_load_ge_two {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : Internal p d a) :
    2 ≤ RotationWords.portLoad d a :=
  RotationWords.positive_port_load_ge_two hd a (internal_load_positive hd a ha)

#print axioms internal_load_ge_two
end LRX.FiniteGaps
