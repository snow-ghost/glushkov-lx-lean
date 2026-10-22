import LRX.PacketCoreBalance
import LRX.PacketPorts
import LRX.LoadedFootprint

/-! Retaining the whole strong packet preserves the load at both incident
ports of every packet vertex, independently of the chosen coordinate cut. -/
namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem positive_passage_touches (d : Fin n → ℤ) (i port : Fin n)
    (hpos : 0 < PeriodicBuffer.edgePassages (n : ℤ)
      ((i : ℤ)-(port : ℤ)) ((i : ℤ)-(port : ℤ)+d i)) :
    BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (port : ℤ) ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) ((port+1 : Fin n) : ℤ) := by
  obtain ⟨k,hlo,hhi⟩ := passage_interval (show (0 : ℤ) < n by exact_mod_cast NeZero.pos n) hpos
  constructor
  · exact ⟨k,by omega,by omega⟩
  · have ht : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) ((port : ℤ)+1) :=
      ⟨k,by omega,by omega⟩
    apply BufferProgram.touches_of_modEq (ht := ht)
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp
end LRX.CycleFootprint

namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem touches_core_implies_core {p : State n} {d : Fin n → ℤ} {root r i : Fin n}
    (hcover : PacketCover p d root) (hroot : p⁻¹ root ≠ root) (hr : InCore p d root r)
    (hdi : d i ≠ 0) (ht : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (r : ℤ)) :
    InCore p d root i := by
  have hm := moving_reachable p d hroot hr.1
  have he : BufferProgram.ServiceEdge p d i r := Or.inr ⟨hm,ht⟩
  exact ⟨packet_cover_reaches p d root hcover i hdi,(Relation.ReflTransGen.single he).trans hr.2⟩

theorem port_load_keeps_core {p : State n} {d : Fin n → ℤ} {root : Fin n}
    (hcover : PacketCover p d root) (hroot : p⁻¹ root ≠ root)
    (S : Finset (Fin n)) (hkeep : KeepsCore p d root S)
    (r port : Fin n) (hr : InCore p d root r) (hp : port=r ∨ port+1=r) :
    portLoad (displacement S d) port=portLoad d port := by
  classical
  rw [port_load_original,port_load_original]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmem : i ∈ S
  · simp [displacement,hmem]
  · have hz : PeriodicBuffer.edgePassages (n : ℤ)
        ((i : ℤ)-(port : ℤ)) ((i : ℤ)-(port : ℤ)+d i)=0 := by
      by_contra hne
      have hpos : 0 < PeriodicBuffer.edgePassages (n : ℤ)
          ((i : ℤ)-(port : ℤ)) ((i : ℤ)-(port : ℤ)+d i) :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have hdi : d i ≠ 0 := by intro h; simp [PeriodicBuffer.edgePassages,h] at hpos
      have ht := CycleFootprint.positive_passage_touches d i port hpos
      have htr : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (r : ℤ) := by
        rcases hp with hp | hp
        · simpa only [hp] using ht.1
        · simpa only [hp] using ht.2
      have hc := touches_core_implies_core hcover hroot hr hdi htr
      exact hmem (hkeep i hc.1 hc.2)
    simp only [displacement,ite_eq_right hmem,add_zero]
    rw [hz]
    simp [PeriodicBuffer.edgePassages]

#print axioms touches_core_implies_core
#print axioms port_load_keeps_core
end LRX.PrunedLift
