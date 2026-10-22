import LRX.FiniteGapSums
import LRX.PacketCoreBalance
import LRX.FiniteWindowRestriction
import LRX.FiniteQuadraticGap

/-! Every gap in the actual packet partition is invariant and has a canonical
finite filling, including the last interval ending at n. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_gap_endpoints {p : State n} {d : Fin n → ℤ}
    (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) (i : Fin n)
    (hi : i ∈ positions (PrunedLift.core p d 0) a) :
    (a : ℤ) < (i : ℤ)+d i ∧ (i : ℤ)+d i < (next (PrunedLift.core p d 0) a : ℕ) := by
  let S := PrunedLift.core p d 0
  change (a : ℤ) < (i : ℤ)+d i ∧ (i : ℤ)+d i < (next S a : ℤ)
  have hi' := (mem_positions S a i).mp hi
  have hnot : ¬PrunedLift.InCore p d 0 i := fun h => gap_avoids_marks S a i hi
    ((PrunedLift.mem_core p d 0 i).mpr h)
  by_cases hz : d i=0
  · simp only [hz,add_zero]
    exact ⟨by exact_mod_cast hi'.1,by exact_mod_cast hi'.2⟩
  have hforward := PrunedLift.packet_cover_reaches p d 0 hcover i hz
  have hback : ¬PrunedLift.Reaches p d i 0 := fun h => hnot ⟨hforward,h⟩
  have hacore := (PrunedLift.mem_core p d 0 a).mp ha
  have hma := PrunedLift.moving_reachable p d hroot hacore.1
  constructor
  · by_contra h
    have he : BufferProgram.ServiceEdge p d i a := by
      refine Or.inr ⟨hma,0,?_,?_⟩ <;> simp only [zero_mul,add_zero] <;> omega
    exact hback ((Relation.ReflTransGen.single he).trans hacore.2)
  · by_cases hn : next S a=n
    · have hb := (PrunedLift.outside_core_endpoints hcover hroot i hnot).2
      simpa only [hn] using hb
    · obtain ⟨r,hr,heq⟩ := next_is_member S a (by have := next_le S a; omega)
      have hrcore := (PrunedLift.mem_core p d 0 r).mp hr
      have hmr := PrunedLift.moving_reachable p d hroot hrcore.1
      by_contra h
      have he : BufferProgram.ServiceEdge p d i r := by
        refine Or.inr ⟨hmr,0,?_,?_⟩ <;> simp only [zero_mul,add_zero] <;> omega
      exact hback ((Relation.ReflTransGen.single he).trans hrcore.2)

theorem packet_gap_inverse_closed {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) (i : Fin n)
    (hi : i ∈ positions (PrunedLift.core p d 0) a) :
    p.symm i ∈ positions (PrunedLift.core p d 0) a := by
  have hnot : ¬PrunedLift.InCore p d 0 i := fun h => gap_avoids_marks _ a i hi
    ((PrunedLift.mem_core p d 0 i).mpr h)
  have hc := PrunedLift.outside_core_canonical hd hcover hroot i hnot
  obtain ⟨hlo,hhi⟩ := packet_gap_endpoints hcover hroot a ha i hi
  apply (mem_positions _ a _).mpr
  constructor <;> omega

theorem packet_gap_invariant {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) :
    ∀ i, p i ∈ positions (PrunedLift.core p d 0) a ↔ i ∈ positions (PrunedLift.core p d 0) a :=
  FiniteWindow.invariant_of_inverse_closed p _ (packet_gap_inverse_closed hd hcover hroot a ha)

theorem packet_gap_filling {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ PrunedLift.core p d 0) :
    ∃ filling : State (size (PrunedLift.core p d 0) a),
      (∀ i, p.symm (FiniteWindow.embed (window (PrunedLift.core p d 0) a) i)=
        FiniteWindow.embed (window (PrunedLift.core p d 0) a) (filling i)) ∧
      (∀ i, d (FiniteWindow.embed (window (PrunedLift.core p d 0) a) i)=(filling i : ℤ)-(i : ℤ)) := by
  let S := PrunedLift.core p d 0
  obtain ⟨filling,hmatch⟩ := FiniteWindow.exists_restriction_of_inverse_closed (window S a) p (fun i hi => by
    have hmem : i ∈ positions S a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    exact (Finset.mem_filter.mp (packet_gap_inverse_closed hd hcover hroot a ha i hmem)).2)
  refine ⟨filling,hmatch,?_⟩
  intro i
  have hi : FiniteWindow.embed (window S a) i ∈ positions S a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,FiniteWindow.contains_embed _ _⟩
  have hc := PrunedLift.outside_core_canonical hd hcover hroot _
    (fun h => gap_avoids_marks S a _ hi ((PrunedLift.mem_core p d 0 _).mpr h))
  rw [hmatch] at hc
  simpa [FiniteWindow.embed] using hc

#print axioms packet_gap_invariant
#print axioms packet_gap_filling
end LRX.FiniteGaps
