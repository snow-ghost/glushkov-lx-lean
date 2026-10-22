import LRX.PacketPorts

/-! Consecutive packet vertices confine all intermediate lifted endpoints.
Thus the open gap has canonical finite displacements. -/
namespace LRX.PrunedLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def InCore (p : State n) (d : Fin n → ℤ) (root i : Fin n) : Prop :=
  Reaches p d root i ∧ Reaches p d i root

theorem gap_endpoint_bounds {p : State n} {d : Fin n → ℤ}
    (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) (right : Fin n)
    (hr : InCore p d 0 right)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < right.val → ¬InCore p d 0 i)
    (i : Fin n) (hi : 0 < i.val) (hi' : i.val < right.val) :
    0 < (i : ℤ)+d i ∧ (i : ℤ)+d i < (right : ℤ) := by
  by_cases hz : d i=0
  · simp only [hz,add_zero]
    exact ⟨by exact_mod_cast hi,by exact_mod_cast hi'⟩
  have hforward := packet_cover_reaches p d 0 hcover i hz
  have hback : ¬Reaches p d i 0 := fun h => hgap i hi hi' ⟨hforward,h⟩
  have hright : p⁻¹ right ≠ right := moving_reachable p d hroot hr.1
  constructor
  · by_contra h
    apply hback
    apply Relation.ReflTransGen.single
    refine Or.inr ⟨hroot,0,?_,?_⟩ <;> simp only [Fin.val_zero,Int.natCast_zero,zero_mul,zero_add] <;> omega
  · by_contra h
    apply hback
    have hedge : BufferProgram.ServiceEdge p d i right := by
      refine Or.inr ⟨hright,0,?_,?_⟩ <;> simp only [zero_mul,add_zero] <;> omega
    exact (Relation.ReflTransGen.single hedge).trans hr.2

theorem gap_canonical_displacement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (right : Fin n) (hr : InCore p d 0 right)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < right.val → ¬InCore p d 0 i)
    (i : Fin n) (hi : 0 < i.val) (hi' : i.val < right.val) :
    d i=(p.symm i : ℤ)-(i : ℤ) ∧ 0 < (p.symm i).val ∧ (p.symm i).val < right.val := by
  obtain ⟨hlo,hhi⟩ := gap_endpoint_bounds hcover hroot right hr hgap i hi hi'
  have hn : (right : ℤ) < (n : ℤ) := by exact_mod_cast right.isLt
  have hm := hd.2 i
  change ((i : ℤ)+d i) % (n : ℤ)=((p.symm i : ℤ)+0) % (n : ℤ) at hm
  rw [add_zero,Int.emod_eq_of_lt (le_of_lt hlo) (lt_trans hhi hn),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (p.symm i).isLt)] at hm
  exact ⟨by omega,by exact_mod_cast (show (0 : ℤ) < (p.symm i : ℤ) by omega),
    by exact_mod_cast (show (p.symm i : ℤ) < (right : ℤ) by omega)⟩

#print axioms gap_endpoint_bounds
#print axioms gap_canonical_displacement
end LRX.PrunedLift
