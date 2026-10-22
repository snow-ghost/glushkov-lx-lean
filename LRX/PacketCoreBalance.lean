import LRX.PacketGapConfinement
import LRX.FiniteRemovalBalance

/-! The source packet is balanced even when the load covers the full circle:
all cycles outside it have canonical endpoints after cutting at the root. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

noncomputable def core (p : State n) (d : Fin n → ℤ) (root : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (InCore p d root)

@[simp] theorem mem_core (p : State n) (d : Fin n → ℤ) (root i : Fin n) :
    i ∈ core p d root ↔ InCore p d root i := by
  classical
  simp [core]

theorem in_core_same_cycle (p : State n) (d : Fin n → ℤ) (root : Fin n)
    {i j : Fin n} (hi : InCore p d root i) (hc : (p⁻¹).SameCycle i j) : InCore p d root j := by
  have hji : Reaches p d j i := Relation.ReflTransGen.single (Or.inl hc.symm)
  exact ⟨hi.1.tail (Or.inl hc),hji.trans hi.2⟩

theorem core_invariant (p : State n) (d : Fin n → ℤ) (root i : Fin n) :
    p i ∈ core p d root ↔ i ∈ core p d root := by
  have hc : (p⁻¹).SameCycle (p i) i := by
    have h := (Equiv.Perm.SameCycle.refl (p⁻¹) (p i)).apply_right
    simpa using h
  simp only [mem_core]
  exact ⟨fun h => in_core_same_cycle p d root h hc,fun h => in_core_same_cycle p d root h hc.symm⟩

theorem outside_core_endpoints {p : State n} {d : Fin n → ℤ}
    (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) (i : Fin n)
    (hi : ¬InCore p d 0 i) : 0 ≤ (i : ℤ)+d i ∧ (i : ℤ)+d i < (n : ℤ) := by
  by_cases hz : d i=0
  · simp only [hz,add_zero]
    exact ⟨by positivity,by exact_mod_cast i.isLt⟩
  have hforward := packet_cover_reaches p d 0 hcover i hz
  have hback : ¬Reaches p d i 0 := fun h => hi ⟨hforward,h⟩
  have hil : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
  have hin : (0 : ℤ) ≤ i := by positivity
  constructor
  · by_contra h
    apply hback
    apply Relation.ReflTransGen.single
    refine Or.inr ⟨hroot,0,?_,?_⟩ <;> simp only [Fin.val_zero,Int.natCast_zero,zero_mul,zero_add] <;> omega
  · by_contra h
    apply hback
    apply Relation.ReflTransGen.single
    refine Or.inr ⟨hroot,1,?_,?_⟩ <;> simp only [Fin.val_zero,Int.natCast_zero,one_mul,zero_add] <;> omega

theorem outside_core_canonical {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (i : Fin n) (hi : ¬InCore p d 0 i) : d i=(p.symm i : ℤ)-(i : ℤ) := by
  obtain ⟨hlo,hhi⟩ := outside_core_endpoints hcover hroot i hi
  have hm := hd.2 i
  change ((i : ℤ)+d i) % (n : ℤ)=((p.symm i : ℤ)+0) % (n : ℤ) at hm
  rw [add_zero,Int.emod_eq_of_lt hlo hhi,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (p.symm i).isLt)] at hm
  omega

theorem core_balance {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) :
    (∑ i ∈ core p d 0, d i)=0 := by
  apply balance_of_finite_removal hd (core p d 0) (core_invariant p d 0)
  intro i hi
  exact outside_core_canonical hd hcover hroot i (fun h => hi ((mem_core p d 0 i).mpr h))

#print axioms outside_core_canonical
#print axioms core_balance
end LRX.PrunedLift
