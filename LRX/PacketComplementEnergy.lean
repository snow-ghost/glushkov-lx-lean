import LRX.GapComplementCoordinates

/-! The complementary interval of a packet gap bounds the packet energy by
2*l*(n-b-l), with l the half-size of the actual packet support. -/
namespace LRX.FiniteCoordinates
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem card_le_of_coordinates (S : Finset α) (f : α → ℤ) (L : ℕ)
    (hf : Set.InjOn f S) (hlo : ∀ i ∈ S, 0 ≤ f i) (hhi : ∀ i ∈ S, f i < L) : S.card ≤ L := by
  classical
  let e : {i // i ∈ S} → Fin L := fun i => ⟨(f i.val).toNat,by
    have := hlo i.val i.property
    have := hhi i.val i.property
    omega⟩
  have hinj : Function.Injective e := by
    intro i j he
    apply Subtype.ext
    apply hf i.property j.property
    have hv := congrArg Fin.val he
    change (f i.val).toNat=(f j.val).toNat at hv
    have := hlo i.val i.property
    have := hlo j.val j.property
    omega
  have h := Fintype.card_le_of_injective e hinj
  simpa using h

#print axioms card_le_of_coordinates
end LRX.FiniteCoordinates
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem core_complement_energy {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r : Fin n) (b : ℕ)
    (hr : r.val=b+1)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i) :
    (∑ i ∈ core p d 0, |d i|) ≤
      2*((core p d 0).card/2 : ℕ)*((n : ℤ)-b-((core p d 0).card/2 : ℕ)) := by
  classical
  let S := core p d 0
  let f := complementCoordinate r
  have hf := complement_coordinate_injective r
  have hb : ∀ i ∈ S, 0 ≤ f i ∧ f i < (n-b : ℕ) := by
    intro i hi
    exact complement_coordinate_bounds p d r b hr hgap i ((mem_core p d 0 i).mp hi)
  have hb' : ∀ i ∈ S, 0 ≤ f (p.symm i) ∧ f (p.symm i) < (n-b : ℕ) := by
    intro i hi
    apply hb
    exact (inverse_mem_iff p S (core_invariant p d 0) i).mpr hi
  have hcard := FiniteCoordinates.card_le_of_coordinates S f (n-b) hf.injOn
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  have hbalance : (∑ i ∈ S, (f (p.symm i)-f i))=0 := by
    rw [Finset.sum_sub_distrib,sum_inverse p S (core_invariant p d 0),sub_self]
  have hcap := FiniteCoordinates.energy_capacity S f (fun i => f (p.symm i)) (n-b)
    hf.injOn (hf.comp p.symm.injective).injOn
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
    (fun i hi => (hb' i hi).1) (fun i hi => (hb' i hi).2) hbalance hcard
  have hmass : (∑ i ∈ S, |d i|) ≤ ∑ i ∈ S, |f (p.symm i)-f i| :=
    Finset.sum_le_sum (fun i _ => displacement_le_complement hd hm r i)
  have hbn : b ≤ n := by have := r.isLt; omega
  rw [Nat.cast_sub hbn] at hcap
  exact hmass.trans hcap

#print axioms core_complement_energy
end LRX.PrunedLift
