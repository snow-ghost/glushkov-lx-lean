import LRX.PartitionComplementEnergy
import Research.CayleyPy.ConnectedComplementCap
import Research.CayleyPy.RootGapArithmetic

/-! The connected square cap for an actual finite family of gap sizes.
The dominant gap is selected from the family and all other squares are summed. -/
namespace LRX.FiniteGaps
open scoped BigOperators

theorem family_square_cap {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → ℤ)
    (n l eta s parity G H : ℤ) (hl : 0 ≤ l) (hs : 0 ≤ s) (heta : eta=0 ∨ eta=1)
    (hn : n=2*l+eta+s) (hp : parity ≤ 1) (hG : 4*G=(s+eta)^2-parity)
    (hH : 0 ≤ H) (hg : ∀ a ∈ I, 0 ≤ g a) (hsum : ∑ a ∈ I, g a ≤ s)
    (hwidth : ∀ a ∈ I, 2*g a ≤ n) (hcomp : ∀ a ∈ I, l*(2*g a-n+l) ≤ H) :
    2*((∑ a ∈ I, (g a)^2)-2*G-2*H) ≤ l^2+1 := by
  by_cases hsmall : ∀ a ∈ I, 2*g a ≤ s
  · have hsquares := CayleyPy.RootGapArithmetic.nondominant_square_sum I g s hs
      (fun a ha => ⟨hg a ha,hsmall a ha⟩) hsum
    have h := CayleyPy.ConnectedComplementCap.nondominant_square_cap s eta parity G H
      (∑ a ∈ I, (g a)^2) hs heta hp hG hH hsquares
    nlinarith [sq_nonneg l]
  · push Not at hsmall
    obtain ⟨a,ha,hlarge⟩ := hsmall
    let c := ∑ j ∈ I.erase a, g j
    let e := s-g a-c
    let t := 2*g a-s
    let u := t-eta
    have hc : 0 ≤ c := Finset.sum_nonneg (fun j hj => hg j (Finset.mem_of_mem_erase hj))
    have hsplit := Finset.sum_erase_add I g ha
    have he : 0 ≤ e := by dsimp [e,c]; omega
    have hsquares : (∑ j ∈ I, (g j)^2) ≤ (g a)^2+c^2 := by
      have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
        (f := g) (s := I.erase a) (fun j hj => hg j (Finset.mem_of_mem_erase hj))
      have hsplit' := Finset.sum_erase_add I (fun j => (g j)^2) ha
      dsimp [c]
      omega
    have hT := CayleyPy.ConnectedComplementCap.dominant_square_upper parity eta t (g a) c e s G H
      (∑ j ∈ I, (g j)^2) heta hc he (by dsimp [t,e]; ring)
      (by dsimp [e]; ring) hG hsquares
    have heta0 : 0 ≤ eta := by rcases heta with rfl | rfl <;> omega
    have hu : 0 ≤ u := by dsimp [u,t]; rcases heta with rfl | rfl <;> omega
    have hu' : u ≤ 2*l := by have := hwidth a ha; dsimp [u,t]; omega
    have hcomp' : l*(u-l) ≤ H := by
      have h := hcomp a ha
      have heq : u-l=2*g a-n+l := by dsimp [u,t]; omega
      rwa [heq]
    exact CayleyPy.ConnectedComplementCap.complement_square_cap l u parity eta H
      ((∑ j ∈ I, (g j)^2)-2*G-2*H) hl hu hu' hp heta0 hH hcomp' hT

#print axioms family_square_cap
end LRX.FiniteGaps
