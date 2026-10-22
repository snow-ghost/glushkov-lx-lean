import LRX.ZeroGapActivityBound
import LRX.FirstGapSharpWord

/-! Zero-gap sorting and majorization give a nonnegative exchange reserve
for every input lift. The stronger source-packet reserve remains separate. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem outside_support_zero {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (i : Fin n) (hi : i ∉ p.support) : d i=0 := by
  have hfix : p i=i := by simpa using hi
  have hinv : p⁻¹ i=i := by
    apply p.injective
    simpa using hfix.symm
  apply BufferProgram.fixed_short_displacement hd i _ hinv
  have h := hshort i
  have h0 := abs_nonneg (d i)
  omega

theorem active_mass_cap {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    (∑ i : Fin n, |d i|) ≤ (p.support.card/2 : ℕ)*((n : ℤ)-(p.support.card/2 : ℕ)) := by
  have hz := outside_support_zero hd (FiniteWindow.majorized_short hd hm)
  have hs : (∑ i ∈ p.support, d i)=∑ i : Fin n, d i :=
    Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i hi)
  have hmass : (∑ i ∈ p.support, |d i|)=∑ i : Fin n, |d i| :=
    Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => abs_eq_zero.mpr (hz i hi))
  have h := AffineLift.balanced_subset_energy hd.1 hm p.support (by rw [hs,hd.1])
  rwa [hmass] at h

theorem exchange_reserve_nonneg {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    0 ≤ FiniteGaps.exchangeReserve d := by
  have hmass := active_mass_cap hd hm
  have hactivity := activity_inversion_bound hd (FiniteWindow.majorized_short hd hm)
  have hhalf : 2*(p.support.card/2) ≤ p.support.card := by omega
  have hC : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      (p.support.card/2 : ℕ)*((n : ℤ)-(p.support.card/2 : ℕ))-(p.support.card/2 : ℕ) := by omega
  have hquad : 4*(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤ ((n : ℤ)-1)^2 := by
    nlinarith [sq_nonneg ((n : ℤ)-1-2*(p.support.card/2 : ℕ))]
  have hQ := FiniteGaps.floor_square_identity n
  have hn : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have hbound : -1 ≤ 4*FiniteGaps.exchangeReserve d := by
    unfold FiniteGaps.exchangeReserve
    nlinarith
  omega

#print axioms active_mass_cap
#print axioms exchange_reserve_nonneg
end LRX.ZeroGap

namespace LRX.FiniteGaps
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The remaining reserve premise is discharged when the packet has at most
three vertices. The cursor and internal-gap hypotheses remain explicit. -/
theorem small_core_first_gap_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hinternal : Internal p d 0)
    (hsmall : (PrunedLift.core p d 0).card ≤ 3)
    (start finish : Fin n) (hxy : start.val ≤ finish.val)
    (hy : finish.val ≤ size (PrunedLift.core p d 0) 0) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  apply first_internal_gap_sharp_word hn hd hm hroot hcover hinternal _ start finish hxy hy
  have h := ZeroGap.exchange_reserve_nonneg hd hm
  unfold PrunedLift.coreHalfSize
  omega

#print axioms small_core_first_gap_word
end LRX.FiniteGaps
