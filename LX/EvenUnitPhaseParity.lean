import LX.EvenUnitStructure
import LX.OddUnitFixedNeighbors
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem fixed_source_displacement (p : State n) (a i : Fin n)
    (hi : i ∈ fixedPositions (permutation p a)) : displacement p a i= -(height p a : ℤ) := by
  have hh := (mem_fixedPositions _ _).mp hi
  rw [displacement_offset,cyclic_offset_normalized,hh,sub_self]
  simp

/-- Two minimum coordinates saturate their subset inequality in even
maximal height. A coordinate one unit above them would violate the
three-coordinate inequality. -/
theorem two_fixed_no_offset_one (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (hn : n=2*height p a+2)
    (hf : (fixedPositions (permutation p a)).card=2) (i : Fin n) :
    (cyclicOffset p a i).val ≠ 1 := by
  intro hi
  let F := fixedPositions (permutation p a)
  have hdi : displacement p a i=1-(height p a : ℤ) := by
    rw [displacement_offset]
    change (((cyclicOffset p a i).val : ℕ) : ℤ)-(height p a : ℤ)=_
    rw [hi]
    norm_num
  have hini : i ∉ F := by
    intro hh
    have hmin := fixed_source_displacement p a i hh
    omega
  have hsum : (∑ j ∈ F,-displacement p a j)=2*(height p a : ℤ) := by
    have heq : (∑ j ∈ F,-displacement p a j)=∑ _j ∈ F,(height p a : ℤ) :=
      Finset.sum_congr rfl (fun j hj => by rw [fixed_source_displacement p a j hj]; ring)
    rw [heq]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (F.card : ℤ)*_=2*_
    change (fixedPositions (permutation p a)).card=2 at hf
    rw [hf]
    norm_num
  have hh := majorized_neg (is_lift p a).1 hm (insert i F)
  rw [Finset.sum_insert hini,hsum,hdi,Finset.card_insert_of_notMem hini] at hh
  have hF : F.card=2 := hf
  rw [hF] at hh
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hh
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  nlinarith

/-- A minimal phase with two fixed positions has another minimal phase
whose relative offset is exactly two. No search or phase-count premise is used. -/
theorem even_unit_two_fixed_next_phase {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1))
    (hf : (fixedPositions (permutation p a)).card=2) :
    ∃ b : Fin n,GlobalMinimum p b ∧ cyclicOffset p a b=2 := by
  let F := fixedPositions (permutation p a)
  have hh := (even_unit_reserve_height m hn ha hunit).1
  have hsum : (∑ j ∈ F,displacement p a j)= -2*(height p a : ℤ) := by
    have heq : (∑ j ∈ F,displacement p a j)=∑ _j ∈ F,-(height p a : ℤ) :=
      Finset.sum_congr rfl (fun j hj => fixed_source_displacement p a j hj)
    rw [heq]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (F.card : ℤ)*_= -2*_
    change (fixedPositions (permutation p a)).card=2 at hf
    rw [hf]
    ring
  have htop : (∑ j ∈ Fᶜ,displacement p a j)=2*(height p a : ℤ) := by
    have he := Finset.sum_compl_add_sum F (displacement p a)
    rw [hsum,displacement_balance] at he
    omega
  have hcard : Fᶜ.card=n-2 := by
    rw [Finset.card_compl,Fintype.card_fin]
    change n-F.card=n-2
    rw [hf]
  have htight : 2*(∑ j ∈ Fᶜ,displacement p a j)=(Fᶜ.card : ℤ)*((n : ℤ)-Fᶜ.card) := by
    rw [htop,hcard,Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num only [Nat.cast_ofNat]
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
    nlinarith
  obtain ⟨b,hb,_,hphase,hx⟩ := zero_slack_phase ha Fᶜ htight
  have hbunit : (inversions (displacement p b) : ℤ)+1=(m : ℤ)*(m-1) := by rwa [hx]
  have hbh := (even_unit_reserve_height m hn hb hbunit).1
  have heighth : height p b=height p a := by omega
  have hphase' : (phase p b : Fin n)=(phase p a : Fin n)-2 := by
    rw [hcard,Nat.cast_sub (by omega : 2 ≤ n),Fin.natCast_self] at hphase
    simpa only [zero_sub,sub_eq_add_neg,Nat.cast_ofNat,zero_add] using hphase
  refine ⟨b,hb,?_⟩
  simp only [phase,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,heighth] at hphase'
  unfold cyclicOffset
  linear_combination -hphase'


#print axioms even_unit_two_fixed_next_phase
end LX.AnchoredPhases
