import LX.DepthBound
import LRX.StrictBandInversionCapacity

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- One concrete phase candidate for each original position. -/
def permutation (p : State n) (a : Fin n) : State n :=
  p.trans (Equiv.addRight (a-p a))

def height (p : State n) (a : Fin n) : ℕ := (descendingPositions (permutation p a)).card

def displacement (p : State n) (a i : Fin n) : ℤ :=
  clockwiseRepresentative (permutation p a) i - (i : ℤ) - height p a

def phase (p : State n) (a : Fin n) : ℤ := (a : ℤ)-(p a : ℤ)-height p a

theorem permutation_anchor (p : State n) (a : Fin n) : permutation p a a = a := by
  simp [permutation]

theorem displacement_balance (p : State n) (a : Fin n) : ∑ i, displacement p a i = 0 := by
  unfold displacement
  rw [Finset.sum_sub_distrib, clockwise_representative_mass]
  simp [height]

theorem displacement_band (p : State n) (a i : Fin n) :
    0 ≤ displacement p a i + height p a ∧ displacement p a i + height p a < (n : ℤ) := by
  have h := clockwise_representative_bounds (permutation p a) i
  unfold displacement
  omega

theorem displacement_anchor (p : State n) (a : Fin n) :
    displacement p a a = -(height p a : ℤ) := by
  simp [displacement, clockwiseRepresentative, permutation_anchor]

theorem height_lt (p : State n) (a : Fin n) : height p a < n := by
  have hs : descendingPositions (permutation p a) ⊆ Finset.univ.erase a := by
    intro i hi
    have hneq : i ≠ a := by
      intro he
      subst i
      simpa [permutation_anchor] using hi
    simp [Finset.mem_erase, hneq]
  have h := Finset.card_le_card hs
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at h
  change height p a ≤ n-1 at h
  have := NeZero.pos n
  omega

/-- The candidate is a balanced lift of the original permutation, not an abstract strip. -/
theorem is_lift (p : State n) (a : Fin n) :
    LRX.AffineLift.IsLift p.symm (phase p a) (displacement p a) := by
  refine ⟨displacement_balance p a, ?_⟩
  intro i
  have hq : Int.ModEq (n : ℤ) (permutation p a i : ℤ)
      ((p i : ℤ)+(a : ℤ)-(p a : ℤ)) := by
    apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp [permutation, Int.cast_sub, Int.cast_add, add_sub_assoc]
  have hm := ((clockwise_representative_modEq (permutation p a) i).trans hq).sub_right (height p a : ℤ)
  change Int.ModEq (n : ℤ) ((i : ℤ)+displacement p a i) ((p i : ℤ)+phase p a)
  convert hm using 1 <;> simp only [displacement, phase] <;> ring

/-- The same height controls the exchanges and the largest number of backward moves. -/
theorem candidate_price_components (p : State n) (a : Fin n) :
    (inversions (displacement p a) : ℤ) ≤ (height p a : ℤ)*(n-height p a-1) ∧
      ∀ i, (backwardDepth (displacement p a) i : ℤ) ≤ height p a := by
  constructor
  · have h := shifted_lift_inversion_capacity (is_lift p a) (height p a : ℤ) (displacement_band p a)
    exact h
  · intro i
    apply backward_depth_le_strip (is_lift p a) (height p a : ℤ)
    intro j
    have h := (displacement_band p a j).1
    omega

theorem candidate_sorting_word (hn : 2 ≤ n) (p : State n) (a : Fin n) :
    ∃ w : List Letter, ScanTrace (displacement p a) w ∧
      p * eval (paidWord (phase p a : Fin n) w) = 1 := by
  exact exists_realized_scan hn p (phase p a) (displacement p a) (is_lift p a)

/-- Every balanced lift of width less than n is recovered by anchoring a minimum coordinate. -/
theorem recovers_strict_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p.symm c d) (a : Fin n)
    (hmin : ∀ i, d a ≤ d i) (hwidth : ∀ i, d i-d a < (n : ℤ)) :
    displacement p a = d ∧ (phase p a : Fin n) = (c : Fin n) := by
  let g : Fin n → ℤ := fun i => (i : ℤ)+d i-d a
  have hphase : (c : Fin n)-(d a : Fin n)=a-p a := by
    have hh := LRX.AffineLift.lift_residue hd a
    simp only [Equiv.symm_symm] at hh
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using hh.symm
  have hmod (i : Fin n) : Int.ModEq (n : ℤ) (g i) (permutation p a i : ℤ) := by
    apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
    have hh := LRX.AffineLift.lift_residue hd i
    simp only [Equiv.symm_symm] at hh
    simp only [g, Int.cast_sub, Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self]
    rw [hh]
    change p i+(c : Fin n)-(d a : Fin n)=p i+(a-p a)
    linear_combination hphase
  have hg : g=clockwiseRepresentative (permutation p a) :=
    clockwise_representative_unique _ g (fun i => by dsimp [g]; have := hmin i; have := hwidth i; omega) hmod
  have hm := clockwise_representative_mass (permutation p a)
  rw [← hg] at hm
  have hsum : (∑ i : Fin n, (g i-(i : ℤ))) = -(n : ℤ)*d a := by
    have he (i : Fin n) : g i-(i : ℤ)=d i-d a := by dsimp [g]; ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, hd.1]
    simp
  rw [hsum] at hm
  have hheight : (height p a : ℤ) = -d a := by
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    apply mul_left_cancel₀ hnz
    change (n : ℤ)*(height p a : ℤ)=(n : ℤ)*(-d a)
    change -(n : ℤ)*d a=(n : ℤ)*(height p a : ℤ) at hm
    nlinarith
  have he : displacement p a=d := by
    funext i
    simp only [displacement, ← hg, hheight, g]
    ring
  refine ⟨he, ?_⟩
  have hnew := LRX.AffineLift.lift_residue (is_lift p a) a
  have hold := LRX.AffineLift.lift_residue hd a
  simp only [Equiv.symm_symm, he] at hnew hold
  exact add_left_cancel (hnew.symm.trans hold)

/-- The finite candidate family contains an actual globally majorized short lift. -/
theorem exists_short_candidate (p : State n) : ∃ a : Fin n,
    LRX.AffineLift.Majorized (displacement p a) ∧
      (∀ i, 2*|displacement p a i| ≤ (n : ℤ)-1) ∧
      height p a ≤ (n-1)/2 := by
  obtain ⟨c,d,hd,hm,hshort,hwidth,_⟩ := LRX.AffineLift.exists_short_lift (NeZero.pos n) p.symm
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) d
    ⟨0, Finset.mem_univ _⟩
  have hmin (i : Fin n) := ha i (Finset.mem_univ _)
  have he := (recovers_strict_strip hd a hmin (fun i => by have := hwidth i a; omega)).1
  refine ⟨a, ?_, ?_, ?_⟩
  · rwa [he]
  · rwa [he]
  · have hh := hshort a
    have hanchor := displacement_anchor p a
    rw [he] at hanchor
    rw [hanchor, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at hh
    omega

#print axioms is_lift
#print axioms candidate_price_components
#print axioms candidate_sorting_word
#print axioms recovers_strict_strip
#print axioms exists_short_candidate
end LX.AnchoredPhases
