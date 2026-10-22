import LRX.TwoBlockSharpPayment
import LRX.InvariantCutRecenter
import LRX.FiniteComponentExtrema
import LRX.FiniteInversionBalance

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- An inversion cannot cross a zero-load cut. -/
theorem inversion_load_path (p : State n) (i j : Fin n)
    (hij : i.val < j.val) (hp : (p j).val < (p i).val) :
    CycleFootprint.LoadPath (displacement p.symm) i j := by
  have hpos (r : Fin n) (hi : i.val ≤ r.val) (hj : r.val < j.val) :
      0 < portLoad (displacement p.symm) r := by
    have hn := port_load_nonneg (displacement p.symm) r
    by_contra h
    have hz : portLoad (displacement p.symm) r = 0 := by omega
    have hc := zero_port_invariant_cut p r hz
    have hpi := (hc i).mpr (by omega)
    have hpj := (hc j).not.mpr (by omega)
    omega
  have hpath := CycleFootprint.integer_load_path (displacement p.symm)
    (i : ℤ) (j : ℤ) (by exact_mod_cast hij.le) (by
      intro z hi hj
      have hz0 : 0 ≤ z := le_trans (by positivity) hi
      have hzn : z < n := lt_trans hj (by exact_mod_cast j.isLt)
      have hv : ((z : Fin n).val : ℤ) = z := by
        simp only [Fin.val_intCast]
        rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_eq_of_lt hz0 hzn]
      exact hpos (z : Fin n) (by omega) (by omega))
  simpa only [Int.cast_natCast, Fin.cast_val_eq_self] using hpath

/-- Incident inversions use distinct other vertices of the same component. -/
theorem inversion_incidence_le_component (p : State n) (i : Fin n) :
    (∑ j, (inversionIndicator p i j + inversionIndicator p j i)) ≤
      ((componentSet p i).card : ℤ) - 1 := by
  classical
  let S := (componentSet p i).erase i
  have hpoint (j : Fin n) :
      inversionIndicator p i j + inversionIndicator p j i ≤
        if j ∈ S then (1 : ℤ) else 0 := by
    have hm (h : i.val < j.val ∧ (p j).val < (p i).val) : j ∈ S := by
      exact Finset.mem_erase.mpr ⟨by intro he; subst j; omega,
        (CycleFootprint.mem_component _ _ _).mpr (inversion_load_path p i j h.1 h.2)⟩
    have hm' (h : j.val < i.val ∧ (p i).val < (p j).val) : j ∈ S := by
      exact Finset.mem_erase.mpr ⟨by intro he; subst j; omega,
        (CycleFootprint.mem_component _ _ _).mpr
          (CycleFootprint.load_path_symm _ (inversion_load_path p j i h.1 h.2))⟩
    unfold inversionIndicator
    split_ifs <;> simp_all <;> omega
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hi : i ∈ componentSet p i :=
    (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
  have hc : S.card + 1 = (componentSet p i).card :=
    Finset.card_erase_add_one hi
  have he : (∑ j : Fin n, if j ∈ S then (1 : ℤ) else 0) = (S.card : ℤ) := by
    simp
  rw [he] at hs
  have hc' : (S.card : ℤ) + 1 = ((componentSet p i).card : ℤ) := by exact_mod_cast hc
  omega

/-- A component size cap gives the inversion budget needed by the two-block route. -/
theorem inversion_budget_of_component_cap (p : State n) (L : ℕ)
    (hcap : ∀ i, (componentSet p i).card ≤ L) :
    2 * (inversionNumber p : ℤ) ≤ (n : ℤ) * ((L : ℤ) - 1) := by
  have hrow (i : Fin n) :
      (∑ j, (inversionIndicator p i j + inversionIndicator p j i)) ≤ (L : ℤ) - 1 := by
    have h := inversion_incidence_le_component p i
    have hc : ((componentSet p i).card : ℤ) ≤ L := by exact_mod_cast hcap i
    omega
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_add_distrib] at h
  have he : (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p j i) =
      (∑ i : Fin n, ∑ j : Fin n, inversionIndicator p i j) := Finset.sum_comm
  rw [he, sum_inversion_indicator] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← two_mul] using h

/-- Actual component sizes discharge the incidence premise of the sharp word. -/
theorem two_block_sharp_word_of_component_cap (a : ℕ) (ha : 2 ≤ a)
    (ham : a ≤ n / 2) (p : State n)
    (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a)
    (hcap : ∀ i, (componentSet p i).card ≤ a) (start finish : Fin n) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹ * p * rotation finish ∧
      w.length ≤ n.choose 2 := by
  exact two_block_sharp_word_of_incidence_bound a ha ham p hcut
    (inversion_budget_of_component_cap p a hcap) start finish

#print axioms two_block_sharp_word_of_component_cap
#print axioms inversion_load_path
#print axioms inversion_incidence_le_component
#print axioms inversion_budget_of_component_cap
end LRX.FiniteCuts
