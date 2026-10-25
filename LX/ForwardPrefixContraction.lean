import LX.FiniteChainMerge
import Mathlib

namespace LX.FiniteDropBudget
open scoped BigOperators
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

def ForwardPrefix (p : LRX.State n) (r : ℕ) : Prop :=
  ∀ i : Fin n,i.val < r → i.val ≤ (p i).val ∧
    ∀ j : Fin n,i.val < j.val → j.val < (p i).val → p j=j

theorem head_merge_forward_prefix (p : LRX.State n) (r : ℕ)
    (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0) (hb : (p 0).val < r) :
    ForwardPrefix (p*Equiv.swap 0 (p 0)) r := by
  let b := p 0
  let q := p*Equiv.swap 0 b
  have hb0 : 0 < b.val := Fin.pos_iff_ne_zero.mpr hhead
  have hr : 0 < r := by omega
  have hnext : b.val < (p b).val := by
    have hh := (hp b hb).1
    have hn : p b ≠ b := by intro he; exact hhead (p.injective he)
    have hn' : (p b).val ≠ b.val := fun he => hn (Fin.ext he)
    omega
  have hq0 : q 0=p b := by simp [q]
  have hqb : q b=b := by simp [q,b]
  have hqi (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : q i=p i := by
    simp only [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib]
  intro i hir
  change i.val ≤ (q i).val ∧ _
  by_cases hi0 : i=0
  · subst i
    rw [hq0]
    refine ⟨by simp,?_⟩
    intro j hj0 hjn
    have hj0' : j ≠ 0 := Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hj0)
    by_cases hjb : j=b
    · exact hjb ▸ hqb
    rw [hqi j hj0' hjb]
    by_cases hjlt : j.val < b.val
    · exact (hp 0 (by simpa using hr)).2 j hj0 hjlt
    · have hjne : j.val ≠ b.val := fun he => hjb (Fin.ext he)
      exact (hp b hb).2 j (by omega) hjn
  by_cases hib : i=b
  · subst i
    rw [hqb]
    exact ⟨le_rfl,fun j h1 h2 => by omega⟩
  rw [hqi i hi0 hib]
  refine ⟨(hp i hir).1,?_⟩
  intro j hij hjp
  have hj0 : j ≠ 0 := by intro he; subst j; simp at hij
  by_cases hjb : j=b
  · exact hjb ▸ hqb
  rw [hqi j hj0 hjb]
  exact (hp i hir).2 j hij hjp

/-- An ascending prefix chain can be merged into the head. All its other
vertices become fixed, without increasing mass minus inversions. -/
theorem contract_forward_prefix (p : LRX.State n) (r : ℕ) (hr : 0 < r)
    (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0) :
    ∃ q : LRX.State n,
      (∀ i : Fin n,0 < i.val → i.val < r → q i=i) ∧
      ForwardPrefix q r ∧ q 0 ≠ 0 ∧
      descendingPositions q=descendingPositions p ∧ backwardUnits q=backwardUnits p ∧
      (∑ i, |displacement q i|)-(inversionNumber q : ℤ) ≤
        (∑ i, |displacement p i|)-(inversionNumber p : ℤ) := by
  generalize he : n-(p 0).val=k
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    by_cases hb : r ≤ (p 0).val
    · refine ⟨p,?_,hp,hhead,rfl,rfl,le_rfl⟩
      intro i hi0 hir
      exact (hp 0 (by simpa using hr)).2 i (by simpa using hi0) (by omega)
    let b := p 0
    have hbpos : 0 < b.val := Fin.pos_iff_ne_zero.mpr hhead
    have hbr : b.val < r := by omega
    have hnext : b.val < (p b).val := by
      have hh := (hp b hbr).1
      have hn : p b ≠ b := by intro he; exact hhead (p.injective he)
      have hn' : (p b).val ≠ b.val := fun he => hn (Fin.ext he)
      omega
    let t := p*Equiv.swap 0 b
    have ht0 : t 0=p b := by simp [t]
    have htpre : ForwardPrefix t r := head_merge_forward_prefix p r hp hhead hbr
    have hthead : t 0 ≠ 0 := by
      intro hz
      have hv := congrArg Fin.val hz
      rw [ht0,Fin.val_zero] at hv
      exact (Nat.ne_of_gt (lt_trans hbpos hnext)) hv
    have hk : n-(t 0).val < k := by rw [ht0]; have := (p b).isLt; omega
    obtain ⟨q,hqfix,hqpre,hqhead,hqd,hqu,hqcost⟩ :=
      ih (n-(t 0).val) hk t htpre hthead rfl
    have htd := head_merge_drops p b hbpos rfl hnext
    have htm := head_merge_mass p b hbpos rfl hnext
    have hti := head_merge_inversions p b hbpos rfl hnext
      (fun j hj0 hjb => (hp 0 (by simpa using hr)).2 j (by simpa using hj0) hjb)
    refine ⟨q,hqfix,hqpre,hqhead,hqd.trans htd.1,hqu.trans htd.2,?_⟩
    change (∑ i, |displacement t i|)=_ at htm
    change inversionNumber t=inversionNumber p+1 at hti
    rw [htm,hti] at hqcost
    push_cast at hqcost
    omega

#print axioms head_merge_forward_prefix
#print axioms contract_forward_prefix
end LX.FiniteDropBudget
