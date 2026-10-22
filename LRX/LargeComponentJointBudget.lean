import LRX.JointInternalExternalBudget
import LRX.ComponentCutExtraction

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- Joint reserve at the actual large component's cut, charged to the original
permutation. Neither a supplied cut nor majorization of the completion is used. -/
theorem large_component_joint_budget (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (a : Fin n)
    (hlarge : (n+1)/2 < (componentSet p a).card) :
    let r := componentLeft p a
    let q := (localTarget p 0 r).symm
    let L := (componentSet p a).card
    ∀ (As : List (FillingWindow n)),
      (∀ A ∈ As, A.Matches q) → As.Pairwise FillingWindow.Apart →
      (∀ A ∈ As, A.window.offset + A.size ≤ L) →
      (∀ A ∈ As, ∃ s : Fin n, s.val+1 = A.window.offset ∧
        0 < portLoad (displacement q) s) →
      ∃ f : State (n-L),
        (∀ i, q (embed (⟨L,by have := Finset.card_le_univ (componentSet p a); simp only [Fintype.card_fin] at this; omega⟩ : Window n (n-L)) i) =
          embed (⟨L,by have := Finset.card_le_univ (componentSet p a); simp only [Fintype.card_fin] at this; omega⟩ : Window n (n-L)) (f i)) ∧
        (As.map FillingWindow.deficit).sum + ((n-L).choose 2 : ℤ) -
          (inversionNumber f : ℤ) + 1 ≤
          ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  dsimp only
  intro As hmatch hapart hinside hboundary
  let r := componentLeft p a
  let q := localTarget p 0 r
  let L := (componentSet p a).card
  have hLn : L ≤ n := by
    have h := Finset.card_le_univ (componentSet p a)
    simpa only [Fintype.card_fin] using h
  obtain ⟨hcut,hcards⟩ := component_recenter_cut p a
  have hcut' : ∀ i : Fin n, (q.symm i).val < L ↔ i.val < L :=
    invariant_cut_inverse q L hcut
  have hz := component_left_port_zero p a
  have hr : componentLeft p a - 1 + 1 = r := by dsimp [r]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 (componentLeft p a-1) hd hmaj hz
  rw [hr] at hqm
  have hc : (componentSet q (a-r)).card = L := by
    have h := hcards (a-r)
    simpa only [r,q,L,sub_add_cancel] using h
  have hlargeq : n-n/2 < (CycleFootprint.component (displacement q.symm) (a-r)).card := by
    change n-n/2 < (componentSet q (a-r)).card
    rw [hc]
    change n-n/2 < (componentSet p a).card
    omega
  have hi := inversion_number_zero_recenter p (componentLeft p a-1) hz
  rw [hr] at hi
  have hI : inversionNumber q.symm = inversionNumber p := by
    exact (inversion_number_inverse q).trans hi
  obtain ⟨f,hf,hbudget⟩ := joint_internal_external_strict_budget hn q.symm L hLn hlarge
    hcut' As hmatch hapart hinside hboundary hqm (a-r) hlargeq
  rw [hI] at hbudget
  exact ⟨f,hf,hbudget⟩

#print axioms large_component_joint_budget
end LRX.FiniteCuts
