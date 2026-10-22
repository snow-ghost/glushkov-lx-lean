import LRX.JointReversalBudget
import LRX.PositiveWindowWidth
import LRX.FiniteWindowRestriction

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n : ℕ} [NeZero n]

/-- Actual positive boundary loads supply every internal width bound. -/
theorem joint_positive_windows_strict_budget (hn : 2 ≤ n)
    (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p)
    (hapart : As.Pairwise FillingWindow.Apart)
    (hboundary : ∀ A ∈ As, ∃ r : Fin n,
      r.val+1 = A.window.offset ∧ 0 < portLoad (displacement p) r)
    (hmaj : AffineLift.Majorized (displacement p))
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component (displacement p) a).card) :
    (As.map FillingWindow.deficit).sum + 1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  apply joint_reversal_strict_inversion_budget hn As p hmatch hapart ?_ hmaj a hlarge
  intro A hA
  obtain ⟨r,hr,hpos⟩ := hboundary A hA
  have hw := positive_boundary_window_width A.window p A.filling (hmatch A hA)
    (FiniteWindow.majorized_short (canonical_lift p) hmaj) r hr hpos
  omega

/-- Reverse the external invariant interval together with all given internal
fillings. Its filling and all width bounds are extracted from the input. -/
theorem joint_internal_external_strict_budget (hn : 2 ≤ n)
    (p : State n) (L : ℕ) (hLn : L ≤ n) (hL : (n+1)/2 < L)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L)
    (As : List (FillingWindow n))
    (hmatch : ∀ A ∈ As, A.Matches p)
    (hapart : As.Pairwise FillingWindow.Apart)
    (hinside : ∀ A ∈ As, A.window.offset + A.size ≤ L)
    (hboundary : ∀ A ∈ As, ∃ r : Fin n,
      r.val+1 = A.window.offset ∧ 0 < portLoad (displacement p) r)
    (hmaj : AffineLift.Majorized (displacement p))
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component (displacement p) a).card) :
    ∃ f : State (n-L),
      (∀ i, p (embed (⟨L,by omega⟩ : Window n (n-L)) i) =
        embed (⟨L,by omega⟩ : Window n (n-L)) (f i)) ∧
      (As.map FillingWindow.deficit).sum + ((n-L).choose 2 : ℤ) -
        (inversionNumber f : ℤ) + 1 ≤
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let W : Window n (n-L) := ⟨L,by omega⟩
  have hc (i : Fin n) (hi : Contains W i) : Contains W (p i) := by
    have hh := hcut i
    have hn' := (p i).isLt
    change L ≤ i.val ∧ i.val < L+(n-L) at hi
    change L ≤ (p i).val ∧ (p i).val < L+(n-L)
    constructor <;> omega
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed W p.symm
    (by simpa only [Equiv.symm_symm] using hc)
  simp only [Equiv.symm_symm] at hf
  let E : FillingWindow n := ⟨n-L,W,f⟩
  have hm : ∀ A ∈ E :: As, A.Matches p := by
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hf
    · exact hmatch A hA
  have hd : (E :: As).Pairwise FillingWindow.Apart := by
    apply List.pairwise_cons.mpr
    refine ⟨?_,hapart⟩
    intro A hA i hi hAi
    have hin := hinside A hA
    change L ≤ i.val ∧ i.val < L+(n-L) at hi
    change A.window.offset ≤ i.val ∧ i.val < A.window.offset+A.size at hAi
    omega
  have hw : ∀ A ∈ E :: As, A.size ≤ (n-1)/2 := by
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · change n-L ≤ (n-1)/2
      omega
    · obtain ⟨r,hr,hpos⟩ := hboundary A hA
      have hh := positive_boundary_window_width A.window p A.filling (hmatch A hA)
        (FiniteWindow.majorized_short (canonical_lift p) hmaj) r hr hpos
      omega
  have hbudget := joint_reversal_strict_inversion_budget hn (E :: As) p hm hd hw hmaj a hlarge
  simp only [List.map_cons,List.sum_cons] at hbudget
  have he : E.deficit = ((n-L).choose 2 : ℤ) - (inversionNumber f : ℤ) := rfl
  rw [he] at hbudget
  exact ⟨f,hf,by omega⟩

#print axioms joint_positive_windows_strict_budget
#print axioms joint_internal_external_strict_budget
end LRX.FiniteWindow
