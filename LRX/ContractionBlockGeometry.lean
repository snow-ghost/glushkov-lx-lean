import LRX.ContractionSelectedArrows

namespace LRX.ContractionBlocks
variable {m k : ℕ}

theorem internal_path_successor (P : State m) (l : List (Fin m)) (hne : l ≠ [])
    (hnd : l.Nodup) (hc : l.IsChain (fun x y => P x=y)) (x : Fin m) (hx : x ∈ l)
    (hlast : x ≠ l.getLast hne) : P x ∈ l ∧ P x ≠ x := by
  induction l generalizing x with
  | nil => exact False.elim (hne rfl)
  | cons a rest ih =>
    cases rest with
    | nil =>
      have he : x=a := by simpa using hx
      subst x
      exact False.elim (hlast rfl)
    | cons b rest =>
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        have he : P a=b := (List.isChain_cons_cons.mp hc).1
        refine ⟨by simp [he],?_⟩
        intro h
        have hba : b=a := he.symm.trans h
        exact (List.nodup_cons.mp hnd).1 (by simp [hba])
      · have ht := ih (by simp) hnd.tail hc.tail x hx (by simpa using hlast)
        exact ⟨List.mem_cons_of_mem a ht.1,ht.2⟩

namespace System
variable {P : State m} {q : State k}

theorem selected_source_moved (B : System P q) (x : Fin m) (hx : x ∈ B.selected) : P x ≠ x := by
  obtain ⟨i,hi,hnot⟩ := (B.selected_iff_internal x).mp hx
  exact (internal_path_successor P (B.nodes i) (B.nonempty i) (B.nodup i) (B.chain i) x hi hnot).2

theorem selected_target_in_block (B : System P q) (i : Fin k) (x : Fin m)
    (hx : x ∈ B.nodes i) (hsel : x ∈ B.selected) : P x ∈ B.nodes i :=
  (internal_path_successor P (B.nodes i) (B.nonempty i) (B.nodup i) (B.chain i) x hx
    ((B.mem_selected x).mp hsel i)).1

/-- Cover and block ordering imply actual interval supports; no interval
assumption is added to the representation. -/
theorem block_interval (B : System P q) (i : Fin k) (x z y : Fin m)
    (hx : x ∈ B.nodes i) (hz : z ∈ B.nodes i) (hxy : x.val ≤ y.val) (hyz : y.val ≤ z.val) :
    y ∈ B.nodes i := by
  obtain ⟨j,hj⟩ := B.cover y
  have he : j=i := by
    by_contra h
    have hne : j.val ≠ i.val := fun he => h (Fin.ext he)
    by_cases hji : j.val < i.val
    · have hh := B.ordered j i hji y hj x hx
      omega
    · have hh := B.ordered i j (by omega) z hz y hj
      omega
  exact he ▸ hj

def Protected (B : System P q) (gap : ℕ) : Prop :=
  ∀ i, ∀ x ∈ B.nodes i, ∀ y ∈ B.nodes i, x.val ≤ gap ↔ y.val ≤ gap

theorem initial_protected (P : State m) (gap : ℕ) : (initial P).Protected gap := by
  intro i x hx y hy
  simp only [initial,List.mem_singleton] at hx hy
  subst x; subst y
  rfl

theorem contract_protected {q : State (k+1)} (B : System P q) (a : Fin (k+1))
    (hadj : |FiniteCuts.displacement q a|=1) (gap : ℕ) (hB : B.Protected gap)
    (hchosen : (B.lastLabel a).val ≤ gap ↔ (P (B.lastLabel a)).val ≤ gap) :
    (B.contract a hadj).Protected gap := by
  have he : P (B.lastLabel a)=B.firstLabel (q a) := B.edge a
  rw [he] at hchosen
  intro i x hx y hy
  change x ∈ mergeLists B.nodes a (q a) i at hx
  change y ∈ mergeLists B.nodes a (q a) i at hy
  by_cases hi : a.succAbove i=q a
  · simp only [mergeLists,if_pos hi,List.mem_append] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hB a x hx y hy
    · exact (hB a x hx (B.lastLabel a) (List.getLast_mem (B.nonempty a))).trans
        (hchosen.trans (hB (q a) (B.firstLabel (q a)) (List.head_mem (B.nonempty (q a))) y hy))
    · exact ((hB a y hy (B.lastLabel a) (List.getLast_mem (B.nonempty a))).trans
        (hchosen.trans (hB (q a) (B.firstLabel (q a)) (List.head_mem (B.nonempty (q a))) x hx))).symm
    · exact hB (q a) x hx y hy
  · simp only [mergeLists,if_neg hi] at hx hy
    exact hB (a.succAbove i) x hx y hy

#print axioms selected_target_in_block
#print axioms block_interval
#print axioms contract_protected
end System
end LRX.ContractionBlocks
