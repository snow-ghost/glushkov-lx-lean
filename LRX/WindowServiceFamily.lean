import LRX.WindowPeakService
import LRX.WindowComposition

/-! Assemble local cycles as exact ambient services without changing their
local prices. Products and integer displacement lists are retained explicitly. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem assemble_window_services (W : Window n b) (l : List (State b))
    (allowed : Fin n → Prop) (price : State b → ℤ)
    (havail : ∀ q ∈ l, ∃ a : ExactService n,
      allowed a.service.port ∧ a.service.target=(permutation W q)⁻¹ ∧
      a.displacement=FiniteCuts.displacement (permutation W q) ∧
      (BufferProgram.rotations a.service.word : ℤ)=price q) :
    ∃ services : List (ExactService n),
      services.map (fun a => a.service.target)=l.map (fun q => (permutation W q)⁻¹) ∧
      services.map ExactService.displacement=l.map (fun q => FiniteCuts.displacement (permutation W q)) ∧
      (∀ a ∈ services, allowed a.service.port) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=(l.map price).sum := by
  induction l with
  | nil => exact ⟨[],rfl,rfl,by simp,rfl⟩
  | cons q l ih =>
    obtain ⟨a,ha,ht,hd,hc⟩ := havail q (by simp)
    obtain ⟨ss,hst,hsd,hsp,hsc⟩ := ih (fun r hr => havail r (by simp [hr]))
    refine ⟨a::ss,?_,?_,?_,?_⟩
    · simp [ht,hst]
    · simp [hd,hsd]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact hsp c hc
    · simp [hc,hsc]

theorem left_window_family (hn : 2 ≤ n) (W : Window n b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (y : ℕ) (hy : y ≤ b)
    (hpos : ∀ q ∈ l, 0 < FiniteCuts.leftPeak q y) :
    ∃ services : List (ExactService n),
      services.map (fun a => a.service.target)=l.map (fun q => (permutation W q)⁻¹) ∧
      services.map ExactService.displacement=l.map (fun q => FiniteCuts.displacement (permutation W q)) ∧
      (∀ a ∈ services, W.offset ≤ a.service.port.val ∧ a.service.port.val+1 ≤ W.offset+y) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
        (l.map (fun q => (∑ i : Fin b, |FiniteCuts.displacement q i|)-2*(FiniteCuts.leftPeak q y : ℤ))).sum := by
  apply assemble_window_services W l
    (fun r => W.offset ≤ r.val ∧ r.val+1 ≤ W.offset+y)
    (fun q => (∑ i : Fin b, |FiniteCuts.displacement q i|)-2*(FiniteCuts.leftPeak q y : ℤ))
  intro q hq
  obtain ⟨a,hlo,hhi,ht,hd,hprice⟩ := left_peak_ambient_service hn W q (hcycles q hq) y hy (hpos q hq)
  exact ⟨a,⟨hlo,hhi⟩,ht,hd,hprice⟩

theorem right_window_family (hn : 2 ≤ n) (W : Window n b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (x : ℕ) (hx : x ≤ b)
    (hpos : ∀ q ∈ l, 0 < FiniteCuts.rightPeak q x) :
    ∃ services : List (ExactService n),
      services.map (fun a => a.service.target)=l.map (fun q => (permutation W q)⁻¹) ∧
      services.map ExactService.displacement=l.map (fun q => FiniteCuts.displacement (permutation W q)) ∧
      (∀ a ∈ services, W.offset+x ≤ a.service.port.val+1 ∧ a.service.port.val+1 < W.offset+b) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
        (l.map (fun q => (∑ i : Fin b, |FiniteCuts.displacement q i|)-2*(FiniteCuts.rightPeak q x : ℤ))).sum := by
  apply assemble_window_services W l
    (fun r => W.offset+x ≤ r.val+1 ∧ r.val+1 < W.offset+b)
    (fun q => (∑ i : Fin b, |FiniteCuts.displacement q i|)-2*(FiniteCuts.rightPeak q x : ℤ))
  intro q hq
  obtain ⟨a,hlo,hhi,ht,hd,hprice⟩ := right_peak_ambient_service hn W q (hcycles q hq) x hx (hpos q hq)
  exact ⟨a,⟨hlo,hhi⟩,ht,hd,hprice⟩

#print axioms left_window_family
#print axioms right_window_family
end LRX.FiniteWindow
