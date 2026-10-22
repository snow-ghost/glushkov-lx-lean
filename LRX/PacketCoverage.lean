import LRX.PrunedReachability

/-! A root packet may contain several cycles. Every child is reached directly
from the strongly connected core, followed by movement inside its own cycle. -/
namespace LRX.PrunedLift
variable {n : ℕ}

abbrev Reaches (p : State n) (d : Fin n → ℤ) := Relation.ReflTransGen (BufferProgram.ServiceEdge p d)

def PacketCover (p : State n) (d : Fin n → ℤ) (root : Fin n) : Prop :=
  ∀ i, d i ≠ 0 → ∃ a j,
    Reaches p d root a ∧ Reaches p d a root ∧
    BufferProgram.ServiceEdge p d a j ∧ (p⁻¹).SameCycle j i

def KeepsCore (p : State n) (d : Fin n → ℤ) (root : Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ a, Reaches p d root a → Reaches p d a root → a ∈ S

theorem root_star_packet_cover (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (hstar : RootStar p d root) : PacketCover p d root := by
  intro i hi
  obtain ⟨a,j,ha,he,hj⟩ := hstar i hi
  exact ⟨a,j,Relation.ReflTransGen.single (Or.inl ha),
    Relation.ReflTransGen.single (Or.inl ha.symm),he,hj⟩

theorem retain_core_path (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hcore : KeepsCore p d root S)
    (a : Fin n) (ha : Reaches p d root a) {b : Fin n} (hab : Reaches p d a b) :
    Reaches p d b root → Reaches (permutation p S hS) (displacement S d) a b := by
  induction hab with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hpath hedge ih =>
    intro hback
    have hb : Reaches p d b root := (Relation.ReflTransGen.single hedge).trans hback
    have hbS := hcore b (ha.trans hpath) hb
    have hcS := hcore c (ha.trans (hpath.tail hedge)) hback
    exact (ih hb).tail (service_edge p d S hS hbS hcS hedge)

theorem packet_cover_pruned (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (hcover : PacketCover p d root) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hcore : KeepsCore p d root S) :
    PacketCover (permutation p S hS) (displacement S d) root := by
  intro i hi
  have hiS : i ∈ S := by by_contra h; exact hi (by simp [displacement,h])
  have hdi : d i ≠ 0 := by simpa [displacement,hiS] using hi
  obtain ⟨a,j,hra,har,he,hj⟩ := hcover i hdi
  have haS := hcore a hra har
  have hjS := same_cycle_mem p S hS hiS hj.symm
  refine ⟨a,j,?_,?_,service_edge p d S hS haS hjS he,same_cycle p S hS hjS hj⟩
  · exact retain_core_path p d root S hS hcore root Relation.ReflTransGen.refl hra har
  · exact retain_core_path p d root S hS hcore a hra har Relation.ReflTransGen.refl

theorem packet_cover_reaches (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (hcover : PacketCover p d root) (i : Fin n) (hi : d i ≠ 0) : Reaches p d root i := by
  obtain ⟨a,j,hra,_,he,hj⟩ := hcover i hi
  exact (hra.tail he).tail (Or.inl hj)

#print axioms retain_core_path
#print axioms packet_cover_pruned
#print axioms packet_cover_reaches
end LRX.PrunedLift
