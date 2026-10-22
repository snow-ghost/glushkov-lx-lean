import LRX.FiniteWindowLoad
import LRX.ShortShallowCycleNeighbor

namespace LRX.FiniteWindow
variable {n b : ℕ}

theorem permutation_support (W : Window n b) (p : State b) :
    (permutation W p).support=p.support.image (embed W) := by
  classical
  ext j
  constructor
  · intro hj
    have hcontains : Contains W j := by
      by_contra hout
      exact (Equiv.Perm.mem_support.mp hj) (permutation_outside W p j hout)
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp hcontains
    apply Finset.mem_image.mpr
    refine ⟨i,?_,rfl⟩
    apply Equiv.Perm.mem_support.mpr
    intro hi
    apply (Equiv.Perm.mem_support.mp hj)
    rw [permutation_embed,hi]
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    apply Equiv.Perm.mem_support.mpr
    rw [permutation_embed]
    intro h
    exact (Equiv.Perm.mem_support.mp hi) (embed_injective W h)

theorem permutation_support_card (W : Window n b) (p : State b) :
    (permutation W p).support.card=p.support.card := by
  rw [permutation_support,Finset.card_image_of_injective _ (embed_injective W)]

/-- A neighboring arrow found in a padded window belongs to the original
cycle, and its rank adjacency pulls back through the increasing embedding. -/
theorem neighbor_pullback (W : Window n b) (p : State b)
    (h : ∃ x y, ZeroGap.RankAdjacent (permutation W p).support x y ∧ permutation W p x=y) :
    ∃ x y, ZeroGap.RankAdjacent p.support x y ∧ p x=y := by
  classical
  obtain ⟨x,y,hxy,hp⟩ := h
  have hx : x ∈ p.support.image (embed W) := by rw [← permutation_support]; exact hxy.1
  have hy : y ∈ p.support.image (embed W) := by rw [← permutation_support]; exact hxy.2.1
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
  refine ⟨a,c,⟨ha,hc,?_,?_⟩,?_⟩
  · intro he
    exact hxy.2.2.1 (congrArg (embed W) he)
  · intro z hz hbetween
    have hmem : embed W z ∈ (permutation W p).support := by
      rw [permutation_support]
      exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
    apply hxy.2.2.2 (embed W z) hmem
    dsimp [embed]
    omega
  · rw [permutation_embed] at hp
    exact embed_injective W hp

#print axioms permutation_support_card
#print axioms neighbor_pullback
end LRX.FiniteWindow
