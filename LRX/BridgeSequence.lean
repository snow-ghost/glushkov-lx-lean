import LRX.OrderedComponentBridges

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def bridgeSequence (p : State n) : List (Fin n × Fin n) → State n
  | [] => p
  | uv::rest => bridgeSequence (componentBridge p uv.1 uv.2) rest

def bridgeBudget (xs : List (Fin n × Fin n)) : ℕ := (xs.map (fun uv => uv.2.val-uv.1.val)).sum

def SeparatedBridges (xs : List (Fin n × Fin n)) : Prop :=
  xs.Pairwise (fun uv xy => uv.2.val < xy.1.val)

theorem valid_bridge_after_left (p : State n) (uv xy : Fin n × Fin n)
    (huv : uv.1.val < uv.2.val) (hxy : ValidBridge p xy) (hsep : uv.2.val < xy.1.val) :
    ValidBridge (componentBridge p uv.1 uv.2) xy := by
  obtain ⟨horder,ha,hb,hgap⟩ := hxy
  have hxu : xy.1 ≠ uv.1 := by intro he; have := congrArg Fin.val he; omega
  have hxv : xy.1 ≠ uv.2 := by intro he; have := congrArg Fin.val he; omega
  have hyu : xy.2 ≠ uv.1 := by intro he; have := congrArg Fin.val he; omega
  have hyv : xy.2 ≠ uv.2 := by intro he; have := congrArg Fin.val he; omega
  refine ⟨horder,?_,?_,?_⟩
  · simpa only [component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hxu hxv] using ha
  · simpa only [component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hyu hyv] using hb
  · intro x hlo hhi
    have hxu' : x ≠ uv.1 := by intro he; have := congrArg Fin.val he; omega
    have hxv' : x ≠ uv.2 := by intro he; have := congrArg Fin.val he; omega
    simp only [componentBridge,Equiv.Perm.mul_apply,hgap x hlo hhi,
      Equiv.swap_apply_of_ne_of_ne hxu' hxv']

theorem valid_bridge_tail (p : State n) (uv : Fin n × Fin n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ uv::xs, ValidBridge p xy) (hs : SeparatedBridges (uv::xs)) :
    ∀ xy ∈ xs, ValidBridge (componentBridge p uv.1 uv.2) xy := by
  intro xy hxy
  exact valid_bridge_after_left p uv xy (hv uv (by simp)).1
    (hv xy (List.mem_cons_of_mem _ hxy)) ((List.pairwise_cons.mp hs).1 xy hxy)

theorem bridge_sequence_inverse_outside (p : State n) (xs : List (Fin n × Fin n))
    (x : Fin n) (hout : ∀ uv ∈ xs, x ≠ uv.1 ∧ x ≠ uv.2) :
    (bridgeSequence p xs).symm x=p.symm x := by
  induction xs generalizing p with
  | nil => rfl
  | cons uv xs ih =>
    rw [bridgeSequence,ih _ (fun xy hxy => hout xy (List.mem_cons_of_mem _ hxy)),
      component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne (hout uv (by simp)).1 (hout uv (by simp)).2]

theorem bridge_sequence_prices (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs) :
    FiniteRankOrder.Below p (bridgeSequence p xs) ∧
    (∑ i, |displacement (bridgeSequence p xs).symm i|)=
      (∑ i, |displacement p.symm i|)+2*(bridgeBudget xs : ℤ) ∧
    inversionNumber (bridgeSequence p xs)+xs.length=inversionNumber p+2*bridgeBudget xs := by
  induction xs generalizing p with
  | nil => exact ⟨FiniteRankOrder.below_refl _,by simp [bridgeSequence,bridgeBudget],by simp [bridgeSequence,bridgeBudget]⟩
  | cons uv xs ih =>
    obtain ⟨horder,ha,hb,hgap⟩ := hv uv (by simp)
    obtain ⟨hrank,hmass,hinv⟩ := ih (componentBridge p uv.1 uv.2) (valid_bridge_tail p uv xs hv hs)
      (List.pairwise_cons.mp hs).2
    have hbr := component_bridge_rank p uv.1 uv.2 horder (by omega)
    have hbm := component_bridge_mass p uv.1 uv.2 horder (le_of_lt ha) (le_of_lt hb)
    have hbi := component_bridge_inversions p uv.1 uv.2 horder (le_of_lt ha) (le_of_lt hb) hgap
    refine ⟨FiniteRankOrder.below_trans hbr hrank,?_,?_⟩
    · change (∑ i, |displacement (bridgeSequence (componentBridge p uv.1 uv.2) xs).symm i|)=_
      rw [hbm] at hmass
      have hw : ((uv.2.val-uv.1.val : ℕ) : ℤ)=(uv.2 : ℤ)-(uv.1 : ℤ) := Nat.cast_sub (le_of_lt horder)
      simp only [bridgeBudget,List.map_cons,List.sum_cons,Nat.cast_add] at hmass ⊢
      omega
    · change inversionNumber (bridgeSequence (componentBridge p uv.1 uv.2) xs)+(uv::xs).length=_
      simp only [bridgeBudget,List.map_cons,List.sum_cons,List.length_cons] at hinv ⊢
      omega

#print axioms bridge_sequence_inverse_outside
#print axioms bridge_sequence_prices
end LRX.FiniteCuts
