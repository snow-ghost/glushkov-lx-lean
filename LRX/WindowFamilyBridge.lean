import LRX.WindowServiceFamily
import LRX.CanonicalServiceFamily

/-! The window constructors satisfy the canonical-family and disjoint-target
contracts needed by periodic root composition. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem window_family_canonical (W : Window n b) (l : List (State b))
    (services : List (ExactService n))
    (ht : services.map (fun a => a.service.target)=l.map (fun q => (permutation W q)⁻¹))
    (hd : services.map ExactService.displacement=l.map (fun q => FiniteCuts.displacement (permutation W q))) :
    CanonicalFamily services := by
  apply List.map_inj_left.mp
  rw [hd]
  have h := congrArg (fun ps : List (State n) => ps.map (fun p => fun i : Fin n => (p.symm i : ℤ)-(i : ℤ))) ht
  unfold FiniteCuts.displacement
  simpa only [List.map_map,Function.comp_def,Equiv.Perm.inv_def,Equiv.symm_symm] using h.symm

theorem window_family_disjoint (W : Window n b) (l : List (State b))
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (services : List (ExactService n))
    (ht : services.map (fun a => a.service.target)=l.map (fun q => (permutation W q)⁻¹)) :
    services.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
  apply List.pairwise_map.mp
  rw [ht]
  exact List.pairwise_map.mpr (hdis.imp (fun h => (permutation_disjoint W _ _ h).inv_left.inv_right))

theorem window_family_mass (W : Window n b) (l : List (State b))
    (services : List (ExactService n))
    (hd : services.map ExactService.displacement=l.map (fun q => FiniteCuts.displacement (permutation W q))) :
    (services.map (fun a => ∑ i : Fin n, |a.displacement i|)).sum=
      (l.map (fun q => ∑ i : Fin b, |FiniteCuts.displacement q i|)).sum := by
  have h := congrArg (fun ds : List (Fin n → ℤ) => (ds.map (fun d => ∑ i : Fin n, |d i|)).sum) hd
  simpa only [List.map_map,Function.comp_def,displacement_mass] using h

omit [NeZero n] in
theorem sum_price {α : Type*} (l : List α) (mass peak : α → ℤ) :
    (l.map (fun a => mass a-2*peak a)).sum=(l.map mass).sum-2*(l.map peak).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

#print axioms window_family_canonical
#print axioms window_family_disjoint
#print axioms window_family_mass
end LRX.FiniteWindow
