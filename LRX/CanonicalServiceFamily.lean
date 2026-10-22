import LRX.SelectedPartService
import LRX.FiniteDisplacementSum
import LRX.FiniteCycleScan

/-! Canonical disjoint services have the canonical displacement and mass of
their product. These identities join finite children to a periodic root. -/
namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def CanonicalFamily (services : List (ExactService n)) : Prop :=
  ∀ a ∈ services, a.displacement=(fun i => (a.service.target.symm i : ℤ)-(i : ℤ))

theorem canonical_family_displacement (services : List (ExactService n))
    (hd : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services) (i : Fin n) :
    (services.map (fun (a : ExactService n) => a.displacement i)).sum=
      (((services.map (fun (a : ExactService n) => a.service.target)).prod.symm i : ℤ)-(i : ℤ)) := by
  let targets := services.map (fun (a : ExactService n) => a.service.target)
  have hdis : targets.Pairwise Equiv.Perm.Disjoint := List.pairwise_map.mpr hd
  have hs := FiniteCuts.displacement_list_prod (targets.map (fun q => q⁻¹))
    (FiniteCuts.inverse_targets_disjoint targets hdis) i
  rw [FiniteCuts.inverse_cycle_product targets hdis] at hs
  have hm : services.map (fun (a : ExactService n) => a.displacement i)=
      (targets.map (fun q => q⁻¹)).map (fun q => FiniteCuts.displacement q i) := by
    simp only [targets,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro a ha
    rw [hc a ha]
    rfl
  rw [hm,← hs]
  rfl

theorem canonical_family_mass (services : List (ExactService n))
    (hd : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services) :
    (services.map (fun (a : ExactService n) => ∑ i : Fin n, |a.displacement i|)).sum=
      ∑ i : Fin n, |((services.map (fun (a : ExactService n) => a.service.target)).prod.symm i : ℤ)-(i : ℤ)| := by
  let targets := services.map (fun (a : ExactService n) => a.service.target)
  have hdis : targets.Pairwise Equiv.Perm.Disjoint := List.pairwise_map.mpr hd
  have hs := FiniteCuts.displacement_mass_list_prod (targets.map (fun q => q⁻¹))
    (FiniteCuts.inverse_targets_disjoint targets hdis)
  rw [FiniteCuts.inverse_cycle_product targets hdis] at hs
  have hm : services.map (fun (a : ExactService n) => ∑ i : Fin n, |a.displacement i|)=
      (targets.map (fun q => q⁻¹)).map (fun q => ∑ i : Fin n, |FiniteCuts.displacement q i|) := by
    simp only [targets,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro a ha
    rw [hc a ha]
    rfl
  rw [hm,← hs]
  rfl

#print axioms canonical_family_displacement
#print axioms canonical_family_mass
end LRX.RotationWords
