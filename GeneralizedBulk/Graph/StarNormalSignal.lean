import GeneralizedBulk.Graph.StarRescale
import GeneralizedBulk.Graph.StarCovariance

/-! Normal rescaling fixes the actual eigenvector star signal exactly. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem normalizedStarNormal_starSample_pairing {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (s : Fin (N n) × Equiv.Perm (Fin d)) (a : Fin k) (E : ℝ)
    (heigen : ∑ v, D.adjacency n ω s.1 v * q a v = E * q a s.1) :
    (∑ j, normalizedStarNormal d E j * D.starSample n ω q s (a,j)) = 0 := by
  have hperm := Equiv.sum_comp s.2 (fun j => q a (D.neighbor n ω s.1 j))
  have hneigh : (∑ j : Fin d, q a (D.neighbor n ω s.1 (s.2 j))) = E * q a s.1 := by
    rw [hperm, D.sum_neighbor n ω, heigen]
  rw [Fin.sum_univ_succ]
  simp only [normalizedStarNormal, entropyStarNormal, starSample, Fin.cases_zero, Fin.cases_succ,
    Finset.sum_mul, one_div]
  have he : (∑ j : Fin d, (Real.sqrt ((d : ℝ)+E^2))⁻¹ * (Real.sqrt (N n) * q a (D.neighbor n ω s.1 (s.2 j)))) =
      (Real.sqrt ((d : ℝ)+E^2))⁻¹ * Real.sqrt (N n) * ∑ j : Fin d, q a (D.neighbor n ω s.1 (s.2 j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, hneigh]
  ring

theorem starNormalProjection_starSample_zero {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (s : Fin (N n) × Equiv.Perm (Fin d)) (a : Fin k) (E : ℝ)
    (heigen : ∑ v, D.adjacency n ω s.1 v * q a v = E * q a s.1) :
    (starNormalProjection d E).mulVec (fun j => D.starSample n ω q s (a,j)) = 0 := by
  rw [starNormalProjection, unitNormalProjection_mulVec,
    D.normalizedStarNormal_starSample_pairing n ω q s a E heigen, zero_smul]

theorem projectionRescale_starSample_fixed {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (s : Fin (N n) × Equiv.Perm (Fin d)) (a : Fin k) (E t : ℝ)
    (heigen : ∑ v, D.adjacency n ω s.1 v * q a v = E * q a s.1) :
    (projectionRescale (starNormalProjection d E) t).mulVec (fun j => D.starSample n ω q s (a,j)) =
      (fun j => D.starSample n ω q s (a,j)) :=
  projectionRescale_fix _ t _ (D.starNormalProjection_starSample_zero n ω q s a E heigen)

end GeneralizedBulk.External.RegularSpectralData
