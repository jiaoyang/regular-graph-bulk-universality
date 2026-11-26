import GeneralizedBulk.Entropy.StarEdgeFunctional
import GeneralizedBulk.Graph.ExtendedEmpiricalWhitening
import GeneralizedBulk.Entropy.MehlerHilbert

/-! The ideal entropy expressions specialize to literal empirical eigenvector
stars and edges, with the same actual retained normalized signals as the
Mehler entropy deficit. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empirical_idealStarEntropy {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (r : ℝ) :
    idealStarEntropy d k hd (fun a => D.eigenvalue n ω (selection a)) (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) =
      differentialEntropy (gaussianMixturePDF (D.empiricalStarWeight n)
        (fun s => r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s)
        (fun _ => coloredExtendedFactor d k hd (fun a => D.eigenvalue n ω (selection a)))) := by
  unfold idealStarEntropy
  apply congrArg (fun mean => differentialEntropy (gaussianMixturePDF (D.empiricalStarWeight n) mean
    (fun _ => coloredExtendedFactor d k hd (fun a => D.eigenvalue n ω (selection a)))))
  funext s
  have hs : Sum.elim (r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s)
      (fun _ : Fin k => 0) =
      r • Sum.elim ((D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) (fun _ : Fin k => 0) := by
    funext a
    cases a <;> simp
  rw [hs, Matrix.mulVec_smul, D.empirical_extendedWhitening_mean n ω hd selection hinj hE s]

theorem empirical_idealEdgeEntropy {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (r : ℝ) (i : Fin d) :
    idealEdgeEntropy d k hd (fun a => D.eigenvalue n ω (selection a)) (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) i =
      differentialEntropy (gaussianMixturePDF (D.empiricalStarWeight n)
        (fun s => fun j : Fin k × Fin 2 =>
          r * D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s (j.1, physicalEdgeIndex i j.2))
        (fun _ => edgePhysicalFactor d k hd (fun a => D.eigenvalue n ω (selection a)) i)) := by
  unfold idealEdgeEntropy
  apply congrArg (fun mean => differentialEntropy (gaussianMixturePDF (D.empiricalStarWeight n) mean
    (fun _ => edgePhysicalFactor d k hd (fun a => D.eigenvalue n ω (selection a)) i)))
  funext s j
  have hv : (scalarCoordinates d k).symm
      (r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) =
      r • D.empiricalWhiteStar n ω hd selection s := by
    rw [map_smul, D.empiricalNormalizedSignal_values n ω hd selection hinj hE s,
      (scalarCoordinates d k).symm_apply_apply]
  rw [hv, real_inner_smul_right]
  congr 1
  exact D.empiricalWhiteStar_row n ω hd selection hE s (j.1, physicalEdgeIndex i j.2)

theorem empirical_edgeObservedNoiseEntropy {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (r : ℝ) (i : Fin d) :
    edgeObservedNoiseEntropy d k hd (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) i =
      identityNoiseEntropy (D.empiricalStarWeight n)
        (fun s => r • ((D.empiricalNormalizedSignal n ω hd selection hinj hE).observedSignal
          (coloredObservationMatrix d k hd i) (coloredObservationMatrix_orthogonal d k hd i)
          (coloredObserved d k hd i)).signal s) := by
  unfold edgeObservedNoiseEntropy
  apply congrArg (identityNoiseEntropy (D.empiricalStarWeight n))
  funext s a
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    NormalizedFiniteSignal.observedSignal, NormalizedFiniteSignal.rotate, NormalizedFiniteSignal.restrict]

end GeneralizedBulk.External.RegularSpectralData
