import GeneralizedBulk.Graph.IdealEmpiricalEntropy
import GeneralizedBulk.Entropy.GaussianMixtureCovarianceEntropy

/-! Every ordered leaf has the same actual empirical ideal edge entropy.
This is exact uniform permutation averaging, including all selected colors. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empiricalEdgeMixturePDF_leaf_eq {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (r : ℝ)
    (M : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ) (i j : Fin d) :
    gaussianMixturePDF (D.empiricalStarWeight n)
      (fun s => fun a : Fin k × Fin 2 => r * D.starSample n ω q s (a.1, physicalEdgeIndex i a.2)) (fun _ => M) =
    gaussianMixturePDF (D.empiricalStarWeight n)
      (fun s => fun a : Fin k × Fin 2 => r * D.starSample n ω q s (a.1, physicalEdgeIndex j a.2)) (fun _ => M) := by
  have hm (leaf : Fin d) (s : EmpiricalStarSample d (N n)) :
      (fun a : Fin k × Fin 2 => r * D.starSample n ω q s (a.1, physicalEdgeIndex leaf a.2)) =
        r • D.orientedEdgeMark n ω q (s.1, s.2 leaf) := by
    rw [← D.starEdgeRestriction_sample n ω q s leaf]
    funext a
    rcases a with ⟨a,t⟩
    fin_cases t <;> rfl
  funext x
  simp only [gaussianMixturePDF, empiricalStarWeight, ← Finset.mul_sum]
  congr 1
  simp_rw [hm]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  exact Graph.sum_perm_eval_eq (fun port => affineGaussianPDF (r • D.orientedEdgeMark n ω q (v,port)) M x) i j

theorem empirical_idealEdgeEntropy_leaf_eq {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (r : ℝ) (i j : Fin d) :
    idealEdgeEntropy d k hd (fun a => D.eigenvalue n ω (selection a)) (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) i =
    idealEdgeEntropy d k hd (fun a => D.eigenvalue n ω (selection a)) (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) j := by
  rw [D.empirical_idealEdgeEntropy n ω hd selection hinj hE r i,
    D.empirical_idealEdgeEntropy n ω hd selection hinj hE r j]
  trans differentialEntropy (gaussianMixturePDF (D.empiricalStarWeight n)
    (fun s => fun a : Fin k × Fin 2 => r * D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s
      (a.1, physicalEdgeIndex i a.2))
    (fun _ => edgePhysicalFactor d k hd (fun a => D.eigenvalue n ω (selection a)) j))
  · apply gaussianMixture_entropy_eq_of_covariance _ _ _ _ (D.empiricalStarWeight_nonneg n)
      (D.empiricalStarWeight_total n)
      (fun _ => edgePhysicalFactor_det_ne_zero d k hd _ hE i)
      (fun _ => edgePhysicalFactor_det_ne_zero d k hd _ hE j)
    intro s
    rw [edgePhysicalFactor_covariance d k hd _ hE i, edgePhysicalFactor_covariance d k hd _ hE j]
  · exact congrArg differentialEntropy (D.empiricalEdgeMixturePDF_leaf_eq n ω _ r _ i j)

theorem empirical_edgeObservedNoiseEntropy_leaf_eq {k : ℕ} (hd : 2 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (r : ℝ) (i j : Fin d) :
    edgeObservedNoiseEntropy d k hd (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) i =
    edgeObservedNoiseEntropy d k hd (D.empiricalStarWeight n)
      (fun s => r • (D.empiricalNormalizedSignal n ω hd selection hinj hE).signal s) j := by
  have he := D.empirical_idealEdgeEntropy_leaf_eq n ω hd selection hinj hE r i j
  rw [idealEdgeEntropy_eq d k hd _ hE _ _ (D.empiricalStarWeight_nonneg n) (D.empiricalStarWeight_total n) i,
    idealEdgeEntropy_eq d k hd _ hE _ _ (D.empiricalStarWeight_nonneg n) (D.empiricalStarWeight_total n) j] at he
  linarith

end GeneralizedBulk.External.RegularSpectralData
