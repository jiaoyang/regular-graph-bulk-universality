import GaussianWave.BS.GraphGaussianLocalTests

/-! Root second moments for the literal perturbed graph marks. These give
the uniform energy budget used in deterministic diagonal realizations. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

def graphMarkRootEnergy {N r : ℕ} (f : Fin r → Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹*∑ a : Fin r,∑ v : Fin N,(f a v)^2

/-- The actual perturbed root energy is integrable under the Gaussian label
source, with no integrability hypothesis on graph data (which are finite). -/
theorem integrable_graphGaussianPerturbedRootEnergy {N m : ℕ}
    (G : RegularGraph N (m+2)) (r : ℕ) (x : ℝ) (b : ℕ)
    (f : Fin r → Fin N → ℝ) (η : ℝ) :
    Integrable (fun ξ => graphMarkRootEnergy (graphGaussianPerturbedMark G r x b f η ξ))
      (gaussianLabelLaw (Fin r × Fin N)) := by
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro a ha
  apply integrable_finset_sum
  intro v hv
  have hmY : Measurable (fun ξ => finiteSupportGaussianSample
      (jointGraphGaussianCoefficient G r x b) ξ (a,v)) :=
    (measurable_pi_apply (a,v)).comp (measurable_finiteSupportGaussianSample _)
  have hY : MemLp (fun ξ => finiteSupportGaussianSample
      (jointGraphGaussianCoefficient G r x b) ξ (a,v)) 2 (gaussianLabelLaw (Fin r × Fin N)) :=
    (memLp_two_iff_integrable_sq hmY.aestronglyMeasurable).2
      (integrable_finiteSupportGaussianSample_pow _ (a,v) 2)
  exact (memLp_two_iff_integrable_sq
    (measurable_const.add (hmY.const_mul η)).aestronglyMeasurable).1
      ((memLp_const (f a v)).add (hY.const_mul η))

/-- A pointwise root-energy inequality for the actual noisy graph marks. -/
theorem graphGaussianPerturbedRootEnergy_le {N m : ℕ}
    (G : RegularGraph N (m+2)) (r : ℕ) (x : ℝ) (b : ℕ)
    (f : Fin r → Fin N → ℝ) (η : ℝ) (ξ : (Fin r × Fin N) → ℝ) :
    graphMarkRootEnergy (graphGaussianPerturbedMark G r x b f η ξ) ≤
      2*graphMarkRootEnergy f+2*η^2*((N : ℝ)⁻¹*∑ a : Fin r,∑ v : Fin N,
        (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))^2) := by
  have hsum : (∑ a : Fin r,∑ v : Fin N,(graphGaussianPerturbedMark G r x b f η ξ a v)^2) ≤
      ∑ a : Fin r,∑ v : Fin N,(2*(f a v)^2+2*η^2*
        (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))^2) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro v hv
    unfold graphGaussianPerturbedMark
    nlinarith [sq_nonneg (f a v-η*finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))]
  have hb := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  apply hb.trans_eq
  simp only [graphMarkRootEnergy,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- The expected root energy has an explicit bound with only the actual
bad-root fraction as an error term. -/
theorem integral_graphGaussianPerturbedRootEnergy_le {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N) (r : ℕ) (x : ℝ) (b : ℕ)
    (f : Fin r → Fin N → ℝ) (η : ℝ) :
    (∫ ξ,graphMarkRootEnergy (graphGaussianPerturbedMark G r x b f η ξ)
      ∂gaussianLabelLaw (Fin r × Fin N)) ≤
      2*graphMarkRootEnergy f+2*η^2*(r : ℝ)*(1+radialGraphCollisionBound (m+2) x b*
        ((N : ℝ)⁻¹*badVertexCoverRootCount G (b+1))) := by
  have hiNoise : Integrable (fun ξ => (N : ℝ)⁻¹*∑ a : Fin r,∑ v : Fin N,
      (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ (a,v))^2)
      (gaussianLabelLaw (Fin r × Fin N)) :=
    (integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun v _ =>
      integrable_finiteSupportGaussianSample_pow _ (a,v) 2))).const_mul _
  have hm := integral_mono (integrable_graphGaussianPerturbedRootEnergy G r x b f η)
    ((integrable_const _).add (hiNoise.const_mul (2*η^2)))
    (graphGaussianPerturbedRootEnergy_le G r x b f η)
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const _) (hiNoise.const_mul (2*η^2)),integral_const] at hm
  simp_rw [integral_const_mul] at hm
  simp only [measureReal_univ_eq_one,one_smul] at hm
  exact hm.trans (add_le_add_left (by
    have h := mul_le_mul_of_nonneg_left (integral_jointGraphGaussianRootEnergy_le G hN r x b)
      (show 0 ≤ 2*η^2 by positivity)
    simpa only [integral_const_mul,mul_assoc] using h) _)

/-- The same deterministic energy budget works at every fixed local block
radius once graph size is large. This is the budget used by the diagonal
probabilistic method; its constant does not grow with the block radius. -/
theorem eventually_integral_graphGaussianPerturbedRootEnergy_le
    (N : ℕ → ℕ) (m r : ℕ) (G : ∀ n,RegularGraph (N n) (m+2))
    (hN : ∀ n,0 < N n) (f : ∀ n,Fin r → Fin (N n) → ℝ)
    (S : ℝ) (hS : ∀ n,graphMarkRootEnergy (f n)≤S) (x η : ℝ)
    (hbad : ∀ k,Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k)
      atTop (𝓝 0)) (b : ℕ) :
    ∀ᶠ n in atTop,
      (∫ ξ,graphMarkRootEnergy (graphGaussianPerturbedMark (G n) r x b (f n) η ξ)
        ∂gaussianLabelLaw (Fin r × Fin (N n))) ≤ 2*S+2*η^2*(r : ℝ)+1 := by
  have ht : Tendsto (fun n => 2*S+2*η^2*(r : ℝ)*
      (1+radialGraphCollisionBound (m+2) x b*
        ((N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (b+1)))) atTop
      (𝓝 (2*S+2*η^2*(r : ℝ))) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hS0 : Tendsto (fun _ : ℕ => 2*S) atTop (𝓝 (2*S)) := tendsto_const_nhds
    simpa only [mul_zero,add_zero,mul_one] using hS0.add
      ((h1.add ((hbad (b+1)).const_mul (radialGraphCollisionBound (m+2) x b))).const_mul
        (2*η^2*(r : ℝ)))
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith :
    2*S+2*η^2*(r : ℝ)<2*S+2*η^2*(r : ℝ)+1))] with n hn
  have h := integral_graphGaussianPerturbedRootEnergy_le (G n) (hN n) r x b (f n) η
  exact le_of_lt ((h.trans (add_le_add_right (by linarith [hS n]) _)).trans_lt hn)

end GaussianWave.BS
