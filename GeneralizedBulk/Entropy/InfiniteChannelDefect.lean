import GeneralizedBulk.Entropy.ChaosDecomposition
import GeneralizedBulk.Entropy.UniformFourthCoercivity

/-! The proved infinite Gaussian decomposition transfers actual star symmetry
to each degree and yields the true fourth-chaos lower bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite.GaussianFrameSystem
variable {I C P : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype P]

/-- Genuine conditional observations preserve every full homogeneous chaos. -/
theorem channel_preserves_degree (G : GaussianFrameSystem I C P) (c : C) (n : ℕ)
    (f : Lp ℝ 2 (standardGaussian I)) (hf : f ∈ fullChaosSpace I n) : G.channel c f ∈ fullChaosSpace I n :=
  subspaceConditionalL2_mem_fullChaos (G.coordinates c) (G.orthogonal c) (G.observed c) n hf

theorem hasSum_defect_components (G : GaussianFrameSystem I C P) (f : Lp ℝ 2 (standardGaussian I)) :
    HasSum (fun n : ℕ => G.defect (chaosComponent I f n)) (G.defect f) :=
  hasSum_linearChannelDefect I G.channel (G.channel_preserves_degree) f

/-- Actual marginal symmetry descends through the genuine infinite-degree
projections because both the conditional and reversal operators preserve degree. -/
theorem admissible_chaosComponent (G : GaussianFrameSystem I C P) (f : Lp ℝ 2 (standardGaussian I))
    (hf : G.Admissible f) (n : ℕ) : G.Admissible (chaosComponent I f n) := by
  intro c
  have hC (g : Lp ℝ 2 (standardGaussian I)) := wholeChaosProjection_commute I (G.channel c)
    (G.channel_preserves_degree c) n g
  let R := (gaussianPullback (G.reversal c) (G.reversal_orthogonal c)).toContinuousLinearMap
  have hR (g : Lp ℝ 2 (standardGaussian I)) := wholeChaosProjection_commute I R
    (fun m g hg => gaussianPullback_mem_fullChaos (G.reversal c) (G.reversal_orthogonal c) m hg) n g
  change R (G.channel c (wholeChaosProjection I n f)) = G.channel c (wholeChaosProjection I n f)
  rw [← hC f, ← hR (G.channel c f)]
  change wholeChaosProjection I n (gaussianPullback (G.reversal c) (G.reversal_orthogonal c) (G.channel c f)) = _
  rw [hf c, hC f]

theorem defect_component_nonneg (G : GaussianFrameSystem I C P) (f : Lp ℝ 2 (standardGaussian I))
    (hf : G.Admissible f) (hcenter : (∫ x, f x ∂standardGaussian I) = 0)
    (hA : ∀ c p, 0 ≤ G.weightA c p) (hB : ∀ c p, 0 ≤ G.weightB c p) (n : ℕ) :
    0 ≤ G.defect (chaosComponent I f n) := by
  by_cases hn : n = 0
  · subst n
    rw [chaosComponent_zero_of_integral_zero I f hcenter]
    simp [GaussianFrameSystem.defect, gaussianChannelDefect]
  · let coeff := fullChaosCoordinates I n (chaosComponent I f n)
    have hcoeff : chaosLp (degreeIndexNat I) coeff = (chaosComponent I f n : Lp ℝ 2 (standardGaussian I)) :=
      fullChaosCoordinates_spec I n (chaosComponent I f n)
    have hadm := G.admissible_chaosComponent f hf n
    rw [← hcoeff] at hadm
    have hh := G.defect_nonneg n (Nat.pos_of_ne_zero hn) coeff hadm hA hB
    rw [hcoeff] at hh
    exact hh

/-- The actual full defect dominates any single degree energy, without an
assumed chaos expansion or assumed summability. -/
theorem defect_component_le (G : GaussianFrameSystem I C P) (f : Lp ℝ 2 (standardGaussian I))
    (hf : G.Admissible f) (hcenter : (∫ x, f x ∂standardGaussian I) = 0)
    (hA : ∀ c p, 0 ≤ G.weightA c p) (hB : ∀ c p, 0 ≤ G.weightB c p) (n : ℕ) :
    G.defect (chaosComponent I f n) ≤ G.defect f := by
  have hs := G.hasSum_defect_components f
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n (fun m hm => G.defect_component_nonneg f hf hcenter hA hB m)

end GeneralizedBulk.Entropy.Hermite.GaussianFrameSystem

namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite

/-- Uniform true fourth-chaos lower bound for every centered, admissible
Gaussian L² density perturbation, with all infinite analytic inputs proved. -/
theorem uniform_actual_defect_fourth_lower (d k : ℕ) (hd : 3 ≤ d)
    (K : Set (StarParameters k)) (hK : IsCompact K)
    (hbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ c ∈ K,
      ∀ f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)),
      (coloredGaussianFrameSystem d k (by omega) c.val c.property).Admissible f →
      (∫ x, f x ∂standardGaussian (ScalarCoordinate d k)) = 0 →
      kappa * ‖chaosComponent (ScalarCoordinate d k) f 4‖ ^ 2 ≤
        (coloredGaussianFrameSystem d k (by omega) c.val c.property).defect f := by
  obtain ⟨κ, hκ, hcoer⟩ := uniform_coloredGaussian_fourth_coercivity d k hd K hK hbulk
  refine ⟨κ, hκ, ?_⟩
  intro c hc f hadm hcenter
  let G := coloredGaussianFrameSystem d k (by omega) c.val c.property
  have hAd := G.admissible_chaosComponent f hadm 4
  have hmem := (coloredChaosAdmissible_iff_actual d k (by omega) 4 c
    (chaosComponent (ScalarCoordinate d k) f 4)).mpr hAd
  have hgap := hcoer c hc (chaosComponent (ScalarCoordinate d k) f 4) hmem
  have hle := G.defect_component_le f hadm hcenter
    (fun _ a => (bulk_weights_pos d hd (c.val a) (hbulk c hc a)).1.le)
    (fun _ a => (bulk_weights_pos d hd (c.val a) (hbulk c hc a)).2.le) 4
  exact hgap.trans hle

end GeneralizedBulk.Entropy.Channel
