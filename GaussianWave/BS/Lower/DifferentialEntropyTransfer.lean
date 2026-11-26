import GaussianWave.BS.FiniteHeatQuantization
import GaussianWave.BS.HeatBlockRecoloring

/-! The genuine analytic passage from finite-alphabet randomized entropy to
differential entropy. The finite-alphabet hypothesis is source Theorem 6.1,
to be proved by graph counting; no differential entropy bound or Gaussianity
is assumed. Every smoothing/quantizer identification and both limits are proved. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy

variable {V W : Type*} [Fintype V] [Fintype W] {r : ℕ}

def recolorMass {F : Type*} (μ : Measure ((V × Fin r) → ℝ))
    (φ : (Fin r → ℝ) → F → ℝ) (b : V → F) : ℝ :=
  ∫ x, ∏ v, φ (fun i => x (v,i)) (b v) ∂μ

/-- The finite-alphabet randomized entropy statement, before any analytic
limit. It retains the literal conditional one-vertex entropy term. -/
def HasFiniteRecoloringEntropyLower
    (μC : Measure ((V × Fin r) → ℝ)) (μE : Measure ((W × Fin r) → ℝ))
    (μo : Measure (Fin r → ℝ)) (w : ℝ) : Prop :=
  ∀ (F : Type) [Fintype F], ∀ φ : (Fin r → ℝ) → F → ℝ,
    (∀ b, Continuous (fun x => φ x b)) →
    (∀ x b, 0 ≤ φ x b) → (∀ x, ∑ b, φ x b = 1) →
    (∫ x, Finite.entropy (φ x) ∂μo) ≤
      Finite.entropy (recolorMass μC φ) - w * Finite.entropy (recolorMass μE φ)

private def flattenLabelsEquiv (V I F : Type*) : (V → I → F) ≃ ((V × I) → F) where
  toFun := fun b p => b p.1 p.2
  invFun := fun b v i => b (v,i)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem entropy_heat_recolorMass
    (μ : Measure ((V × Fin r) → ℝ)) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) (a : ℝ) (K : ℕ) :
    Finite.entropy (recolorMass μ (heatQuantizerMass (clippedGridVector a K) t)) =
      finiteHeatGridEntropy μ t a K := by
  have hm : recolorMass μ (heatQuantizerMass (clippedGridVector a K) t) =
      lawMass (heatedLaw μ t) (blockQuantizer (clippedGridVector a K)) := by
    funext b
    exact (lawMass_heatedLaw_block_recoloring μ _ (measurable_clippedGridVector a K) ht b).symm
  rw [hm]
  have he := finite_entropy_law_equiv (heatedLaw μ t) (blockQuantizer (clippedGridVector a K))
    (flattenLabelsEquiv V (Fin r) (Fin (2*(K+1))))
  have hq : (flattenLabelsEquiv V (Fin r) (Fin (2*(K+1)))) ∘ blockQuantizer (clippedGridVector a K) =
      coordinatewiseQuantizer (codedClippedGridLabel a (K+1) (by omega)) := by
    funext x p
    rfl
  rw [hq] at he
  unfold finiteHeatGridEntropy
  convert he.symm using 1
  unfold Finite.entropy
  congr 1
  ext b
  simp

/-- Cutoff removal in the actual finite Gaussian recoloring inequality. -/
theorem countableHeatGridEntropy_lower_of_finite_recoloring
    (μC : Measure ((V × Fin r) → ℝ)) [IsProbabilityMeasure μC]
    (μE : Measure ((W × Fin r) → ℝ)) [IsProbabilityMeasure μE]
    (μo : Measure (Fin r → ℝ)) [IsProbabilityMeasure μo]
    (hC : Integrable (squareRadius (I := V × Fin r)) μC)
    (hE : Integrable (squareRadius (I := W × Fin r)) μE) (w : ℝ)
    (hfinite : HasFiniteRecoloringEntropyLower μC μE μo w)
    {t : ℝ} (ht : 0 < t) (a : ℝ) (ha : 0 < a) :
    (∫ x, heatGridConditionalEntropy a t x ∂μo) ≤
      countableHeatGridEntropy μC t a - w * countableHeatGridEntropy μE t a := by
  have hineq (K : ℕ) : (∫ x, heatFiniteConditionalEntropy a t K x ∂μo) ≤
      finiteHeatGridEntropy μC t a K - w * finiteHeatGridEntropy μE t a K := by
    have h := hfinite (Fin r → Fin (2*(K+1))) (heatQuantizerMass (clippedGridVector a K) t)
      (continuous_heatQuantizerMass _ (measurable_clippedGridVector a K) ht)
      (heatQuantizerMass_nonneg _ t)
      (heatQuantizerMass_sum _ (measurable_clippedGridVector a K) t)
    rw [entropy_heat_recolorMass μC ht, entropy_heat_recolorMass μE ht] at h
    exact h
  exact le_of_tendsto_of_tendsto
    (tendsto_integral_heatFiniteConditionalEntropy_cutoff μo ht a ha)
    ((tendsto_finiteHeatGridEntropy_cutoff μC hC ht a ha).sub
      ((tendsto_finiteHeatGridEntropy_cutoff μE hE ht a ha).const_mul w))
    (Eventually.of_forall hineq)

/-- Source's ambient Gaussian-smoothed lower entropy bound, including the
full joint vector conditional-noise entropy. No scalar-channel reduction is
used: each vertex's whole r-vector is recolored as one joint finite color. -/
theorem heat_entropy_lower_of_finite_recoloring
    (μC : Measure ((V × Fin r) → ℝ)) [IsProbabilityMeasure μC]
    (μE : Measure ((W × Fin r) → ℝ)) [IsProbabilityMeasure μE]
    (μo : Measure (Fin r → ℝ)) [IsProbabilityMeasure μo]
    (hC : Integrable (squareRadius (I := V × Fin r)) μC)
    (hE : Integrable (squareRadius (I := W × Fin r)) μE) (w : ℝ)
    (hdim : (Fintype.card V : ℝ) - w * Fintype.card W = 1)
    (hfinite : HasFiniteRecoloringEntropyLower μC μE μo w)
    {t : ℝ} (ht : 0 < t) :
    gaussianEntropyValue (Fin r) (heatVariance t) ≤
      densityEntropy volume (heatDensity μC t) - w * densityEntropy volume (heatDensity μE t) := by
  let a := fun n : ℕ => ((n+1 : ℕ) : ℝ)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hdim' : (Fintype.card (V × Fin r) : ℝ) - w * Fintype.card (W × Fin r) = r := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    nlinarith [congrArg (fun x : ℝ => x * (r : ℝ)) hdim]
  have hineq (n : ℕ) :
      (∫ x, heatGridConditionalEntropy (a n) t x ∂μo) + (r : ℝ)*Real.log (a n) ≤
      (countableHeatGridEntropy μC t (a n) + (Fintype.card (V × Fin r) : ℝ)*Real.log (a n)) -
        w * (countableHeatGridEntropy μE t (a n) + (Fintype.card (W × Fin r) : ℝ)*Real.log (a n)) := by
    have h := countableHeatGridEntropy_lower_of_finite_recoloring μC μE μo hC hE w hfinite ht (a n) (ha n)
    have hlog := congrArg (fun x : ℝ => x * Real.log (a n)) hdim'
    dsimp only at hlog
    nlinarith
  exact le_of_tendsto_of_tendsto
    (tendsto_integral_heatGridConditionalEntropy_mesh μo ht a ha ha0)
    ((tendsto_countableHeatGridEntropy_mesh μC hC ht a ha ha0).sub
      ((tendsto_countableHeatGridEntropy_mesh μE hE ht a ha ha0).const_mul w))
    (Eventually.of_forall hineq)
end GaussianWave.BS.Lower
