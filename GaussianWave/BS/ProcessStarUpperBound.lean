import GaussianWave.BS.ProcessStar

/-! The heat-flow upper inequality and its strict equality case for an
actual invariant, normalized, common-energy tree eigenprocess. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem coloredPhysicalStarInverseMatrix_mulVec (d r : ℕ) (c : ℝ)
    (z : (Fin r × Fin (d+1)) → ℝ) :
    (coloredPhysicalStarInverseMatrix d r c).mulVec z=coloredPhysicalStarInverse d r c z := by
  ext av
  rcases av with ⟨a,i⟩
  exact (channelLiftMatrix_mulVec r (physicalStarInverseMatrix d c) z a i).trans
    (congrFun (physicalStarInverseMatrix_mulVec d c (fun j => z (a,j))) i)

def processStarWhiteLaw {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (c : ℝ) :=
  Measure.map (coloredPhysicalStarInverseMatrix d r c).mulVec (processStarLaw μ)

instance processStarWhiteLaw_probability {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) [IsProbabilityMeasure μ] (c : ℝ) :
    IsProbabilityMeasure (processStarWhiteLaw μ c) :=
  isProbabilityMeasure_map (measurable_finiteMatrixAction _).aemeasurable

theorem processStarWhiteLaw_reconstruction {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (energy : ℝ)
    (hc : |energy/(m+2)|<1)
    (hE : ∀ a,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a none x=0) :
    Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
      (processStarWhiteLaw μ (energy/(m+2)))=processStarLaw μ := by
  rw [processStarWhiteLaw,Measure.map_map
    (coloredPhysicalStarMap (m+2) r (energy/(m+2))).continuous_of_finiteDimensional.measurable
    (measurable_finiteMatrixAction _)]
  calc
    _ = Measure.map id (processStarLaw μ) := by
      apply Measure.map_congr
      filter_upwards [processStarLaw_ae_hyperplane μ energy hE] with z hz
      rw [Function.comp_apply,coloredPhysicalStarInverseMatrix_mulVec]
      exact coloredPhysicalStarInverse_right_inverse (m+2) r (by omega) _ hc z hz
    _ = _ := Measure.map_id

theorem process_star_entropy_upper {r m : ℕ} (hm : 0 < m)
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ)
    (hbulk : (energy/(m+2))^2 < 4*(((m+2 : ℕ) : ℝ)-1)/((m+2 : ℕ) : ℝ)^2)
    (hE : ∀ b v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0)
    (hroot : HasIdentitySecondMoments (rootChannelLaw μ))
    (chart : coloredPhysicalStarHyperplane (m+2) r (energy/(m+2)) ≃ₗ[ℝ] ((Fin r × Fin (m+2)) → ℝ))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv (m+2) r (by omega) (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1 y))
      (processStarWhiteLaw μ (energy/(m+2)))))
    (g : ∀ i,FiniteEntropyDensity (processEdgeLaw μ i)) :
    f.entropy-(1/2 : ℝ)*∑ i,(g i).entropy ≤
      (coloredPhysicalGaussianStarEntropyDensity (m+2) r (by omega) (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1 chart).entropy-
      (m+2 : ℝ)/2*(coloredPhysicalGaussianEdgeEntropyDensity r (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1).entropy := by
  have hrec := processStarWhiteLaw_reconstruction μ energy
    (bulk_rho_lower (m+2) (by omega) _ hbulk).1 (fun a => hE a none)
  have hC : HasSecondMoments
      (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
        (processStarWhiteLaw μ (energy/(m+2))))
      (coloredPhysicalStarCovariance (m+2) r (energy/(m+2))) := by
    rw [hrec]
    exact processStarLaw_secondMoments μ hμ hi energy hE hroot
  let g' := fun i => (g i).cast (congrArg (Measure.map (coloredPhysicalEdgeCoordinates i)) hrec)
  have hrev (i : Fin (m+2)) : Measure.map (edgeFlipLinear r)
      (Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
          (processStarWhiteLaw μ (energy/(m+2))))) =
      Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
          (processStarWhiteLaw μ (energy/(m+2)))) := by
    rw [hrec]
    exact processEdgeLaw_reversal μ hμ i
  simpa only [g',FiniteEntropyDensity.cast_entropy,Nat.cast_add,Nat.cast_ofNat] using
    colored_physical_star_entropy_upper (m+2) r (by omega) _ hbulk chart
      (processStarWhiteLaw μ (energy/(m+2))) hC f g' hrev

theorem process_star_entropy_equality_iff_white_gaussian {r m : ℕ} (hm : 0 < m)
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ChannelTreeInvariant μ) (hi : ∀ av,Integrable (fun x => x av^2) μ)
    (energy : ℝ)
    (hbulk : (energy/(m+2))^2 < 4*(((m+2 : ℕ) : ℝ)-1)/((m+2 : ℕ) : ℝ)^2)
    (hE : ∀ b v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) b v x=0)
    (hroot : HasIdentitySecondMoments (rootChannelLaw μ))
    (chart : coloredPhysicalStarHyperplane (m+2) r (energy/(m+2)) ≃ₗ[ℝ] ((Fin r × Fin (m+2)) → ℝ))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv (m+2) r (by omega) (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1 y))
      (processStarWhiteLaw μ (energy/(m+2)))))
    (g : ∀ i,FiniteEntropyDensity (processEdgeLaw μ i)) :
    (f.entropy-(1/2 : ℝ)*∑ i,(g i).entropy =
      (coloredPhysicalGaussianStarEntropyDensity (m+2) r (by omega) (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1 chart).entropy-
      (m+2 : ℝ)/2*(coloredPhysicalGaussianEdgeEntropyDensity r (energy/(m+2))
        (bulk_rho_lower (m+2) (by omega) _ hbulk).1).entropy) ↔
      processStarWhiteLaw μ (energy/(m+2))=standardVector (Fin r × Fin (m+2)) := by
  have hrec := processStarWhiteLaw_reconstruction μ energy
    (bulk_rho_lower (m+2) (by omega) _ hbulk).1 (fun a => hE a none)
  have hC : HasSecondMoments
      (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
        (processStarWhiteLaw μ (energy/(m+2))))
      (coloredPhysicalStarCovariance (m+2) r (energy/(m+2))) := by
    rw [hrec]
    exact processStarLaw_secondMoments μ hμ hi energy hE hroot
  let g' := fun i => (g i).cast (congrArg (Measure.map (coloredPhysicalEdgeCoordinates i)) hrec)
  have hrev (i : Fin (m+2)) : Measure.map (edgeFlipLinear r)
      (Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
          (processStarWhiteLaw μ (energy/(m+2))))) =
      Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
          (processStarWhiteLaw μ (energy/(m+2)))) := by
    rw [hrec]
    exact processEdgeLaw_reversal μ hμ i
  have hperm (p : Equiv.Perm (Fin (m+2))) : Measure.map (coloredPhysicalStarPermutation p)
      (Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
        (processStarWhiteLaw μ (energy/(m+2)))) =
      Measure.map (coloredPhysicalStarMap (m+2) r (energy/(m+2)))
        (processStarWhiteLaw μ (energy/(m+2))) := by
    rw [hrec]
    exact processStarLaw_permutation μ hμ p
  simpa only [g',FiniteEntropyDensity.cast_entropy,Nat.cast_add,Nat.cast_ofNat] using
    colored_physical_star_entropy_equality_iff_standardVector (m+2) r (by omega) _ hbulk chart
      (processStarWhiteLaw μ (energy/(m+2))) hC f g' hrev hperm

theorem processStarLaw_gaussian_of_white_gaussian {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (energy : ℝ)
    (hc : |energy/(m+2)| < 1)
    (hE : ∀ a,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a none x=0)
    (hwhite : processStarWhiteLaw μ (energy/(m+2))=standardVector (Fin r × Fin (m+2))) :
    HasGaussianCovariance (processStarLaw μ)
      (coloredPhysicalStarCovariance (m+2) r (energy/(m+2))) := by
  rw [← processStarWhiteLaw_reconstruction μ energy hc hE,hwhite,
    ← coloredPhysicalStarMatrix_gram (m+2) r (by omega) _ hc]
  exact linearImageGaussian_characteristic (coloredPhysicalStarMatrix (m+2) r (energy/(m+2)))

end GaussianWave.BS
