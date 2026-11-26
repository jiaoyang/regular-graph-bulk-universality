import GaussianWave.BS.IndependentAddition
import GaussianWave.BS.JointGaussianBlockFactor

/-! Finite-window independent smoothing by the actual Gaussian-wave law is
approximated by the actual finite-radius iid Gaussian block rules. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

/-- The independent noise in the smoothing closure is the constructed tree
reference, obtained by an actual blockfactor limit. No approximation law is
provided as a hypothesis. -/
theorem independentAdd_jointGaussianBlock_weakConverges
    (r m : ℕ) (hm : 0 < m) (x : ℝ) (hx : |x|<1)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2))
    (μ : Measure ((Fin r × J) → ℝ)) [IsProbabilityMeasure μ] (η : ℝ) :
    WeakLawConverges
      (fun b => independentAddLaw μ (Measure.map
        (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun aj : Fin r × J => z (aj.1,site aj.2))
        (jointRadialGaussianBlockLaw r (m+2) x b)) η)
      (independentAddLaw μ (Measure.map
        (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun aj : Fin r × J => z (aj.1,site aj.2))
        (jointGaussianTreeProcessLaw r m (radialEnergy m x))) η) := by
  let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun aj : Fin r × J => z (aj.1,site aj.2)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  letI (b : ℕ) : IsProbabilityMeasure (Measure.map W (jointRadialGaussianBlockLaw r (m+2) x b)) :=
    isProbabilityMeasure_map hW.aemeasurable
  letI : IsProbabilityMeasure (Measure.map W (jointGaussianTreeProcessLaw r m (radialEnergy m x))) :=
    isProbabilityMeasure_map hW.aemeasurable
  exact independentAddLaw_weakConverges_right μ _ _ η
    (jointRadialGaussianBlockLaw_weakConverges_to_tree_reference r m hm x hx site)

end GaussianWave.BS
