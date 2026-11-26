import GaussianWave.BS.GaussianLabelRestriction
import GaussianWave.BS.Lower.LocalRecoloringConcentration
import GaussianWave.BS.Lower.BoundedDependencyVariance

/-! Concentration of genuinely local bounded observations of the actual
independent Gaussian labels on a finite regular graph. Independence and
integrability are derived, including for the continuous Gaussian source. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph
open Lower

variable {N d : ℕ}

def graphGaussianLocalObservation (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → ℝ) → ℝ)
    (v : Fin N) (ξ : Fin N → ℝ) : ℝ := f v (fun w => ξ w)

/-- Disjoint graph label balls give actual independence of their local
observations under the literal Gaussian product measure. -/
theorem graphGaussianLocalObservation_indep (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → ℝ) → ℝ)
    (hf : ∀ v,Measurable (f v)) (v w : Fin N)
    (hfar : w ∉ graphBallVertices G.val v (2*R)) :
    IndepFun (graphGaussianLocalObservation G R f v) (graphGaussianLocalObservation G R f w)
      (gaussianLabelLaw (Fin N)) := by
  have hi := (gaussianLabelLaw_iIndepFun (Fin N)).indepFun_finset
    (graphBallVertices G.val v R) (graphBallVertices G.val w R)
    (graphBall_disjoint_of_far G R v w hfar) (fun i => measurable_pi_apply i)
  exact hi.comp (hf v) (hf w)

/-- The empirical average of bounded radius-R Gaussian observations has
variance at most B_d(2R)/N. No moment or independence premise for the
observations is assumed. -/
theorem graphGaussianLocalAverage_variance (G : RegularGraph N d) (hN : 0 < N) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → ℝ) → ℝ)
    (hfm : ∀ v,Measurable (f v)) (hf0 : ∀ v z,0 ≤ f v z) (hf1 : ∀ v z,f v z ≤ 1) :
    (∫ ξ,((N : ℝ)⁻¹*∑ v,graphGaussianLocalObservation G R f v ξ-
      ∫ z,(N : ℝ)⁻¹*∑ v,graphGaussianLocalObservation G R f v z
        ∂gaussianLabelLaw (Fin N))^2 ∂gaussianLabelLaw (Fin N)) ≤
      (regularBallBound d (2*R) : ℝ)/(N : ℝ) := by
  simpa only [Fintype.card_fin] using
    integral_centered_average_sq_le_of_ae_bounded (gaussianLabelLaw (Fin N))
      (by simpa only [Fintype.card_fin] using hN) (graphGaussianLocalObservation G R f)
      (fun v => ((hfm v).comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))).aemeasurable)
      (fun v => Filter.Eventually.of_forall (fun ξ => ⟨hf0 v _,hf1 v _⟩))
      (fun v => graphBallVertices G.val v (2*R)) (regularBallBound d (2*R))
      (fun v => regular_graphBall_card_le G.val G.property v (2*R))
      (fun v w hfar => graphGaussianLocalObservation_indep G R f hfm v w hfar)

/-- A measurable observation that is constant on label fields agreeing on
its ball is an actual measurable function of those local labels. -/
theorem graphGaussianAverage_variance_of_local (G : RegularGraph N d) (hN : 0 < N) (R : ℕ)
    (X : Fin N → (Fin N → ℝ) → ℝ) (hXm : ∀ v,Measurable (X v))
    (hX0 : ∀ v ξ,0 ≤ X v ξ) (hX1 : ∀ v ξ,X v ξ ≤ 1)
    (hlocal : ∀ v ξ ζ,(∀ w,G.val.edist v w ≤ R → ξ w=ζ w) → X v ξ=X v ζ) :
    (∫ ξ,((N : ℝ)⁻¹*∑ v,X v ξ-
      ∫ ζ,(N : ℝ)⁻¹*∑ v,X v ζ ∂gaussianLabelLaw (Fin N))^2
      ∂gaussianLabelLaw (Fin N)) ≤ (regularBallBound d (2*R) : ℝ)/(N : ℝ) := by
  let extend (v : Fin N) (z : (graphBallVertices G.val v R) → ℝ) (w : Fin N) : ℝ :=
    if hw : w ∈ graphBallVertices G.val v R then z ⟨w,hw⟩ else 0
  let f (v : Fin N) (z : (graphBallVertices G.val v R) → ℝ) := X v (extend v z)
  have hm (v : Fin N) : Measurable (f v) := by
    apply (hXm v).comp
    apply measurable_pi_lambda
    intro w
    dsimp only [extend]
    split_ifs <;> fun_prop
  have heq (v : Fin N) (ξ : Fin N → ℝ) : graphGaussianLocalObservation G R f v ξ=X v ξ := by
    apply hlocal
    intro w hw
    have hmem : w ∈ graphBallVertices G.val v R := by
      simpa only [graphBallVertices,Finset.mem_filter,Finset.mem_univ,true_and] using hw
    simp only [extend,dif_pos hmem]
  have hb := graphGaussianLocalAverage_variance G hN R f hm
    (fun v z => hX0 v _) (fun v z => hX1 v _)
  simpa only [heq] using hb

end GaussianWave.BS
