import GeneralizedBulk.Entropy.FullChaosEvaluation
import GeneralizedBulk.Entropy.ContinuousChannels
import GeneralizedBulk.Analysis.UniformCoercivity

/-! A uniform positive fourth-chaos gap for the actual correlated-star
Gaussian channels on any compact bulk parameter set. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite

/-- The actual conditional channel restricted to the fixed finite Gaussian
chaos. It is independent of the bulk correlations. -/
def coloredChaosChannel (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (i : Fin d) :
    fullChaosSpace (ScalarCoordinate d k) degree →L[ℝ] fullChaosSpace (ScalarCoordinate d k) degree :=
  ((subspaceConditionalL2 (coloredObservationMatrix d k hd i)
    (coloredObservationMatrix_orthogonal d k hd i) (coloredObserved d k hd i)).comp
      (fullChaosSpace (ScalarCoordinate d k) degree).subtypeL).codRestrict
        (fullChaosSpace (ScalarCoordinate d k) degree)
          (fun f => subspaceConditionalL2_mem_fullChaos _ _ _ degree f.property)

@[simp] theorem coloredChaosChannel_coe (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (i : Fin d)
    (f : fullChaosSpace (ScalarCoordinate d k) degree) :
    (coloredChaosChannel d k hd degree i f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k))) =
      subspaceConditionalL2 (coloredObservationMatrix d k hd i) (coloredObservationMatrix_orthogonal d k hd i)
        (coloredObserved d k hd i) (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k))) := rfl

/-- The actual inherited Gaussian L² defect, the same quadratic form for
all correlation parameters. -/
def coloredChaosDefect (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ)
    (f : fullChaosSpace (ScalarCoordinate d k) degree) : ℝ :=
  ‖f‖ ^ 2 - (1 / 2 : ℝ) * ∑ i : Fin d, ‖coloredChaosChannel d k hd degree i f‖ ^ 2

/-- Actual marginal reversal admissibility, expressed by equivalent pointwise
polynomial evaluations to expose its closed graph. -/
def coloredChaosAdmissible (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (c : StarParameters k) :
    Submodule ℝ (fullChaosSpace (ScalarCoordinate d k) degree) :=
  ⨅ i : Fin d, ⨅ x : ScalarCoordinate d k → ℝ,
    LinearMap.ker (((fullChaosEval (ScalarCoordinate d k) degree ((coloredReversalMatrix d k hd c.val i).mulVec x) -
      fullChaosEval (ScalarCoordinate d k) degree x).comp (coloredChaosChannel d k hd degree i)).toLinearMap)

theorem mem_coloredChaosAdmissible_iff (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (c : StarParameters k)
    (f : fullChaosSpace (ScalarCoordinate d k) degree) :
    f ∈ coloredChaosAdmissible d k hd degree c ↔
      ∀ i x, fullChaosEval (ScalarCoordinate d k) degree ((coloredReversalMatrix d k hd c.val i).mulVec x)
        (coloredChaosChannel d k hd degree i f) =
        fullChaosEval (ScalarCoordinate d k) degree x (coloredChaosChannel d k hd degree i f) := by
  simp only [coloredChaosAdmissible, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, sub_eq_zero]

/-- This admissibility submodule is exactly symmetry of the genuine Gaussian
conditional observation, rather than a surrogate constraint. -/
theorem coloredChaosAdmissible_iff_actual (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (c : StarParameters k)
    (f : fullChaosSpace (ScalarCoordinate d k) degree) :
    f ∈ coloredChaosAdmissible d k hd degree c ↔
      (coloredGaussianFrameSystem d k hd c.val c.property).Admissible
        (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k))) := by
  rw [mem_coloredChaosAdmissible_iff]
  constructor
  · intro h i
    exact (fullChaos_pullback_eq_iff (ScalarCoordinate d k) degree (coloredReversalMatrix d k hd c.val i)
      (isometryMatrix_orthogonal (scalarAdaptedBasis d k) (coloredReversal d k hd c.val i))
      (coloredChaosChannel d k hd degree i f)).mpr (h i)
  · intro h i
    exact (fullChaos_pullback_eq_iff (ScalarCoordinate d k) degree (coloredReversalMatrix d k hd c.val i)
      (isometryMatrix_orthogonal (scalarAdaptedBasis d k) (coloredReversal d k hd c.val i))
      (coloredChaosChannel d k hd degree i f)).mp (h i)

/-- Joint continuity of an actual observed polynomial evaluated at the
parameter-dependent orthogonal reversal. -/
theorem continuous_coloredChaos_reversal_evaluation (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ)
    (i : Fin d) (x : ScalarCoordinate d k → ℝ) :
    Continuous (fun z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree =>
      fullChaosEval (ScalarCoordinate d k) degree ((coloredReversalMatrix d k hd z.1.val i).mulVec x)
        (coloredChaosChannel d k hd degree i z.2)) := by
  have hC : Continuous (fun z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree =>
      coloredChaosChannel d k hd degree i z.2) :=
    (coloredChaosChannel d k hd degree i).continuous.comp continuous_snd
  have hR : Continuous (fun z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree =>
      (coloredReversalMatrix d k hd z.1.val i).mulVec x) :=
    (continuous_coloredReversalMatrix_mulVec d k hd i x).comp continuous_fst
  have hp := hC.prodMk hR
  have hh := Continuous.comp
    (g := fun z : fullChaosSpace (ScalarCoordinate d k) degree × (ScalarCoordinate d k → ℝ) =>
      fullChaosEval (ScalarCoordinate d k) degree z.2 z.1)
    (f := fun z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree =>
      (coloredChaosChannel d k hd degree i z.2, (coloredReversalMatrix d k hd z.1.val i).mulVec x))
    (continuous_fullChaosEval (ScalarCoordinate d k) degree) hp
  exact hh

/-- Reversal admissibility varies with a genuinely closed graph, proved from
joint continuous evaluation on the actual finite Gaussian chaos. -/
theorem isClosed_coloredChaosAdmissible_graph (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) :
    IsClosed {z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree |
      z.2 ∈ coloredChaosAdmissible d k hd degree z.1} := by
  have heq : {z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree |
      z.2 ∈ coloredChaosAdmissible d k hd degree z.1} =
      ⋂ i : Fin d, ⋂ x : ScalarCoordinate d k → ℝ,
        {z | fullChaosEval (ScalarCoordinate d k) degree ((coloredReversalMatrix d k hd z.1.val i).mulVec x)
          (coloredChaosChannel d k hd degree i z.2) =
          fullChaosEval (ScalarCoordinate d k) degree x (coloredChaosChannel d k hd degree i z.2)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_coloredChaosAdmissible_iff]
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro x
  have hC : Continuous (fun z : StarParameters k × fullChaosSpace (ScalarCoordinate d k) degree =>
      coloredChaosChannel d k hd degree i z.2) :=
    (coloredChaosChannel d k hd degree i).continuous.comp continuous_snd
  exact isClosed_eq (continuous_coloredChaos_reversal_evaluation d k hd degree i x)
    ((fullChaosEval (ScalarCoordinate d k) degree x).continuous.comp hC)

theorem continuous_coloredChaosDefect (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) :
    Continuous (coloredChaosDefect d k hd degree) := by
  exact (continuous_norm.pow 2).sub (continuous_const.mul
    (continuous_finset_sum _ (fun i _ => ((coloredChaosChannel d k hd degree i).continuous.norm.pow 2))))

theorem coloredChaosDefect_smul (d k : ℕ) (hd : 2 ≤ d) (degree : ℕ) (t : ℝ)
    (f : fullChaosSpace (ScalarCoordinate d k) degree) :
    coloredChaosDefect d k hd degree (t • f) = t ^ 2 * coloredChaosDefect d k hd degree f := by
  unfold coloredChaosDefect
  simp only [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum]
  ring

/-- The full uniform source fourth-chaos coercivity theorem on an arbitrary
compact subset of the strict bulk. BS/HY play no role in this analytic proof. -/
theorem uniform_coloredGaussian_fourth_coercivity (d k : ℕ) (hd : 3 ≤ d)
    (K : Set (StarParameters k)) (hK : IsCompact K)
    (hbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ c ∈ K,
      ∀ f : fullChaosSpace (ScalarCoordinate d k) 4,
      f ∈ coloredChaosAdmissible d k (by omega) 4 c →
        kappa * ‖f‖ ^ 2 ≤ coloredChaosDefect d k (by omega) 4 f := by
  apply GeneralizedBulk.Analysis.uniform_coercivity_of_compact K hK
    (coloredChaosAdmissible d k (by omega) 4) (isClosed_coloredChaosAdmissible_graph d k (by omega) 4)
    (fun _ f => coloredChaosDefect d k (by omega) 4 f)
    ((continuous_coloredChaosDefect d k (by omega) 4).comp continuous_snd)
    (fun _ t f => coloredChaosDefect_smul d k (by omega) 4 t f)
  · intro c hc f hf
    let coeff := fullChaosCoordinates (ScalarCoordinate d k) 4 f
    have hcoeff : chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff =
        (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k))) := fullChaosCoordinates_spec _ _ f
    have hadm := (coloredChaosAdmissible_iff_actual d k (by omega) 4 c f).mp hf
    rw [← hcoeff] at hadm
    have hh := coloredGaussian_defect_nonneg d k hd c.val (hbulk c hc) 4 (by decide) coeff hadm
    rw [hcoeff] at hh
    exact hh
  · intro c hc f hf hz
    let coeff := fullChaosCoordinates (ScalarCoordinate d k) 4 f
    have hcoeff : chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff =
        (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k))) := fullChaosCoordinates_spec _ _ f
    have hadm := (coloredChaosAdmissible_iff_actual d k (by omega) 4 c f).mp hf
    rw [← hcoeff] at hadm
    have hzero : (coloredGaussianFrameSystem d k (by omega) c.val
        (fun a => (bulk_rho_lower d hd (c.val a) (hbulk c hc a)).1)).defect
          (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) = 0 := by
      rw [hcoeff]
      exact hz
    have hh := coloredGaussian_fourth_zero_kernel d k hd c.val (hbulk c hc) coeff hadm hzero
    apply Subtype.ext
    rw [← hcoeff, hh]
    rfl

end GeneralizedBulk.Entropy.Channel
