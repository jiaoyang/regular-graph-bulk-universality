import GeneralizedBulk.Graph.WindowResolvent
import GeneralizedBulk.Graph.WindowMarkLaw
import GeneralizedBulk.Gaussian.WindowStateLaw

/-! The actual covariance-centered finite window field in common state coordinates. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

def microscopicWindowMatrix (n : ℕ) (E : ℝ) (parameters : Parameters) (R : ℝ)
    (w : GraphNonreal) (z : Ω × ProposalSample (N n) d) : EndpointMatrix :=
  fun i j => D.fixedCovariancePartialProposalResolvent n z.1
    (D.eigenvalueWindow n z.1 E (microscopicStep (N n) parameters.scale * R)) parameters.p
    (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val i j z.2

theorem measurable_microscopicWindowMatrix (n : ℕ) (E : ℝ) (parameters : Parameters)
    (R : ℝ) (w : GraphNonreal) : Measurable (D.microscopicWindowMatrix n E parameters R w) := by
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable
  intro t
  change Measurable (fun ω => ∑ k ∈ D.eigenvalueWindow n ω E
    (microscopicStep (N n) parameters.scale * R),
    ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
      (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val)⁻¹) *
      ((D.proposalQuadratic n ω k i j t - covarianceMatrix parameters.p i j : ℝ) : ℂ))
  simp only [eigenvalueWindow,Finset.sum_filter]
  apply Finset.measurable_sum
  intro k hk
  have hmem : MeasurableSet {ω | |D.eigenvalue n ω k-E| ≤ microscopicStep (N n) parameters.scale*R} :=
    measurableSet_le (((D.measurable_eigenvalue n k).sub_const E).abs) measurable_const
  apply Measurable.ite hmem
  · have hi := D.measurable_selectedEigenvector n (fun _ => k)
      (fun ω => D.proposalEndpoints n ω t i) measurable_const (D.measurable_proposalEndpoints n t i)
    have hj := D.measurable_selectedEigenvector n (fun _ => k)
      (fun ω => D.proposalEndpoints n ω t j) measurable_const (D.measurable_proposalEndpoints n t j)
    have hq : Measurable (fun ω => D.proposalQuadratic n ω k i j t) := (hi.const_mul _).mul hj
    exact (((D.measurable_eigenvalue n k).complex_ofReal.sub_const _).inv.const_mul _).mul
      ((hq.sub_const _).complex_ofReal)
  · exact measurable_const

def microscopicWindowState (n : ℕ) (E center : ℝ) (parameters : Parameters) (R : ℝ)
    (w : V → GraphNonreal) (z : Ω × ProposalSample (N n) d) : WindowFieldState V :=
  (D.microscopicCountingState n z.1 E parameters.scale center,
    fun v => D.microscopicWindowMatrix n E parameters R (w v) z)

theorem measurable_microscopicWindowState (n : ℕ) (E center : ℝ) (parameters : Parameters)
    (R : ℝ) (w : V → GraphNonreal) : Measurable (D.microscopicWindowState n E center parameters R w) :=
  ((D.measurable_microscopicCountingState n E parameters.scale center).comp measurable_fst).prodMk
    (measurable_pi_lambda _ (fun v => D.measurable_microscopicWindowMatrix n E parameters R (w v)))

/-- On its actual retained-count stratum, the physical covariance-centered
window field is exactly the common polynomial of the selected endpoint marks. -/
theorem microscopicWindowState_eq_polynomial_of_count {m : ℕ} (n : ℕ)
    (E center : ℝ) (parameters : Parameters) (R : ℝ) (w : V → GraphNonreal)
    (fallback : Ω → Fin m → Fin (N n)) (z : Ω × ProposalSample (N n) d)
    (hm : D.windowEigenCount n z.1 E parameters.scale (-R) R = m) :
    D.microscopicWindowState n E center parameters R w z =
      windowPolynomialState parameters (fun v => ((w v).val,false))
        (D.windowMarkSample n E parameters.scale center R
          (D.paddedWindowSelection n · E parameters.scale (-R) R fallback) z) := by
  apply Prod.ext
  · rfl
  · funext v
    ext i j
    have h := D.fixedCovariancePartial_eq_finiteParticleField n z.1 parameters E R (w v) z.2 i j
    dsimp only [microscopicWindowState,microscopicWindowMatrix,windowPolynomialState,windowMarkSample,windowData,finiteParticleFamily]
    rw [D.paddedWindowSelection_of_count_eq n z.1 E parameters.scale (-R) R fallback hm]
    cases hm
    exact h

/-- Exact law-level reparameterization on a retained-count stratum. -/
theorem microscopicWindowState_restrict_law {m : ℕ} (P : Measure Ω) (n : ℕ)
    (E center : ℝ) (parameters : Parameters) (R : ℝ) (w : V → GraphNonreal)
    (fallback : Ω → Fin m → Fin (N n)) (hfallback : ∀ i,Measurable (fun ω => fallback ω i)) :
    (Measure.map (D.microscopicWindowState n E center parameters R w)
      (P.prod (uniformOrientedProposals (N n) d))).restrict
        {z | intervalCount z.1.val.1 (-R) R=m} =
    Measure.map (windowPolynomialState parameters (fun v => ((w v).val,false)))
      ((D.windowMarkLaw P n E parameters.scale center R
        (D.paddedWindowSelection n · E parameters.scale (-R) R fallback)).restrict
          (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m})) := by
  have hsel := D.measurable_paddedWindowSelection n E parameters.scale (-R) R fallback hfallback
  have hmark := D.measurable_windowMarkSample n E parameters.scale center R
    (D.paddedWindowSelection n · E parameters.scale (-R) R fallback) hsel
  have hS : MeasurableSet {z : WindowFieldState V | intervalCount z.1.val.1 (-R) R=m} :=
    (((measurable_intervalCount (-R) R).comp
      (measurable_fst.comp measurable_subtype_coe)).comp measurable_fst) (measurableSet_singleton m)
  have hT : MeasurableSet (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m} : Set (WindowData m × ((Fin m × Fin 4) → ℝ))) :=
    (measurable_fst.comp (measurable_snd.comp measurable_fst)) (measurableSet_singleton m)
  rw [Measure.restrict_map (D.measurable_microscopicWindowState n E center parameters R w) hS,
    windowMarkLaw,Measure.restrict_map hmark hT,
    Measure.map_map (continuous_windowPolynomialState parameters _).measurable hmark]
  apply Measure.map_congr
  have hm : MeasurableSet {z : Ω × ProposalSample (N n) d |
      D.windowEigenCount n z.1 E parameters.scale (-R) R=m} :=
    ((D.measurable_windowEigenCount n E parameters.scale (-R) R).comp measurable_fst)
      (measurableSet_singleton m)
  change (D.microscopicWindowState n E center parameters R w) =ᵐ[
    (P.prod (uniformOrientedProposals (N n) d)).restrict
      {z | D.windowEigenCount n z.1 E parameters.scale (-R) R=m}] _
  filter_upwards [ae_restrict_mem hm] with z hz
  exact D.microscopicWindowState_eq_polynomial_of_count n E center parameters R w fallback z hz

end GeneralizedBulk.External.RegularSpectralData
