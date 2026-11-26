import GeneralizedBulk.Graph.ResolventJetEnvelope
import GeneralizedBulk.Graph.ResolventAnalytic
import GeneralizedBulk.Analysis.FiniteDifferenceJets

/-! Genuine finite graph raw resolvent jets, with their joint weak convergence
deduced from value laws and scalar-anchor tightness. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Classical Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def rawParticleMark (n : ℕ) (sigma : ℝ) (z : Ω × ProposalSample (N n) d)
    (j : RawComplexCoordinate) (k : Fin (N n)) : ℂ :=
  match j with
  | Sum.inl _ => 1
  | Sum.inr ij => (sigma : ℂ)*(D.proposalQuadratic n z.1 k ij.1 ij.2 z.2 : ℂ)

def rawCoordinateCenter (sigma center : ℝ) (j : RawComplexCoordinate) : ℂ :=
  match j with
  | Sum.inl _ => (center/sigma : ℝ)
  | Sum.inr _ => 0

def rawCoordinateExtension (n : ℕ) (E sigma center : ℝ)
    (z : Ω × ProposalSample (N n) d) (w : ℂ) (j : RawComplexCoordinate) : ℂ :=
  finiteResolvent (D.microscopicEigenvalue n z.1 E sigma) (D.rawParticleMark n sigma z j) w -
    rawCoordinateCenter sigma center j

def rawCoordinateDerivative (n : ℕ) (E sigma : ℝ)
    (z : Ω × ProposalSample (N n) d) (w : ℂ) (j : RawComplexCoordinate) : ℂ :=
  finiteResolventDerivative (D.microscopicEigenvalue n z.1 E sigma) (D.rawParticleMark n sigma z j) w

theorem rawCoordinateExtension_scalar (n : ℕ) (ω : Ω) (t : ProposalSample (N n) d)
    (E sigma center : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    D.rawCoordinateExtension n E sigma center (ω,t) w.val (Sum.inl ()) =
      D.microscopicScalar n ω E sigma center hsigma w := by
  rw [D.microscopicScalar_eq_finite n ω E sigma center hsigma w]
  simp [rawCoordinateExtension,finiteResolvent,rawParticleMark,rawCoordinateCenter,microscopicResolvent]

theorem rawCoordinateExtension_matrix (n : ℕ) (ω : Ω) (t : ProposalSample (N n) d)
    (E sigma center : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (i j : Fin 4) :
    D.rawCoordinateExtension n E sigma center (ω,t) w.val (Sum.inr (i,j)) =
      D.resolvent n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val
        (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) := by
  rw [D.proposal_resolvent_spectral_expansion n ω _
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).property]
  simp only [rawCoordinateExtension,finiteResolvent,rawParticleMark,rawCoordinateCenter,sub_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.microscopic_coefficient_eq n ω E sigma hsigma w k]
  ring

theorem hasDerivAt_rawCoordinateExtension (n : ℕ) (z : Ω × ProposalSample (N n) d)
    (E sigma center : ℝ) (w : ℂ) (hw : w.im ≠ 0) (j : RawComplexCoordinate) :
    HasDerivAt (fun u => D.rawCoordinateExtension n E sigma center z u j)
      (D.rawCoordinateDerivative n E sigma z w j) w := by
  exact (HasDerivAt.sum (u := Finset.univ) (fun k hk =>
    (hasDerivAt_reciprocal (D.microscopicEigenvalue n z.1 E sigma k) hw).mul_const _)).sub_const _

/-- The derivative coordinate is the literal microscopic derivative of the
physical compressed resolvent, including its microscopic scale. -/
theorem rawCoordinateDerivative_matrix (n : ℕ) (ω : Ω) (t : ProposalSample (N n) d)
    (E sigma center : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (i j : Fin 4) :
    D.rawCoordinateDerivative n E sigma (ω,t) w.val (Sum.inr (i,j)) =
      (microscopicStep (N n) sigma : ℂ) *
        ((D.resolvent n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val *
          D.resolvent n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val)
          (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j)) := by
  let c : ℂ := microscopicStep (N n) sigma
  let p : ℂ → ℂ := fun u => (E : ℂ)+c*u
  have hp : HasDerivAt p c w.val := by
    simpa only [p,id_eq,mul_one] using ((hasDerivAt_id w.val).const_mul c).const_add (E : ℂ)
  have hphys := (D.hasDerivAt_resolvent_entry n ω (p w.val)
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).property
    (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j)).comp w.val hp
  have hraw := D.hasDerivAt_rawCoordinateExtension n (ω,t) E sigma center w.val w.property (Sum.inr (i,j))
  have hraw' : HasDerivAt
      (fun u => D.resolvent n ω (p u) (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j))
      (D.rawCoordinateDerivative n E sigma (ω,t) w.val (Sum.inr (i,j))) w.val := by
    apply hraw.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds w.property] with u hu
    simpa only [p,c,microscopicParameter] using
      (D.rawCoordinateExtension_matrix n ω t E sigma center hsigma ⟨u,hu⟩ i j).symm
  exact hraw'.unique hphys |>.trans (mul_comm _ _)

theorem measurable_rawCoordinateExtension (n : ℕ) (E sigma center : ℝ) (w : ℂ) :
    Measurable (fun z => D.rawCoordinateExtension n E sigma center z w) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable
  intro t
  apply Measurable.sub_const
  apply Finset.measurable_sum
  intro k hk
  have hx : Measurable (fun ω => ((D.microscopicEigenvalue n ω E sigma k : ℂ)-w)⁻¹) := by
    have he := D.measurable_eigenvalue n k
    unfold microscopicEigenvalue
    fun_prop
  apply hx.mul
  cases j with
  | inl u => exact measurable_const
  | inr ij => exact (D.measurable_proposalQuadratic n k ij.1 ij.2 t).complex_ofReal.const_mul _

theorem measurable_rawCoordinateDerivative (n : ℕ) (E sigma : ℝ) (w : ℂ) :
    Measurable (fun z => D.rawCoordinateDerivative n E sigma z w) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable
  intro t
  unfold rawCoordinateDerivative finiteResolventDerivative
  apply Finset.measurable_sum
  intro k hk
  have hx : Measurable (fun ω => (((D.microscopicEigenvalue n ω E sigma k : ℂ)-w)⁻¹)^2) := by
    have he := D.measurable_eigenvalue n k
    unfold microscopicEigenvalue
    fun_prop
  apply hx.mul
  cases j with
  | inl u => exact measurable_const
  | inr ij => exact (D.measurable_proposalQuadratic n k ij.1 ij.2 t).complex_ofReal.const_mul _

theorem rawParticleMark_weighted_norm_le_envelope (n : ℕ) (E sigma : ℝ)
    (z : Ω × ProposalSample (N n) d) (j : RawComplexCoordinate) :
    (∑ k,nevanlinnaWeight (D.microscopicEigenvalue n z.1 E sigma k) *
      ‖D.rawParticleMark n sigma z j k‖) ≤ D.resolventJetEnvelope n E sigma z := by
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (nevanlinnaWeight_nonneg _)
  cases j with
  | inl u =>
    simp only [rawParticleMark,norm_one]
    have hs : 0 ≤ |sigma| * ∑ ij : Fin 4 × Fin 4,|D.proposalQuadratic n z.1 k ij.1 ij.2 z.2| := by positivity
    linarith
  | inr ij =>
    simp only [rawParticleMark,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hb : |D.proposalQuadratic n z.1 k ij.1 ij.2 z.2| ≤
        ∑ ab : Fin 4 × Fin 4,|D.proposalQuadratic n z.1 k ab.1 ab.2 z.2| :=
      Finset.single_le_sum (f := fun ab : Fin 4 × Fin 4 => |D.proposalQuadratic n z.1 k ab.1 ab.2 z.2|)
        (fun ab hab => abs_nonneg _) (Finset.mem_univ ij)
    nlinarith [abs_nonneg sigma]

theorem rawCoordinate_derivative_error_le (n : ℕ) (E sigma center : ℝ)
    (z : Ω × ProposalSample (N n) d) (w : ℂ) (hw : w.im ≠ 0)
    (h : ℝ) (hh : h ≠ 0) (j : RawComplexCoordinate) :
    ‖D.rawCoordinateDerivative n E sigma z w j - (h : ℂ)⁻¹ *
      (D.rawCoordinateExtension n E sigma center z (w+(h : ℂ)) j -
        D.rawCoordinateExtension n E sigma center z w j)‖ ≤
      |h| *(reciprocalSquareEnvelope w/|w.im|)*D.resolventJetEnvelope n E sigma z := by
  have he : D.rawCoordinateDerivative n E sigma z w j - (h : ℂ)⁻¹ *
      (D.rawCoordinateExtension n E sigma center z (w+(h : ℂ)) j -
        D.rawCoordinateExtension n E sigma center z w j) =
      finiteResolventDerivative (D.microscopicEigenvalue n z.1 E sigma) (D.rawParticleMark n sigma z j) w -
        (h : ℂ)⁻¹*(finiteResolvent (D.microscopicEigenvalue n z.1 E sigma) (D.rawParticleMark n sigma z j) (w+(h : ℂ)) -
          finiteResolvent (D.microscopicEigenvalue n z.1 E sigma) (D.rawParticleMark n sigma z j) w) := by
    simp only [rawCoordinateExtension,rawCoordinateDerivative,sub_sub_sub_cancel_right]
  rw [he]
  exact (finiteResolvent_derivative_error_le _ _ w hw h hh).trans
    (mul_le_mul_of_nonneg_left (D.rawParticleMark_weighted_norm_le_envelope n E sigma z j)
      (mul_nonneg (abs_nonneg h) (div_nonneg (reciprocalSquareEnvelope_nonneg w) (abs_nonneg _))))

def rawJetDifferenceConstant {I : Type*} [Fintype I] (w : I → GraphNonreal) : ℝ :=
  ∑ i,reciprocalSquareEnvelope (w i).val/|(w i).val.im|

theorem rawJetDifferenceConstant_nonneg {I : Type*} [Fintype I] (w : I → GraphNonreal) :
    0 ≤ rawJetDifferenceConstant w :=
  Finset.sum_nonneg (fun i hi => div_nonneg (reciprocalSquareEnvelope_nonneg _) (abs_nonneg _))

theorem rawValueJet_difference_error_le {I : Type*} [Fintype I]
    (w : I → GraphNonreal) (n R : ℕ) (E sigma center : ℝ)
    (z : Ω × ProposalSample (N n) d) :
    dist (finiteValueJet (fun i => (w i).val)
      (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z))
      (finiteDifferenceJet (fun i => (w i).val) (1/((R : ℝ)+1))
        (D.rawCoordinateExtension n E sigma center z)) ≤
      (rawJetDifferenceConstant w/((R : ℝ)+1))*D.resolventJetEnvelope n E sigma z := by
  have hM := D.resolventJetEnvelope_nonneg n E sigma z
  have hK := rawJetDifferenceConstant_nonneg w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨i,b,j⟩
  cases b
  · simp only [finiteValueJet,finiteDifferenceJet,finiteDifferenceTransform,finitePairedValues,
      Bool.false_eq_true,↓reduceIte,add_zero,dist_self]
    positivity
  · simp only [finiteValueJet,finiteDifferenceJet,finiteDifferenceTransform,finitePairedValues,
      Bool.false_eq_true,↓reduceIte,add_zero,dist_eq_norm]
    change ‖D.rawCoordinateDerivative n E sigma z (w i).val j -
        ((1/((R : ℝ)+1) : ℝ) : ℂ)⁻¹ *
          (D.rawCoordinateExtension n E sigma center z ((w i).val+((1/((R : ℝ)+1) : ℝ) : ℂ)) j -
            D.rawCoordinateExtension n E sigma center z (w i).val j)‖ ≤ _
    have hb := D.rawCoordinate_derivative_error_le n E sigma center z (w i).val
      (w i).property (1/((R : ℝ)+1)) (by positivity) j
    rw [abs_of_pos (by positivity : 0 < 1/((R : ℝ)+1))] at hb
    have hCi : reciprocalSquareEnvelope (w i).val/|(w i).val.im| ≤ rawJetDifferenceConstant w :=
      Finset.single_le_sum (f := fun l => reciprocalSquareEnvelope (w l).val/|(w l).val.im|)
        (fun l hl => div_nonneg (reciprocalSquareEnvelope_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    apply hb.trans
    calc
      _ ≤ (1/((R : ℝ)+1))*rawJetDifferenceConstant w*D.resolventJetEnvelope n E sigma z := by gcongr
      _ = _ := by ring

/-- The actual finite graph spectral derivatives require no independent
window theorem: value laws and the proved scalar-anchor tightness determine
their full joint finite-dimensional weak limit. -/
theorem weakLaw_rawValueJet_of_value_laws
    {I T : Type*} [Fintype I] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (Q : Measure T) [IsProbabilityMeasure Q] (E sigma center : ℝ) (w : I → GraphNonreal)
    (Z L : T → ℂ → RawComplexCoordinate → ℂ)
    (hZ : ∀ u,Measurable (fun z => Z z u)) (hL : ∀ u,Measurable (fun z => L z u))
    (hvalues : ∀ R : ℕ,External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (D.rawCoordinateExtension n E sigma center z)))
      (Q.map (fun z => finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1)) (Z z))))
    (htight : ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧ ∀ n,
      P.real {ω | A < ‖(D.microscopicCountingState n ω E sigma center).val.2‖} ≤ δ)
    (hderiv : ∀ᵐ z ∂Q,∀ i j,HasDerivAt (fun u => Z z u j) (L z (w i).val j) (w i).val) :
    External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map (fun z =>
        finiteValueJet (fun i => (w i).val) (D.rawCoordinateExtension n E sigma center z)
          (D.rawCoordinateDerivative n E sigma z)))
      (Q.map (fun z => finiteValueJet (fun i => (w i).val) (Z z) (L z))) := by
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N n) d) :=
    fun n => uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  apply weakLaw_valueJet_of_tight_difference_error
    (fun n => P.prod (uniformOrientedProposals (N n) d)) Q (fun i => (w i).val)
    (fun n => D.rawCoordinateExtension n E sigma center) (fun n => D.rawCoordinateDerivative n E sigma)
    Z L (fun n u => D.measurable_rawCoordinateExtension n E sigma center u)
    (fun n u => D.measurable_rawCoordinateDerivative n E sigma u) hZ hL hvalues
    (fun n => D.resolventJetEnvelope n E sigma) (rawJetDifferenceConstant w)
    (rawJetDifferenceConstant_nonneg w)
    (D.resolventJetEnvelope_uniform_tails P hd E sigma center htight)
    (fun R n z => D.rawValueJet_difference_error_le w n R E sigma center z) hderiv

end GeneralizedBulk.External.RegularSpectralData
