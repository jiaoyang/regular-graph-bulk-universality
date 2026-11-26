import GeneralizedBulk.Graph.ProposalSecondMoment
import GeneralizedBulk.Graph.TruncationErrorMeasurable
import GeneralizedBulk.Graph.RawPairCompactness
import GeneralizedBulk.Analysis.ConditionalTightness
import GeneralizedBulk.Analysis.ResolventDifference

/-! The actual finite endpoint quadratics give a tight Nevanlinna-weighted
envelope for all raw resolvent coordinates and their spectral derivatives. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem integral_abs_proposalQuadratic_le_one (n : ℕ) (ω : Ω) (hd : 0 < d)
    (k : Fin (N n)) (i j : Fin 4) :
    (∫ t,|D.proposalQuadratic n ω k i j t| ∂uniformOrientedProposals (N n) d) ≤ 1 := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let sel : Fin 1 → Fin (N n) := fun _ => k
  let y := D.proposalMark n ω (fun a => D.eigenvector n ω (sel a))
  have hp (a b : Fin 4) (t : ProposalSample (N n) d) :
      y t (0,a)*y t (0,b)=D.proposalQuadratic n ω k a b t :=
    D.proposalMark_product n ω sel 0 a b t
  have hs (a : Fin 4) : (∫ t,(y t (0,a))^2 ∂uniformOrientedProposals (N n) d)=1 :=
    D.proposalMark_coordinate_second n ω hd sel (0,a)
  have hpoint (t : ProposalSample (N n) d) :
      |D.proposalQuadratic n ω k i j t| ≤ ((y t (0,i))^2+(y t (0,j))^2)/2 := by
    rw [← hp i j t,abs_mul]
    nlinarith [sq_nonneg (|y t (0,i)|-|y t (0,j)|),sq_abs (y t (0,i)),sq_abs (y t (0,j))]
  calc
    _ ≤ ∫ t,((y t (0,i))^2+(y t (0,j))^2)/2 ∂uniformOrientedProposals (N n) d :=
      integral_mono (integrable_finiteUniform_real _) (integrable_finiteUniform_real _) hpoint
    _ = 1 := by rw [integral_div,integral_add (μ := uniformOrientedProposals (N n) d) (integrable_finiteUniform_real _) (integrable_finiteUniform_real _),hs,hs]; norm_num

def resolventJetEnvelope (n : ℕ) (E sigma : ℝ) (z : Ω × ProposalSample (N n) d) : ℝ :=
  ∑ k,nevanlinnaWeight (D.microscopicEigenvalue n z.1 E sigma k) *
    (1+|sigma| *∑ ij : Fin 4 × Fin 4,|D.proposalQuadratic n z.1 k ij.1 ij.2 z.2|)

theorem resolventJetEnvelope_nonneg (n : ℕ) (E sigma : ℝ)
    (z : Ω × ProposalSample (N n) d) : 0 ≤ D.resolventJetEnvelope n E sigma z := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (nevanlinnaWeight_nonneg _) (by positivity)

theorem measurable_resolventJetEnvelope (n : ℕ) (E sigma : ℝ) :
    Measurable (D.resolventJetEnvelope n E sigma) := by
  apply measurable_from_prod_countable
  intro t
  apply Finset.measurable_sum
  intro k hk
  have hx : Measurable (fun ω => nevanlinnaWeight (D.microscopicEigenvalue n ω E sigma k)) := by
    unfold nevanlinnaWeight microscopicEigenvalue
    have he := D.measurable_eigenvalue n k
    fun_prop
  exact hx.mul (measurable_const.add
    ((Finset.measurable_sum _ (fun (ij : Fin 4 × Fin 4) _ => (D.measurable_proposalQuadratic n k ij.1 ij.2 t).abs)).const_mul _))

theorem integral_resolventJetEnvelope_le_anchor (n : ℕ) (ω : Ω) (hd : 0 < d)
    (E sigma center : ℝ) :
    (∫ t,D.resolventJetEnvelope n E sigma (ω,t) ∂uniformOrientedProposals (N n) d) ≤
      (1+16*|sigma|)*‖(D.microscopicCountingState n ω E sigma center).val.2‖ := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hq (k : Fin (N n)) :
      (∫ t,∑ ij : Fin 4 × Fin 4,|D.proposalQuadratic n ω k ij.1 ij.2 t|
        ∂uniformOrientedProposals (N n) d) ≤ 16 := by
    rw [integral_finset_sum (μ := uniformOrientedProposals (N n) d) _ (fun ij _ => integrable_finiteUniform_real _)]
    calc
      _ ≤ ∑ _ij : Fin 4 × Fin 4,(1 : ℝ) := Finset.sum_le_sum (fun ij hij => D.integral_abs_proposalQuadratic_le_one n ω hd k ij.1 ij.2)
      _ = _ := by norm_num
  have hw : (∑ k,nevanlinnaWeight (D.microscopicEigenvalue n ω E sigma k)) ≤
      ‖(D.microscopicCountingState n ω E sigma center).val.2‖ := by
    have hh := Complex.im_le_norm (D.microscopicCountingState n ω E sigma center).val.2
    change (microscopicResolvent (D.microscopicEigenvalue n ω E sigma) (center/sigma) Complex.I).im ≤ _ at hh
    rwa [microscopicResolvent_im_I_eq_weight] at hh
  calc
    _ = ∑ k,nevanlinnaWeight (D.microscopicEigenvalue n ω E sigma k) *
        (1+|sigma| *(∫ t,∑ ij : Fin 4 × Fin 4,|D.proposalQuadratic n ω k ij.1 ij.2 t|
          ∂uniformOrientedProposals (N n) d)) := by
      unfold resolventJetEnvelope
      rw [integral_finset_sum (μ := uniformOrientedProposals (N n) d) _ (fun k _ => integrable_finiteUniform_real _)]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [integral_const_mul,integral_add (μ := uniformOrientedProposals (N n) d)
        (integrable_const _) ((integrable_finiteUniform_real _).const_mul _),integral_const_mul]
      simp
    _ ≤ ∑ k,nevanlinnaWeight (D.microscopicEigenvalue n ω E sigma k)*(1+|sigma| *16) := by
      apply Finset.sum_le_sum
      intro k hk
      have hweight := nevanlinnaWeight_nonneg (D.microscopicEigenvalue n ω E sigma k)
      gcongr
      exact hq k
    _ = (1+16*|sigma|)*(∑ k,nevanlinnaWeight (D.microscopicEigenvalue n ω E sigma k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

theorem resolventJetEnvelope_uniform_tails
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d) (E sigma center : ℝ)
    (htight : ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧ ∀ n,
      P.real {ω | A < ‖(D.microscopicCountingState n ω E sigma center).val.2‖} ≤ δ) :
    ∀ δ : ℝ,0 < δ → ∃ B : ℝ,0 < B ∧ ∀ n,
      (P.prod (uniformOrientedProposals (N n) d)).real
        {z | B < D.resolventJetEnvelope n E sigma z} ≤ δ := by
  letI : ∀ n,Nonempty (Fin (N n)) := fun n => ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N n) d) :=
    fun n => uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  apply uniform_tails_of_conditional_first_bound (fun _ => P)
    (fun n => uniformOrientedProposals (N n) d)
    (fun n ω => ‖(D.microscopicCountingState n ω E sigma center).val.2‖)
    (fun n => ((measurable_snd.comp (D.measurable_microscopicCountingState n E sigma center).subtype_val)).norm)
    (fun n => D.resolventJetEnvelope n E sigma)
    (fun n => D.measurable_resolventJetEnvelope n E sigma)
    (fun n z => D.resolventJetEnvelope_nonneg n E sigma z) (1+16*|sigma|) (by positivity)
    (fun n ω => integrable_finiteUniform_real _)
    (fun n ω => D.integral_resolventJetEnvelope_le_anchor n ω hd E sigma center) htight

end GeneralizedBulk.External.RegularSpectralData
