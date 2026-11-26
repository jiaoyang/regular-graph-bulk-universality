import GeneralizedBulk.Graph.ProposalQuadraticMean
import GeneralizedBulk.Graph.WindowMarkLaw
import GeneralizedBulk.Analysis.GoodFiberMoments

/-! Every selected physical endpoint mark has exact second moment one on
every graph. Consequently finite mark tightness needs no Gaussian limit or
exceptional-event moment estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem proposalMark_coordinate_second {m : ℕ} (hd : 0 < d)
    (selection : Fin m → Fin (N n)) (j : Fin m × Fin 4) :
    (∫ t,(D.proposalMark n ω (fun a => D.eigenvector n ω (selection a)) t j)^2
      ∂uniformOrientedProposals (N n) d)=1 := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have heq (t : ProposalSample (N n) d) :
      (D.proposalMark n ω (fun a => D.eigenvector n ω (selection a)) t j)^2 =
        D.proposalQuadratic n ω (selection j.1) j.2 j.2 t := by
    dsimp [proposalMark,proposalQuadratic]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (N n))]
    ring
  simp_rw [heq]
  by_cases hc : selection j.1=⟨0,D.size_pos n⟩
  · simp only [hc,D.proposalQuadratic_constant n ω,integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul]
  · rw [D.proposalQuadratic_mean_nonconstant n ω hd _ hc]
    have hdiag : ∀ i : Fin 4,covarianceMatrix (D.eigenvalue n ω (selection j.1)/(d : ℝ)) i i=1 := by
      intro i
      fin_cases i <;> simp [covarianceMatrix_eq]
    exact hdiag j.2

theorem proposalMark_norm_second_le {m : ℕ} (hm : 0 < m) (hd : 0 < d)
    (selection : Fin m → Fin (N n)) :
    (∫ t,‖D.proposalMark n ω (fun a => D.eigenvector n ω (selection a)) t‖^2
      ∂uniformOrientedProposals (N n) d) ≤ (4*m : ℕ) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin m × Fin 4) := ⟨(⟨0,hm⟩,0)⟩
  have hp (x : (Fin m × Fin 4) → ℝ) : ‖x‖^2 ≤ ∑ j,x j^2 := by
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) Finset.univ_nonempty
    have hnorm : ‖x‖ ≤ ‖x j‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun l => hmax l (Finset.mem_univ l))
    calc
      _ ≤ ‖x j‖^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = x j^2 := by rw [Real.norm_eq_abs,sq_abs]
      _ ≤ _ := Finset.single_le_sum (fun j hj => sq_nonneg _) (Finset.mem_univ j)
  calc
    _ ≤ ∫ t,∑ j,(D.proposalMark n ω (fun a => D.eigenvector n ω (selection a)) t j)^2
        ∂uniformOrientedProposals (N n) d :=
      integral_mono (integrable_finiteUniform_real _) (integrable_finiteUniform_real _) (fun t => hp _)
    _ = ∑ j,∫ t,(D.proposalMark n ω (fun a => D.eigenvector n ω (selection a)) t j)^2
        ∂uniformOrientedProposals (N n) d := integral_finset_sum _ (fun _ _ => integrable_finiteUniform_real _)
    _ = _ := by simp only [D.proposalMark_coordinate_second n ω hd selection,Finset.sum_const,Finset.card_univ,
        Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]; ring

def selectedProposalMarks {m : ℕ} (selection : Ω → Fin m → Fin (N n))
    (z : Ω × ProposalSample (N n) d) : (Fin m × Fin 4) → ℝ :=
  D.proposalMark n z.1 (fun a => D.eigenvector n z.1 (selection z.1 a)) z.2

theorem measurable_selectedProposalMarks {m : ℕ} (selection : Ω → Fin m → Fin (N n))
    (hselection : ∀ a,Measurable (fun ω => selection ω a)) :
    Measurable (D.selectedProposalMarks n selection) := by
  apply measurable_pi_lambda
  rintro ⟨a,i⟩
  apply measurable_from_prod_countable
  intro t
  exact (D.measurable_selectedEigenvector n (fun ω => selection ω a)
    (fun ω => D.proposalEndpoints n ω t i) (hselection a) (D.measurable_proposalEndpoints n t i)).const_mul _

omit ω in
theorem selectedProposalMarks_second_integrable_bound {m : ℕ} (hm : 0 < m) (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (selection : Ω → Fin m → Fin (N n))
    (hselection : ∀ a,Measurable (fun ω => selection ω a)) :
    Integrable (fun z => ‖D.selectedProposalMarks n selection z‖^2) (P.prod (uniformOrientedProposals (N n) d)) ∧
      (∫ z,‖D.selectedProposalMarks n selection z‖^2 ∂P.prod (uniformOrientedProposals (N n) d)) ≤ (4*m : ℕ) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hh := integrableOn_prod_good_of_fiber_bound P (uniformOrientedProposals (N n) d) Set.univ MeasurableSet.univ
    (fun z => ‖D.selectedProposalMarks n selection z‖^2)
    ((D.measurable_selectedProposalMarks n selection hselection).norm.pow_const 2)
    (fun z => sq_nonneg _) (4*m : ℕ) (Nat.cast_nonneg _)
    (fun ω _ => integrable_finiteUniform_real _) (fun ω _ => D.proposalMark_norm_second_le n ω hm hd (selection ω))
  simpa only [Set.univ_prod_univ,Measure.restrict_univ,integrableOn_univ] using hh

end GeneralizedBulk.External.RegularSpectralData
