import GeneralizedBulk.Graph.RawCouplingLimit
import GeneralizedBulk.Analysis.CouplingSubsequence

/-! Actual raw switched-pair weak subsequences from the proved convergence
of their common marginal. Matrix values are handled by explicit finite real
coordinates, without adding a matrix norm convention. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open Exterior GeneralizedSwitching Analysis

abbrev RawComplexCoordinate := Unit ⊕ (Fin 4 × Fin 4)
abbrev RawRealCoordinate := RawComplexCoordinate × Fin 2

def rawComplexCoordinate (x : RawValue) : RawComplexCoordinate → ℂ :=
  Sum.elim (fun _ => x.1) (fun ij => x.2 ij.1 ij.2)

def rawRealCoordinates (x : RawValue) (j : RawRealCoordinate) : ℝ :=
  ![(rawComplexCoordinate x j.1).re,(rawComplexCoordinate x j.1).im] j.2

def rawFromRealCoordinates (v : RawRealCoordinate → ℝ) : RawValue :=
  (⟨v (Sum.inl (),0),v (Sum.inl (),1)⟩,
    fun i j => ⟨v (Sum.inr (i,j),0),v (Sum.inr (i,j),1)⟩)

def rawRealHomeomorph : RawValue ≃ₜ (RawRealCoordinate → ℝ) where
  toFun := rawRealCoordinates
  invFun := rawFromRealCoordinates
  left_inv x := by
    apply Prod.ext
    · apply Complex.ext <;> rfl
    · funext i j
      apply Complex.ext <;> rfl
  right_inv v := by
    funext j
    rcases j with ⟨j,t⟩
    cases j with
    | inl u => cases u; fin_cases t <;> rfl
    | inr ij => fin_cases t <;> rfl
  continuous_toFun := by
    apply continuous_pi
    rintro ⟨j,t⟩
    cases j with
    | inl u =>
      fin_cases t
      · change Continuous (fun x : RawValue => x.1.re)
        fun_prop
      · change Continuous (fun x : RawValue => x.1.im)
        fun_prop
    | inr ij =>
      fin_cases t
      · change Continuous (fun x : RawValue => (x.2 ij.1 ij.2).re)
        fun_prop
      · change Continuous (fun x : RawValue => (x.2 ij.1 ij.2).im)
        fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · change Continuous (fun v : RawRealCoordinate → ℝ => (⟨v (Sum.inl (),0),v (Sum.inl (),1)⟩ : ℂ))
      have hp : Continuous (fun v : RawRealCoordinate → ℝ => (v (Sum.inl (),0),v (Sum.inl (),1))) :=
        (continuous_apply _).prodMk (continuous_apply _)
      exact Complex.equivRealProdCLM.symm.continuous.comp hp
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun v : RawRealCoordinate → ℝ => (⟨v (Sum.inr (i,j),0),v (Sum.inr (i,j),1)⟩ : ℂ))
      have hp : Continuous (fun v : RawRealCoordinate → ℝ => (v (Sum.inr (i,j),0),v (Sum.inr (i,j),1))) :=
        (continuous_apply _).prodMk (continuous_apply _)
      exact Complex.equivRealProdCLM.symm.continuous.comp hp

theorem microscopicRawPairLaw_subsequence_of_marginal_weak
    (N : ℕ → ℕ) (hN : ∀ n,0 < N n) (d : ℕ) (hd : 0 < d)
    [∀ n,Nonempty (RegularGraph (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (ρ : Measure RawValue) [IsProbabilityMeasure ρ]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawLaw (d := d) (hN n) E sigma a hsigma w) ρ) :
    ∃ (ν : ProbabilityMeasure RawPair) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges
        (fun n => microscopicRawPairLaw (d := d) (hN (r n)) E sigma a hsigma w) (ν : Measure RawPair) ∧
      (ν : Measure RawPair).map Prod.fst = ρ ∧ (ν : Measure RawPair).map Prod.snd = ρ := by
  letI : ∀ n,Nonempty (EdgePairState (N n) d) := fun n => edgePairState_nonempty (hN n) hd
  let laws : ℕ → ProbabilityMeasure RawPair :=
    fun n => ⟨microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w,inferInstance⟩
  have hleft : External.WeakLawConverges (fun n => (laws n : Measure RawPair).map Prod.fst) ρ := by
    intro F
    change Tendsto (fun n => ∫ x,F x ∂Measure.map Prod.fst (microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w)) atTop _
    simp_rw [microscopicRawPairLaw_fst]
    exact hweak F
  have hright : External.WeakLawConverges (fun n => (laws n : Measure RawPair).map Prod.snd) ρ := by
    intro F
    change Tendsto (fun n => ∫ x,F x ∂Measure.map Prod.snd (microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w)) atTop _
    simp_rw [microscopicRawPairLaw_snd]
    exact hweak F
  obtain ⟨ν,r,hr,hw⟩ := coupling_subsequence_of_weak_marginals_finite_homeomorph laws ρ hleft hright rawRealHomeomorph
  have hpair : External.WeakLawConverges
      (fun n => microscopicRawPairLaw (d := d) (hN (r n)) E sigma a hsigma w) (ν : Measure RawPair) := by
    intro F
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw F
  have hmarginal : External.WeakLawConverges
      (fun n => microscopicRawLaw (d := d) (hN (r n)) E sigma a hsigma w) ρ := fun F =>
    (hweak F).comp hr.tendsto_atTop
  have hboth := microscopicRawPairLimit_marginals (fun n => N (r n)) (fun n => hN (r n)) d E sigma a hsigma w
    (ν : Measure RawPair) ρ hpair hmarginal
  exact ⟨ν,r,hr,hpair,hboth⟩

/-- Real coordinates for a whole finite spectral family. The same graph and
proposal are retained at every spectral parameter. -/
def rawFieldRealHomeomorph (I : Type*) : (I → RawValue) ≃ₜ ((I × RawRealCoordinate) → ℝ) where
  toFun x ij := rawRealHomeomorph (x ij.1) ij.2
  invFun y i := rawRealHomeomorph.symm (fun j => y (i,j))
  left_inv x := by
    funext i
    exact rawRealHomeomorph.symm_apply_apply (x i)
  right_inv y := by
    funext ij
    exact congrFun (rawRealHomeomorph.apply_symm_apply (fun j => y (ij.1,j))) ij.2
  continuous_toFun := by
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.2).comp (rawRealHomeomorph.continuous.comp (continuous_apply ij.1))
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact rawRealHomeomorph.symm.continuous.comp (continuous_pi (fun j => continuous_apply (i,j)))

abbrev RawField (I : Type*) := I → RawValue
abbrev RawFieldPair (I : Type*) := RawField I × RawField I

def microscopicRawField {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal)
    (s : EdgePairState N d) : RawField I :=
  fun i => microscopicRawValue hN E sigma a hsigma (w i) s

def microscopicRawFieldPair {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal)
    (s : EdgePairState N d) : RawFieldPair I :=
  (microscopicRawField hN E sigma a hsigma w s,
    microscopicRawField hN E sigma a hsigma w (proposalSwitch s))

def microscopicRawFieldLaw {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) : Measure (RawField I) :=
  Measure.map (microscopicRawField (d := d) hN E sigma a hsigma w) (edgePairLaw N d)

def microscopicRawFieldPairLaw {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) : Measure (RawFieldPair I) :=
  Measure.map (microscopicRawFieldPair (d := d) hN E sigma a hsigma w) (edgePairLaw N d)

instance microscopicRawFieldLaw_isProbability {I : Type*} {N d : ℕ}
    [Nonempty (EdgePairState N d)] (hN : 0 < N) (E sigma a : ℝ)
    (hsigma : 0 < sigma) (w : I → GraphNonreal) :
    IsProbabilityMeasure (microscopicRawFieldLaw (d := d) hN E sigma a hsigma w) := by
  letI : IsProbabilityMeasure (edgePairLaw N d) := finiteUniform_isProbability _
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

instance microscopicRawFieldPairLaw_isProbability {I : Type*} {N d : ℕ}
    [Nonempty (EdgePairState N d)] (hN : 0 < N) (E sigma a : ℝ)
    (hsigma : 0 < sigma) (w : I → GraphNonreal) :
    IsProbabilityMeasure (microscopicRawFieldPairLaw (d := d) hN E sigma a hsigma w) := by
  letI : IsProbabilityMeasure (edgePairLaw N d) := finiteUniform_isProbability _
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem microscopicRawFieldPairLaw_fst {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) :
    Measure.map Prod.fst (microscopicRawFieldPairLaw (d := d) hN E sigma a hsigma w) =
      microscopicRawFieldLaw (d := d) hN E sigma a hsigma w := by
  rw [microscopicRawFieldPairLaw,Measure.map_map measurable_fst (measurable_of_finite _)]
  rfl

theorem microscopicRawFieldPairLaw_snd {I : Type*} {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) :
    Measure.map Prod.snd (microscopicRawFieldPairLaw (d := d) hN E sigma a hsigma w) =
      microscopicRawFieldLaw (d := d) hN E sigma a hsigma w := by
  rw [microscopicRawFieldPairLaw,Measure.map_map measurable_snd (measurable_of_finite _)]
  change Measure.map (microscopicRawField hN E sigma a hsigma w ∘ proposalSwitch)
    (edgePairLaw N d) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),edgePairLaw_switch_invariant]
  rfl

/-- Actual switched graph pairs have joint weak subsequences for every finite
spectral family as soon as the common single-field marginal converges. Both
limiting marginals are identified with that entire joint field law. -/
theorem microscopicRawFieldPairLaw_subsequence_of_marginal_weak
    {I : Type*} [Fintype I]
    (N : ℕ → ℕ) (hN : ∀ n,0 < N n) (d : ℕ) (hd : 0 < d)
    [∀ n,Nonempty (RegularGraph (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal)
    (ρ : Measure (RawField I)) [IsProbabilityMeasure ρ]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawFieldLaw (d := d) (hN n) E sigma a hsigma w) ρ) :
    ∃ (ν : ProbabilityMeasure (RawFieldPair I)) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges
        (fun n => microscopicRawFieldPairLaw (d := d) (hN (r n)) E sigma a hsigma w)
        (ν : Measure (RawFieldPair I)) ∧
      (ν : Measure (RawFieldPair I)).map Prod.fst = ρ ∧
      (ν : Measure (RawFieldPair I)).map Prod.snd = ρ := by
  letI : ∀ n,Nonempty (EdgePairState (N n) d) := fun n => edgePairState_nonempty (hN n) hd
  let laws : ℕ → ProbabilityMeasure (RawFieldPair I) :=
    fun n => ⟨microscopicRawFieldPairLaw (d := d) (hN n) E sigma a hsigma w,inferInstance⟩
  have hleft : External.WeakLawConverges (fun n => (laws n : Measure (RawFieldPair I)).map Prod.fst) ρ := by
    intro F
    change Tendsto (fun n => ∫ x,F x ∂Measure.map Prod.fst
      (microscopicRawFieldPairLaw (d := d) (hN n) E sigma a hsigma w)) atTop _
    simp_rw [microscopicRawFieldPairLaw_fst]
    exact hweak F
  have hright : External.WeakLawConverges (fun n => (laws n : Measure (RawFieldPair I)).map Prod.snd) ρ := by
    intro F
    change Tendsto (fun n => ∫ x,F x ∂Measure.map Prod.snd
      (microscopicRawFieldPairLaw (d := d) (hN n) E sigma a hsigma w)) atTop _
    simp_rw [microscopicRawFieldPairLaw_snd]
    exact hweak F
  obtain ⟨ν,r,hr,hw⟩ := coupling_subsequence_of_weak_marginals_finite_homeomorph
    laws ρ hleft hright (rawFieldRealHomeomorph I)
  have hpair : External.WeakLawConverges
      (fun n => microscopicRawFieldPairLaw (d := d) (hN (r n)) E sigma a hsigma w)
      (ν : Measure (RawFieldPair I)) := by
    intro F
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw F
  have hmarginal : External.WeakLawConverges
      (fun n => microscopicRawFieldLaw (d := d) (hN (r n)) E sigma a hsigma w) ρ :=
    fun F => (hweak F).comp hr.tendsto_atTop
  have hleft' : External.WeakLawConverges
      (fun n => Measure.map Prod.fst
        (microscopicRawFieldPairLaw (d := d) (hN (r n)) E sigma a hsigma w)) ρ := by
    simpa only [microscopicRawFieldPairLaw_fst] using hmarginal
  have hright' : External.WeakLawConverges
      (fun n => Measure.map Prod.snd
        (microscopicRawFieldPairLaw (d := d) (hN (r n)) E sigma a hsigma w)) ρ := by
    simpa only [microscopicRawFieldPairLaw_snd] using hmarginal
  exact ⟨ν,r,hr,hpair,
    weak_limit_marginal_eq _ _ hpair Prod.fst continuous_fst ρ hleft',
    weak_limit_marginal_eq _ _ hpair Prod.snd continuous_snd ρ hright'⟩

def rawFieldPairEvaluation {I : Type*} (i : I) (x : RawFieldPair I) : RawPair :=
  (x.1 i,x.2 i)

theorem continuous_rawFieldPairEvaluation {I : Type*} (i : I) :
    Continuous (rawFieldPairEvaluation i) :=
  ((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem microscopicRawFieldPairLaw_evaluation {I : Type*} [Fintype I] {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) (i : I) :
    Measure.map (rawFieldPairEvaluation i)
      (microscopicRawFieldPairLaw (d := d) hN E sigma a hsigma w) =
      microscopicRawPairLaw (d := d) hN E sigma a hsigma (w i) := by
  rw [microscopicRawFieldPairLaw,
    Measure.map_map (continuous_rawFieldPairEvaluation i).measurable (measurable_of_finite _)]
  rfl

/-- One common limiting event carries the inverse-free switch identity at
every parameter of the retained finite spectral family. -/
theorem microscopicRawFieldPairLimit_inverse_free
    {I : Type*} [Fintype I]
    (N : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNlimit : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) [∀ n,Nonempty (RegularGraph (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal)
    (ν : Measure (RawFieldPair I)) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawFieldPairLaw (d := d) (hN n) E sigma a hsigma w) ν) :
    ∀ᵐ x ∂ν,∀ i,(1 + (x.1 i).2 * switchIncrement) *
      (endpointPermutation * (x.2 i).2 * endpointPermutation) = (x.1 i).2 := by
  apply ae_all_iff.mpr
  intro i
  have hc := continuous_rawFieldPairEvaluation i
  letI : IsProbabilityMeasure (Measure.map (rawFieldPairEvaluation i) ν) :=
    isProbabilityMeasure_map hc.measurable.aemeasurable
  have hw := weakLaw_map _ ν hweak (rawFieldPairEvaluation i) hc
  simp_rw [microscopicRawFieldPairLaw_evaluation] at hw
  have hi := microscopicRawPairLimit_inverse_free N hN hNlimit d hd E sigma a hsigma (w i)
    (Measure.map (rawFieldPairEvaluation i) ν) hw
  exact ae_of_ae_map hc.measurable.aemeasurable hi

theorem microscopicRawFieldPairLimit_rank_bound
    {I : Type*} [Fintype I]
    (N : ℕ → ℕ) (hN : ∀ n,0 < N n) (d : ℕ)
    [∀ n,Nonempty (EdgePairState (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal)
    (ν : Measure (RawFieldPair I)) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawFieldPairLaw (d := d) (hN n) E sigma a hsigma w) ν) :
    ∀ᵐ x ∂ν,∀ i,‖(x.2 i).1 - (x.1 i).1‖ ≤ 4 / |(w i).val.im| := by
  apply ae_all_iff.mpr
  intro i
  have hc := continuous_rawFieldPairEvaluation i
  letI : IsProbabilityMeasure (Measure.map (rawFieldPairEvaluation i) ν) :=
    isProbabilityMeasure_map hc.measurable.aemeasurable
  have hw := weakLaw_map _ ν hweak (rawFieldPairEvaluation i) hc
  simp_rw [microscopicRawFieldPairLaw_evaluation] at hw
  have hi := microscopicRawPairLimit_rank_bound N hN d E sigma a hsigma (w i)
    (Measure.map (rawFieldPairEvaluation i) ν) hw
  exact ae_of_ae_map hc.measurable.aemeasurable hi

end GeneralizedBulk.Graph
