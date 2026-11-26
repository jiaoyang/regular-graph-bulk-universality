import GeneralizedBulk.LocalLaw.SourceProbability
import GeneralizedBulk.LocalLaw.SourceScaling
import GeneralizedBulk.Graph.HYResolventChannel
import SpectralConsequences.SourceDiagonalCap

/-! The actual source local law supplies the exact mesoscopic HY record on
the original uniform regular-graph ensemble, at every positive exponent. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.LocalLawBridge LocalLaw SpectralConsequences

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

private theorem source_transform_norm_le {M : ℕ} (hM : 0 < M)
    (g : LocalLaw.RegularGraph M d) (z : ℂ) (C : ℝ)
    (hdiag : ∀ i, ‖g.G z i i‖ ≤ C) :
    ‖LocalLaw.empiricalTransform g.H z‖ ≤ C := by
  have hm : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hsum : ‖∑ i : Fin M, g.G z i i‖ ≤ (M : ℝ) * C := by
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (fun i _ => hdiag i)).trans_eq (by simp)
  calc
    ‖LocalLaw.empiricalTransform g.H z‖ =
        (M : ℝ)⁻¹ * ‖∑ i : Fin M, g.G z i i‖ := by
      simp only [LocalLaw.empiricalTransform, Matrix.trace, LocalLaw.RegularGraph.G,
        Fintype.card_fin, norm_mul, norm_inv, Complex.norm_natCast]
      rfl
    _ ≤ (M : ℝ)⁻¹ * ((M : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm.le)
    _ = C := by field_simp

/-- The fixed source structural/local-law event, pulled back to the actual
spectral graph sample. -/
def sourceMesoscopicGood (hd : 3 ≤ d) (n : ℕ) : Set Ω :=
  {ω | LocalLaw.RegularGraph.structural
      (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
        ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ (D.localLawGraph n ω) ∧
      SourceLocalLawGood (D.localLawGraph n ω) (by omega) (1/128)}

theorem measurableSet_sourceMesoscopicGood (hd : 3 ≤ d) (n : ℕ) :
    MeasurableSet (D.sourceMesoscopicGood hd n) := by
  change MeasurableSet ((D.spectralRegularGraph n) ⁻¹'
    {g : Graph.RegularGraph (N n) d | LocalLaw.RegularGraph.structural
      (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
        ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128)})
  exact (D.measurable_spectralRegularGraph n) (Set.to_countable _).measurableSet

/-- No mesoscopic trace bound is assumed: the normalized source diagonal cap,
the exact raw-adjacency scaling, and polynomial source probabilities construct
all fields of HYMesoscopicInput. The energy set may be arbitrary. -/
def provedHYMesoscopicInput (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n, Measure.map (D.spectralRegularGraph n) P = regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (K : Set ℝ) (α : ℝ) (hα : 0 < α) :
    HYMesoscopicInput D P K α := by
  classical
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  let C : ℝ := 3 + sourceEigenvectorConstant d / s
  have hsource : 0 < sourceEigenvectorConstant d := sourceEigenvectorConstant_positive d hd
  have hC : 0 < C := by dsimp [C]; positivity
  have hCthree : (3 : ℝ) ≤ C := by
    dsimp [C]
    linarith [div_nonneg hsource.le hs.le]
  have hprob := D.size_tendsto.eventually (regularGraphLaw_source_structural_local_law d hd)
  have hcap := D.size_tendsto.eventually
    (SpectralConsequences.RegularGraph.eventually_source_local_law_diagonal_cap d (1/4) (1/128)
      hd (by norm_num) (by norm_num) (by norm_num))
  have hcut := D.size_tendsto.eventually
    (LocalLaw.eventually_const_mul_log_rpow_le s 300 α hα)
  have hex := eventually_atTop.mp (hprob.and (hcap.and hcut))
  let T := Classical.choose hex
  have hT := Classical.choose_spec hex
  let events : PolynomialGoodEvents P N := {
    good := D.sourceMesoscopicGood hd
    measurable_good := D.measurableSet_sourceMesoscopicGood hd
    exponent := 1/32
    constant := C
    exponent_pos := by norm_num
    constant_pos := hC
    threshold := T
    failure_bound := by
      intro n hn
      have hnonempty : Nonempty (LocalLaw.RegularGraph (N n) d) :=
        ⟨D.localLawGraph n (Classical.choice inferInstance)⟩
      have hp := (hT n hn).1 hnonempty
      have hset : MeasurableSet {g : Graph.RegularGraph (N n) d |
          ¬(LocalLaw.RegularGraph.structural
            (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
              ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128))} :=
        (Set.to_countable _).measurableSet
      have he : (P (D.sourceMesoscopicGood hd n)ᶜ).toReal =
          (regularGraphLaw (N n) d {g | ¬(LocalLaw.RegularGraph.structural
            (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
              ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128))}).toReal := by
        rw [← hUniform n, Measure.map_apply (D.measurable_spectralRegularGraph n) hset]
        rfl
      apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
      rw [he]
      exact hp.trans (mul_le_mul_of_nonneg_right hCthree (Real.rpow_nonneg (Nat.cast_nonneg _) _)) }
  refine { alpha_pos := hα, events := events, trace_bound := ?_ }
  intro n hn ω hgood x hx η hη hηlower hηupper
  have hg := hgood
  change LocalLaw.RegularGraph.structural
      (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
        ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ (D.localLawGraph n ω) ∧
      SourceLocalLawGood (D.localLawGraph n ω) (by omega) (1/128) at hg
  have hnreal : (0 : ℝ) < N n := Nat.cast_pos.mpr (D.size_pos n)
  have hcut' : s * Real.log (N n : ℝ)^300 ≤ (N n : ℝ)^α := by
    simpa only [show (300 : ℝ) = ((300 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      using (hT n hn).2.2
  let z : ℂ := ((x : ℂ) + η*Complex.I)/(s : ℂ)
  have hzim : z.im = η/s := by simp [z, Complex.div_ofReal_im]
  have hz : 0 < z.im := hzim ▸ div_pos hη hs
  have hfloor : Real.log (N n : ℝ)^300/(N n : ℝ) ≤ z.im := by
    rw [hzim]
    apply (div_le_div_iff₀ hnreal hs).mpr
    calc
      Real.log (N n : ℝ)^300*s = s*Real.log (N n : ℝ)^300 := mul_comm _ _
      _ ≤ (N n : ℝ)^α := hcut'
      _ = (N n : ℝ)^(-1+α)*(N n : ℝ) := by
        calc
          (N n : ℝ)^α = (N n : ℝ)^((-1+α)+1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hnreal, Real.rpow_one]
      _ ≤ η*(N n : ℝ) := mul_le_mul_of_nonneg_right hηlower hnreal.le
  have hdiag := (hT n hn).2.1 (D.localLawGraph n ω) hg.1 hg.2 z hz hfloor
  have hnorm := source_transform_norm_le (D.size_pos n) (D.localLawGraph n ω) z
    (sourceEigenvectorConstant d) hdiag
  have him : 0 < ((x : ℂ)+η*Complex.I).im := by simpa using hη
  have hscalar : ‖D.scalarResolvent n ω ((x : ℂ)+η*Complex.I)‖ ≤
      sourceEigenvectorConstant d/s := by
    rw [D.scalarResolvent_eq_localLaw_transform hd n ω _ him, norm_mul]
    have hsinv : ‖(Real.sqrt ((d : ℝ)-1) : ℂ)⁻¹‖ = s⁻¹ := by
      simp [s, abs_of_pos hs]
    rw [hsinv]
    calc
      s⁻¹ * ‖LocalLaw.empiricalTransform (D.localLawGraph n ω).H
          (((x : ℂ)+η*Complex.I)/(Real.sqrt ((d : ℝ)-1) : ℂ))‖ ≤
          s⁻¹ * sourceEigenvectorConstant d :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hs.le)
      _ = sourceEigenvectorConstant d/s := by ring
  exact (Complex.im_le_norm _).trans (hscalar.trans (by dsimp [events,C]; linarith))

end GeneralizedBulk.External.RegularSpectralData
