import GeneralizedBulk.Exterior.GaussianOrdinaryLaw

/-!
# Recovering derivative jets measurably from spectral values

Horizontal difference quotients remain in the same half-plane. Real and
imaginary limsups give a Borel extraction defined even on arbitrary functions;
on differentiable fields it equals the actual derivative. Consequently value
law symmetry suffices for the derivative-jet law used by the flow.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GeneralizedBulk.Exterior

def horizontalStep (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

def horizontalShift (w : NonrealSpectral) (n : ℕ) : NonrealSpectral :=
  ⟨w.1 + horizontalStep n, by simpa [horizontalStep] using w.2⟩

def horizontalDifference (K : NonrealSpectral → Mat) (w : NonrealSpectral) (n : ℕ) : Mat :=
  (horizontalStep n)⁻¹ • (K (horizontalShift w n) - K w)

def spectralDerivative (K : NonrealSpectral → Mat) (w : NonrealSpectral) : Mat :=
  fun i j => ((limsup (fun n => (horizontalDifference K w n i j).re) atTop : ℝ) : ℂ) +
    ((limsup (fun n => (horizontalDifference K w n i j).im) atTop : ℝ) : ℂ) * Complex.I

theorem measurable_spectralDerivative (w : NonrealSpectral) :
    Measurable (fun K => spectralDerivative K w) := by
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi
    (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hd (n : ℕ) : Measurable (fun K => horizontalDifference K w n i j) := by
    have he (u : NonrealSpectral) : Measurable (fun K : NonrealSpectral → Mat => K u i j) :=
      ((show Continuous (fun A : Mat => A i j) from
        (continuous_apply j).comp (continuous_apply i)).measurable.comp (measurable_pi_apply u))
    exact ((he (horizontalShift w n)).sub (he w)).const_mul _
  exact ((Measurable.limsup (fun n => (hd n).re)).complex_ofReal).add
    (((Measurable.limsup (fun n => (hd n).im)).complex_ofReal).mul_const Complex.I)

theorem spectralDerivative_eq_of_tendsto (K : NonrealSpectral → Mat)
    (w : NonrealSpectral) (L : Mat)
    (h : Tendsto (horizontalDifference K w) atTop (𝓝 L)) :
    spectralDerivative K w = L := by
  ext i j
  have he := ((continuous_apply j).comp (continuous_apply i)).tendsto L |>.comp h
  have hr : Tendsto (fun n => (horizontalDifference K w n i j).re) atTop (𝓝 (L i j).re) :=
    (Complex.continuous_re.tendsto (L i j)).comp he
  have hi : Tendsto (fun n => (horizontalDifference K w n i j).im) atTop (𝓝 (L i j).im) :=
    (Complex.continuous_im.tendsto (L i j)).comp he
  simp only [spectralDerivative, hr.limsup_eq, hi.limsup_eq, Complex.re_add_im]

theorem horizontalStep_tendsto : Tendsto horizontalStep atTop (𝓝 (0 : ℂ)) := by
  simpa only [horizontalStep, Complex.ofReal_zero] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat

theorem horizontalStep_ne_zero (n : ℕ) : horizontalStep n ≠ 0 := by
  simp only [horizontalStep, ne_eq, Complex.ofReal_eq_zero, one_div, inv_eq_zero]
  positivity

theorem horizontalDifference_tendsto_of_hasDerivAt
    {f : ℂ → Mat} {f' : Mat} {w : NonrealSpectral} (hf : HasDerivAt f f' w.1) :
    Tendsto (horizontalDifference (fun u => f u.1) w) atTop (𝓝 f') := by
  have hs : Tendsto horizontalStep atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨horizontalStep_tendsto,
      Eventually.of_forall horizontalStep_ne_zero⟩
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have he := hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) j
  simpa only [horizontalDifference, horizontalShift, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul] using he.tendsto_slope_zero.comp hs

abbrev ValueState := (NonrealSpectral → ℂ) × (NonrealSpectral → Mat)

def liftValueState (state : ValueState) : JetState NonrealSpectral :=
  (state.1, fun slot => if slot.2 then spectralDerivative state.2 slot.1 else state.2 slot.1)

theorem measurable_liftValueState : Measurable liftValueState := by
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun slot => ?_)
  cases hb : slot.2
  · exact (measurable_pi_apply slot.1).comp measurable_snd
  · exact (measurable_spectralDerivative slot.1).comp measurable_snd

def valueOfJet (state : JetState NonrealSpectral) : ValueState :=
  (state.1, fun w => state.2 (w, false))

theorem measurable_valueOfJet : Measurable valueOfJet :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun w =>
    (measurable_pi_apply (w, false)).comp measurable_snd)

theorem horizontalDifference_conjugate (K : NonrealSpectral → Mat)
    (Q : Mat) (w : NonrealSpectral) (n : ℕ) :
    horizontalDifference (fun u => Q * K u * Q.transpose) w n =
      Q * horizontalDifference K w n * Q.transpose := by
  simp only [horizontalDifference, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem liftValueState_eq_jet (state : JetState NonrealSpectral)
    (hd : ∀ w, Tendsto (horizontalDifference (fun u => state.2 (u, false)) w)
      atTop (𝓝 (state.2 (w, true)))) :
    liftValueState (valueOfJet state) = state := by
  apply Prod.ext
  · rfl
  · funext slot
    rcases slot with ⟨w, tag⟩
    cases tag
    · rfl
    · exact spectralDerivative_eq_of_tendsto _ w _ (hd w)

theorem liftValueState_action_eq (state : JetState NonrealSpectral)
    (hd : ∀ w, Tendsto (horizontalDifference (fun u => state.2 (u, false)) w)
      atTop (𝓝 (state.2 (w, true)))) (Q : Mat) :
    liftValueState (action Q (valueOfJet state)) = action Q state := by
  change liftValueState (valueOfJet (action Q state)) = action Q state
  apply liftValueState_eq_jet
  intro w
  have hc : Continuous (fun A : Mat => Q * A * Q.transpose) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have ht := (hc.tendsto _).comp (hd w)
  change Tendsto (horizontalDifference (fun u => Q * state.2 (u, false) * Q.transpose) w)
    atTop (𝓝 (Q * state.2 (w, true) * Q.transpose))
  convert ht using 1
  funext n
  exact horizontalDifference_conjugate _ Q w n

/-- Equality of exterior value laws lifts to equality of jet laws; the
derivative law is not an additional switching hypothesis. -/
theorem jet_law_symmetry_of_value_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jet : Ω → JetState NonrealSpectral) (hjet : Measurable jet) (Q : Mat)
    (hd : ∀ᵐ ω ∂P, ∀ w,
      Tendsto (horizontalDifference (fun u => (jet ω).2 (u, false)) w)
        atTop (𝓝 ((jet ω).2 (w, true))))
    (hsym : Measure.map (action Q) (Measure.map (fun ω => valueOfJet (jet ω)) P) =
      Measure.map (fun ω => valueOfJet (jet ω)) P) :
    Measure.map (action Q) (Measure.map jet P) = Measure.map jet P := by
  have hleft : Measure.map liftValueState
      (Measure.map (action Q) (Measure.map (fun ω => valueOfJet (jet ω)) P)) =
        Measure.map (action Q) (Measure.map jet P) := by
    rw [Measure.map_map measurable_liftValueState (measurable_action Q),
      Measure.map_map (f := fun ω => valueOfJet (jet ω))
        (measurable_liftValueState.comp (measurable_action Q))
        (measurable_valueOfJet.comp hjet), Measure.map_map (measurable_action Q) hjet]
    apply Measure.map_congr
    exact hd.mono (fun ω h => liftValueState_action_eq (jet ω) h Q)
  have hright : Measure.map liftValueState
      (Measure.map (fun ω => valueOfJet (jet ω)) P) = Measure.map jet P := by
    rw [Measure.map_map (f := fun ω => valueOfJet (jet ω))
      measurable_liftValueState (measurable_valueOfJet.comp hjet)]
    exact Measure.map_congr (hd.mono (fun ω h => liftValueState_eq_jet (jet ω) h))
  rw [← hleft, hsym, hright]

end GeneralizedBulk.Exterior
