import GeneralizedBulk.Gaussian.PresentedAnalytic
import GeneralizedBulk.Gaussian.WeightedEvent
import GeneralizedBulk.Analysis.MeasurableSeries
import GeneralizedBulk.Exterior.Rotation

/-!
# A single measurable analytic field on scalar states times Gaussian marks

The anchor is one jointly measurable matrix random variable. The correction is
an actual pointwise sum of raw Gaussian marks. Setting the correction to zero
outside its proved measurable probability-one event makes every spectral
evaluation measurable, with no state-dependent choice of representatives.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian
variable {I S : Type*} [Countable I] [MeasurableSpace S]

def slotCorrection (x : ℝ) (v : ℂ × Bool) : ℂ :=
  if v.2 then particleCoefficient x v else anchorCorrection x v.1

theorem measurable_slotCorrection (v : ℂ × Bool) : Measurable (fun x => slotCorrection x v) := by
  unfold slotCorrection
  split_ifs
  · exact measurable_particleCoefficient v
  · unfold anchorCorrection
    split_ifs
    · exact measurable_const
    · exact (measurable_particleCoefficient (v.1, false)).sub
        (measurable_particleCoefficient (Complex.I, false))

def rawMarkMatrix (p : ℝ) (y : Fin 4 → ℝ) : EndpointMatrix :=
  fun i j => (rawQuadratic p i j y : ℂ)

def globalSeriesTerm (X : S → PresentedState I) (p : ℝ) (sigma : ℂ)
    (v : ℂ × Bool) (i j : Fin 4) (n : I) (z : S × (I → (Fin 4 → ℝ))) : ℂ := by
  classical
  exact if z ∈ weightedEvent X p then
    sigma * slotCorrection ((X z.1).location n) v * rawMarkMatrix p (z.2 n) i j else 0

def globalCenteredField (X : S → PresentedState I) (p : ℝ) (sigma : ℂ)
    (anchor : S × (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (v : ℂ × Bool) (z : S × (I → (Fin 4 → ℝ))) : EndpointMatrix := by
  classical
  exact fun i j => if z ∈ weightedEvent X p ∧ v.1.im ≠ 0 then
    (if v.2 then 0 else anchor z i j) + ∑' n, globalSeriesTerm X p sigma v i j n z else 0

theorem summable_globalSeriesTerm (X : S → PresentedState I) (p : ℝ) (sigma : ℂ)
    (v : ℂ × Bool) (i j : Fin 4) (z : S × (I → (Fin 4 → ℝ))) :
    Summable (fun n => globalSeriesTerm X p sigma v i j n z) := by
  classical
  by_cases hz : z ∈ weightedEvent X p
  · have hwgt := weightedEvent_entry_summable hz i j
    by_cases hw : v.1.im = 0
    · simpa [globalSeriesTerm, hz, slotCorrection, particleCoefficient, anchorCorrection, hw] using
        (summable_zero : Summable (fun _ : I => (0 : ℂ)))
    · rcases v with ⟨w, tag⟩
      cases tag
      · simpa [globalSeriesTerm, hz, slotCorrection, rawMarkMatrix] using
          Presented.summable_correction (X z.1).presentation sigma
            (fun n => (rawQuadratic p i j (z.2 n) : ℂ)) hwgt hw
      · simpa [globalSeriesTerm, hz, slotCorrection, rawMarkMatrix] using
          Presented.summable_derivative (X z.1).presentation sigma
            (fun n => (rawQuadratic p i j (z.2 n) : ℂ)) hwgt hw
  · simpa [globalSeriesTerm, hz] using (summable_zero : Summable (fun _ : I => (0 : ℂ)))

theorem measurable_globalCenteredField (X : S → PresentedState I) (hX : Measurable X)
    (p : ℝ) (sigma : ℂ) (anchor : S × (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (ha : Measurable anchor) (v : ℂ × Bool) : Measurable (globalCenteredField X p sigma anchor v) := by
  classical
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi
    (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hm (n : I) : Measurable (globalSeriesTerm X p sigma v i j n) := by
    apply Measurable.ite (measurableSet_weightedEvent X hX p)
    · exact (((measurable_slotCorrection v).comp
        (((PresentedState.measurable_location n).comp hX).comp measurable_fst)).const_mul sigma).mul
          ((measurable_rawQuadratic p i j).complex_ofReal.comp ((measurable_pi_apply n).comp measurable_snd))
    · exact measurable_const
  have hs := GeneralizedBulk.Analysis.measurable_tsum_of_summable
    (fun n => globalSeriesTerm X p sigma v i j n) hm
    (summable_globalSeriesTerm X p sigma v i j)
  have hanchor : Measurable (fun z => if v.2 then (0 : ℂ) else anchor z i j) := by
    cases htag : v.2
    · simpa only [htag, Bool.false_eq_true, ↓reduceIte] using
        (((continuous_apply j).comp (continuous_apply i)).measurable.comp ha)
    · simp only [htag, ↓reduceIte]
      exact measurable_const
  apply Measurable.ite _ (hanchor.add hs) measurable_const
  by_cases hw : v.1.im ≠ 0
  · convert measurableSet_weightedEvent X hX p using 1
    ext z
    exact and_iff_left hw
  · convert MeasurableSet.empty (α := S × (I → (Fin 4 → ℝ))) using 1
    ext z
    simp [hw]

/-- On the common event this is literally the presented analytic field,
simultaneously in every spectral parameter and derivative slot. -/
theorem globalCenteredField_eq_presented (X : S → PresentedState I) (p : ℝ) (sigma : ℂ)
    (anchor : S × (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (z : S × (I → (Fin 4 → ℝ))) (hz : z ∈ weightedEvent X p) (v : ℂ × Bool) :
    globalCenteredField X p sigma anchor v z =
      Presented.matrixField (X z.1).presentation (fun γ => anchor (z.1, γ)) sigma
        (fun n γ => rawMarkMatrix p (γ n)) v z.2 := by
  ext i j
  by_cases hw : v.1.im = 0
  · simp [globalCenteredField, Presented.matrixField, Presented.value,
      Presented.derivative, Presented.anchoredEntry, hw]
  · cases htag : v.2 <;>
      simp [globalCenteredField, globalSeriesTerm, slotCorrection, hz, hw, htag,
        Presented.matrixField, Presented.value, Presented.derivative, Presented.anchoredEntry,
        PresentedState.presentation, htag, particleCoefficient]

/-- One full-measure event supports the actual spectral derivative of all
entries at all nonreal points of this jointly measurable random-state field. -/
theorem globalCenteredField_hasDerivAt_ae
    (P : Measure S) [SFinite P] (X : S → PresentedState I) (hX : Measurable X)
    (p : ℝ) (sigma : ℂ) (anchor : S × (I → (Fin 4 → ℝ)) → EndpointMatrix) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw p) I), ∀ i j : Fin 4, ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun u => globalCenteredField X p sigma anchor (u, false) z i j)
        (globalCenteredField X p sigma anchor (w, true) z i j) w := by
  filter_upwards [ae_weightedEvent P X hX p] with z hz
  intro i j w hw
  have h := Presented.hasDerivAt_anchoredEntry (X z.1).presentation (anchor z i j) sigma
    (fun n => (rawQuadratic p i j (z.2 n) : ℂ)) (weightedEvent_entry_summable hz i j) hw
  convert h using 1
  · funext u
    rw [globalCenteredField_eq_presented X p sigma anchor z hz (u, false)]
    rfl
  · rw [globalCenteredField_eq_presented X p sigma anchor z hz (w, true)]
    simp only [Presented.matrixField, Presented.derivative, hw, ↓reduceIte, rawMarkMatrix]

end GeneralizedBulk.Gaussian
