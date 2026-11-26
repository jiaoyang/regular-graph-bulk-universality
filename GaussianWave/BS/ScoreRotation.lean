import GaussianWave.BS.ScoreProjection

/-! Actual score projection under arbitrary finite orthonormal-row observations.
The proof completes the rows to orthogonal coordinates and transports the
proved coordinate-fiber conditional expectation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def orthogonalMatrixEquiv
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1) :
    (I → ℝ) ≃L[ℝ] (K → ℝ) :=
  (Matrix.toLin'OfInv hRT hRR).toContinuousLinearEquiv

@[simp] theorem orthogonalMatrixEquiv_apply
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1) (x : I → ℝ) :
    orthogonalMatrixEquiv R hRR hRT x = R.mulVec x := rfl

@[simp] theorem orthogonalMatrixEquiv_symm_apply
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1) (x : K → ℝ) :
    (orthogonalMatrixEquiv R hRR hRT).symm x = R.transpose.mulVec x := rfl

theorem heatKernel_orthogonal_change
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1)
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatKernel t (R.mulVec x) = heatKernel t x := by
  have hcard : Fintype.card I = Fintype.card K := by
    simpa using (LinearEquiv.finrank_eq (orthogonalMatrixEquiv R hRR hRT).toLinearEquiv)
  have hsq : squareMass (R.mulVec x) = squareMass x := by
    simpa only [Matrix.vecMul_transpose] using
      squareMass_vecMul_of_orthonormal_rows R.transpose (by simpa using hRT) x
  rw [heatKernel_factor ht, heatKernel_factor ht, hsq]
  congr 1
  simp only [heatKernelBound, Finset.prod_const, Finset.card_univ, hcard]

theorem heatDensity_orthogonal_change
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1)
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatDensity (Measure.map (fun y => R.mulVec y) μ) t (R.mulVec x) = heatDensity μ t x := by
  unfold heatDensity
  have hm : AEStronglyMeasurable (fun y : K → ℝ => heatKernel t (R.mulVec x - y))
      (Measure.map (fun y => R.mulVec y) μ) :=
    (((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  rw [integral_map (measurable_finiteMatrixAction R).aemeasurable
    hm]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← Matrix.mulVec_sub, heatKernel_orthogonal_change R hRR hRT ht]

/-- A full orthogonal coordinate change transforms the actual directional
heat score by the genuine chain rule. -/
theorem heatDirectionalScore_orthogonal_change
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (R : Matrix K I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1)
    {t : ℝ} (ht : 0 < t) (v x : I → ℝ) :
    heatDirectionalScore (Measure.map (fun y => R.mulVec y) μ) t (R.mulVec v) (R.mulVec x) =
      heatDirectionalScore μ t v x := by
  let μR := Measure.map (fun y => R.mulVec y) μ
  let R₀ := orthogonalMatrixEquiv R hRR hRT
  letI : IsProbabilityMeasure μR := isProbabilityMeasure_map (measurable_finiteMatrixAction R).aemeasurable
  have heq : heatDensity μR t ∘ R₀ = heatDensity μ t := by
    funext y
    exact heatDensity_orthogonal_change μ R hRR hRT ht y
  have hd := (hasFDerivAt_heatDensity μR ht (R₀ x)).comp x R₀.hasFDerivAt
  rw [heq] at hd
  have h := congrArg (fun L : (I → ℝ) →L[ℝ] ℝ => L v)
    (hd.unique (hasFDerivAt_heatDensity μ ht x))
  rw [← (hasFDerivAt_heatDensity μR ht (R₀ x)).fderiv,
    ← (hasFDerivAt_heatDensity μ ht x).fderiv] at h
  change fderiv ℝ (heatDensity μR t) (R.mulVec x) (R.mulVec v) =
    fderiv ℝ (heatDensity μ t) x v at h
  rw [heatDirectionalScore_eq_fderiv μR ht, heatDirectionalScore_eq_fderiv μ ht,
    h, heatDensity_orthogonal_change μ R hRR hRT ht]

theorem condExp_heatDirectionalScore_completed_coordinates
    {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (R : Matrix (J ⊕ L) I ℝ) (hRR : R * R.transpose = 1) (hRT : R.transpose * R = 1)
    (j : J) :
    let observation := fun x : I → ℝ => leftCoordinates (R.mulVec x)
    (heatedLaw μ t)[heatDirectionalScore μ t (R (Sum.inl j)) |
      MeasurableSpace.comap observation inferInstance] =ᵐ[heatedLaw μ t]
        (fun x => heatDirectionalScore (Measure.map observation μ) t (Pi.single j 1) (observation x)) := by
  intro observation
  let μR := Measure.map (fun y => R.mulVec y) μ
  letI : IsProbabilityMeasure μR := isProbabilityMeasure_map (measurable_finiteMatrixAction R).aemeasurable
  letI : Fact (0 < t) := ⟨ht⟩
  let R₀ := orthogonalMatrixEquiv R hRR hRT
  let eR := R₀.toHomeomorph.toMeasurableEquiv
  let eS := MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ L => ℝ)
  let e := eR.trans eS
  have hRpres : MeasurePreserving eR (heatedLaw μ t) (heatedLaw μR t) :=
    ⟨eR.measurable, heatedLaw_map_orthonormal_rows μ R hRR t⟩
  have hSpres : MeasurePreserving eS (heatedLaw μR t) (splitHeatedLaw μR t) :=
    ⟨eS.measurable, (splitHeatedLaw_eq_map μR ht).symm⟩
  have he : MeasurePreserving e (heatedLaw μ t) (splitHeatedLaw μR t) := hSpres.comp hRpres
  have hjoin (x : I → ℝ) : Sum.elim (e x).1 (e x).2 = R.mulVec x := by
    ext a
    cases a <;> rfl
  have hvec : R.mulVec (R (Sum.inl j)) = Pi.single (Sum.inl j) 1 := by
    have hr : R.transpose.mulVec (Pi.single (Sum.inl j) 1) = R (Sum.inl j) := by
      ext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← hr, Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec]
  have hfull : (fun x => splitHeatCoordinateScore μR t j (e x)) =
      heatDirectionalScore μ t (R (Sum.inl j)) := by
    funext x
    unfold splitHeatCoordinateScore splitHeatedDensity
    rw [hjoin, ← heatDirectionalScore_coordinate]
    rw [← hvec]
    exact heatDirectionalScore_orthogonal_change μ R hRR hRT ht _ x
  have hleft : Measure.map leftCoordinates μR = Measure.map observation μ := by
    rw [Measure.map_map measurable_leftCoordinates (measurable_finiteMatrixAction R)]
    rfl
  have hCE := condExp_heatDensity_coordinate_score μR ht j
  change (splitHeatedLaw μR t)[splitHeatCoordinateScore μR t j |
    MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[splitHeatedLaw μR t]
      (fun p : (J → ℝ) × (L → ℝ) =>
        heatDensityGradient (Measure.map leftCoordinates μR) t p.1 j /
          heatDensity (Measure.map leftCoordinates μR) t p.1) at hCE
  have h := condExp_observation_comp_equiv (heatedLaw μ t) (splitHeatedLaw μR t) e he
    Prod.fst measurable_fst (splitHeatCoordinateScore μR t j)
    ((memLp_splitHeatCoordinateScore μR ht j).integrable one_le_two)
  rw [hfull] at h
  have hpull := he.quasiMeasurePreserving.ae_eq hCE
  have hres := h.trans hpull
  change (heatedLaw μ t)[heatDirectionalScore μ t (R (Sum.inl j)) |
    MeasurableSpace.comap observation inferInstance] =ᵐ[heatedLaw μ t]
      (fun x => heatDensityGradient (Measure.map leftCoordinates μR) t (observation x) j /
        heatDensity (Measure.map leftCoordinates μR) t (observation x)) at hres
  simpa only [hleft, heatDirectionalScore_coordinate] using hres

/-- The actual conditional-score identity for every finite orthonormal-row
observation of an arbitrary heated law. The score projection is a conclusion. -/
theorem condExp_heatDirectionalScore_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J) :
    (heatedLaw μ t)[heatDirectionalScore μ t (O j) |
      MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance] =ᵐ[heatedLaw μ t]
        (fun x => heatDirectionalScore (Measure.map (fun y : I → ℝ => O.mulVec y) μ)
          t (Pi.single j 1) (O.mulVec x)) := by
  obtain ⟨R, hfirst, hRR, hRT⟩ := exists_orthogonal_row_completion O hO
  have hobs : (fun x : I → ℝ => leftCoordinates (R.mulVec x)) = (fun x => O.mulVec x) := by
    funext x
    ext j
    change R (Sum.inl j) ⬝ᵥ x = O j ⬝ᵥ x
    rw [hfirst]
  have h := condExp_heatDirectionalScore_completed_coordinates μ ht R hRR hRT j
  have hobs' (x : I → ℝ) : leftCoordinates (R.mulVec x) = O.mulVec x := congrFun hobs x
  simpa only [hobs, hobs', hfirst] using h

/-- The same identity for the genuine full-law L2 scores used by U3. -/
theorem conditionalScore_heatDirectionalScore_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J) :
    (conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)) :
        (I → ℝ) → ℝ) =ᵐ[heatedLaw μ t]
          (fun x => heatDirectionalScore (Measure.map (fun y : I → ℝ => O.mulVec y) μ)
            t (Pi.single j 1) (O.mulVec x)) := by
  have h := (memLp_heatDirectionalScore μ ht (O j)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (measurable_finiteMatrixAction O).comap_le
  exact h.trans (condExp_heatDirectionalScore_orthonormal_rows μ ht O hO j)

end GaussianWave.BS
