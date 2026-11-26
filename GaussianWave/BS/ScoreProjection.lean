import GaussianWave.BS.UpperGeometry
import GaussianWave.BS.HeatDerivatives
import GaussianWave.BS.HeatIntegrationByParts
import GaussianWave.BS.HeatSymmetry
import GaussianWave.BS.HeatScores

/-!
# Directional score transformation under actual marginal reversal

Only an edge marginal must have reversal symmetry; no symmetry of the full
star law under this reflection is assumed. A chain-rule calculation transforms
the actual density score, and Lebesgue change of variables gives equal
observed directional Fisher energies. The kernel-to-conditional-expectation
identity is a separate analytic step.
-/
noncomputable section
open MeasureTheory
open scoped Topology BigOperators

namespace GaussianWave.BS

/-- Actual directional score of a differentiable density. At a positive
density this is the directional derivative of its logarithm. -/
def directionalScore {I : Type*} [Fintype I] (f : (I → ℝ) → ℝ)
    (u x : I → ℝ) : ℝ := fderiv ℝ f x u / f x

/-- The ordinary directional Fisher square integral of the actual density. -/
def directionalFisherEnergy {I : Type*} [Fintype I] (f : (I → ℝ) → ℝ)
    (u : I → ℝ) : ℝ := ∫ x, directionalScore f u x ^ 2 * f x

/-- Differentiating an actual density symmetry transforms every directional
score. No score transformation or energy equality is assumed as an input. -/
theorem directionalScore_equivariance {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (R : (I → ℝ) ≃L[ℝ] (I → ℝ)) (hsym : ∀ x, f (R x) = f x)
    (u x : I → ℝ) :
    directionalScore f (R u) (R x) = directionalScore f u x := by
  have heq : f ∘ R = f := funext hsym
  have hd : HasFDerivAt (f ∘ R)
      ((fderiv ℝ f (R x)).comp R.toContinuousLinearMap) x :=
    (hf (R x)).hasFDerivAt.comp x R.hasFDerivAt
  rw [heq] at hd
  have he := congrArg (fun L : (I → ℝ) →L[ℝ] ℝ => L u)
    (hd.unique (hf x).hasFDerivAt)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at he
  unfold directionalScore
  rw [he, hsym]

/-- A literal change of variables gives equal observed Fisher energies for
an actual reversible edge marginal. This is source equation(11.6). -/
theorem directionalFisherEnergy_reversal {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (R : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (hR : MeasurePreserving R (volume : Measure (I → ℝ)) volume)
    (hsym : ∀ x, f (R x) = f x) (u : I → ℝ) :
    directionalFisherEnergy f (R u) = directionalFisherEnergy f u := by
  have h := hR.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => directionalScore f (R u) x ^ 2 * f x)
  have he (x : I → ℝ) :
      directionalScore f (R u) (R x) ^ 2 * f (R x) = directionalScore f u x ^ 2 * f x := by
    rw [directionalScore_equivariance f hf R hsym, hsym]
  simp_rw [he] at h
  exact h.symm

/-- Reversal transfers finiteness of Fisher information between the two
actual marginal directions, so the equality is not using totalized integrals
as a substitute for integrability. -/
theorem integrable_directionalFisher_reversal {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (R : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (hR : MeasurePreserving R (volume : Measure (I → ℝ)) volume)
    (hsym : ∀ x, f (R x) = f x) (u : I → ℝ)
    (hfinite : Integrable (fun x => directionalScore f u x ^ 2 * f x)) :
    Integrable (fun x => directionalScore f (R u) x ^ 2 * f x) := by
  apply (hR.integrable_comp_emb R.toHomeomorph.measurableEmbedding).mp
  have he : (fun x => directionalScore f (R u) (R x) ^ 2 * f (R x)) =
      (fun x => directionalScore f u x ^ 2 * f x) := by
    funext x
    rw [directionalScore_equivariance f hf R hsym, hsym]
  change Integrable (fun x => directionalScore f (R u) (R x) ^ 2 * f (R x)) volume
  rw [he]
  exact hfinite

end GaussianWave.BS

namespace GaussianWave.BS

/-- Every actual orthonormal-row observation admits a full orthogonal
coordinate completion. Only finite-dimensional geometry is used. -/
theorem exists_orthogonal_row_completion
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) :
    ∃ R : Matrix (J ⊕ Fin (Fintype.card I - Fintype.card J)) I ℝ,
      (∀ j, R (Sum.inl j) = O j) ∧ R * R.transpose = 1 ∧ R.transpose * R = 1 := by
  classical
  let row : J → EuclideanSpace ℝ I := fun j => (WithLp.equiv 2 (I → ℝ)).symm (O j)
  have hrow : Orthonormal ℝ row := by
    rw [orthonormal_iff_ite]
    intro j k
    have h := congrArg (fun M : Matrix J J ℝ => M j k) hO
    simpa [row, EuclideanSpace.inner_piLp_equiv_symm, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, dotProduct, mul_comm] using h
  have hcard : Fintype.card J ≤ Fintype.card I := by
    simpa using hrow.linearIndependent.fintype_card_le_finrank
  let K := J ⊕ Fin (Fintype.card I - Fintype.card J)
  let s : Set K := Set.range Sum.inl
  let v : K → EuclideanSpace ℝ I := Sum.elim row (fun _ => 0)
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨p, ⟨j, rfl⟩⟩ ⟨q, ⟨k, rfl⟩⟩
    simpa [K, s, v, Set.restrict_apply, Sum.inl.injEq] using (orthonormal_iff_ite.mp hrow j k)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ I) = Fintype.card K := by
    simp only [finrank_euclideanSpace, K, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hdim
  let R : Matrix K I ℝ := fun j i => b j i
  have hRR : R * R.transpose = 1 := by
    ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    simpa [R, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h
  refine ⟨R, ?_, hRR, ?_⟩
  · intro j
    have h := hb (Sum.inl j) ⟨j, rfl⟩
    ext i
    exact congrArg (fun x : EuclideanSpace ℝ I => x i) h
  · have hcardK : Fintype.card K = Fintype.card I := by simpa using hdim.symm
    exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcardK)).mp hRR

end GaussianWave.BS

namespace GaussianWave.BS

/-- Conditional expectation for an actual observation commutes with a
measure-preserving change of the underlying coordinates. -/
theorem condExp_observation_comp_equiv
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) (Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (e : A ≃ᵐ B) (he : MeasurePreserving e P Q)
    (observation : B → C) (hobs : Measurable observation)
    (f : B → ℝ) (hf : Integrable f Q) :
    P[(fun x => f (e x)) | MeasurableSpace.comap (observation ∘ e) inferInstance] =ᵐ[P]
      (fun x => Q[f | MeasurableSpace.comap observation inferInstance] (e x)) := by
  have hmB : MeasurableSpace.comap observation inferInstance ≤
      (inferInstance : MeasurableSpace B) := hobs.comap_le
  have hmA : MeasurableSpace.comap (observation ∘ e) inferInstance ≤
      (inferInstance : MeasurableSpace A) := (hobs.comp e.measurable).comap_le
  have hfi : Integrable (fun x => f (e x)) P :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hci : Integrable
      (fun x => Q[f | MeasurableSpace.comap observation inferInstance] (e x)) P :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hmA hfi
  · intro s _ _
    exact hci.integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hpre : (observation ∘ e) ⁻¹' u = e ⁻¹' (observation ⁻¹' u) := rfl
    rw [hpre, he.setIntegral_preimage_emb e.measurableEmbedding,
      he.setIntegral_preimage_emb e.measurableEmbedding]
    exact setIntegral_condExp hmB hf (show MeasurableSet[MeasurableSpace.comap observation inferInstance]
      (observation ⁻¹' u) from ⟨u, hu, rfl⟩)
  · have hsm : StronglyMeasurable[MeasurableSpace.comap observation inferInstance]
        (Q[f | MeasurableSpace.comap observation inferInstance]) := stronglyMeasurable_condExp
    have hcomp := hsm.comp_measurable (comap_measurable e)
    rw [MeasurableSpace.comap_comp] at hcomp
    exact hcomp.aestronglyMeasurable

end GaussianWave.BS

namespace GaussianWave.BS
section FiberConditionalScore

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- Integration over the coordinates discarded by an observation. -/
def fiberIntegral (f : X × Y → ℝ) (x : X) : ℝ := ∫ y, f (x, y) ∂ν

/-- Cancellation of an actual positive density in a set integral. -/
theorem setIntegral_density_ratio (f g : X × Y → ℝ)
    (hf : Measurable f) (hpos : ∀ p, 0 < f p) (s : Set (X × Y))
    (hs : MeasurableSet s) :
    (∫ p in s, g p / f p ∂(μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))) =
      ∫ p in s, g p ∂μ.prod ν := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _ hs]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [ENNReal.toReal_ofReal (hpos p).le, smul_eq_mul]
  exact mul_div_cancel₀ (g p) (ne_of_gt (hpos p))

/-- The density-ratio score is integrable whenever its actual derivative
numerator is integrable in Lebesgue coordinates. -/
theorem integrable_density_ratio (f g : X × Y → ℝ)
    (hf : Measurable f) (hpos : ∀ p, 0 < f p) (hg : Integrable g (μ.prod ν)) :
    Integrable (fun p => g p / f p)
      ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he : (fun p => (ENNReal.ofReal (f p)).toReal • (g p / f p)) = g := by
    funext p
    simp only [ENNReal.toReal_ofReal (hpos p).le, smul_eq_mul]
    exact mul_div_cancel₀ (g p) (ne_of_gt (hpos p))
  rw [he]
  exact hg

/-- A finite actual Fisher square produces the genuine L2 density score. -/
theorem memLp_density_ratio_two (f g : X × Y → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hpos : ∀ p, 0 < f p)
    (hFisher : Integrable (fun p => (g p) ^ 2 / f p) (μ.prod ν)) :
    MemLp (fun p => g p / f p) 2
      ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))) := by
  apply (memLp_two_iff_integrable_sq (hg.div hf).aestronglyMeasurable).mpr
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he : (fun p => (ENNReal.ofReal (f p)).toReal • (g p / f p) ^ 2) =
      (fun p => (g p) ^ 2 / f p) := by
    funext p
    simp only [ENNReal.toReal_ofReal (hpos p).le, smul_eq_mul]
    field_simp [ne_of_gt (hpos p)]
    ring
  rw [he]
  exact hFisher

/-- Fiber averaging preserves L1 integrability for the actual density-ratio
score. This supplies the integrability obligation in the conditional-density
calculation, rather than assuming it in the final score identity. -/
theorem integrable_fiber_density_ratio (f g : X × Y → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hpos : ∀ p, 0 < f p) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) (hM : ∀ x, 0 < fiberIntegral ν f x) :
    Integrable (fun p : X × Y => fiberIntegral ν g p.1 / fiberIntegral ν f p.1)
      ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))) := by
  have hG : Measurable (fiberIntegral ν g) := hgmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hF : Measurable (fiberIntegral ν f) := hfmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hweighted : Integrable
      (fun p : X × Y => f p * (fiberIntegral ν g p.1 / fiberIntegral ν f p.1))
      (μ.prod ν) := by
    apply (integrable_prod_iff
      (hfmeas.mul ((hG.div hF).comp measurable_fst)).aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hf.prod_right_ae] with x hx
      change Integrable (fun y => f (x, y) * (fiberIntegral ν g x / fiberIntegral ν f x)) ν
      exact hx.mul_const _
    · have he (x : X) :
          (∫ y, ‖f (x, y) * (fiberIntegral ν g x / fiberIntegral ν f x)‖ ∂ν) =
            ‖fiberIntegral ν g x‖ := by
        simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hpos _)]
        rw [integral_mul_const]
        change fiberIntegral ν f x * |fiberIntegral ν g x / fiberIntegral ν f x| = _
        rw [abs_div, abs_of_pos (hM x)]
        exact mul_div_cancel₀ _ (ne_of_gt (hM x))
      change Integrable (fun x => ∫ y,
        ‖f (x, y) * (fiberIntegral ν g x / fiberIntegral ν f x)‖ ∂ν) μ
      simp_rw [he]
      exact hg.integral_prod_left.norm
  apply (integrable_withDensity_iff_integrable_smul' hfmeas.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul] using hweighted

/-- The actual conditional density calculation. Its input is a positive
joint density and an integrable derivative numerator, not a score-projection
identity. Fubini and the defining set integrals of conditional expectation
give the discarded-coordinate average of the score.

The extra integrability of the lifted marginal ratio is discharged below
from the same derivative numerator. Keeping it explicit here also makes the
measure-theoretic identity reusable for other densities. -/
theorem condExp_fiber_density_ratio
    (f g : X × Y → ℝ) (hf : Measurable f) (hgmeas : Measurable g)
    (hpos : ∀ p, 0 < f p) (hg : Integrable g (μ.prod ν))
    (hM : ∀ x, 0 < fiberIntegral ν f x)
    (hfinite : IsFiniteMeasure ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))))
    (hratio : Integrable
      (fun p : X × Y => fiberIntegral ν g p.1 / fiberIntegral ν f p.1)
      ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p)))) :
    let P := (μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))
    P[(fun p => g p / f p) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P]
      (fun p : X × Y => fiberIntegral ν g p.1 / fiberIntegral ν f p.1) := by
  intro P
  letI : IsFiniteMeasure P := hfinite
  have hm : MeasurableSpace.comap (Prod.fst : X × Y → X) inferInstance ≤
      (inferInstance : MeasurableSpace (X × Y)) := measurable_fst.comap_le
  have hG : Measurable (fiberIntegral ν g) := hgmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hF : Measurable (fiberIntegral ν f) := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmeas : @Measurable (X × Y) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance
      (fun p => fiberIntegral ν g p.1 / fiberIntegral ν f p.1) :=
    (hG.div hF).comp (comap_measurable Prod.fst)
  have hweighted : Integrable
      (fun p : X × Y => f p * (fiberIntegral ν g p.1 / fiberIntegral ν f p.1))
      (μ.prod ν) := by
    have h := (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hratio
    simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul] using h
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (integrable_density_ratio μ ν f g hf hpos hg)
  · intro s _ _
    exact hratio.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hpre : (Prod.fst : X × Y → X) ⁻¹' t = t ×ˢ Set.univ := by ext p; simp
    rw [hpre]
    change (∫ p in t ×ˢ Set.univ,
      fiberIntegral ν g p.1 / fiberIntegral ν f p.1
        ∂(μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))) = _
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _ (ht.prod MeasurableSet.univ)]
    simp only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul]
    rw [setIntegral_density_ratio μ ν f g hf hpos _ (ht.prod MeasurableSet.univ),
      setIntegral_prod _ hweighted.integrableOn, setIntegral_prod _ hg.integrableOn]
    simp only [Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [integral_mul_const]
    change fiberIntegral ν f x * (fiberIntegral ν g x / fiberIntegral ν f x) =
      fiberIntegral ν g x
    exact mul_div_cancel₀ _ (ne_of_gt (hM x))
  · exact hmeas.stronglyMeasurable.aestronglyMeasurable

/-- The actual joint-density conditional score identity, with every L1
obligation proved from integrability of the density and derivative numerator.
When `g` is a density derivative, the right side is its genuine integrated
fiber numerator divided by the genuine marginal density. -/
theorem condExp_fiber_density_ratio_of_integrable
    (f g : X × Y → ℝ) (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hpos : ∀ p, 0 < f p) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) (hM : ∀ x, 0 < fiberIntegral ν f x) :
    let P := (μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))
    P[(fun p => g p / f p) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P]
      (fun p : X × Y => fiberIntegral ν g p.1 / fiberIntegral ν f p.1) := by
  exact condExp_fiber_density_ratio μ ν f g hfmeas hgmeas hpos hg hM
    (isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral)
    (integrable_fiber_density_ratio μ ν f g hfmeas hgmeas hpos hf hg hM)

/-- The preceding actual-density calculation in the L2 projection form used
by the weighted frame theorem. The full score is explicitly identified with
its density derivative ratio; its conditional score is a proved conclusion. -/
theorem conditionalScore_fiber_density_ratio
    (f g : X × Y → ℝ) (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hpos : ∀ p, 0 < f p) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) (hM : ∀ x, 0 < fiberIntegral ν f x)
    (u : ScoreSpace ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))))
    (hu : (u : X × Y → ℝ) =ᵐ[(μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))]
      (fun p => g p / f p)) :
    let P := (μ.prod ν).withDensity (fun p => ENNReal.ofReal (f p))
    (conditionalScore P (MeasurableSpace.comap Prod.fst inferInstance)
      measurable_fst.comap_le u : X × Y → ℝ) =ᵐ[P]
        (fun p : X × Y => fiberIntegral ν g p.1 / fiberIntegral ν f p.1) := by
  intro P
  letI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  have hCE := (Lp.memLp u).condExpL2_ae_eq_condExp (𝕜 := ℝ) measurable_fst.comap_le
  rw [Lp.toLp_coeFn] at hCE
  exact hCE.trans ((condExp_congr_ae hu).trans
    (condExp_fiber_density_ratio_of_integrable μ ν f g hfmeas hgmeas hpos hf hg hM))

end FiberConditionalScore
end GaussianWave.BS

namespace GaussianWave.BS
section HeatFibers
variable {I J : Type*} [Fintype I] [Fintype J]

def leftCoordinates (z : (I ⊕ J) → ℝ) : I → ℝ := fun i => z (Sum.inl i)
def rightCoordinates (z : (I ⊕ J) → ℝ) : J → ℝ := fun j => z (Sum.inr j)

theorem measurable_leftCoordinates : Measurable (leftCoordinates (I := I) (J := J)) := by
  unfold leftCoordinates
  fun_prop

theorem measurable_rightCoordinates : Measurable (rightCoordinates (I := I) (J := J)) := by
  unfold rightCoordinates
  fun_prop

theorem heatKernel_sum (t : ℝ) (x : I → ℝ) (y : J → ℝ) :
    heatKernel t (Sum.elim x y) = heatKernel t x * heatKernel t y := by
  simp [heatKernel, Fintype.prod_sum_type]

theorem heatKernel_split_sub (t : ℝ) (x : I → ℝ) (y : J → ℝ) (z : (I ⊕ J) → ℝ) :
    heatKernel t (Sum.elim x y - z) =
      heatKernel t (x - leftCoordinates z) * heatKernel t (y - rightCoordinates z) := by
  have he : Sum.elim x y - z = Sum.elim (x - leftCoordinates z) (y - rightCoordinates z) := by
    ext a
    cases a <;> rfl
  rw [he, heatKernel_sum]

theorem heatKernelGradient_split_sub (t : ℝ) (x : I → ℝ) (y : J → ℝ)
    (z : (I ⊕ J) → ℝ) (i : I) :
    heatKernelGradient t (Sum.elim x y - z) (Sum.inl i) =
      heatKernelGradient t (x - leftCoordinates z) i * heatKernel t (y - rightCoordinates z) := by
  simp only [heatKernelGradient, heatKernel_split_sub, Pi.sub_apply, Sum.elim_inl, leftCoordinates]
  ring

/-- Integrating the discarded heat coordinates gives exactly one, including
an arbitrary deterministic shift of those coordinates. -/
theorem integral_heatKernel_sub {t : ℝ} (ht : 0 < t) (z : J → ℝ) :
    (∫ y, heatKernel t (y - z)) = 1 := by
  rw [integral_sub_right_eq_self, integral_heatKernel ht]

/-- Fubini for an actual Gaussian fiber. The domination is supplied by the
L1 numerator, while the discarded Gaussian fiber has total mass one. -/
theorem integral_heat_fiber_mixture
    (μ : Measure ((I ⊕ J) → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (L : ((I ⊕ J) → ℝ) → ℝ) (hLm : Measurable L) (hL : Integrable L μ) :
    (∫ y : J → ℝ, ∫ z, L z * heatKernel t (y - rightCoordinates z) ∂μ) = ∫ z, L z ∂μ := by
  have hprod : Integrable
      (fun p : (((I ⊕ J) → ℝ) × (J → ℝ)) =>
        L p.1 * heatKernel t (p.2 - rightCoordinates p.1)) (μ.prod volume) := by
    apply (integrable_prod_iff
      ((hLm.comp measurable_fst).mul ((measurable_heatKernel t).comp
        (measurable_snd.sub (measurable_rightCoordinates.comp measurable_fst)))).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ (fun z =>
        ((integrable_heatKernel t).comp_sub_right (rightCoordinates z)).const_mul (L z))
    · have he (z : (I ⊕ J) → ℝ) :
          (∫ y : J → ℝ, ‖L z * heatKernel t (y - rightCoordinates z)‖) = ‖L z‖ := by
        simp_rw [norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (heatKernel_nonneg t _)]
        rw [integral_const_mul, integral_heatKernel_sub ht, mul_one]
      change Integrable (fun z => ∫ y : J → ℝ, ‖L z * heatKernel t (y - rightCoordinates z)‖) μ
      simp_rw [he]
      exact hL.norm
  rw [← integral_integral_swap hprod]
  simp_rw [integral_const_mul, integral_heatKernel_sub ht, mul_one]

/-- The marginal density is the actual heat density of the projected input
law, proved by integration of the discarded coordinates. -/
theorem fiber_heatDensity
    (μ : Measure ((I ⊕ J) → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    (∫ y : J → ℝ, heatDensity μ t (Sum.elim x y)) =
      heatDensity (Measure.map leftCoordinates μ) t x := by
  have hL : Integrable (fun z => heatKernel t (x - leftCoordinates z)) μ :=
    (integrable_heatKernel_shift (Measure.map leftCoordinates μ) t x).comp_measurable
      measurable_leftCoordinates
  unfold heatDensity
  simp_rw [heatKernel_split_sub]
  rw [integral_heat_fiber_mixture μ ht (fun z => heatKernel t (x - leftCoordinates z))
    ((measurable_heatKernel t).comp (measurable_const.sub measurable_leftCoordinates)) hL]
  exact (integral_map measurable_leftCoordinates.aemeasurable
    (((continuous_heatKernel t).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)).symm

/-- The discarded-coordinate integral of the actual derivative numerator
is exactly the derivative numerator of the actual marginal heat density.
No differentiation/marginalization commutation is assumed. -/
theorem fiber_heatDensityGradient
    (μ : Measure ((I ⊕ J) → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) :
    (∫ y : J → ℝ, heatDensityGradient μ t (Sum.elim x y) (Sum.inl i)) =
      heatDensityGradient (Measure.map leftCoordinates μ) t x i := by
  have hL : Integrable (fun z => heatKernelGradient t (x - leftCoordinates z) i) μ :=
    (integrable_heatKernelGradient_shift (Measure.map leftCoordinates μ) ht x i).comp_measurable
      measurable_leftCoordinates
  unfold heatDensityGradient
  simp_rw [heatKernelGradient_split_sub]
  rw [integral_heat_fiber_mixture μ ht (fun z => heatKernelGradient t (x - leftCoordinates z) i)
    ((continuous_heatKernelGradient t i).measurable.comp
      (measurable_const.sub measurable_leftCoordinates)) hL]
  exact (integral_map measurable_leftCoordinates.aemeasurable
    (((continuous_heatKernelGradient t i).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)).symm

theorem measurable_heatDensityGradient_coordinate
    {K : Type*} [Fintype K] (μ : Measure (K → ℝ)) [IsFiniteMeasure μ] (t : ℝ) (i : K) :
    Measurable (fun x => heatDensityGradient μ t x i) := by
  have h : Continuous (fun p : (K → ℝ) × (K → ℝ) =>
      heatKernelGradient t (p.1 - p.2) i) :=
    (continuous_heatKernelGradient t i).comp (continuous_fst.sub continuous_snd)
  exact h.measurable.stronglyMeasurable.integral_prod_right'.measurable

/-- The coordinate-split heated density has exactly the ordinary product
Lebesgue integrability needed by the actual fiber conditional expectation. -/
theorem integrable_heatDensity_split
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : (I → ℝ) × (J → ℝ) => heatDensity μ t (Sum.elim p.1 p.2))
      (volume.prod volume) := by
  have h := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ J => ℝ)).integrable_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurableEmbedding
    (g := heatDensity μ t)
  exact h.mpr (integrable_heatDensity μ ht)

theorem integrable_heatDensityGradient_split [DecidableEq I] [DecidableEq J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun p : (I → ℝ) × (J → ℝ) =>
      heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i)) (volume.prod volume) := by
  have h := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ J => ℝ)).integrable_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurableEmbedding
    (g := fun x => heatDensityGradient μ t x (Sum.inl i))
  exact h.mpr (integrable_heatDensityGradient μ ht (Sum.inl i))

def splitHeatedDensity (μ : Measure ((I ⊕ J) → ℝ)) (t : ℝ)
    (p : (I → ℝ) × (J → ℝ)) : ℝ := heatDensity μ t (Sum.elim p.1 p.2)

/-- The split-coordinate heat law, written using its actual density. The
next lemma identifies it with the pushforward of the actual convolution. -/
def splitHeatedLaw (μ : Measure ((I ⊕ J) → ℝ)) (t : ℝ) :
    Measure ((I → ℝ) × (J → ℝ)) :=
  (volume.prod volume).withDensity (fun p => ENNReal.ofReal (splitHeatedDensity μ t p))

theorem splitHeatedLaw_eq_map
    (μ : Measure ((I ⊕ J) → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    splitHeatedLaw μ t = Measure.map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)) (heatedLaw μ t) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)
  apply Measure.ext_of_lintegral
  intro q hq
  rw [lintegral_map hq e.measurable, heatedLaw_eq_withDensity μ ht]
  have hqe : Measurable (fun z => q (e z)) := hq.comp e.measurable
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_heatDensity μ t).ennreal_ofReal hqe]
  change (∫⁻ p, q p ∂(volume.prod volume).withDensity
    (fun p => ENNReal.ofReal (heatDensity μ t (e.symm p)))) = _
  have hfe : Measurable (fun p => ENNReal.ofReal (heatDensity μ t (e.symm p))) :=
    ((measurable_heatDensity μ t).comp e.symm.measurable).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul (volume.prod volume) hfe hq]
  have h := (volume_measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).lintegral_comp
    (((measurable_heatDensity μ t).comp e.symm.measurable).ennreal_ofReal.mul hq)
  change (∫⁻ z, ENNReal.ofReal (heatDensity μ t (e.symm (e z))) * q (e z)) =
    ∫⁻ p, ENNReal.ofReal (heatDensity μ t (e.symm p)) * q p ∂volume.prod volume at h
  simpa only [e.symm_apply_apply] using h.symm

instance splitHeatedLaw_isProbabilityMeasure
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] (t : ℝ) [ht : Fact (0 < t)] :
    IsProbabilityMeasure (splitHeatedLaw μ t) := by
  rw [splitHeatedLaw_eq_map μ ht.out]
  exact MeasureTheory.isProbabilityMeasure_map
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).measurable.aemeasurable

def splitHeatCoordinateScore (μ : Measure ((I ⊕ J) → ℝ)) (t : ℝ) (i : I)
    (p : (I → ℝ) × (J → ℝ)) : ℝ :=
  heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i) / splitHeatedDensity μ t p

theorem memLp_splitHeatCoordinateScore [DecidableEq I] [DecidableEq J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    MemLp (splitHeatCoordinateScore μ t i) 2 (splitHeatedLaw μ t) := by
  have hj : Measurable (fun p : (I → ℝ) × (J → ℝ) => Sum.elim p.1 p.2) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurable
  apply memLp_density_ratio_two (volume : Measure (I → ℝ)) (volume : Measure (J → ℝ))
    (splitHeatedDensity μ t) (fun p => heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i))
    ((measurable_heatDensity μ t).comp hj)
    ((measurable_heatDensityGradient μ t (Sum.inl i)).comp hj)
    (fun p => heatDensity_pos μ ht _)
  have h := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ J => ℝ)).integrable_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurableEmbedding
    (g := heatFisherCoordinate μ t (Sum.inl i))
  exact h.mpr (integrable_heatFisherCoordinate μ ht (Sum.inl i))

/-- A genuine L2 score of the actual convolution in coordinate-split form. -/
def splitHeatCoordinateScoreL2 [DecidableEq I] [DecidableEq J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    ScoreSpace (splitHeatedLaw μ t) :=
  (memLp_splitHeatCoordinateScore μ ht i).toLp (splitHeatCoordinateScore μ t i)

/-- Actual score projection for a coordinate observation of an arbitrary
heated probability law. Both full and marginal numerators are the actual
heat-density derivatives. There is no assumed conditional-score identity. -/
theorem condExp_heatDensity_coordinate_score [DecidableEq I] [DecidableEq J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    let f := fun p : (I → ℝ) × (J → ℝ) => heatDensity μ t (Sum.elim p.1 p.2)
    let P := (volume.prod volume).withDensity (fun p => ENNReal.ofReal (f p))
    P[(fun p => heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i) / f p) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[P]
        (fun p : (I → ℝ) × (J → ℝ) =>
          heatDensityGradient (Measure.map leftCoordinates μ) t p.1 i /
            heatDensity (Measure.map leftCoordinates μ) t p.1) := by
  intro f P
  letI : IsProbabilityMeasure (Measure.map (leftCoordinates (I := I) (J := J)) μ) :=
    MeasureTheory.isProbabilityMeasure_map measurable_leftCoordinates.aemeasurable
  have hj : Measurable (fun p : (I → ℝ) × (J → ℝ) => Sum.elim p.1 p.2) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurable
  have hF : ∀ x, 0 < fiberIntegral (volume : Measure (J → ℝ)) f x := by
    intro x
    change 0 < ∫ y, heatDensity μ t (Sum.elim x y)
    rw [fiber_heatDensity μ ht]
    exact heatDensity_pos (Measure.map leftCoordinates μ) ht x
  have h := condExp_fiber_density_ratio_of_integrable
    (volume : Measure (I → ℝ)) (volume : Measure (J → ℝ)) f
    (fun p => heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i))
    ((measurable_heatDensity μ t).comp hj)
    ((measurable_heatDensityGradient μ t (Sum.inl i)).comp hj)
    (fun p => heatDensity_pos μ ht _) (integrable_heatDensity_split μ ht)
    (integrable_heatDensityGradient_split μ ht i) hF
  have hnum (x : I → ℝ) :
      fiberIntegral (volume : Measure (J → ℝ))
        (fun p : (I → ℝ) × (J → ℝ) => heatDensityGradient μ t (Sum.elim p.1 p.2) (Sum.inl i)) x =
      heatDensityGradient (Measure.map leftCoordinates μ) t x i :=
    fiber_heatDensityGradient μ ht x i
  have hden (x : I → ℝ) : fiberIntegral (volume : Measure (J → ℝ)) f x =
      heatDensity (Measure.map leftCoordinates μ) t x := fiber_heatDensity μ ht x
  simpa only [hnum, hden] using h

/-- The true conditional-score identity in the Hilbert projection form of
U3, for every coordinate observation of an arbitrary heated probability law.
The full score is constructed from the actual derivative ratio and proved
L2 by the actual Fisher bound. No score-projection hypothesis remains. -/
theorem conditionalScore_heatDensity_coordinate_score [DecidableEq I] [DecidableEq J]
    (μ : Measure ((I ⊕ J) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    (conditionalScore (splitHeatedLaw μ t)
      (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
      (splitHeatCoordinateScoreL2 μ ht i) : (I → ℝ) × (J → ℝ) → ℝ) =ᵐ[splitHeatedLaw μ t]
        (fun p : (I → ℝ) × (J → ℝ) =>
          heatDensityGradient (Measure.map leftCoordinates μ) t p.1 i /
            heatDensity (Measure.map leftCoordinates μ) t p.1) := by
  letI : Fact (0 < t) := ⟨ht⟩
  have h := (memLp_splitHeatCoordinateScore μ ht i).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) measurable_fst.comap_le
  exact h.trans (condExp_heatDensity_coordinate_score μ ht i)

end HeatFibers
end GaussianWave.BS

namespace GaussianWave.BS

theorem directionalScore_eq_log_derivative {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < f x) (u x : I → ℝ) :
    directionalScore f u x = fderiv ℝ (fun y => Real.log (f y)) x u := by
  have h := ((hf x).hasFDerivAt.log (ne_of_gt (hpos x))).fderiv
  rw [h]
  simp [directionalScore, div_eq_mul_inv, mul_comm]

theorem continuous_directionalScore {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x) (u : I → ℝ) :
    Continuous (directionalScore f u) := by
  have hd : Continuous (fun x => fderiv ℝ f x u) :=
    (hf.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  exact hd.div hf.continuous (fun x => ne_of_gt (hpos x))

/-- Actual finite-coordinate permutation, as a continuous linear equivalence. -/
def coordinatePermutation {I : Type*} [Fintype I] (e : Equiv.Perm I) :
    (I → ℝ) ≃L[ℝ] (I → ℝ) := (LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv

@[simp] theorem coordinatePermutation_apply {I : Type*} [Fintype I]
    (e : Equiv.Perm I) (x : I → ℝ) (i : I) : coordinatePermutation e x i = x (e i) := rfl

theorem coordinatePermutation_volume_preserving {I : Type*} [Fintype I] (e : Equiv.Perm I) :
    MeasurePreserving (coordinatePermutation e) (volume : Measure (I → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : I => ℝ) e.symm
  convert h using 1
  ext x i
  simpa using (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I => ℝ)
    e.symm x (e i)).symm

/-- Pushforward of an actual density under a Lebesgue-preserving linear
change of coordinates. This is proved as an equality of actual measures. -/
theorem map_linearEquiv_density {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (R : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (hR : MeasurePreserving R (volume : Measure (I → ℝ)) volume) :
    Measure.map R (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal (f (R.symm x))) := by
  apply Measure.ext_of_lintegral
  intro q hq
  rw [lintegral_map hq R.continuous.measurable]
  have hqR : Measurable (fun x => q (R x)) := hq.comp R.continuous.measurable
  rw [lintegral_withDensity_eq_lintegral_mul volume hf.ennreal_ofReal hqR]
  have hfR : Measurable (fun x => ENNReal.ofReal (f (R.symm x))) :=
    (hf.comp R.symm.continuous.measurable).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume hfR hq]
  have h := hR.lintegral_comp (hfR.mul hq)
  change (∫⁻ x, ENNReal.ofReal (f (R.symm (R x))) * q (R x)) =
    ∫⁻ x, ENNReal.ofReal (f (R.symm x)) * q x at h
  simpa only [R.symm_apply_apply] using h

/-- Law invariance forces pointwise invariance of its continuous nonnegative
density. The proof uses uniqueness of density and the full support of
Lebesgue measure, rather than assuming the density symmetry. -/
theorem density_symmetry_of_map_invariant {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (R : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (hR : MeasurePreserving R (volume : Measure (I → ℝ)) volume)
    (hinv : Measure.map R (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ x, f (R x) = f x := by
  rw [map_linearEquiv_density f hf.measurable R hR] at hinv
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((hf.comp R.symm.continuous).measurable.ennreal_ofReal.aemeasurable)
    hf.measurable.ennreal_ofReal.aemeasurable).mp hinv
  have hareal : (fun x => f (R.symm x)) =ᵐ[volume] f := by
    filter_upwards [hae] with x hx
    have h := congrArg ENNReal.toReal hx
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hpos _)] using h
  have he := (volume : Measure (I → ℝ)).eq_of_ae_eq hareal (hf.comp R.symm.continuous) hf
  intro x
  have h := congrFun he (R x)
  simpa only [R.symm_apply_apply] using h.symm

/-- In the endpoint-adapted coordinates, the actual root/leaf reversal swaps
its two orthonormal direction families simultaneously in all channels. -/
def edgeFlipIndex (k : ℕ) : Equiv.Perm (Bool × Fin k) where
  toFun p := (!p.1, p.2)
  invFun p := (!p.1, p.2)
  left_inv := by rintro ⟨b, a⟩; cases b <;> rfl
  right_inv := by rintro ⟨b, a⟩; cases b <;> rfl

def edgeFlipLinear (k : ℕ) :
    ((Bool × Fin k) → ℝ) ≃L[ℝ] ((Bool × Fin k) → ℝ) := coordinatePermutation (edgeFlipIndex k)

@[simp] theorem edgeFlipLinear_basis (k : ℕ) (a : Fin k) :
    edgeFlipLinear k (Pi.single (false, a) 1) = Pi.single (true, a) 1 := by
  ext p
  rcases p with ⟨b, j⟩
  cases b <;> simp [edgeFlipLinear, edgeFlipIndex, Pi.single_apply]

/-- Source equation(11.6), proved for the actual simultaneous edge reversal
in every channel, rather than assumed as an energy identity. -/
theorem edge_reversal_directionalFisher_equal (k : ℕ)
    (f : ((Bool × Fin k) → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (hsym : ∀ x, f (edgeFlipLinear k x) = f x) (a : Fin k) :
    directionalFisherEnergy f (Pi.single (false, a) 1) =
      directionalFisherEnergy f (Pi.single (true, a) 1) := by
  have h := directionalFisherEnergy_reversal f hf (edgeFlipLinear k)
    (coordinatePermutation_volume_preserving (edgeFlipIndex k)) hsym (Pi.single (false, a) 1)
  rw [edgeFlipLinear_basis] at h
  exact h.symm

/-- Observed Fisher equality derived from invariance of the actual marginal
law under edge reversal. Pointwise density symmetry is no longer an input. -/
theorem edge_reversal_directionalFisher_equal_of_law (k : ℕ)
    (f : ((Bool × Fin k) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 ≤ f x)
    (hinv : Measure.map (edgeFlipLinear k)
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
        volume.withDensity (fun x => ENNReal.ofReal (f x))) (a : Fin k) :
    directionalFisherEnergy f (Pi.single (false, a) 1) =
      directionalFisherEnergy f (Pi.single (true, a) 1) := by
  apply edge_reversal_directionalFisher_equal k f (hf.differentiable le_rfl)
  exact density_symmetry_of_map_invariant f hf.continuous hpos (edgeFlipLinear k)
    (coordinatePermutation_volume_preserving (edgeFlipIndex k)) hinv

/-- Computing a Fisher square under the actual marginal density agrees with
its ordinary weighted Lebesgue integral. -/
theorem directionalFisherEnergy_density_integral {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (u : I → ℝ) :
    (∫ x, directionalScore f u x ^ 2
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = directionalFisherEnergy f u := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- If U2 identifies a conditional score with the lifted actual marginal
score, its Hilbert energy is that marginal's literal Fisher square integral.
The derivative/projection identity is visible as an intermediate assumption;
it is not an entropy upper bound or a Gaussian-classification premise. -/
theorem conditionalScore_energy_eq_marginal
    {Ω I : Type*} [m0 : MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (observation : Ω → (I → ℝ)) (hobs : Measurable observation)
    (m : {m : MeasurableSpace Ω // m ≤ m0}) (u : ScoreSpace (m0 := m0) P)
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hmap : Measure.map observation P = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (direction : I → ℝ)
    (hscore : (conditionalScore (m0 := m0) P m.val m.property u : Ω → ℝ) =ᵐ[P]
      (fun ω => directionalScore f direction (observation ω))) :
    ‖conditionalScore (m0 := m0) P m.val m.property u‖ ^ 2 = directionalFisherEnergy f direction := by
  rw [score_norm_sq_eq_integral]
  calc
    _ = ∫ ω, directionalScore f direction (observation ω) ^ 2 ∂P :=
      integral_congr_ae (hscore.mono (fun _ h => congrArg (fun s : ℝ => s ^ 2) h))
    _ = ∫ x, directionalScore f direction x ^ 2 ∂Measure.map observation P :=
      (integral_map hobs.aemeasurable
        (((continuous_directionalScore f hf hpos direction).pow 2).measurable.aestronglyMeasurable)).symm
    _ = directionalFisherEnergy f direction := by
      rw [hmap, directionalFisherEnergy_density_integral f hf.continuous.measurable
        (fun x => (hpos x).le)]

/-- The same actual marginal-score identity gives genuine integrability of
the Fisher square. Thus the preceding identity is between finite energies. -/
theorem conditionalScore_marginal_fisher_integrable
    {Ω I : Type*} [m0 : MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (observation : Ω → (I → ℝ)) (hobs : Measurable observation)
    (m : {m : MeasurableSpace Ω // m ≤ m0}) (u : ScoreSpace (m0 := m0) P)
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hmap : Measure.map observation P = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (direction : I → ℝ)
    (hscore : (conditionalScore (m0 := m0) P m.val m.property u : Ω → ℝ) =ᵐ[P]
      (fun ω => directionalScore f direction (observation ω))) :
    Integrable (fun x => directionalScore f direction x ^ 2 * f x) := by
  have hsq : Integrable (fun ω => directionalScore f direction (observation ω) ^ 2) P :=
    (Lp.memLp (conditionalScore (m0 := m0) P m.val m.property u)).integrable_sq.congr
      (hscore.mono (fun _ h => congrArg (fun s : ℝ => s ^ 2) h))
  have hmapint : Integrable (fun x => directionalScore f direction x ^ 2)
      (Measure.map observation P) :=
    (integrable_map_measure
      (((continuous_directionalScore f hf hpos direction).pow 2).measurable.aestronglyMeasurable)
      hobs.aemeasurable).mpr hsq
  rw [hmap] at hmapint
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    hf.continuous.measurable.ennreal_ofReal
    (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))).mp hmapint
  simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul, mul_comm] using hweighted

/-- A reversible actual edge marginal makes its two observed conditional
score energies equal. The equality in U3 is now a conclusion; the remaining
analytic input is the explicit score/conditional-expectation identification. -/
theorem conditionalScore_edge_reversal_energy_equal
    {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) (k : ℕ)
    (observation : Ω → ((Bool × Fin k) → ℝ)) (hobs : Measurable observation)
    (m : {m : MeasurableSpace Ω // m ≤ m0}) (uA uB : ScoreSpace (m0 := m0) P)
    (f : ((Bool × Fin k) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hmap : Measure.map observation P = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hsym : ∀ x, f (edgeFlipLinear k x) = f x) (a : Fin k)
    (hA : (conditionalScore (m0 := m0) P m.val m.property uA : Ω → ℝ) =ᵐ[P]
      (fun ω => directionalScore f (Pi.single (false, a) 1) (observation ω)))
    (hB : (conditionalScore (m0 := m0) P m.val m.property uB : Ω → ℝ) =ᵐ[P]
      (fun ω => directionalScore f (Pi.single (true, a) 1) (observation ω))) :
    ‖conditionalScore (m0 := m0) P m.val m.property uA‖ ^ 2 =
      ‖conditionalScore (m0 := m0) P m.val m.property uB‖ ^ 2 := by
  rw [conditionalScore_energy_eq_marginal P observation hobs m uA f hf hpos hmap _ hA,
    conditionalScore_energy_eq_marginal P observation hobs m uB f hf hpos hmap _ hB]
  exact edge_reversal_directionalFisher_equal k f (hf.differentiable le_rfl) hsym a

/-- U3 applied to actual reversible edge marginal densities. In particular,
equality of observed directional energies is derived rather than supplied. -/
theorem fisherDefect_nonneg_of_reversible_marginal_scores
    {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    (d k : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (r : Fin k → ScoreSpace P) (z : Fin k → Fin d → ScoreSpace P)
    (hz : ∀ a, ∑ i, z a i = 0)
    (m : Fin d → {m : MeasurableSpace Ω // m ≤ m0})
    (observation : Fin d → Ω → ((Bool × Fin k) → ℝ))
    (hobs : ∀ i, Measurable (observation i))
    (f : Fin d → ((Bool × Fin k) → ℝ) → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hpos : ∀ i x, 0 < f i x)
    (hmap : ∀ i, Measure.map (observation i) P =
      volume.withDensity (fun x => ENNReal.ofReal (f i x)))
    (hsym : ∀ i x, f i (edgeFlipLinear k x) = f i x)
    (hA : ∀ a i, (conditionalScore P (m i).val (m i).property
      (frameScoreA P c r z a i) : Ω → ℝ) =ᵐ[P]
        (fun ω => directionalScore (f i) (Pi.single (false, a) 1) (observation i ω)))
    (hB : ∀ a i, (conditionalScore P (m i).val (m i).property
      (frameScoreB P c r z a i) : Ω → ℝ) =ᵐ[P]
        (fun ω => directionalScore (f i) (Pi.single (true, a) 1) (observation i ω))) :
    0 ≤ fisherDefect P c r z (fun i => (m i).val) (fun i => (m i).property) := by
  apply fisherDefect_nonneg P d k hd c hbulk r z hz
  intro a i
  exact conditionalScore_edge_reversal_energy_equal P k (observation i) (hobs i) (m i)
    (frameScoreA P c r z a i) (frameScoreB P c r z a i)
    (f i) (hf i) (hpos i) (hmap i) (hsym i) a (hA a i) (hB a i)

end GaussianWave.BS
