import GeneralizedBulk.Exterior.MarkedPositivity
import GeneralizedBulk.Exterior.GaussianOrdinaryLaw
import GeneralizedBulk.Exterior.JointAnchorSymmetry

/-!
# Sign definiteness of the jointly constructed Gaussian resolvent

The joint L² anchor has an absolutely convergent imaginary part. This gives
one common event for all nonreal parameters, with the correct half-plane sign.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology ComplexOrder
namespace GeneralizedBulk.Exterior
open Gaussian

variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

/-- The imaginary part of the genuine joint L² anchor is its absolute
imaginary series. The original complex anchor need not converge samplewise. -/
theorem constructedAnchor_imaginary_ae (parameters : Parameters) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ i j : Fin 4,
      (presentedGlobalAnchorMatrix P X hX hm parameters z i j).im =
        ∑' n, parameters.scale * nevanlinnaWeight ((X z.1).location n) *
          rawQuadratic parameters.p i j (z.2 n) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  let A := presentedAnchorCoefficient X parameters.scale
  let hA := measurable_presentedAnchorCoefficient X hX (parameters.scale : ℂ)
  let hA2 := integrable_presentedAnchorCoefficient_sq P X hX hm (parameters.scale : ℂ)
  let terms : I → Lp ℂ 2 (P.prod (iidLaw (markLaw parameters.p) I)) :=
    fun n => jointTerm P parameters.p A hA hA2 n i j
  let raw := fun n => jointTermFunction parameters.p A n i j
  have hs : Summable terms := summable_jointTerm P parameters.p parameters.abs_p_lt_one
    A hA hA2 (summable_presentedAnchorCoefficient_integrals P X hX hm (parameters.scale : ℂ)) i j
  have ht (n : I) :
      (terms n : S × (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[P.prod (iidLaw (markLaw parameters.p) I)] raw n :=
    jointTerm_ae P parameters.p A hA hA2 n i j
  have ha : (fun z => presentedGlobalAnchorMatrix P X hX hm parameters z i j) =ᵐ[
      P.prod (iidLaw (markLaw parameters.p) I)] (fun z => (∑' n, terms n) z) :=
    Eventually.of_forall (fun z => rfl)
  have hi : ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I),
      Summable (fun n => (raw n z).im) := by
    filter_upwards [ae_weightedEvent P X hX parameters.p] with z hz
    have hw := weightedEvent_entry_summable hz i j
    have hq : Summable (fun n => nevanlinnaWeight ((X z.1).location n) *
        rawQuadratic parameters.p i j (z.2 n)) := by
      apply Summable.of_norm_bounded _ hw
      intro n
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (nevanlinnaWeight_nonneg _)]
    simpa only [raw, jointTermFunction, A, presentedAnchorCoefficient,
      markQuadraticFamily, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, zero_add, add_zero, particleCoefficient_im_I, mul_assoc]
      using hq.mul_left parameters.scale
  have hh := imaginary_anchor_eq_tsum (P.prod (iidLaw (markLaw parameters.p) I))
    terms raw (fun z => presentedGlobalAnchorMatrix P X hX hm parameters z i j) ht hs ha hi
  simpa only [raw, jointTermFunction, A, presentedAnchorCoefficient,
    markQuadraticFamily, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, zero_add, add_zero, particleCoefficient_im_I] using hh

/-- All nonreal parameters have the correct strict imaginary sign in the
actual joint model. The same event handles arbitrary mixed products. -/
theorem constructedMatrix_ae_signDefinite_selection (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ w : NonrealSpectral,
      ImaginarySignDefinite (constructedMatrix P X hX hm parameters z w) := by
  have hspan : ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I),
      ∀ a : I → ℝ, (∀ n, 0 < a n) →
      Summable (fun n => (a n : ℂ) • outerMatrix (fun k => (z.2 n k : ℂ))) →
      (∑' n, (a n : ℂ) • outerMatrix (fun k => (z.2 n k : ℂ))).PosDef :=
    Measure.quasiMeasurePreserving_snd.ae
      (gaussianMarks_ae_posDef_all_weighted_tsum_selection
        parameters.p parameters.abs_p_lt_one I e he)
  have hlin : ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I),
      anchoredLinearCoefficient (X z.1).scalar = 0 := Measure.quasiMeasurePreserving_fst.ae hlinear
  filter_upwards [constructedAnchor_imaginary_ae P X hX hm parameters,
    ae_weightedEvent P X hX parameters.p, hspan, hlin] with z him hz hspan hlin
  intro w
  let p := (X z.1).presentation
  let anchor := fun γ => presentedGlobalAnchorMatrix P X hX hm parameters (z.1, γ)
  have hM : constructedMatrix P X hX hm parameters z w =
      presentedRawMatrix p parameters.p parameters.scale parameters.center parameters.r anchor w.1 z.2 := by
    rw [constructedMatrix, mean_eq_covariance, constructedField,
      globalCenteredField_eq_presented X parameters.p parameters.scale
        (presentedGlobalAnchorMatrix P X hX hm parameters) z hz (w.1, false)]
    rfl
  have hsym : (anchor z.2).transpose = anchor z.2 :=
    presentedGlobalAnchorMatrix_transpose P X hX hm parameters z
  have hweight (i j : Fin 4) : Summable (fun n => nevanlinnaWeight (p.location n) *
      ‖(rawQuadratic parameters.p i j (z.2 n) : ℂ)‖) := weightedEvent_entry_summable hz i j
  have hid := imaginaryPart_presentedRawMatrix p parameters.p parameters.scale parameters.center
    parameters.r anchor hlin z.2 hsym him hweight w.2
  have hs := summable_uncentered_poissonMatrix p parameters.p parameters.scale hlin z.2 hweight w.2
  rw [hM]
  by_cases hupper : 0 < w.1.im
  · apply Or.inl
    rw [hid]
    exact hspan _ (fun n => mul_pos parameters.scale_pos (poissonWeight_pos _ hupper)) hs
  · apply Or.inr
    have hlower : w.1.im < 0 := lt_of_le_of_ne (le_of_not_gt hupper) w.2
    have hpneg (n : I) : 0 < -(parameters.scale * poissonWeight (p.location n) w.1) := by
      have hwneg : poissonWeight (p.location n) w.1 < 0 :=
        div_neg_of_neg_of_pos hlower (Complex.normSq_pos.mpr (real_sub_ne_zero _ w.2))
      exact neg_pos.mpr (mul_neg_of_pos_of_neg parameters.scale_pos hwneg)
    have hn : Summable (fun n => ((-(parameters.scale * poissonWeight (p.location n) w.1) : ℝ) : ℂ) •
        outerMatrix (fun k => (z.2 n k : ℂ))) := by
      simpa only [Complex.ofReal_neg, neg_smul] using hs.neg
    rw [hid]
    have heq : -(∑' n, ((parameters.scale * poissonWeight (p.location n) w.1 : ℝ) : ℂ) •
        outerMatrix (fun k => (z.2 n k : ℂ))) =
      ∑' n, ((-(parameters.scale * poissonWeight (p.location n) w.1) : ℝ) : ℂ) •
        outerMatrix (fun k => (z.2 n k : ℂ)) := by
      simpa only [Complex.ofReal_neg, neg_smul] using
        (tsum_neg (f := fun n => ((parameters.scale * poissonWeight (p.location n) w.1 : ℝ) : ℂ) •
          outerMatrix (fun k => (z.2 n k : ℂ)))).symm
    rw [heq]
    exact hspan _ hpneg hn

/-- On an infinite label space the four required occurrences are selected
canonically; strict positivity is a theorem, not an additional model premise. -/
theorem constructedMatrix_ae_signDefinite [Infinite I] (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ w : NonrealSpectral,
      ImaginarySignDefinite (constructedMatrix P X hX hm parameters z w) := by
  let e : Fin 4 → I := fun n => Infinite.natEmbedding I n
  have he : Function.Injective e := (Infinite.natEmbedding I).injective.comp Fin.val_injective
  exact constructedMatrix_ae_signDefinite_selection P X hX hm parameters hlinear e he

/-- Every actual raw matrix and exterior inverse exists simultaneously at
all nonreal spectral parameters. -/
theorem constructedMatrix_ae_isUnit [Infinite I] (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ w : NonrealSpectral,
      IsUnit (constructedMatrix P X hX hm parameters z w) := by
  filter_upwards [constructedMatrix_ae_signDefinite P X hX hm parameters hlinear] with z hz
  intro w
  exact isUnit_of_imaginary_signDefinite _ (hz w)

end GeneralizedBulk.Exterior
