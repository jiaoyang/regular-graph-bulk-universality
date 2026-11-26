import GaussianWave.BS.InnovationRelativeSSA
import GaussianWave.BS.FiniteGluingUniqueness

/-! Actual conditional gluing with reference marginals recovers the actual
independent reference law. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

variable {V Z A Y J : Type*} [Fintype V] [Fintype Z] [Fintype A] [Fintype Y] [Fintype J]
    [DecidableEq Z] [DecidableEq Y] [DecidableEq J]

theorem innovationLocalDensity_reference_law
    (L : ((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ))
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :
    (innovationLocalDensity L (innovationReferenceLocal L gZ gY)).law = (gZ.prod gY).law := by
  have hL : Measurable (L : _ → _) := L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hLs : Measurable (L.symm : _ → _) := L.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  rw [innovationLocalDensity, PositiveEntropyDensity.transport_law,
    PositiveEntropyDensity.linearEquiv_law, innovationReferenceLocal,
    PositiveEntropyDensity.linearEquiv_law, Measure.map_map hLs hL]
  have hinv : (L.symm : _ → _) ∘ L = id := funext L.symm_apply_apply
  rw [hinv, Measure.map_id, innovationReferenceLocalVector, PositiveEntropyDensity.transport_law,
    Measure.map_map (sumProductCoordinates Z Y).measurable (sumProductCoordinates Z Y).symm.measurable]
  have hsum : (sumProductCoordinates Z Y : _ → _) ∘ (sumProductCoordinates Z Y).symm = id :=
    funext (sumProductCoordinates Z Y).apply_symm_apply
  rw [hsum, Measure.map_id]

theorem innovation_eq_reference_of_gluing (e : V ≃ Z ⊕ (A × Y))
    (L : A → (((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ)))
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ)))
    (p : A → PositiveEntropyDensity (volume : Measure (J → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ)))
    (hp : ∀ a, (p a).law = (innovationReferenceLocal (L a) gZ gY).law)
    (hs : s.law = gZ.law)
    (hglue : (innovationSplitDensity e f).law = finiteConditionalGluingLaw
      (volume : Measure (Y → ℝ)) (volume : Measure (Z → ℝ))
      (fun a => innovationLocalDensity (L a) (p a)) s) :
    f.law = (innovationReferenceFull e gZ gY).law := by
  have hlocal (a : A) : (innovationLocalDensity (L a) (p a)).law = (gZ.prod gY).law := by
    rw [innovationLocalDensity, PositiveEntropyDensity.transport_law, PositiveEntropyDensity.linearEquiv_law,
      hp a]
    simpa only [innovationLocalDensity, PositiveEntropyDensity.transport_law,
      PositiveEntropyDensity.linearEquiv_law] using innovationLocalDensity_reference_law (L a) gZ gY
  have hfull : (innovationSplitDensity e f).law = gZ.law.prod (Measure.pi (fun _ : A => gY.law)) :=
    hglue.trans ((finiteConditionalGluingLaw_congr_of_laws
      (volume : Measure (Y → ℝ)) (volume : Measure (Z → ℝ))
      (fun a => innovationLocalDensity (L a) (p a)) (fun _ : A => gZ.prod gY) s gZ hlocal hs).trans
      (finiteConditionalGluingLaw_product _ _ gZ (fun _ : A => gY)))
  rw [innovationSplitDensity, PositiveEntropyDensity.transport_law] at hfull
  rw [innovationReferenceFull, PositiveEntropyDensity.transport_law,
    PositiveEntropyDensity.prod_law, PositiveEntropyDensity.iid_law, ← hfull,
    Measure.map_map (finiteInnovationSplitEquiv e).symm.measurable (finiteInnovationSplitEquiv e).measurable]
  have hinv : (finiteInnovationSplitEquiv e).symm ∘ finiteInnovationSplitEquiv e = id :=
    funext (finiteInnovationSplitEquiv e).symm_apply_apply
  rw [hinv, Measure.map_id]

end GaussianWave.BS
