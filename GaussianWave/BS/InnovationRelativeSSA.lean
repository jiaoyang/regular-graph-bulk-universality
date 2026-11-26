import GaussianWave.BS.InnovationEntropyCoordinates

/-!
# Relative SSA in actual innovation charts

The inputs are positive density laws and their literal coordinate marginal
identities.  Both reference laws are constructed from independent new blocks.
No entropy inequality, zero entropy gap, or conditional independence of the
source is an input.  Equality gives the actual conditional gluing law.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

variable {V Z A Y J : Type*} [Fintype V] [Fintype Z] [Fintype A] [Fintype Y] [Fintype J]
    [DecidableEq Z] [DecidableEq Y] [DecidableEq J]

def innovationCoreProjection (e : V ≃ Z ⊕ (A × Y)) (x : V → ℝ) : Z → ℝ :=
  (finiteInnovationSplitEquiv e x).1

def innovationLocalProjection (e : V ≃ Z ⊕ (A × Y)) (a : A) (x : V → ℝ) : (Z ⊕ Y) → ℝ :=
  concatenateVector ((finiteInnovationSplitEquiv e x).1, (finiteInnovationSplitEquiv e x).2 a)

theorem measurable_innovationCoreProjection (e : V ≃ Z ⊕ (A × Y)) :
    Measurable (innovationCoreProjection e) := measurable_fst.comp (finiteInnovationSplitEquiv e).measurable

theorem measurable_innovationLocalProjection (e : V ≃ Z ⊕ (A × Y)) (a : A) :
    Measurable (innovationLocalProjection e a) :=
  measurable_concatenateVector.comp ((measurable_fst.prodMk
    ((measurable_pi_apply a).comp measurable_snd)).comp (finiteInnovationSplitEquiv e).measurable)

def innovationSplitDensity (e : V ≃ Z ⊕ (A × Y))
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ))) :=
  f.transport (finiteInnovationSplitEquiv e) (finiteInnovationSplitEquiv_volumePreserving e)

def innovationLocalDensity (L : ((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ))
    (p : PositiveEntropyDensity (volume : Measure (J → ℝ))) :=
  (p.linearEquiv L.symm).transport (sumProductCoordinates Z Y)
    (sumProductCoordinates_volumePreserving Z Y)

def innovationReferenceLocalVector
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :=
  (gZ.prod gY).transport (sumProductCoordinates Z Y).symm
    (sumProductCoordinates_volumePreserving Z Y).symm

def innovationReferenceLocal (L : ((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ))
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :=
  (innovationReferenceLocalVector gZ gY).linearEquiv L

def innovationReferenceFull (e : V ≃ Z ⊕ (A × Y))
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :=
  (gZ.prod (gY.iid A)).transport (finiteInnovationSplitEquiv e).symm
    (finiteInnovationSplitEquiv_volumePreserving e).symm

theorem innovationLocalDensity_law (e : V ≃ Z ⊕ (A × Y))
    (L : ((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ)) (a : A)
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ)))
    (p : PositiveEntropyDensity (volume : Measure (J → ℝ)))
    (hp : Measure.map (L ∘ innovationLocalProjection e a) f.law = p.law) :
    Measure.map (fun zy : (Z → ℝ) × (A → Y → ℝ) => (zy.1, zy.2 a))
      (innovationSplitDensity e f).law = (innovationLocalDensity L p).law := by
  have hL : Measurable (L : ((Z ⊕ Y) → ℝ) → (J → ℝ)) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hLs : Measurable (L.symm : (J → ℝ) → ((Z ⊕ Y) → ℝ)) :=
    L.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have hlocal : Measure.map (innovationLocalProjection e a) f.law = Measure.map L.symm p.law := by
    rw [← hp, Measure.map_map hLs (hL.comp (measurable_innovationLocalProjection e a))]
    congr 1
    funext x
    exact (L.symm_apply_apply (innovationLocalProjection e a x)).symm
  rw [innovationSplitDensity, PositiveEntropyDensity.transport_law,
    innovationLocalDensity, PositiveEntropyDensity.transport_law,
    PositiveEntropyDensity.linearEquiv_law, ← hlocal,
    Measure.map_map (by fun_prop) (finiteInnovationSplitEquiv e).measurable,
    Measure.map_map (sumProductCoordinates Z Y).measurable (measurable_innovationLocalProjection e a)]
  rfl

theorem innovationSplitDensity_core_law (e : V ≃ Z ⊕ (A × Y))
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (hs : Measure.map (innovationCoreProjection e) f.law = s.law) :
    Measure.map Prod.fst (innovationSplitDensity e f).law = s.law := by
  rw [innovationSplitDensity, PositiveEntropyDensity.transport_law,
    Measure.map_map measurable_fst (finiteInnovationSplitEquiv e).measurable]
  exact hs

theorem innovationLocalDensity_relative_entropy
    (L : ((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ))
    (p : PositiveEntropyDensity (volume : Measure (J → ℝ)))
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :
    (innovationLocalDensity L p).entropy - (gZ.prod gY).entropy =
      p.entropy - (innovationReferenceLocal L gZ gY).entropy := by
  have hL : Measurable (L : ((Z ⊕ Y) → ℝ) → (J → ℝ)) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hLs : Measurable (L.symm : (J → ℝ) → ((Z ⊕ Y) → ℝ)) :=
    L.symm.toLinearMap.continuous_of_finiteDimensional.measurable
  have hrec : ((p.linearEquiv L.symm).linearEquiv L).law = p.law := by
    rw [PositiveEntropyDensity.linearEquiv_law, PositiveEntropyDensity.linearEquiv_law,
      Measure.map_map hL hLs]
    have hcomp : (L : _ → _) ∘ L.symm = id := funext L.apply_symm_apply
    rw [hcomp, Measure.map_id]
  have hent := ((p.linearEquiv L.symm).linearEquiv L).toFiniteEntropy.entropy_eq_of_measure_eq
    p.toFiniteEntropy hrec
  have h := (p.linearEquiv L.symm).linearEquiv_entropy_difference
    (innovationReferenceLocalVector gZ gY) L
  change ((p.linearEquiv L.symm).linearEquiv L).entropy = p.entropy at hent
  rw [hent] at h
  simpa only [innovationLocalDensity, innovationReferenceLocal, innovationReferenceLocalVector,
    PositiveEntropyDensity.transport_entropy] using h.symm

theorem innovationRelativeSSA_nonneg (e : V ≃ Z ⊕ (A × Y))
    (L : A → (((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ)))
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ)))
    (p : A → PositiveEntropyDensity (volume : Measure (J → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (hp : ∀ a, Measure.map ((L a) ∘ innovationLocalProjection e a) f.law = (p a).law)
    (hs : Measure.map (innovationCoreProjection e) f.law = s.law)
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :
    0 ≤ (∑ a, ((p a).entropy - (innovationReferenceLocal (L a) gZ gY).entropy)) -
      (Fintype.card A - 1 : ℝ) * (s.entropy - gZ.entropy) -
      (f.entropy - (innovationReferenceFull e gZ gY).entropy) := by
  have h := relativeFiniteStrongSubadditivity_of_product_reference
    (volume : Measure (Y → ℝ)) (volume : Measure (Z → ℝ)) (innovationSplitDensity e f)
    (fun a => innovationLocalDensity (L a) (p a)) s
    (fun a => innovationLocalDensity_law e (L a) a f (p a) (hp a))
    (innovationSplitDensity_core_law e f s hs) gZ gY (gZ.prod (gY.iid A))
    (by rw [PositiveEntropyDensity.prod_law, PositiveEntropyDensity.iid_law])
  simpa only [innovationLocalDensity_relative_entropy, innovationSplitDensity,
    innovationReferenceFull, PositiveEntropyDensity.transport_entropy] using h

theorem innovationRelativeSSA_equality_iff (e : V ≃ Z ⊕ (A × Y))
    (L : A → (((Z ⊕ Y) → ℝ) ≃ₗ[ℝ] (J → ℝ)))
    (f : PositiveEntropyDensity (volume : Measure (V → ℝ)))
    (p : A → PositiveEntropyDensity (volume : Measure (J → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (hp : ∀ a, Measure.map ((L a) ∘ innovationLocalProjection e a) f.law = (p a).law)
    (hs : Measure.map (innovationCoreProjection e) f.law = s.law)
    (gZ : PositiveEntropyDensity (volume : Measure (Z → ℝ)))
    (gY : PositiveEntropyDensity (volume : Measure (Y → ℝ))) :
    ((∑ a, ((p a).entropy - (innovationReferenceLocal (L a) gZ gY).entropy)) -
      (Fintype.card A - 1 : ℝ) * (s.entropy - gZ.entropy) -
      (f.entropy - (innovationReferenceFull e gZ gY).entropy) = 0) ↔
      (innovationSplitDensity e f).law = finiteConditionalGluingLaw
        (volume : Measure (Y → ℝ)) (volume : Measure (Z → ℝ))
        (fun a => innovationLocalDensity (L a) (p a)) s := by
  have h := relativeFiniteStrongSubadditivity_equality_iff_of_product_reference
    (volume : Measure (Y → ℝ)) (volume : Measure (Z → ℝ)) (innovationSplitDensity e f)
    (fun a => innovationLocalDensity (L a) (p a)) s
    (fun a => innovationLocalDensity_law e (L a) a f (p a) (hp a))
    (innovationSplitDensity_core_law e f s hs) gZ gY (gZ.prod (gY.iid A))
    (by rw [PositiveEntropyDensity.prod_law, PositiveEntropyDensity.iid_law])
  simpa only [innovationLocalDensity_relative_entropy, innovationSplitDensity,
    innovationReferenceFull, PositiveEntropyDensity.transport_entropy] using h

end GaussianWave.BS
