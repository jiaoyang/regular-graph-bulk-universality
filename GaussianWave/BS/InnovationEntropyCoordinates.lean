import GaussianWave.BS.IndependentPositiveDensity
import GaussianWave.BS.RelativeEntropyCoordinates

/-!
# Entropy in literal common-core and extension coordinates

All maps in this file are genuine coordinate rearrangements.  In particular,
their entropy transport is proved from preservation of product Lebesgue
measure, rather than imposed as a chart compatibility condition.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

namespace PositiveEntropyDensity
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {m : Measure E} {n : Measure F}

def transport (p : PositiveEntropyDensity m) (e : E ≃ᵐ F) (he : MeasurePreserving e m n) :
    PositiveEntropyDensity n where
  density := fun y => p.density (e.symm y)
  measurable := p.measurable.comp e.symm.measurable
  positive := fun _ => p.positive _
  integrable := (he.integrable_comp_emb e.measurableEmbedding).mp (by
    simpa only [Function.comp_def, e.symm_apply_apply] using p.integrable)
  integral_one := by
    have h := he.integral_comp e.measurableEmbedding (fun y => p.density (e.symm y))
    simpa only [e.symm_apply_apply, p.integral_one] using h.symm
  integrable_log := (he.integrable_comp_emb e.measurableEmbedding).mp (by
    simpa only [Function.comp_def, e.symm_apply_apply] using p.integrable_log)

theorem transport_law (p : PositiveEntropyDensity m) (e : E ≃ᵐ F) (he : MeasurePreserving e m n) :
    (p.transport e he).law = Measure.map e p.law := by
  rw [law, law, map_withDensity_measurableEquiv m e _ p.measurable.ennreal_ofReal, he.map_eq]
  rfl

@[simp] theorem transport_entropy (p : PositiveEntropyDensity m) (e : E ≃ᵐ F)
    (he : MeasurePreserving e m n) : (p.transport e he).entropy = p.entropy := by
  have h := he.integral_comp e.measurableEmbedding
    (fun y => p.density (e.symm y) * Real.log (p.density (e.symm y)))
  simp only [e.symm_apply_apply] at h
  exact congrArg Neg.neg h.symm

def toFiniteEntropy {I : Type*} [Fintype I]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ))) : FiniteEntropyDensity p.law where
  density := p.density
  measurable := p.measurable
  nonneg := fun x => (p.positive x).le
  integrable := p.integrable
  integral_eq_one := p.integral_one
  integrable_log := p.integrable_log
  measure_eq := rfl

@[simp] theorem toFiniteEntropy_entropy {I : Type*} [Fintype I]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ))) :
    p.toFiniteEntropy.entropy = p.entropy := rfl

end PositiveEntropyDensity

def sumProductCoordinates (I J : Type*) : ((I ⊕ J) → ℝ) ≃ᵐ ((I → ℝ) × (J → ℝ)) where
  toEquiv := Equiv.sumArrowEquivProdArrow I J ℝ
  measurable_toFun := by
    exact (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).prodMk
      (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
  measurable_invFun := measurable_concatenateVector

theorem sumProductCoordinates_volumePreserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (sumProductCoordinates I J) volume (volume.prod volume) := by
  simpa only [volume_pi] using
    (measurePreserving_sumPiEquivProdPi (X := fun _ : I ⊕ J => ℝ) (fun _ => volume))

def finiteInnovationSplitEquiv {V Z A Y : Type*} (e : V ≃ Z ⊕ (A × Y)) :
    (V → ℝ) ≃ᵐ ((Z → ℝ) × (A → Y → ℝ)) where
  toFun x := (fun z => x (e.symm (Sum.inl z)), fun a y => x (e.symm (Sum.inr (a, y))))
  invFun p := fun v => Sum.elim p.1 (fun ay => p.2 ay.1 ay.2) (e v)
  left_inv x := by
    funext v
    cases h : e v with
    | inl z =>
      simp only [h, Sum.elim_inl]
      rw [← h, e.symm_apply_apply]
    | inr ay =>
      simp only [h, Sum.elim_inr]
      rw [← h, e.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · funext z; simp
    · funext a y; simp
  measurable_toFun := by
    exact (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).prodMk
      (measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun _ => measurable_pi_apply _)))
  measurable_invFun := by
    apply measurable_pi_lambda
    intro v
    change Measurable (fun p : (Z → ℝ) × (A → Y → ℝ) =>
      Sum.elim p.1 (fun ay => p.2 ay.1 ay.2) (e v))
    cases h : e v with
    | inl z =>
      simpa only [h, Sum.elim_inl] using
        (show Measurable (fun p : (Z → ℝ) × (A → Y → ℝ) => p.1 z) from
          (measurable_pi_apply z).comp measurable_fst)
    | inr ay =>
      simpa only [h, Sum.elim_inr] using
        (show Measurable (fun p : (Z → ℝ) × (A → Y → ℝ) => p.2 ay.1 ay.2) from
          (measurable_pi_apply ay.2).comp ((measurable_pi_apply ay.1).comp measurable_snd))

theorem finiteInnovationSplitEquiv_volumePreserving {V Z A Y : Type*}
    [Fintype V] [Fintype Z] [Fintype A] [Fintype Y] (e : V ≃ Z ⊕ (A × Y)) :
    MeasurePreserving (finiteInnovationSplitEquiv e) volume
      (volume.prod (Measure.pi (fun _ : A => (volume : Measure (Y → ℝ))))) := by
  have hp := measurePreserving_partitionProductCoordinates e (volume : Measure ℝ)
  have hc := measurePreserving_curryBlocks (A := A) (B := Y) (volume : Measure ℝ)
  have hid : MeasurePreserving (id : (Z → ℝ) → (Z → ℝ)) volume volume :=
    ⟨measurable_id, Measure.map_id⟩
  convert (hid.prod hc).comp hp using 1 <;> simp only [volume_pi]

def coloredForestSplit (κ A : Type*) (m k : ℕ) :
    (κ × ForestInnovation A m (k + 1)) ≃
      (κ × ForestInnovation A m k) ⊕ (A × (κ × NewBranchInnovation m k)) where
  toFun cj := Sum.elim (fun old => Sum.inl (cj.1, old))
    (fun an => Sum.inr (an.1, (cj.1, an.2))) (forestInnovationSplit A m k cj.2)
  invFun := Sum.elim (fun co => (co.1, (forestInnovationSplit A m k).symm (Sum.inl co.2)))
    (fun acn => (acn.2.1, (forestInnovationSplit A m k).symm (Sum.inr (acn.1, acn.2.2))))
  left_inv cj := by
    cases h : forestInnovationSplit A m k cj.2 with
    | inl old => simp only [h, Sum.elim_inl]; rw [← h, Equiv.symm_apply_apply]
    | inr an => simp only [h, Sum.elim_inr]; rw [← h, Equiv.symm_apply_apply]
  right_inv j := by
    cases j with
    | inl co => simp only [Equiv.apply_symm_apply, Sum.elim_inl]
    | inr acn => simp only [Equiv.apply_symm_apply, Sum.elim_inr]

def coloredForestSplitCoordinates (κ A : Type*) (m k : ℕ) :=
  finiteInnovationSplitEquiv (coloredForestSplit κ A m k)

theorem coloredForestSplitCoordinates_volumePreserving (κ A : Type*) [Fintype κ] [Fintype A]
    (m k : ℕ) : MeasurePreserving (coloredForestSplitCoordinates κ A m k) volume
      (volume.prod (Measure.pi (fun _ : A => (volume : Measure ((κ × NewBranchInnovation m k) → ℝ))))) :=
  finiteInnovationSplitEquiv_volumePreserving _

def channelwiseLinearEquiv (κ : Type*) {I J : Type*}
    (e : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) : ((κ × I) → ℝ) ≃ₗ[ℝ] ((κ × J) → ℝ) where
  toFun x := fun kj => e (fun i => x (kj.1, i)) kj.2
  invFun x := fun ki => e.symm (fun j => x (ki.1, j)) ki.2
  left_inv x := by funext ⟨a, i⟩; exact congrFun (e.symm_apply_apply (fun i => x (a, i))) i
  right_inv x := by funext ⟨a, j⟩; exact congrFun (e.apply_symm_apply (fun j => x (a, j))) j
  map_add' x y := by funext ⟨a, j⟩; exact congrFun (e.map_add _ _) j
  map_smul' r x := by funext ⟨a, j⟩; exact congrFun (e.map_smul r _) j

theorem FiniteEntropyDensity.linearEquiv_positive {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity μ) (hf : ∀ x, 0 < f.density x)
    (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) (x : J → ℝ) :
    0 < (f.linearEquiv A).density x := by
  letI : IsProbabilityMeasure (Measure.map (coordinateReindex (linearChartIndexEquiv A)) μ) :=
    isProbabilityMeasure_map (measurable_coordinateReindex _).aemeasurable
  exact (f.reindex (linearChartIndexEquiv A)).linearImage_positive (fun y => hf _)
    (squareChartMatrix A) (squareChartMatrix_det_ne_zero A) x

def PositiveEntropyDensity.linearEquiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ)))
    (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) : PositiveEntropyDensity (volume : Measure (J → ℝ)) :=
  (p.toFiniteEntropy.linearEquiv A).toPositive
    (p.toFiniteEntropy.linearEquiv_positive p.positive A)

@[simp] theorem PositiveEntropyDensity.linearEquiv_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (p : PositiveEntropyDensity (volume : Measure (I → ℝ)))
    (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    (p.linearEquiv A).law = Measure.map A p.law := FiniteEntropyDensity.toPositive_law _ _

theorem PositiveEntropyDensity.linearEquiv_entropy_difference {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (p q : PositiveEntropyDensity (volume : Measure (I → ℝ)))
    (A : (I → ℝ) ≃ₗ[ℝ] (J → ℝ)) :
    (p.linearEquiv A).entropy - (q.linearEquiv A).entropy = p.entropy - q.entropy :=
  p.toFiniteEntropy.linearEquiv_entropy_difference q.toFiniteEntropy A

end GaussianWave.BS
