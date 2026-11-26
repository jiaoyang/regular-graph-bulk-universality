import GeneralizedBulk.Gaussian.Nondegenerate
import GeneralizedBulk.Exterior.PositiveSeries
import Mathlib

/-!
# Almost sure spanning of independent nondegenerate endpoint marks

The generic argument uses only that every proper real subspace has measure
zero. The Gaussian law verifies this condition separately, so no spanning
certificate is postulated for the random marked series.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ComplexOrder
namespace GeneralizedBulk.Exterior

abbrev RealEndpoint := Fin 4 → ℝ

def ProperSubmoduleNull (ν : Measure RealEndpoint) : Prop :=
  ∀ S : Submodule ℝ RealEndpoint, S ≠ ⊤ → ν (S : Set RealEndpoint) = 0

private theorem span_prefix_ne_top {n : ℕ} (hn : n < 4) (v : Fin n → RealEndpoint) :
    Submodule.span ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have h := finrank_le_of_span_eq_top htop
  simp only [Module.finrank_fin_fun, Fintype.card_fin] at h
  omega

private theorem continuous_cons (n : ℕ) :
    Continuous (fun z : RealEndpoint × (Fin n → RealEndpoint) => (Fin.cons z.1 z.2 : Fin (n + 1) → RealEndpoint)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous (fun z : RealEndpoint × (Fin n → RealEndpoint) => z.1))
  · simpa using ((continuous_apply j).comp continuous_snd :
      Continuous (fun z : RealEndpoint × (Fin n → RealEndpoint) => z.2 j))

/-- Up to the ambient dimension, independent samples from a subspace-null
probability law are linearly independent almost surely. -/
theorem ae_linearIndependent_pi (ν : Measure RealEndpoint) [IsProbabilityMeasure ν]
    (hν : ProperSubmoduleNull ν) (n : ℕ) (hn : n ≤ 4) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => ν), LinearIndependent ℝ v := by
  induction n with
  | zero => exact Eventually.of_forall (fun v => linearIndependent_empty_type)
  | succ n ih =>
      have hnlt : n < 4 := by omega
      have ih' := ih (by omega)
      have hmeas : MeasurableSet {z : RealEndpoint × (Fin n → RealEndpoint) |
          LinearIndependent ℝ (Fin.cons z.1 z.2)} :=
        (isOpen_setOf_linearIndependent.preimage (continuous_cons n)).measurableSet
      have htail : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => ν),
          ∀ᵐ x ∂ν, LinearIndependent ℝ (Fin.cons x v) := by
        filter_upwards [ih'] with v hv
        have hnull := hν (Submodule.span ℝ (Set.range v)) (span_prefix_ne_top hnlt v)
        have hnot : ∀ᵐ x ∂ν, x ∉ Submodule.span ℝ (Set.range v) := by
          simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hnull
        filter_upwards [hnot] with x hx
        exact linearIndependent_fin_cons.mpr ⟨hv, hx⟩
      have hhead : ∀ᵐ x ∂ν, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => ν),
          LinearIndependent ℝ (Fin.cons x v) := (Measure.ae_ae_comm hmeas).mpr htail
      have hprod : ∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
          LinearIndependent ℝ (Fin.cons z.1 z.2) := (Measure.ae_prod_iff_ae_ae hmeas).mpr hhead
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => RealEndpoint) 0
      have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (0 : Fin (n + 1))
      have hmap : ∀ᵐ z ∂Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ν)),
          LinearIndependent ℝ (Fin.cons z.1 z.2) := by
        rw [he.map_eq]
        exact hprod
      have hpull := ae_of_ae_map he.measurable.aemeasurable hmap
      filter_upwards [hpull] with v hv
      simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.cons_self_tail] using hv

/-- Any injective selection of four coordinates of the actual iid product is
linearly independent almost surely under a proper-subspace-null law. -/
theorem ae_linearIndependent_iid_selection
    (ν : Measure RealEndpoint) [IsProbabilityMeasure ν] (hν : ProperSubmoduleNull ν)
    (I : Type*) (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ ω ∂Gaussian.iidLaw ν I, LinearIndependent ℝ (fun i : Fin 4 => ω (e i)) := by
  have hmap : ∀ᵐ v ∂Measure.map (fun ω : I → RealEndpoint => fun i : Fin 4 => ω (e i))
      (Gaussian.iidLaw ν I), LinearIndependent ℝ v := by
    rw [Gaussian.iidLaw_map_injectiveSelection ν I e he]
    exact ae_linearIndependent_pi ν hν 4 le_rfl
  exact ae_of_ae_map (measurable_pi_lambda _ fun i => measurable_pi_apply (e i)).aemeasurable hmap

/-- Four independent nondegenerate Gaussian marks span the endpoint space. -/
theorem gaussianMarks_ae_linearIndependent (p : ℝ) (hp : |p| < 1)
    (I : Type*) (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) I,
      LinearIndependent ℝ (fun i : Fin 4 => ω (e i)) :=
  ae_linearIndependent_iid_selection (Gaussian.markLaw p)
    (Gaussian.markLaw_properSubmodule_null p hp) I e he

/-- The columns are four selected endpoint marks. -/
def markMatrix {I : Type*} (e : Fin 4 → I) (ω : I → RealEndpoint) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j => ω (e j) i

theorem gaussianMarks_ae_markMatrix_isUnit (p : ℝ) (hp : |p| < 1)
    (I : Type*) (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) I, IsUnit (markMatrix e ω) := by
  filter_upwards [gaussianMarks_ae_linearIndependent p hp I e he] with ω hω
  exact Matrix.linearIndependent_cols_iff_isUnit.mp hω

/-- Complexification preserves the actual invertibility of the four-mark
matrix; no complex Gaussian nondegeneracy assumption is introduced. -/
theorem gaussianMarks_ae_complexMarkMatrix_isUnit (p : ℝ) (hp : |p| < 1)
    (I : Type*) (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) I,
      IsUnit ((markMatrix e ω).map Complex.ofReal) := by
  filter_upwards [gaussianMarks_ae_markMatrix_isUnit p hp I e he] with ω hω
  exact hω.map Complex.ofRealHom.mapMatrix

/-- Every positive weighting of four selected Gaussian marks gives a strictly
positive endpoint contribution almost surely. -/
theorem gaussianMarks_ae_positive_weighted_gram (p : ℝ) (hp : |p| < 1)
    (I : Type*) (e : Fin 4 → I) (he : Function.Injective e)
    (weight : Fin 4 → ℝ) (hw : ∀ i, 0 < weight i) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) I,
      (((markMatrix e ω).map Complex.ofReal) *
        Matrix.diagonal (fun i => (weight i : ℂ)) *
        ((markMatrix e ω).map Complex.ofReal).conjTranspose).PosDef := by
  filter_upwards [gaussianMarks_ae_complexMarkMatrix_isUnit p hp I e he] with ω hω
  exact positive_weighted_gram _ hω weight hw

/-- One full-probability event works for every strictly positive weighting of
any summable endpoint outer-product series. This is the common event needed
for positivity at all off-real spectral parameters simultaneously. -/
theorem gaussianMarks_ae_posDef_all_weighted_tsum (p : ℝ) (hp : |p| < 1) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) ℕ,
      ∀ a : ℕ → ℝ, (∀ n, 0 < a n) →
      Summable (fun n => (a n : ℂ) • outerMatrix (fun i => (ω n i : ℂ))) →
      (∑' n, (a n : ℂ) • outerMatrix (fun i => (ω n i : ℂ))).PosDef := by
  have he : Function.Injective (fun i : Fin 4 => (i : ℕ)) := Fin.val_injective
  filter_upwards [gaussianMarks_ae_complexMarkMatrix_isUnit p hp ℕ _ he] with ω hω
  intro a ha hs
  have hprefix : (∑ n ∈ Finset.range 4,
      (a n : ℂ) • outerMatrix (fun i => (ω n i : ℂ))).PosDef := by
    have hg := positive_weighted_gram _ hω (fun i : Fin 4 => a i) (fun i => ha i)
    rw [weighted_gram_eq_sum] at hg
    simpa only [Fin.sum_univ_eq_sum_range, markMatrix, Matrix.map_apply] using hg
  exact posDef_tsum_of_prefix _
    (fun n => weighted_outer_posSemidef _ (a n) (ha n).le) hs 4 hprefix

/-- Intrinsic-label version: four selected particle occurrences force strict
positivity of every positive weighted summable mark series on the same event. -/
theorem gaussianMarks_ae_posDef_all_weighted_tsum_selection
    (p : ℝ) (hp : |p| < 1) (I : Type*) (e : Fin 4 → I) (he : Function.Injective e) :
    ∀ᵐ ω ∂Gaussian.iidLaw (Gaussian.markLaw p) I,
      ∀ a : I → ℝ, (∀ i, 0 < a i) →
      Summable (fun i => (a i : ℂ) • outerMatrix (fun k => (ω i k : ℂ))) →
      (∑' i, (a i : ℂ) • outerMatrix (fun k => (ω i k : ℂ))).PosDef := by
  classical
  filter_upwards [gaussianMarks_ae_complexMarkMatrix_isUnit p hp I e he] with ω hω
  intro a ha hs
  let F := fun i => (a i : ℂ) • outerMatrix (fun k => (ω i k : ℂ))
  have hprefix : (∑ i ∈ Finset.univ.image e, F i).PosDef := by
    rw [Finset.sum_image (fun i _ j _ hij => he hij)]
    have hg := positive_weighted_gram _ hω (fun i : Fin 4 => a (e i)) (fun i => ha (e i))
    rw [weighted_gram_eq_sum] at hg
    simpa only [F, markMatrix, Matrix.map_apply] using hg
  exact posDef_tsum_of_finset F
    (fun i => weighted_outer_posSemidef _ (a i) (ha i).le) hs _ hprefix

end GeneralizedBulk.Exterior
