import GeneralizedBulk.Graph.EntryObstruction

/-! A finite entry envelope transports entrywise Gaussian moments to matrix perturbation bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Graph
open Exterior

def entryEnvelope (M : Mat) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem entryEnvelope_nonneg (M : Mat) : 0 ≤ entryEnvelope M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))

theorem continuous_entryEnvelope : Continuous entryEnvelope := by
  unfold entryEnvelope
  exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).norm))

theorem entryEnvelope_bound (M : Mat) : EntryBound M (entryEnvelope M) := by
  intro i j
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (M i j)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (M i j)))
      (Finset.mem_univ i))

@[simp] theorem entryEnvelope_eq_zero_iff (M : Mat) : entryEnvelope M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    exact norm_eq_zero.mp (le_antisymm (by simpa only [h] using entryEnvelope_bound M i j)
      (norm_nonneg _))
  · intro h
    subst M
    simp [entryEnvelope]

theorem entryEnvelope_square_le (M : Mat) :
    entryEnvelope M ^ 2 ≤ 16 * (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin 4 × Fin 4 => ‖M p.1 p.2‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul] at h
  simp only [Fintype.sum_prod_type] at h
  simpa only [entryEnvelope,mul_comm] using h

theorem aestronglyMeasurable_entryEnvelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Mat)
    (hM : ∀ i j, AEStronglyMeasurable (fun ω => M ω i j) P) :
    AEStronglyMeasurable (fun ω => entryEnvelope (M ω)) P :=
  Finset.univ.aestronglyMeasurable_sum (fun i _ =>
    Finset.univ.aestronglyMeasurable_sum (fun j _ => (hM i j).norm))

/-- The envelope square is integrable directly from the sixteen entry
second moments, with an explicit finite-dimensional constant. -/
theorem integrable_entryEnvelope_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Mat)
    (hM : ∀ i j, AEStronglyMeasurable (fun ω => M ω i j) P)
    (hM2 : ∀ i j, Integrable (fun ω => ‖M ω i j‖ ^ 2) P) :
    Integrable (fun ω => entryEnvelope (M ω) ^ 2) P := by
  have hi := (integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hM2 i j))).const_mul 16
  apply hi.mono' ((aestronglyMeasurable_entryEnvelope P M hM).pow 2)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact entryEnvelope_square_le (M ω)

/-- Actual entry variances bound the actual matrix-envelope second moment. -/
theorem integral_entryEnvelope_square_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Mat)
    (hM : ∀ i j, AEStronglyMeasurable (fun ω => M ω i j) P)
    (hM2 : ∀ i j, Integrable (fun ω => ‖M ω i j‖ ^ 2) P) :
    (∫ ω, entryEnvelope (M ω) ^ 2 ∂P) ≤
      16 * (∑ i, ∑ j, ∫ ω, ‖M ω i j‖ ^ 2 ∂P) := by
  have hiSum := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hM2 i j))
  have hb := integral_mono (integrable_entryEnvelope_square P M hM hM2)
    (hiSum.const_mul 16) (fun ω => entryEnvelope_square_le (M ω))
  rw [integral_const_mul,integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hM2 i j))] at hb
  simp_rw [integral_finset_sum _ (fun j _ => hM2 _ j)] at hb
  exact hb

end GeneralizedBulk.Graph
