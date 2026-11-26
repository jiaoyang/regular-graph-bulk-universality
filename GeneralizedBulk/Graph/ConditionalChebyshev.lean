import GeneralizedBulk.Graph.FiniteConditional
import GeneralizedBulk.Graph.EntryObstruction

/-!
# Relative concentration failure from finite conditional variances

The probability of entrywise concentration failure is proved by Markov's
inequality and exact graph-fiber averaging. No concentration bound is assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open Exterior

/-- Sixteen genuine entry second moments bound the probability of failure of
an entrywise matrix threshold. -/
theorem entryFailure_probability_le
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (X : S → Mat) (R V : ℝ) (hR : 0 < R)
    (hi : ∀ i j, Integrable (fun s => ‖X s i j‖ ^ 2) P)
    (hV : ∀ i j, (∫ s, ‖X s i j‖ ^ 2 ∂P) ≤ V) :
    P.real {s | ¬ EntryBound (X s) R} ≤ 16 * V / R ^ 2 := by
  let Y (s : S) : ℝ := ∑ i : Fin 4, ∑ j : Fin 4, ‖X s i j‖ ^ 2
  have hY : Integrable Y P := integrable_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hi i j))
  have hY0 (s : S) : 0 ≤ Y s :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hsubset : {s | ¬ EntryBound (X s) R} ⊆ {s | R ^ 2 ≤ Y s} := by
    intro s hs
    simp only [EntryBound, not_forall, not_le] at hs
    obtain ⟨i,j,hij⟩ := hs
    have hinner : ‖X s i j‖ ^ 2 ≤ ∑ j : Fin 4, ‖X s i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin 4 => ‖X s i j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have houter : (∑ j : Fin 4, ‖X s i j‖ ^ 2) ≤ Y s :=
      Finset.single_le_sum (f := fun i : Fin 4 => ∑ j : Fin 4, ‖X s i j‖ ^ 2)
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
    exact (le_of_lt ((sq_lt_sq₀ hR.le (norm_nonneg _)).mpr hij)).trans (hinner.trans houter)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hY0) hY (R ^ 2)
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsubset) (sq_nonneg R)
  have htotal : (∫ s, Y s ∂P) ≤ 16 * V := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hi _ j)]
    calc
      _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, V :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hV i j))
      _ = _ := by simp; ring
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by
    simpa only [mul_comm] using (hmono.trans hmark).trans htotal)

/-- A conditional variance growing only as `1+T` gives the relative failure
rate `32 C / (delta² T)` above unit height. -/
theorem entryRelativeFailure_probability_le
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (X : S → Mat) (delta C T : ℝ) (hdelta : 0 < delta) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hi : ∀ i j, Integrable (fun s => ‖X s i j‖ ^ 2) P)
    (hV : ∀ i j, (∫ s, ‖X s i j‖ ^ 2 ∂P) ≤ C * (1 + T)) :
    P.real {s | ¬ EntryBound (X s) (delta * T)} ≤ (32 * C / delta ^ 2) / T := by
  have hTpos : 0 < T := by linarith
  apply (entryFailure_probability_le P X (delta * T) (C * (1 + T))
    (mul_pos hdelta hTpos) hi hV).trans
  calc
    _ ≤ 16 * (C * (2 * T)) / (delta * T) ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- Averaging over the exact uniform graph fibers gives the failure rate on
any graph-height tail. Only the conditional second-moment bounds are input. -/
theorem finiteUniform_fiber_relative_entry_failure
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (K : ℕ) (hK : 0 < K)
    (hfiber : ∀ b, Fintype.card {a // f a = b} = K)
    (good : Set β) (T : β → ℝ) (X : α → Mat) (delta C U : ℝ)
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hU : 1 ≤ U)
    (hvariance : ∀ b ∈ good, U ≤ T b → ∀ i j,
      (∫ a : {a // f a = b}, ‖X a i j‖ ^ 2 ∂finiteUniform {a // f a = b}) ≤ C * (1 + T b))
    (t : ℝ) (ht : U ≤ t) :
    (finiteUniform α).real {a | f a ∈ good ∧ t < T (f a) ∧
      ¬ EntryBound (X a) (delta * T (f a))} ≤
      ((32 * C / delta ^ 2) / t) *
        (finiteUniform α).real {a | f a ∈ good ∧ t < T (f a)} := by
  letI := finiteUniform_isProbability α
  letI := finiteUniform_isProbability β
  letI (b : β) : Nonempty {a // f a = b} := Fintype.card_pos_iff.mp (by rw [hfiber]; exact hK)
  letI (b : β) := finiteUniform_isProbability {a // f a = b}
  let E : Set β := {b | b ∈ good ∧ t < T b}
  let F : Set α := {a | ¬ EntryBound (X a) (delta * T (f a))}
  have htpos : 0 < t := by linarith
  have hcond (b : β) (hb : b ∈ E) :
      (finiteUniform {a // f a = b}).real {a | (a : α) ∈ F} ≤ (32 * C / delta ^ 2) / t := by
    have hT : 1 ≤ T b := hU.trans (ht.trans hb.2.le)
    have hprob := entryRelativeFailure_probability_le (finiteUniform {a // f a = b})
      (fun a => X a) delta C (T b) hdelta hC hT
      (fun i j => integrable_finiteUniform_real _)
      (hvariance b hb.1 (ht.trans hb.2.le))
    have heq : {a : {a // f a = b} | (a : α) ∈ F} =
        {a : {a // f a = b} | ¬EntryBound (X a) (delta * T b)} := by
      ext a
      simp only [F, Set.mem_setOf_eq, a.property]
    rw [heq]
    exact hprob.trans (div_le_div_of_nonneg_left (by positivity) htpos hb.2.le)
  have hp := finiteUniform_fiber_event_bound f K hK hfiber E F _ hcond
  have hmap := finiteUniform_map_of_fiber_card f K hK (fun b => by
    rw [← Fintype.card_subtype]
    exact hfiber b)
  have hbase : (finiteUniform β).real E = (finiteUniform α).real {a | f a ∈ E} := by
    rw [← hmap, measureReal_def, Measure.map_apply (measurable_of_finite _)
      (Set.toFinite E |>.measurableSet)]
    rfl
  rw [hbase] at hp
  simpa only [E, F, Set.mem_setOf_eq, and_assoc] using hp

end GeneralizedBulk.Graph
