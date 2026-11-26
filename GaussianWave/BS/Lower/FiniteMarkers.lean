import GaussianWave.BS.Lower.FiniteRecoloring
import GaussianWave.BS.Lower.OrbitEntropy

/-! Literal iid uniform finite markers: normalization, entropy and the
collision bound used to make finite tree recoding actions free. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

variable {N m : ℕ}

def uniformMarkerMass (m : ℕ) (_b : Fin m) : ℝ := (m : ℝ)⁻¹

theorem uniformMarkerMass_nonneg (m : ℕ) (b : Fin m) : 0 ≤ uniformMarkerMass m b :=
  inv_nonneg.mpr (Nat.cast_nonneg m)

theorem uniformMarkerMass_sum (m : ℕ) (hm : 0 < m) : (∑ b,uniformMarkerMass m b) = 1 := by
  simp only [uniformMarkerMass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hm))

def uniformMarkerLaw (N m : ℕ) (hm : 0 < m) : Measure (Fin N → Fin m) :=
  independentColoringLaw (fun _ : Fin N => uniformMarkerMass m)
    (fun _ => uniformMarkerMass_nonneg m) (fun _ => uniformMarkerMass_sum m hm)

instance uniformMarkerLaw_isProbability (N m : ℕ) (hm : 0 < m) :
    IsProbabilityMeasure (uniformMarkerLaw N m hm) := by unfold uniformMarkerLaw; infer_instance

theorem uniformMarkerMass_entropy (m : ℕ) (hm : 0 < m) :
    entropy (uniformMarkerMass m) = Real.log m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [entropy,uniformMarkerMass,Real.negMulLog,Real.log_inv,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem uniformMarkerLaw_entropy (N m : ℕ) (hm : 0 < m) :
    entropy (lawMass (uniformMarkerLaw N m hm) id) = (N : ℝ)*Real.log m := by
  rw [uniformMarkerLaw,independentColoringLaw_entropy]
  simp only [uniformMarkerMass_entropy m hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem uniformMarkerLaw_eval_singleton (N m : ℕ) (hm : 0 < m) (v : Fin N) (b : Fin m) :
    (uniformMarkerLaw N m hm).real {c | c v = b} = (m : ℝ)⁻¹ := by
  have he : uniformMarkerLaw N m hm ((fun c : Fin N → Fin m => c v) ⁻¹' {b}) =
      ENNReal.ofReal ((m : ℝ)⁻¹) := by
    rw [← Measure.map_apply (measurable_pi_apply v) (measurableSet_singleton b),uniformMarkerLaw,
      independentColoringLaw_eval,finiteColorLaw_singleton]
    rfl
  have h := congrArg ENNReal.toReal he
  simpa only [Measure.real,Set.preimage_setOf_eq,Set.mem_singleton_iff,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m))] using h

/-- Coincidence of any two distinct actual iid markers has probability `1/m`.
Only the upper bound is needed for the collision union bound. -/
theorem uniformMarkerLaw_pair_collision (N m : ℕ) (hm : 0 < m) (i j : Fin N) (hij : i ≠ j) :
    (uniformMarkerLaw N m hm).real {c | c i = c j} ≤ (m : ℝ)⁻¹ := by
  let P := uniformMarkerLaw N m hm
  have hind : IndepFun (fun c : Fin N → Fin m => c i) (fun c => c j) P :=
    (independentColoringLaw_iIndepFun (fun _ : Fin N => uniformMarkerMass m)
      (fun _ => uniformMarkerMass_nonneg m) (fun _ => uniformMarkerMass_sum m hm)).indepFun hij
  have hp (b : Fin m) : P.real {c | c i = b ∧ c j = b} = ((m : ℝ)⁻¹)^2 := by
    have h := hind.measure_inter_preimage_eq_mul {b} {b} (measurableSet_singleton b) (measurableSet_singleton b)
    have hreal := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_mul] at hreal
    change P.real {c | c i = b ∧ c j = b} = P.real {c | c i = b}*P.real {c | c j = b} at hreal
    rw [uniformMarkerLaw_eval_singleton N m hm i b,uniformMarkerLaw_eval_singleton N m hm j b] at hreal
    simpa only [pow_two] using hreal
  have he : {c : Fin N → Fin m | c i = c j} = ⋃ b : Fin m,{c | c i = b ∧ c j = b} := by
    ext c
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · intro h; exact ⟨c i,rfl,h.symm⟩
    · rintro ⟨b,hb1,hb2⟩; exact hb1.trans hb2.symm
  change P.real {c | c i = c j} ≤ _
  rw [he]
  calc
    _ ≤ ∑ b : Fin m,P.real {c | c i = b ∧ c j = b} := measureReal_iUnion_fintype_le _
    _ = (m : ℝ)*((m : ℝ)⁻¹)^2 := by simp only [hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = _ := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      field_simp <;> ring

/-- The probability that an actual iid uniform finite marker field is not
injective is bounded by `N²/m`, uniformly in every original color law. -/
theorem uniformMarkerLaw_noninjective_probability (N m : ℕ) (hm : 0 < m) :
    (uniformMarkerLaw N m hm).real {c | ¬Function.Injective c} ≤ (N : ℝ)^2/(m : ℝ) := by
  let P := uniformMarkerLaw N m hm
  have he : {c : Fin N → Fin m | ¬Function.Injective c} =
      ⋃ ij : Fin N × Fin N,{c | ij.1 ≠ ij.2 ∧ c ij.1 = c ij.2} := by
    ext c
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · intro h
      unfold Function.Injective at h
      push_neg at h
      obtain ⟨i,j,hc,hij⟩ := h
      exact ⟨(i,j),hij,hc⟩
    · rintro ⟨⟨i,j⟩,hij,hc⟩ hi
      exact hij (hi hc)
  change P.real {c | ¬Function.Injective c} ≤ _
  rw [he]
  calc
    _ ≤ ∑ ij : Fin N × Fin N,P.real {c | ij.1 ≠ ij.2 ∧ c ij.1 = c ij.2} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ij : Fin N × Fin N,(m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro ij hij
      by_cases hne : ij.1 = ij.2
      · simp only [hne,ne_eq,not_true_eq_false,false_and,Set.setOf_false,measureReal_empty]
        positivity
      · simpa only [hne,ne_eq,not_false_eq_true,true_and] using
          uniformMarkerLaw_pair_collision N m hm ij.1 ij.2 hne
    _ = _ := by simp [Fintype.card_prod,pow_two,div_eq_mul_inv,Nat.cast_mul]

end GaussianWave.BS.Lower
