import GeneralizedBulk.Entropy.GridEntropy
import GeneralizedBulk.Entropy.GaussianEnvelope
import GeneralizedBulk.Entropy.IntegerShannon

/-! Finite first moments give genuine summability of the grid entropy. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Analysis GeneralizedBulk.Entropy.Mehler
variable {I : Type*} [Fintype I]

def gridEnergy (a : ℝ) (x : I → ℝ) : ℝ := ∑ i, |(gridLabel a x i : ℝ)|

theorem measurable_gridEnergy (a : ℝ) : Measurable (gridEnergy (I := I) a) := by
  unfold gridEnergy gridLabel
  fun_prop

theorem abs_floor_le_abs_add_one (x : ℝ) : |(Int.floor x : ℝ)| ≤ |x| + 1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem gridEnergy_le (a : ℝ) (ha : 0 < a) (x : I → ℝ) :
    gridEnergy a x ≤ coordinateL1 x / a + Fintype.card I := by
  have h (i : I) : |(gridLabel a x i : ℝ)| ≤ |x i| / a + 1 := by
    simpa only [gridLabel, abs_div, abs_of_pos ha] using abs_floor_le_abs_add_one (x i / a)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa only [gridEnergy, coordinateL1, Finset.sum_add_distrib, Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hh

theorem integrable_mul_gridEnergy (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hL1 : Integrable (fun x => f x * coordinateL1 x)) :
    Integrable (fun x => f x * gridEnergy a x) := by
  have hi := (hL1.div_const a).add (hf.mul_const (Fintype.card I : ℝ))
  apply hi.mono' (hm.mul (measurable_gridEnergy a)).aestronglyMeasurable
  filter_upwards [] with x
  have hg : 0 ≤ gridEnergy a x := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos x) hg)]
  simp only [Pi.add_apply]
  have h := mul_le_mul_of_nonneg_left (gridEnergy_le a ha x) (hpos x)
  simpa only [mul_add, mul_div_assoc] using h

theorem gridMass_energy_hasSum (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hL1 : Integrable (fun x => f x * coordinateL1 x)) :
    HasSum (fun j : I → ℤ => gridMass a f j * ∑ i, |(j i : ℝ)|) (∫ x, f x * gridEnergy a x) := by
  have h := hasSum_gridCell_integral a ha _ (integrable_mul_gridEnergy a ha f hm hpos hf hL1)
  have he (j : I → ℤ) : (∫ x in gridCell a j, f x * gridEnergy a x) = gridMass a f j * ∑ i, |(j i : ℝ)| := by
    calc
      _ = ∫ x in gridCell a j, f x * ∑ i, |(j i : ℝ)| := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_gridCell a j)] with x hx
        have hh := (mem_gridCell_iff a ha j x).mp hx
        simp only [gridEnergy, hh]
      _ = _ := integral_mul_const _ _
  simpa only [he] using h

theorem summable_grid_entropy {m : ℕ} (a : ℝ) (ha : 0 < a) (f : (Fin m → ℝ) → ℝ)
    (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hf : Integrable f) (hnorm : ∫ x, f x = 1)
    (hL1 : Integrable (fun x => f x * coordinateL1 x)) :
    Summable (fun j => Real.negMulLog (gridMass a f j)) := by
  apply summable_integer_entropy (gridMass a f) (fun j => integral_nonneg (fun x => hpos x))
    (gridMass_hasSum a ha f hf hnorm)
  exact (gridMass_energy_hasSum a ha f hm hpos hf hL1).summable

end GeneralizedBulk.Entropy
