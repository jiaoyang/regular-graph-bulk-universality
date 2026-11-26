import GaussianWave.BS.Reused.Entropy.GridMoments
import GaussianWave.BS.Reused.Entropy.IntegerClippingEntropy

/-! Genuine second moments of the grid energy, polynomial in the vector
dimension and requiring only coordinate second moments. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GaussianWave.BS.Reused.Entropy

theorem gridEnergy_sq_le {m : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin m → ℝ) :
    gridEnergy a x^2 ≤ (2*(m : ℝ)/a^2)*(∑ i,x i^2)+2*(m : ℝ)^2 := by
  have h (i : Fin m) : |(gridLabel a x i : ℝ)|^2 ≤ 2*x i^2/a^2+2 := by
    have hf := abs_floor_le_abs_add_one (x i/a)
    have hnon : 0 ≤ |(gridLabel a x i : ℝ)| := abs_nonneg _
    have he : |(gridLabel a x i : ℝ)| ≤ |x i/a|+1 := hf
    have hb : |(gridLabel a x i : ℝ)|^2 ≤ 2*(x i/a)^2+2 := by
      nlinarith [sq_nonneg (|x i/a|-1),sq_abs (x i/a)]
    simpa only [div_pow,mul_div_assoc] using hb
  calc
    _ ≤ (m : ℝ)*∑ i,|(gridLabel a x i : ℝ)|^2 := by
      simpa only [gridEnergy,Finset.card_univ,Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |(gridLabel a x i : ℝ)|))
    _ ≤ (m : ℝ)*∑ i,(2*x i^2/a^2+2) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => h i)) (by positivity)
    _ = _ := by
      have hs : (∑ i,2*x i^2/a^2) = (2/a^2)*∑ i,x i^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [Finset.sum_add_distrib,hs]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem memLp_gridEnergy {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin m → ℝ) (hX : Measurable X) (hcoord : ∀ i,MemLp (fun x => X x i) 2 μ)
    (a : ℝ) (ha : 0 < a) : MemLp (fun x => gridEnergy a (X x)) 2 μ := by
  have hs : MemLp (fun x => ∑ i,|X x i|) 2 μ := by
    simpa only [Real.norm_eq_abs] using
      (memLp_finset_sum Finset.univ (fun i hi => (hcoord i).norm))
  have hd : MemLp (fun x => (∑ i,|X x i|)/a) 2 μ := by
    simpa only [div_eq_mul_inv,mul_comm] using hs.const_mul a⁻¹
  have hb : MemLp (fun x => (∑ i,|X x i|)/a+(m : ℝ)) 2 μ :=
    hd.add (memLp_const _)
  apply hb.mono' ((measurable_gridEnergy a).comp hX).aestronglyMeasurable
  filter_upwards [] with x
  change |gridEnergy a (X x)| ≤ _
  rw [abs_of_nonneg (show 0 ≤ gridEnergy a (X x) from Finset.sum_nonneg (fun i hi => abs_nonneg _))]
  simpa only [Mehler.coordinateL1,Fintype.card_fin] using gridEnergy_le a ha (X x)

set_option maxHeartbeats 1000000 in
theorem integral_gridEnergy_sq_le {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin m → ℝ) (hX : Measurable X) (hcoord : ∀ i,MemLp (fun x => X x i) 2 μ)
    (B : ℝ) (hB : ∀ i,(∫ x,X x i^2 ∂μ) ≤ B) (a : ℝ) (ha : 0 < a) :
    (∫ x,gridEnergy a (X x)^2 ∂μ) ≤ (m : ℝ)^2*(2*B/a^2+2) := by
  have hi (i : Fin m) : Integrable (fun x => X x i^2) μ :=
    (memLp_two_iff_integrable_sq (hcoord i).aestronglyMeasurable).mp (hcoord i)
  have hs := integrable_finset_sum (f := fun i x => X x i^2) Finset.univ (fun i _ => hi i)
  have hb := (hs.const_mul (2*(m : ℝ)/a^2)).add (integrable_const (2*(m : ℝ)^2))
  have hgrid := (memLp_two_iff_integrable_sq (memLp_gridEnergy μ X hX hcoord a ha).aestronglyMeasurable).mp
    (memLp_gridEnergy μ X hX hcoord a ha)
  calc
    _ ≤ ∫ x,(2*(m : ℝ)/a^2)*(∑ i,X x i^2)+2*(m : ℝ)^2 ∂μ :=
      integral_mono hgrid hb (fun x => gridEnergy_sq_le a ha (X x))
    _ = (2*(m : ℝ)/a^2)*(∑ i,∫ x,X x i^2 ∂μ)+2*(m : ℝ)^2 := by
      rw [integral_add (hs.const_mul _) (integrable_const _),integral_const_mul,
        integral_finset_sum Finset.univ (fun i hi' => hi i),integral_const]
      simp only [measureReal_univ_eq_one,smul_eq_mul,one_mul]
    _ ≤ (2*(m : ℝ)/a^2)*((m : ℝ)*B)+2*(m : ℝ)^2 := by
      gcongr
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        (Finset.sum_le_sum (fun i (hi : i ∈ Finset.univ) => hB i))
    _ = _ := by ring

end GaussianWave.BS.Reused.Entropy
