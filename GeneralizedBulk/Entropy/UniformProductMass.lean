import GeneralizedBulk.Entropy.ConditionalFiniteWeights
import GeneralizedBulk.Entropy.FiniteSampleMap

/-! The actual bad-root mass in a uniform finite product is its exact root
fraction, independently of the number of port or permutation labels. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Entropy

theorem uniformProduct_root_subset_mass {N : ℕ} (hN : 0 < N) (C : Type*) [Fintype C] [Nonempty C]
    (bad : Finset (Fin N)) :
    subsetWeightMass (uniformSampleWeight (Fin N × C)) (fun s => s.1 ∈ bad)=(bad.card : ℝ)/N := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hCr : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (∑ r : Fin N,if r ∈ bad then (1:ℝ) else 0)=bad.card := by simp
  simp only [subsetWeightMass,uniformSampleWeight,Fintype.sum_prod_type,Finset.sum_ite_irrel,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_const_zero,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  calc
    _ = (Fintype.card C : ℝ)*((N : ℝ)*Fintype.card C)⁻¹*(∑ r : Fin N,if r ∈ bad then (1:ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> simp
    _ = _ := by rw [hs]; field_simp; ring

theorem uniformProduct_bad_mass_le_sqrt_reciprocal {N : ℕ} (hN : 0 < N)
    (C : Type*) [Fintype C] [Nonempty C] (bad : Finset (Fin N))
    (hbad : (bad.card : ℝ) ≤ (N : ℝ)^(1/2 : ℝ)) :
    subsetWeightMass (uniformSampleWeight (Fin N × C)) (fun s => s.1 ∈ bad) ≤ (N : ℝ)^(-(1/2 : ℝ)) := by
  rw [uniformProduct_root_subset_mass hN C bad]
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  calc
    _ ≤ (N : ℝ)^(1/2 : ℝ)/(N : ℝ) := div_le_div_of_nonneg_right hbad hNr.le
    _ = (N : ℝ)^((1/2 : ℝ)-1) := by rw [Real.rpow_sub hNr,Real.rpow_one]
    _ = _ := by norm_num

end GeneralizedBulk.Entropy
