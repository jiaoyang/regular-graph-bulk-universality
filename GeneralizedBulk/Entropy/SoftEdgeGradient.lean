import GeneralizedBulk.Entropy.SoftEdgeSensitivity
import GeneralizedBulk.Entropy.CoordinateSensitivity

/-! Actual C¹ soft word averages have the exact coordinate-gradient bound
needed for correlated Gaussian Poincaré. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {k N d : ℕ}

theorem softEdgeAverage_fderiv_bound (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d)
    (φ : Fin k × Fin 2 → ℝ → ℝ) (hφ0 : ∀ i z,0 ≤ φ i z) (hφ1 : ∀ i z,φ i z ≤ 1)
    (hφ : ∀ i,ContDiff ℝ 1 (φ i))
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ i x y,|φ i x-φ i y| ≤ L*|x-y|)
    (a x : Fin k × Fin N → ℝ) (i : Fin k × Fin N) :
    |fderiv ℝ (softEdgeAverage nb φ a) x (Pi.single i 1)| ≤ 2*L/(N : ℝ) := by
  apply coordinate_fderiv_le_of_l1_sensitivity _ x
    ((contDiff_one_softEdgeAverage nb φ hφ a).differentiable le_rfl x) _ (by positivity)
  intro y z
  exact softEdgeAverage_l1_sensitivity nb hnb hN hd φ hφ0 hφ1 L hL hlip a y z

theorem softEdgeAverage_nonneg (nb : Fin N → Fin d → Fin N)
    (φ : Fin k × Fin 2 → ℝ → ℝ) (hφ0 : ∀ i z,0 ≤ φ i z)
    (a x : Fin k × Fin N → ℝ) : 0 ≤ softEdgeAverage nb φ a x := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun u hu => Finset.sum_nonneg (fun j hj =>
    Finset.prod_nonneg (fun i hi => hφ0 i _)))

theorem softEdgeAverage_le_one (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (φ : Fin k × Fin 2 → ℝ → ℝ) (hφ0 : ∀ i z,0 ≤ φ i z) (hφ1 : ∀ i z,φ i z ≤ 1)
    (a x : Fin k × Fin N → ℝ) : softEdgeAverage nb φ a x ≤ 1 := by
  have hp (u v : Fin N) : edgeLabelProduct φ (a+x) u v ≤ 1 :=
    Finset.prod_le_one (fun i hi => hφ0 i _) (fun i hi => hφ1 i _)
  have hs : (∑ u,∑ j,edgeLabelProduct φ (a+x) u (nb u j)) ≤ (N*d : ℕ) := by
    calc
      _ ≤ ∑ _u : Fin N,∑ _j : Fin d,(1 : ℝ) :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun j hj => hp u (nb u j)))
      _ = _ := by simp
  have hnd : (0 : ℝ) < (N*d : ℕ) := by positivity
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hnd.le)
  rwa [inv_mul_cancel₀ (ne_of_gt hnd)] at h

variable {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]

def quantizedSoftEdgeAverage (nb : Fin N → Fin d → Fin N) (J : ℝ → B) (ℓ : ℝ)
    (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) : (Fin k × Fin N → ℝ) → ℝ :=
  softEdgeAverage nb (fun i => softLabel J ℓ (word i)) a

theorem contDiff_one_quantizedSoftEdgeAverage (nb : Fin N → Fin d → Fin N)
    (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    ContDiff ℝ 1 (quantizedSoftEdgeAverage nb J ℓ a word) :=
  contDiff_one_softEdgeAverage nb _ (fun i => contDiff_one_softLabel J hJ ℓ hℓ (word i)) a

theorem quantizedSoftEdgeAverage_abs_le_one (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a x : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    |quantizedSoftEdgeAverage nb J ℓ a word x| ≤ 1 := by
  unfold quantizedSoftEdgeAverage
  rw [abs_of_nonneg (softEdgeAverage_nonneg nb _ (fun i => softLabel_nonneg J ℓ hℓ (word i)) a x)]
  exact softEdgeAverage_le_one nb hN hd _ (fun i => softLabel_nonneg J ℓ hℓ (word i))
    (fun i => softLabel_le_one J hJ ℓ hℓ (word i)) a x

set_option maxHeartbeats 1000000 in
theorem quantizedSoftEdgeAverage_coordinate_bound (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a x : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) (i : Fin k × Fin N) :
    |fderiv ℝ (quantizedSoftEdgeAverage nb J ℓ a word) x (Pi.single i 1)| ≤ ((N : ℝ)*ℓ)⁻¹ := by
  have h := softEdgeAverage_fderiv_bound nb hnb hN hd (fun i => softLabel J ℓ (word i))
    (fun i => softLabel_nonneg J ℓ hℓ (word i)) (fun i => softLabel_le_one J hJ ℓ hℓ (word i))
    (fun i => contDiff_one_softLabel J hJ ℓ hℓ (word i)) ((2*ℓ)⁻¹) (by positivity)
    (fun i => softLabel_abs_sub_le J hJ ℓ hℓ (word i)) a x i
  have he : 2*(2*ℓ)⁻¹/(N : ℝ) = ((N : ℝ)*ℓ)⁻¹ := by field_simp; ring
  rwa [he] at h

theorem quantizedSoftEdgeAverage_gradient_energy (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a x : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    (∑ i : Fin k × Fin N,(fderiv ℝ (quantizedSoftEdgeAverage nb J ℓ a word) x (Pi.single i 1))^2) ≤
      (k : ℝ)/((N : ℝ)*ℓ^2) := by
  calc
    _ ≤ ∑ _i : Fin k × Fin N,(((N : ℝ)*ℓ)⁻¹)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
        (quantizedSoftEdgeAverage_coordinate_bound nb hnb hN hd J hJ ℓ hℓ a x word i)
      simpa only [sq_abs] using h
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      field_simp
      ring

end GeneralizedBulk.Entropy
