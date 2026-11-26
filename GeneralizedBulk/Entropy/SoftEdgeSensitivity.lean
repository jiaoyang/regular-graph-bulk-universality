import GeneralizedBulk.Entropy.UnitProducts
import GeneralizedBulk.Entropy.SoftQuantizer
import GeneralizedBulk.Graph.StarCovariance

/-! Genuine coordinate sensitivity of soft oriented-edge word averages. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {k N d : ℕ}

def edgeLabelProduct (φ : Fin k × Fin 2 → ℝ → ℝ) (z : Fin k × Fin N → ℝ)
    (u v : Fin N) : ℝ :=
  ∏ i : Fin k × Fin 2, φ i (z (i.1,if i.2 = 0 then u else v))

def softEdgeAverage (nb : Fin N → Fin d → Fin N) (φ : Fin k × Fin 2 → ℝ → ℝ)
    (a x : Fin k × Fin N → ℝ) : ℝ :=
  ((N*d : ℕ) : ℝ)⁻¹ * ∑ u,∑ j,edgeLabelProduct φ (a+x) u (nb u j)

theorem edgeLabelProduct_abs_sub_le (φ : Fin k × Fin 2 → ℝ → ℝ)
    (hφ0 : ∀ i z,0 ≤ φ i z) (hφ1 : ∀ i z,φ i z ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ i x y,|φ i x-φ i y| ≤ L*|x-y|)
    (a x y : Fin k × Fin N → ℝ) (u v : Fin N) :
    |edgeLabelProduct φ (a+x) u v-edgeLabelProduct φ (a+y) u v| ≤
      L*∑ r : Fin k,(|x (r,u)-y (r,u)|+|x (r,v)-y (r,v)|) := by
  apply (abs_prod_sub_prod_le_sum _ _ (fun i => hφ0 i _) (fun i => hφ1 i _)
    (fun i => hφ0 i _) (fun i => hφ1 i _)).trans
  calc
    _ ≤ ∑ i : Fin k × Fin 2,L*|x (i.1,if i.2 = 0 then u else v)-y (i.1,if i.2 = 0 then u else v)| := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hlip i ((a+x) (i.1,if i.2 = 0 then u else v)) ((a+y) (i.1,if i.2 = 0 then u else v))
      simpa only [Pi.add_apply,add_sub_add_left_eq_sub] using h
    _ = _ := by
      rw [← Finset.mul_sum,Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two,Fin.zero_eta,Fin.isValue,ite_true,Fin.mk_one,Fin.reduceEq,ite_false]

set_option maxHeartbeats 1000000 in
theorem sum_edge_endpoint_terms (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (A : Fin k → Fin N → ℝ) :
    (∑ u,∑ j,∑ r : Fin k,(A r u+A r (nb u j))) = 2*d*(∑ r : Fin k,∑ v,A r v) := by
  calc
    _ = ∑ u,∑ r : Fin k,∑ j,(A r u+A r (nb u j)) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_comm
    _ = ∑ r : Fin k,∑ u,∑ j,(A r u+A r (nb u j)) := Finset.sum_comm
    _ = ∑ r : Fin k,((d : ℝ)*∑ u,A r u+(d : ℝ)*∑ v,A r v) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.sum_add_distrib]
      rw [hnb]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]; ring

set_option maxHeartbeats 1000000 in
theorem softEdgeAverage_l1_sensitivity (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d)
    (φ : Fin k × Fin 2 → ℝ → ℝ) (hφ0 : ∀ i z,0 ≤ φ i z) (hφ1 : ∀ i z,φ i z ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ i x y,|φ i x-φ i y| ≤ L*|x-y|)
    (a x y : Fin k × Fin N → ℝ) :
    |softEdgeAverage nb φ a x-softEdgeAverage nb φ a y| ≤
      (2*L/(N : ℝ))*∑ i : Fin k × Fin N,|x i-y i| := by
  dsimp only [softEdgeAverage]
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((N*d : ℕ) : ℝ)⁻¹),
    ← Finset.sum_sub_distrib]
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hd' : (d : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ((N*d : ℕ) : ℝ)⁻¹*∑ u,|∑ j,edgeLabelProduct φ (a+x) u (nb u j)-∑ j,edgeLabelProduct φ (a+y) u (nb u j)| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((N*d : ℕ) : ℝ)⁻¹*∑ u,∑ j,|edgeLabelProduct φ (a+x) u (nb u j)-edgeLabelProduct φ (a+y) u (nb u j)| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u hu
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((N*d : ℕ) : ℝ)⁻¹*∑ u,∑ j,L*∑ r : Fin k,(|x (r,u)-y (r,u)|+|x (r,nb u j)-y (r,nb u j)|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.sum_le_sum (fun j hj => edgeLabelProduct_abs_sub_le φ hφ0 hφ1 L hL hlip a x y u (nb u j))
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [sum_edge_endpoint_terms nb hnb (fun r v => |x (r,v)-y (r,v)|),Fintype.sum_prod_type]
      push_cast
      field_simp
      ring

theorem contDiff_one_softEdgeAverage (nb : Fin N → Fin d → Fin N)
    (φ : Fin k × Fin 2 → ℝ → ℝ) (hφ : ∀ i,ContDiff ℝ 1 (φ i))
    (a : Fin k × Fin N → ℝ) : ContDiff ℝ 1 (softEdgeAverage nb φ a) := by
  unfold softEdgeAverage
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro u hu
  apply ContDiff.sum
  intro j hj
  unfold edgeLabelProduct
  apply contDiff_prod
  intro i hi
  apply (hφ i).comp
  fun_prop

end GeneralizedBulk.Entropy
