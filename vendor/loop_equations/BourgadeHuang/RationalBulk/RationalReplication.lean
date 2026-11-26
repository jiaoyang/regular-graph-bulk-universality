import BourgadeHuang.RationalBulk.ChargedObservables
import BourgadeHuang.RationalChargeMatching

/-! Rationally balanced replicated observables contain every ordinary
characteristic-ratio test as an exact diagonal specialization. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

def replicateCoordinates {k : ℕ} (r : ℕ) (v : Fin k → ℂ) : Fin (k*r) → ℂ :=
  fun i => v (finProdFinEquiv.symm i).1

def degenerateNumerators {k : ℕ} (p : ℕ) (hp : 0 < p) (u v : Fin k → ℂ) :
    Fin (k*p) → ℂ :=
  fun i => if (finProdFinEquiv.symm i).2 = ⟨0,hp⟩ then u (finProdFinEquiv.symm i).1
    else v (finProdFinEquiv.symm i).1

theorem sum_replicateCoordinates {k : ℕ} (r : ℕ) (v : Fin k → ℂ) :
    (∑ i, replicateCoordinates r v i) = (r:ℂ)*∑ j, v j := by
  have h := (finProdFinEquiv : Fin k × Fin r ≃ Fin (k*r)).sum_comp
    (replicateCoordinates r v)
  simpa [replicateCoordinates, Fintype.sum_prod_type, ← Finset.mul_sum] using h.symm

theorem sum_degenerateNumerators {k : ℕ} (p : ℕ) (hp : 0 < p) (u v : Fin k → ℂ) :
    (∑ i, degenerateNumerators p hp u v i) =
      (∑ j, u j) + ((p:ℂ)-1)*∑ j, v j := by
  have h := (finProdFinEquiv : Fin k × Fin p ≃ Fin (k*p)).sum_comp
    (degenerateNumerators p hp u v)
  rw [← h]
  simp only [degenerateNumerators, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have hpoint (j : Fin k) (r : Fin p) :
      (if r = ⟨0,hp⟩ then u j else v j) = v j + if r = ⟨0,hp⟩ then u j-v j else 0 := by
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Each block has `p` numerator copies and `q` denominator copies. Collapse all
but one numerator onto the denominator; neutrality cancels every excess power. -/
theorem chargedObservable_rational_diagonal {k p q : ℕ} {β : ℝ}
    (hp : 0 < p) (hrat : β*(q:ℝ) = 2*(p:ℝ))
    (u v b : Fin k → ℂ) (hu : ∀ j, SameOpenHalfPlane (u j) (b j))
    (hv : ∀ j, SameOpenHalfPlane (v j) (b j)) (s : AnchoredCountingState) :
    chargedObservable (charges β (k*p) (k*q))
      (Fin.append (replicateCoordinates p b) (replicateCoordinates q b)) s
      (Fin.append (degenerateNumerators p hp u v) (replicateCoordinates q v)) =
      anchoredCharacteristicRatios s u v := by
  have hz : ∀ j, SameOpenHalfPlane
      (Fin.append (degenerateNumerators p hp u v) (replicateCoordinates q v) j)
      (Fin.append (replicateCoordinates p b) (replicateCoordinates q b) j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left, degenerateNumerators, replicateCoordinates]
      split_ifs
      · exact hu _
      · exact hv _
    · simpa only [Fin.append_right, replicateCoordinates] using hv (finProdFinEquiv.symm i).1
  rw [chargedObservable_eq_exp _ _ _ hz]
  simp only [charges, realCharges, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat,
    neg_one_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hN : (∑ i : Fin (k*p), nevanlinnaPathPrimitive s
      (degenerateNumerators p hp u v i) (replicateCoordinates p b i)) =
      (∑ j, nevanlinnaPathPrimitive s (u j) (b j)) +
        ((p:ℂ)-1)*∑ j, nevanlinnaPathPrimitive s (v j) (b j) := by
    convert sum_degenerateNumerators p hp
      (fun j => nevanlinnaPathPrimitive s (u j) (b j))
      (fun j => nevanlinnaPathPrimitive s (v j) (b j)) using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [degenerateNumerators, replicateCoordinates]
    split_ifs <;> rfl
  have hD : (∑ i : Fin (k*q), nevanlinnaPathPrimitive s
      (replicateCoordinates q v i) (replicateCoordinates q b i)) =
        (q:ℂ)*∑ j, nevanlinnaPathPrimitive s (v j) (b j) :=
    sum_replicateCoordinates q (fun j => nevanlinnaPathPrimitive s (v j) (b j))
  rw [hN,hD]
  have hratC : (β:ℂ)*(q:ℂ)=2*(p:ℂ) := by exact_mod_cast hrat
  have he : -(∑ j, nevanlinnaPathPrimitive s (u j) (b j) +
      ((p:ℂ)-1)*∑ j, nevanlinnaPathPrimitive s (v j) (b j)) +
      (β:ℂ)/2*((q:ℂ)*∑ j, nevanlinnaPathPrimitive s (v j) (b j)) =
        ∑ j, -nevanlinnaPathPrimitive s (u j) (v j) := by
    simp_rw [nevanlinnaPathPrimitive_cocycle s (hu _) (hv _), neg_sub,
      Finset.sum_sub_distrib]
    linear_combination (∑ j, nevanlinnaPathPrimitive s (v j) (b j))/2 * hratC
  rw [he, Complex.exp_sum]
  simp only [anchoredCharacteristicRatios, anchoredCharacteristicRatio_eq_exp_primitive]

theorem expectedChargedObservable_rational_diagonal {k p q : ℕ} {β : ℝ}
    (ν : Measure AnchoredCountingState) (hp : 0 < p) (hrat : β*(q:ℝ) = 2*(p:ℝ))
    (u v b : Fin k → ℂ) (hu : ∀ j, SameOpenHalfPlane (u j) (b j))
    (hv : ∀ j, SameOpenHalfPlane (v j) (b j)) :
    expectedChargedObservable ν (charges β (k*p) (k*q))
      (Fin.append (replicateCoordinates p b) (replicateCoordinates q b))
      (Fin.append (degenerateNumerators p hp u v) (replicateCoordinates q v)) =
      expectedCharacteristicRatios ν u v := by
  unfold expectedChargedObservable expectedCharacteristicRatios
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (chargedObservable_rational_diagonal hp hrat u v b hu hv)

end BourgadeHuang.RationalBulk
