import BourgadeHuang.RationalBulk.FiniteSingularFTC
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Fubini integration by parts along a particle coordinate. A finite set of
collision hyperplanes is allowed, and integrability replaces boundary limits. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem integral_coordinate_derivative_eq_zero {N : ℕ} (i : Fin (N+1))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : (Fin (N+1) → ℝ) → E) (hc : Continuous f)
    (hd : ∀ x, (∀ j, j ≠ i → x i ≠ x j) →
      HasDerivAt (fun t => f (Function.update x i t)) (g x) (x i))
    (hf : Integrable f) (hg : Integrable g) : (∫ x, g x) = 0 := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) i
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => ℝ) i).symm
  have hfi : Integrable (fun p : ℝ × (Fin N → ℝ) => f (e.symm p)) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  have hgi : Integrable (fun p : ℝ × (Fin N → ℝ) => g (e.symm p)) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hg
  rw [← he.integral_comp' g]
  change (∫ x : ℝ × (Fin N → ℝ), g (e.symm x) ∂volume.prod volume) = 0
  rw [integral_prod_symm _ hgi]
  apply integral_eq_zero_of_ae
  filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with y hfy hgy
  have heq (t : ℝ) : e.symm (t,y) = i.insertNth t y := rfl
  simp only [heq] at hfy hgy ⊢
  apply integral_eq_zero_of_hasDerivAt_off_finset_of_integrable
    (Finset.univ.image y) _ _ hgy hfy
  · apply hc.comp
    apply continuous_pi
    intro j
    refine i.succAboveCases ?_ (fun k => ?_) j
    · simpa using (continuous_id : Continuous (fun t : ℝ => t))
    · simpa using (continuous_const : Continuous (fun _ : ℝ => y k))
  · intro t ht
    have ht' (k : Fin N) : t ≠ y k := by
      intro h
      apply ht
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,h.symm⟩
    have hsep : ∀ j : Fin (N+1), j ≠ i →
        (i.insertNth t y : Fin (N+1) → ℝ) i ≠ (i.insertNth t y : Fin (N+1) → ℝ) j := by
      intro j hji
      obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
      simpa using ht' k
    simpa only [Fin.update_insertNth, Fin.insertNth_apply_same] using hd (i.insertNth t y) hsep

end BourgadeHuang.RationalBulk
