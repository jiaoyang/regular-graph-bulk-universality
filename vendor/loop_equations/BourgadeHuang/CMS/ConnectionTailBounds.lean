import BourgadeHuang.CMS.FullSubsetRadial

/-! Uniform tail bounds for the actual connection acting on scaled radial
vectors, with the empty and nonempty components treated at their true orders. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
namespace SectorialData
variable {d : ℕ} (D : SectorialData d)

/-- The degree-conjugated action of one actual connection row. -/
theorem scaled_single_connection_action (i : Fin d) (z : Point d)
    (S : Finset (Fin d)) (X : Finset (Fin d) → ℂ) {t : ℂ} (ht : t≠0) :
    t^S.card*(∑T : Finset (Fin d),D.connection i z S T*X T)=
      (if i∈S then -(D.phase i) else 0)*(t^S.card*X S)+
      (∑T : Finset (Fin d),D.lowCoordinate (fun _=>1) z t S T i*(t^T.card*X T))+
      t⁻¹*(∑T : Finset (Fin d),D.highCoordinate (fun _=>1) z t S T i*(t^T.card*X T)) := by
  classical
  rw [Finset.mul_sum]
  have he (T : Finset (Fin d)) := congrArg (fun a : ℂ=>a*X T)
    (D.scaled_connection_entry (fun _=>1) z S T i ht)
  simp only [mul_one,one_mul,add_mul,mul_assoc] at he
  simp_rw [he]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  congr 2
  by_cases hi : i∈S
  · simp [hi,mul_ite,ite_mul,←Finset.mul_sum]
  · simp [hi]

/-- A common bound on the scaled connection uses only bounded full values
and O(t⁻¹) nonempty values. The correction empty column really vanishes. -/
theorem norm_scaled_connection_le (i : Fin d) (S : Finset (Fin d))
    (z : Point d) (Y : Finset (Fin d) → ℂ) {t B0 B1 : ℝ}
    (ht : 0<t) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖)
    (hY0 : ∀T,‖Y T‖≤B0)
    (hY1 : ∀T : NonemptySubset d,‖Y T.val‖≤B1/t) :
    ‖(t:ℂ)^S.card*(∑T : Finset (Fin d),D.connection i z S T*
      (((t:ℂ)^T.card)⁻¹*Y T))‖≤
      (‖D.phase i‖*B1+
        (Fintype.card (NonemptySubset d):ℝ)*SquareFreeTerm.rowBound (D.correctionRow S i)*B1+
        (Fintype.card (Finset (Fin d)):ℝ)*(1+SquareFreeTerm.rowBound (D.correctionRow S i))*B0)/t := by
  classical
  have htc : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [D.scaled_single_connection_action i z S _ htc]
  simp only [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ htc),one_mul]
  let M := SquareFreeTerm.rowBound (D.correctionRow S i)
  have hM : 0≤M := SquareFreeTerm.rowBound_nonneg _
  have hd : ‖(if i∈S then -(D.phase i) else 0)*Y S‖≤‖D.phase i‖*B1/t := by
    by_cases hi : i∈S
    · rw [if_pos hi,norm_mul,norm_neg]
      exact (mul_le_mul_of_nonneg_left (hY1 ⟨S,⟨i,hi⟩⟩) (norm_nonneg _)).trans_eq (by ring)
    · simp only [if_neg hi,zero_mul,norm_zero]
      positivity
  have hl0 : D.lowCoordinate (fun _=>1) z t S ∅ i=0 := by
    unfold lowCoordinate
    split
    · rw [SquareFreeTerm.homogeneousEntry_low_empty _ (D.correctionRow_spec S i),mul_zero]
    · rfl
  have hl : ‖∑T : Finset (Fin d),D.lowCoordinate (fun _=>1) z t S T i*Y T‖≤
      (Fintype.card (NonemptySubset d):ℝ)*M*B1/t := by
    rw [sum_subsets,hl0,zero_mul,zero_add]
    apply (norm_sum_le _ _).trans
    calc
      (∑T : NonemptySubset d,‖D.lowCoordinate (fun _=>1) z t S T.val i*Y T.val‖)≤
          ∑_T : NonemptySubset d,M*(B1/t) := by
        apply Finset.sum_le_sum
        intro T hT
        rw [norm_mul]
        have hb := D.norm_lowCoordinate_le (fun _=>1) S T.val i ht hsep
        simp only [norm_one,one_mul] at hb
        exact mul_le_mul hb (hY1 T) (norm_nonneg _) hM
      _=_ := by simp; ring
  have hh : ‖∑T : Finset (Fin d),D.highCoordinate (fun _=>1) z t S T i*Y T‖≤
      (Fintype.card (Finset (Fin d)):ℝ)*(1+M)*B0 := by
    apply (norm_sum_le _ _).trans
    calc
      (∑T : Finset (Fin d),‖D.highCoordinate (fun _=>1) z t S T i*Y T‖)≤
          ∑_T : Finset (Fin d),(1+M)*B0 := by
        apply Finset.sum_le_sum
        intro T hT
        rw [norm_mul]
        have hb := D.norm_highCoordinate_le (fun _=>1) S T i ht hsep
        simp only [norm_one,one_mul] at hb
        exact mul_le_mul hb (hY0 T) (norm_nonneg _) (by positivity)
      _=_ := by simp; ring
  apply (norm_add_le _ _).trans
  apply le_trans (add_le_add ((norm_add_le _ _).trans (add_le_add hd hl)) ?_)
  · change ‖D.phase i‖*B1/t+(Fintype.card (NonemptySubset d):ℝ)*M*B1/t+
      ((Fintype.card (Finset (Fin d)):ℝ)*(1+M)*B0)/t≤_
    dsimp only [M]
    ring_nf
    exact le_rfl
  · rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq (by ring)

end SectorialData
end BourgadeHuang.CMS
