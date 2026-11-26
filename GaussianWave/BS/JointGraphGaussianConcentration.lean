import GaussianWave.BS.GraphGaussianConcentration

/-! Joint-channel local concentration from actual independent Gaussian
labels. The dependency constant depends only on the graph ball, not on the
number of channels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

/-- Measurable functions of disjoint finite Gaussian-label supports are
independent, with the local factorization constructed by extension by zero. -/
theorem gaussianLabelLaw_indep_of_disjoint_support {V : Type*}
    (S T : Finset V) (hST : Disjoint S T) (X Y : (V → ℝ) → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hXS : ∀ ξ ζ,(∀ v ∈ S,ξ v=ζ v) → X ξ=X ζ)
    (hYT : ∀ ξ ζ,(∀ v ∈ T,ξ v=ζ v) → Y ξ=Y ζ) :
    IndepFun X Y (gaussianLabelLaw V) := by
  let extS (z : S → ℝ) (v : V) : ℝ := if hv : v ∈ S then z ⟨v,hv⟩ else 0
  let extT (z : T → ℝ) (v : V) : ℝ := if hv : v ∈ T then z ⟨v,hv⟩ else 0
  have hmS : Measurable extS := by
    apply measurable_pi_lambda
    intro v
    dsimp only [extS]
    split_ifs <;> fun_prop
  have hmT : Measurable extT := by
    apply measurable_pi_lambda
    intro v
    dsimp only [extT]
    split_ifs <;> fun_prop
  have heX : X=(X ∘ extS) ∘ (fun ξ : V → ℝ => fun v : S => ξ v) := by
    funext ξ
    apply hXS
    intro v hv
    simp only [extS,dif_pos hv]
  have heY : Y=(Y ∘ extT) ∘ (fun ξ : V → ℝ => fun v : T => ξ v) := by
    funext ξ
    apply hYT
    intro v hv
    simp only [extT,dif_pos hv]
  rw [heX,heY]
  exact ((gaussianLabelLaw_iIndepFun V).indepFun_finset S T hST
    (fun v => measurable_pi_apply v)).comp (hXm.comp hmS) (hYm.comp hmT)

/-- Bounded observations using all channels in a radius-R graph ball have
variance at most B_d(2R)/N under actual channel-times-vertex Gaussian labels. -/
theorem jointGraphGaussianAverage_variance_of_local {N d : ℕ}
    (G : RegularGraph N d) (hN : 0 < N) (r R : ℕ)
    (X : Fin N → ((Fin r × Fin N) → ℝ) → ℝ) (hXm : ∀ v,Measurable (X v))
    (hX0 : ∀ v ξ,0 ≤ X v ξ) (hX1 : ∀ v ξ,X v ξ ≤ 1)
    (hlocal : ∀ v ξ ζ,(∀ a w,G.val.edist v w ≤ R → ξ (a,w)=ζ (a,w)) → X v ξ=X v ζ) :
    (∫ ξ,((N : ℝ)⁻¹*∑ v,X v ξ-
      ∫ ζ,(N : ℝ)⁻¹*∑ v,X v ζ ∂gaussianLabelLaw (Fin r × Fin N))^2
      ∂gaussianLabelLaw (Fin r × Fin N)) ≤ (regularBallBound d (2*R) : ℝ)/(N : ℝ) := by
  let S (v : Fin N) : Finset (Fin r × Fin N) := Finset.univ ×ˢ graphBallVertices G.val v R
  have hindep (v w : Fin N) (hfar : w ∉ graphBallVertices G.val v (2*R)) :
      IndepFun (X v) (X w) (gaussianLabelLaw (Fin r × Fin N)) := by
    have hdis : Disjoint (S v) (S w) := by
      apply Finset.disjoint_left.mpr
      intro aw hav haw
      exact (Finset.disjoint_left.mp (graphBall_disjoint_of_far G R v w hfar))
        (Finset.mem_product.mp hav).2 (Finset.mem_product.mp haw).2
    apply gaussianLabelLaw_indep_of_disjoint_support (S v) (S w) hdis (X v) (X w) (hXm v) (hXm w)
    · intro ξ ζ he
      apply hlocal v ξ ζ
      intro a u hu
      apply he (a,u)
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
    · intro ξ ζ he
      apply hlocal w ξ ζ
      intro a u hu
      apply he (a,u)
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
  simpa only [Fintype.card_fin] using
    integral_centered_average_sq_le_of_ae_bounded (gaussianLabelLaw (Fin r × Fin N))
      (by simpa only [Fintype.card_fin] using hN) X (fun v => (hXm v).aemeasurable)
      (fun v => Filter.Eventually.of_forall (fun ξ => ⟨hX0 v ξ,hX1 v ξ⟩))
      (fun v => graphBallVertices G.val v (2*R)) (regularBallBound d (2*R))
      (fun v => regular_graphBall_card_le G.val G.property v (2*R)) hindep

end GaussianWave.BS
