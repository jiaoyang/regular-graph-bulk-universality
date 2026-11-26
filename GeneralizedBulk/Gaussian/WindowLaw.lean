import GeneralizedBulk.Gaussian.WindowLabels
import GeneralizedBulk.Gaussian.FiniteMarks
import GeneralizedBulk.Gaussian.MarkFamily
import GeneralizedBulk.Exterior.Rotation

/-! Exact finite-window laws of the actual iid Gaussian marked presentation. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology
namespace GeneralizedBulk.Gaussian
open Counting

def finiteParticleField {m : ℕ} (parameters : Parameters) (x : Fin m → ℝ) (v : ℂ × Bool)
    (y : (Fin m × Fin 4) → ℝ) : EndpointMatrix :=
  fun i j => ∑ k, (parameters.scale : ℂ) * particleCoefficient (x k) v *
    (rawQuadratic parameters.p i j (fun a => y (k,a)) : ℂ)

theorem continuous_finiteParticleField {m : ℕ} (parameters : Parameters) (x : Fin m → ℝ) (v : ℂ × Bool) :
    Continuous (finiteParticleField parameters x v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_finset_sum
  intro k hk
  dsimp only [finiteParticleField,rawQuadratic]
  fun_prop

theorem continuous_particleCoefficient (v : ℂ × Bool) : Continuous (fun x : ℝ => particleCoefficient x v) := by
  unfold particleCoefficient
  split_ifs
  · exact continuous_const
  · apply Continuous.pow
    apply Continuous.inv₀ (Complex.continuous_ofReal.sub continuous_const)
    intro x h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    contradiction
  · apply Continuous.inv₀ (Complex.continuous_ofReal.sub continuous_const)
    intro x h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    contradiction

/-- Finite marked coefficients vary continuously with the genuine sorted
particle locations and all Gaussian mark coordinates. -/
theorem continuous_finiteParticleField_joint {m : ℕ} (parameters : Parameters) (v : ℂ × Bool) :
    Continuous (fun z : (Fin m → ℝ) × ((Fin m × Fin 4) → ℝ) => finiteParticleField parameters z.1 v z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_finset_sum
  intro k hk
  have hc : Continuous (fun z : (Fin m → ℝ) × ((Fin m × Fin 4) → ℝ) => particleCoefficient (z.1 k) v) :=
    (continuous_particleCoefficient v).comp ((continuous_apply k).comp continuous_fst)
  have hq : Continuous (fun z : (Fin m → ℝ) × ((Fin m × Fin 4) → ℝ) =>
      (rawQuadratic parameters.p i j (fun a => z.2 (k,a)) : ℂ)) := by
    unfold rawQuadratic
    fun_prop
  exact (continuous_const.mul hc).mul hq

variable {I : Type*} [Countable I] {s : AnchoredCountingState}

def windowField (parameters : Parameters) (p : ParticlePresentation s I) (a b : ℝ)
    (v : ℂ × Bool) (γ : I → Fin 4 → ℝ) : EndpointMatrix := by
  letI : Finite (p.WindowLabels a b) := p.finite_windowLabels a b
  letI := Fintype.ofFinite (p.WindowLabels a b)
  exact fun i j => ∑ k : p.WindowLabels a b,
    (parameters.scale : ℂ) * particleCoefficient (p.location k.val) v *
      (rawQuadratic parameters.p i j (γ k.val) : ℂ)

/-- The actual window projection law is the canonical finite Gaussian mark
law evaluated at the sorted window locations, independently of labels. -/
theorem windowField_law (parameters : Parameters) (p : ParticlePresentation s I)
    (a b : ℝ) (v : ℂ × Bool) :
    Measure.map (windowField parameters p a b v) (iidLaw (markLaw parameters.p) I) =
      Measure.map (finiteParticleField parameters
        (fun k : Fin (intervalCount s.val.1 a b) => windowOccurrence s.val.1 a b k.val) v)
          (finiteMarkLaw parameters.p (intervalCount s.val.1 a b)) := by
  classical
  obtain ⟨e,he,hloc,hrange⟩ := p.exists_window_selection a b
  letI : Finite (p.WindowLabels a b) := p.finite_windowLabels a b
  letI := Fintype.ofFinite (p.WindowLabels a b)
  have hmem (k : Fin (intervalCount s.val.1 a b)) : p.location (e k) ∈ Set.Icc a b := by
    have h : e k ∈ Set.range e := Set.mem_range_self k
    rw [hrange] at h
    exact h
  let liftE : Fin (intervalCount s.val.1 a b) → p.WindowLabels a b := fun k => ⟨e k,hmem k⟩
  have hbij : Function.Bijective liftE := by
    constructor
    · intro k l hkl
      exact he (congrArg Subtype.val hkl)
    · intro i
      have hi : i.val ∈ Set.range e := by rw [hrange]; exact i.property
      obtain ⟨k,hk⟩ := hi
      exact ⟨k,Subtype.ext hk⟩
  let q : Fin (intervalCount s.val.1 a b) ≃ p.WindowLabels a b := Equiv.ofBijective liftE hbij
  let select := fun γ : I → Fin 4 → ℝ => flattenMarks (fun k => γ (e k))
  have hselect : Measurable select := measurable_flattenMarks.comp
    (measurable_pi_lambda _ (fun k => measurable_pi_apply (e k)))
  have hlaw : Measure.map select (iidLaw (markLaw parameters.p) I) =
      finiteMarkLaw parameters.p (intervalCount s.val.1 a b) := by
    rw [finiteMarkLaw,← iidLaw_map_injectiveSelection (markLaw parameters.p) I e he,
      Measure.map_map measurable_flattenMarks (measurable_pi_lambda _ (fun k => measurable_pi_apply (e k)))]
    rfl
  have heq : windowField parameters p a b v =
      finiteParticleField parameters (fun k => windowOccurrence s.val.1 a b k.val) v ∘ select := by
    funext γ
    ext i j
    change (∑ k : p.WindowLabels a b, (parameters.scale : ℂ) * particleCoefficient (p.location k.val) v *
      (rawQuadratic parameters.p i j (γ k.val) : ℂ)) = _
    have hs := Fintype.sum_equiv q
      (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location (e k)) v *
        (rawQuadratic parameters.p i j (γ (e k)) : ℂ))
      (fun l : p.WindowLabels a b => (parameters.scale : ℂ) * particleCoefficient (p.location l.val) v *
        (rawQuadratic parameters.p i j (γ l.val) : ℂ)) (fun k => rfl)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [hloc k]
    rfl
  rw [heq,← Measure.map_map (continuous_finiteParticleField parameters _ v).measurable hselect,hlaw]

end GeneralizedBulk.Gaussian
