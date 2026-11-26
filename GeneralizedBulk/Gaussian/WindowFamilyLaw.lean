import GeneralizedBulk.Gaussian.WindowLaw

/-! One common Gaussian selection gives the joint law at every spectral parameter. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators Topology
namespace GeneralizedBulk.Gaussian
open Counting
variable {V I : Type*} [Countable I] {s : AnchoredCountingState}

def finiteParticleFamily {m : ℕ} (parameters : Parameters) (x : Fin m → ℝ)
    (spectral : V → ℂ × Bool) (y : (Fin m × Fin 4) → ℝ) : V → EndpointMatrix :=
  fun v => finiteParticleField parameters x (spectral v) y

theorem continuous_finiteParticleFamily {m : ℕ} (parameters : Parameters)
    (x : Fin m → ℝ) (spectral : V → ℂ × Bool) :
    Continuous (finiteParticleFamily parameters x spectral) :=
  continuous_pi (fun v => continuous_finiteParticleField parameters x (spectral v))

def windowFamily (parameters : Parameters) (p : ParticlePresentation s I)
    (a b : ℝ) (spectral : V → ℂ × Bool) (γ : I → Fin 4 → ℝ) : V → EndpointMatrix :=
  fun v => windowField parameters p a b (spectral v) γ

theorem windowFamily_law (parameters : Parameters) (p : ParticlePresentation s I)
    (a b : ℝ) (spectral : V → ℂ × Bool) :
    Measure.map (windowFamily parameters p a b spectral) (iidLaw (markLaw parameters.p) I) =
      Measure.map (finiteParticleFamily parameters
        (fun k : Fin (intervalCount s.val.1 a b) => windowOccurrence s.val.1 a b k.val) spectral)
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
  have heq : windowFamily parameters p a b spectral =
      finiteParticleFamily parameters (fun k => windowOccurrence s.val.1 a b k.val) spectral ∘ select := by
    funext γ
    funext v
    ext i j
    change (∑ k : p.WindowLabels a b, (parameters.scale : ℂ) * particleCoefficient (p.location k.val) (spectral v) *
      (rawQuadratic parameters.p i j (γ k.val) : ℂ)) = _
    have hs := Fintype.sum_equiv q
      (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location (e k)) (spectral v) *
        (rawQuadratic parameters.p i j (γ (e k)) : ℂ))
      (fun l : p.WindowLabels a b => (parameters.scale : ℂ) * particleCoefficient (p.location l.val) (spectral v) *
        (rawQuadratic parameters.p i j (γ l.val) : ℂ)) (fun k => rfl)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [hloc k]
    rfl
  have hfamily : Measurable (finiteParticleFamily parameters
      (fun k : Fin (intervalCount s.val.1 a b) => windowOccurrence s.val.1 a b k.val) spectral) :=
    measurable_pi_lambda _ (fun v => (continuous_finiteParticleField parameters _ (spectral v)).measurable)
  rw [heq,← Measure.map_map hfamily hselect,hlaw]

end GeneralizedBulk.Gaussian
