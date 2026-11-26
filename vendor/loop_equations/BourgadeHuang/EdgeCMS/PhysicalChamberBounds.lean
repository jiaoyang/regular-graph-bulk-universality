import BourgadeHuang.EdgeCMS.PhysicalChamber

/-! Uniform local geometry of the concrete physical cone. Every base point
has a neighborhood with common positive height and finite size bounds; every
nonempty square-free jet block has a positive radial spectral gap. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS

theorem physicalChamber_uniform_gap {d : ℕ} (hd : 0<d)
    {c : Fin d→ℂ} {upper : Fin d→Bool} {y : Point d}
    (hy : y∈physicalChamberSet c upper) :
    ∃γ : ℝ, 0<γ ∧ ∀S : Finset (Fin d), S.Nonempty →
      γ≤(∑i∈S,-2*c i*y i).re := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let g := fun i=> (-2*c i*y i).re
  let γ := Finset.univ.inf' Finset.univ_nonempty g
  have hγ : 0<γ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => physicalChamber_gap hy i)
  refine ⟨γ,hγ,fun S hS=>?_⟩
  obtain ⟨i,hi⟩ := hS
  have hgi : γ≤g i := Finset.inf'_le _ (Finset.mem_univ i)
  have hsum : g i≤∑j∈S,g j := Finset.single_le_sum
    (fun j _ => (physicalChamber_gap hy j).le) hi
  simpa only [Complex.re_sum,g] using hgi.trans hsum

/-- A true neighborhood, not just a single ray, has uniform deterministic
constants for the edge-loop concentration estimate. -/
theorem physicalChamber_neighborhood_bounds {d : ℕ} (hd : 0<d)
    {c : Fin d→ℂ} {upper : Fin d→Bool} {y : Point d}
    (hy : y∈physicalChamberSet c upper) :
    ∃(U : Set (Point d)) (η M : ℝ), U∈𝓝 y ∧ 0<η ∧ 0<M ∧
      U⊆physicalChamberSet c upper ∧
      ∀v∈U,∀i, η≤(reflectComplex (upper i) (airyInverse (v i))).im ∧
        ‖airyInverse (v i)‖≤M := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let H := fun i=>(reflectComplex (upper i) (airyInverse (y i))).im
  have hH (i) : 0<H i := (hy.1 i).1.2.1.trans (hy.1 i).1.2.2
  let h := Finset.univ.inf' Finset.univ_nonempty H
  have hh : 0<h := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hH i)
  let η := h/2
  have hη : 0<η := half_pos hh
  have hηi i : η<H i := lt_of_lt_of_le (half_lt_self hh)
    (Finset.inf'_le H (Finset.mem_univ i))
  let M := 1+∑i,‖airyInverse (y i)‖
  have hM : 0<M := by dsimp [M]; positivity
  have hMi i : ‖airyInverse (y i)‖<M := by
    have hs := Finset.single_le_sum (fun j (_ : j∈(Finset.univ:Finset (Fin d))) =>
      norm_nonneg (airyInverse (y j))) (Finset.mem_univ i)
    dsimp [M]
    linarith
  have hev (i : Fin d) : ∀ᶠ v in 𝓝 y,
      η<(reflectComplex (upper i) (airyInverse (v i))).im ∧ ‖airyInverse (v i)‖<M := by
    have hc : ContinuousAt (fun v : Point d=>airyInverse (v i)) y :=
      (analyticAt_airyInverse (hy.1 i).1.1).continuousAt.comp
        (f := fun v : Point d => v i) (continuous_apply i).continuousAt
    have hcH := (Complex.continuous_im.comp (continuous_reflectComplex (upper i))).continuousAt.comp hc
    exact (hcH.eventually (lt_mem_nhds (hηi i))).and
      (hc.norm.eventually (gt_mem_nhds (hMi i)))
  have hall : ∀ᶠ v in 𝓝 y,∀i,η<(reflectComplex (upper i) (airyInverse (v i))).im ∧
      ‖airyInverse (v i)‖<M := eventually_all.mpr hev
  let U := {v | v∈physicalChamberSet c upper ∧
    ∀i,η≤(reflectComplex (upper i) (airyInverse (v i))).im ∧ ‖airyInverse (v i)‖≤M}
  refine ⟨U,η,M,?_,hη,hM,fun v hv=>hv.1,fun v hv=>hv.2⟩
  filter_upwards [(isOpen_physicalChamberSet c upper).mem_nhds hy,hall] with v hv hbounds
  exact ⟨hv,fun i=>⟨(hbounds i).1.le,(hbounds i).2.le⟩⟩

end BourgadeHuang.EdgeCMS
