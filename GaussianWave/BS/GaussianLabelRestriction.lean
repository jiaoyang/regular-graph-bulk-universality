import GaussianWave.BS.GraphGaussianBlockFactor

/-! Injective finite restrictions of actual iid Gaussian labels. In particular,
locally injective cover windows give the exact tree blockfactor law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

/-- Any injectively sampled finite set of Gaussian labels has the literal
standard finite product law. The ambient label set may be infinite. -/
theorem gaussianLabelLaw_map_injective {V J : Type*} [Fintype J]
    (site : J → V) (hsite : Function.Injective site) :
    Measure.map (fun ξ : V → ℝ => fun j => ξ (site j)) (gaussianLabelLaw V) =
      Measure.pi (fun _ : J => gaussianReal 0 1) := by
  let S : Finset V := Finset.univ.image site
  let f : J → S := fun j => ⟨site j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hfi : Function.Injective f := fun a b hab => hsite (congrArg Subtype.val hab)
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp v.property
    exact ⟨j,Subtype.ext he⟩
  let e : J ≃ S := Equiv.ofBijective f ⟨hfi,hfs⟩
  have he : (fun ξ : V → ℝ => fun j => ξ (site j)) =
      (fun z : S → ℝ => fun j => z (e j)) ∘ S.restrict := rfl
  have hr : (fun z : S → ℝ => fun j => z (e j)) =
      MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e.symm := by
    funext z j
    obtain ⟨v,rfl⟩ := e.symm.surjective j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp
  have hT : Measurable (fun z : S → ℝ => fun j : J => z (e j)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hR : Measurable (S.restrict : (V → ℝ) → S → ℝ) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [he,← Measure.map_map hT hR,gaussianLabelLaw,
    Measure.infinitePi_map_restrict,hr]
  exact (measurePreserving_piCongrLeft (fun _ : J => gaussianReal 0 1) e.symm).map_eq

/-- Every coordinate of the actual Gaussian label field has its stated law. -/
theorem gaussianLabelLaw_eval {V : Type*} (v : V) :
    Measure.map (fun ξ : V → ℝ => ξ v) (gaussianLabelLaw V) = gaussianReal 0 1 := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply v) hs]
  have he : (fun ξ : V → ℝ => ξ v) ⁻¹' s = Set.pi ({v} : Finset V) (fun _ => s) := by
    ext ξ
    simp
  rw [he,gaussianLabelLaw,Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

/-- The actual Gaussian coordinate labels are mutually independent, for
arbitrary ambient index sets. -/
theorem gaussianLabelLaw_iIndepFun (V : Type*) :
    iIndepFun (fun v (ξ : V → ℝ) => ξ v) (gaussianLabelLaw V) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have he : (⋂ i ∈ S,(fun ξ : V → ℝ => ξ i) ⁻¹' sets i) = Set.pi S sets := by
    ext ξ
    simp [Set.mem_pi]
  rw [he,gaussianLabelLaw,Measure.infinitePi_pi _ hsets]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Measure.map_apply (measurable_pi_apply i) (hsets i hi)]
  exact congrArg (fun μ : Measure ℝ => μ (sets i)) (gaussianLabelLaw_eval i).symm

/-- Coefficient pushforward preserves the actual sampled Gaussian law when
there are no collisions on the union of the rows' supports. -/
theorem finiteSupportGaussianLaw_mapDomain_of_injOn {V W J : Type*} [Fintype J]
    (a : J → V →₀ ℝ) (F : V → W)
    (hF : Set.InjOn F (finiteSupportGaussianUnion a : Set V)) :
    finiteSupportGaussianLaw (fun j => Finsupp.mapDomain F (a j)) =
      finiteSupportGaussianLaw a := by
  let S := finiteSupportGaussianUnion a
  let site : S → W := fun v => F v.val
  have hs : Function.Injective site := by
    intro v w he
    exact Subtype.ext (hF v.property w.property he)
  have hsample : finiteSupportGaussianSample (fun j => Finsupp.mapDomain F (a j)) =
      (finiteSupportGaussianMatrix a).mulVec ∘
        (fun ξ : W → ℝ => fun v : S => ξ (site v)) := by
    funext ξ
    have he : finiteSupportGaussianSample (fun j => Finsupp.mapDomain F (a j)) ξ =
        finiteSupportGaussianSample a (ξ ∘ F) := by
      funext j
      exact finiteSupportGaussianSample_mapDomain F (a j) ξ
    rw [he,finiteSupportGaussianSample_eq_matrix]
    rfl
  rw [finiteSupportGaussianLaw,hsample,← Measure.map_map (measurable_finiteMatrixAction _)
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)),gaussianLabelLaw_map_injective site hs,
    finiteSupportGaussianLaw_eq_linearImage]
  rfl

/-- An injective cover window has exactly the same joint Gaussian output as
the actual tree rule, with no covariance or Gaussianity premise. -/
theorem graphRadialGaussianLaw_cover_window {N m : ℕ}
    (G : Reused.Graph.RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (x : ℝ) (b : ℕ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hinj : Set.InjOn (infiniteVertexGraphCover G k seed)
      (finiteSupportGaussianUnion (fun j => radialGaussianBlockCoefficient (m+2) x b (site j)) :
        Set (RegularTreeVertex (m+2)))) :
    finiteSupportGaussianLaw (fun j => graphRadialGaussianCoefficient G.val (m+2) x b
      (infiniteVertexGraphCover G k seed (site j))) =
    finiteSupportGaussianLaw (fun j => radialGaussianBlockCoefficient (m+2) x b (site j)) := by
  have he : (fun j => graphRadialGaussianCoefficient G.val (m+2) x b
      (infiniteVertexGraphCover G k seed (site j))) =
      fun j => Finsupp.mapDomain (infiniteVertexGraphCover G k seed)
        (radialGaussianBlockCoefficient (m+2) x b (site j)) := by
    funext j
    exact (graphRadialGaussianCoefficient_cover G k seed x b (site j)).symm
  rw [he]
  exact finiteSupportGaussianLaw_mapDomain_of_injOn _ _ hinj

end GaussianWave.BS
