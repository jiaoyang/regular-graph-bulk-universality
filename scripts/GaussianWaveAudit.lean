import GaussianWave
import Lean.Util.CollectAxioms

/-! Audit every theorem declared in the GaussianWave namespace, including
helpers. Only Lean's three standard classical foundations are permitted. -/
open Lean Elab Command

#print axioms GaussianWave.BS.Lower.exists_common_graph_good_events
#print axioms GaussianWave.BS.Lower.common_graph_all_radius_finite_recoloring_entropy_lower
#print axioms GaussianWave.BS.exists_graph_realization_independent_gaussian_wave_sum
#print axioms GaussianWave.BS.Lower.common_graph_gaussian_wave_sum_finite_recoloring_entropy_lower
#print axioms GaussianWave.BS.smooth_normalized_eigenprocess_eq_jointGaussian
#print axioms GaussianWave.BS.common_graph_eigenprocess_finite_gaussian
#print axioms GaussianWave.BS.common_graph_approximate_BSJointClassification
#print axioms GaussianWave.BS.exists_RRGClassificationEvents
#print axioms GaussianWave.BS.RRGClassificationEvents.good_probability_tendsto_one
#print axioms GaussianWave.BS.RRGClassificationEvents.eigenvectors_BSJointClassification
#print axioms GaussianWave.BS.RRGClassificationEvents.signals_BSJointClassification

run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let names ← env.constants.foldM (init := (#[] : Array Name)) fun names n info => do
    if (`GaussianWave).isPrefixOf n || n.toString.startsWith "_private.GaussianWave." then
      pure (if info.isTheorem then names.push n else names)
    else
      pure names
  let collection : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (collection.run env).run {}
  for a in state.axioms do
    unless allowed.contains a do
      throwError "Unexpected axiom in project theorem dependencies: {a}"
  logInfo m!"Axiom audit passed for {names.size} GaussianWave theorems."
  logInfo "Allowed foundations: propext, Classical.choice, Quot.sound."

#print axioms GaussianWave.uniformStar_wasserstein_of_oneEdgeQuadraticBound
#print axioms GaussianWave.eigenvectors_normalizedStar_wasserstein
#print axioms GaussianWave.wassersteinTwo_tendsto_zero_of_common_weak_limit
#print axioms GaussianWave.RegularEigenData.twoEdge_weighted_bound_of_oneEdgeQuadraticBound
#print axioms GaussianWave.RegularEigenData.physical_centered_bulk_input
#print axioms GaussianWave.uniform_normalizedWindow_wasserstein_inProbability
#print axioms GaussianWave.almostEigenvectors_normalizedStar_wasserstein
#print axioms GaussianWave.quenched_twoEdge_L1_and_stable_factorization
#print axioms GaussianWave.starGaussian_eigenrelation
#print axioms GaussianWave.BS.hasDerivAt_heatEntropy
#print axioms GaussianWave.BS.tendsto_heatDensity_entropy_zero
#print axioms GaussianWave.BS.conditionalScore_heatDirectionalScore_orthonormal_rows
#print axioms GaussianWave.BS.star_heatFrameFisherDefect_nonneg
#print axioms GaussianWave.BS.star_entropy_upper
#print axioms GaussianWave.BS.star_entropy_equality_heat_and_fisher_zero
#print axioms GaussianWave.BS.star_entropy_equality_iff_standardVector
#print axioms GaussianWave.BS.colored_star_entropy_upper
#print axioms GaussianWave.BS.physical_hyperplane_entropy_upper
#print axioms GaussianWave.BS.physical_single_edge_entropy_upper_and_equality
#print axioms GaussianWave.BS.colored_star_entropy_equality_iff_standardVector
#print axioms GaussianWave.BS.colored_physical_hyperplane_entropy_equality_iff_gaussian
#print axioms GaussianWave.BS.singular_channel_entropy_equality_iff_gaussian
#print axioms GaussianWave.BS.singular_channel_heated_entropy_equality_iff_gaussian
#print axioms GaussianWave.BS.singular_physical_entropy_equality_iff_gaussian
