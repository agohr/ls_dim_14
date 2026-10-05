import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex

/-! Pointwise tensor agreement expressed at an original twistor point and its
preimage under the genuine homothety diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyAtlasPointwise
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyPointwiseComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem tangentComplex_at_original_point (s : ℝ) (hs : s ≠ 0)
    (x : SphereBundleTotal Q) (u : E × EuclideanSpace ℝ (Fin 2)) :
    let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
    tangentComplex Q D x u =
      tangentComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) (e x) u := by
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  have h := tangentComplex_at_homothety_point Q D s hs (e x) u
  have hex : sphereTotalDiffeomorph Q s hs (e x) = x := by
    exact (sphereTotalDiffeomorph Q s hs).apply_symm_apply x
  simpa only [hex] using h.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyAtlasPointwise
