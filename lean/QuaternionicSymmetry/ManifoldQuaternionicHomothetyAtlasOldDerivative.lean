import QuaternionicSymmetry.ManifoldQuaternionicHomothetyOperatorEqualities

/-! The independently constructed real twistor atlas sees the derivative of
the actual homothety map as the identity, at an arbitrary original point. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyAtlasOldDerivative
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyDerivativeAccessor
open ManifoldQuaternionicHomothetyOperatorEqualities
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem oldDerivative_eq_id (s : ℝ) (hs : s ≠ 0)
    (x : SphereBundleTotal Q) :
    let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
    mfderiv (RealModel (E := E)) (RealModel (E := E)) e.symm (e x) =
      ContinuousLinearMap.id ℝ (E × EuclideanSpace ℝ (Fin 2)) := by
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  change homothetyTwistorDerivative Q s hs (e x) =
    ContinuousLinearMap.id ℝ (E × EuclideanSpace ℝ (Fin 2))
  exact derivative_eq_id Q s hs (e x)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyAtlasOldDerivative
