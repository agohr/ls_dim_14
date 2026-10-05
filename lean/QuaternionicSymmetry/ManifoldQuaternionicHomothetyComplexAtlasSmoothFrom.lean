import QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothTo

/-! Reverse compatibility of the pulled normalized complex atlas with the
original twistor's independently constructed real smooth atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothFrom
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyComplexAtlasCharts
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem smoothFromExisting (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    letI := charts Q D s hs n A
    ContMDiff (RealModel (E := E)) 𝓘(ℝ,ComplexTwistorModel n) ∞
      (id : SphereBundleTotal Q → SphereBundleTotal Q) := by
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  let RX : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2))) (SphereBundleTotal Q) :=
    inferInstance
  let RY : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (SphereBundleTotal (rescaleMetric Q s hs)) := inferInstance
  have hForward :
      letI := RX
      letI := RY
      ContMDiff (RealModel (E := E)) (RealModel (E := E)) ∞ e := by
    exact (sphereTotalDiffeomorph Q s hs).symm.contMDiff
  exact HomeomorphPulledAtlasGeneralRealSmooth.smooth_from_old
    (RealModel (E := E)) e A.charts RX RY
    A.realManifold A.smoothFromExisting hForward

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothFrom
