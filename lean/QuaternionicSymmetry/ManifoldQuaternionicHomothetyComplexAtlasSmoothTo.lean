import QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasReal
import QuaternionicSymmetry.HomeomorphPulledAtlasGeneralRealSmooth

/-! Compatibility of the pulled normalized complex atlas with the original
twistor's existing real smooth atlas, in the forward direction. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothTo
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

theorem smoothToExisting (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    letI := charts Q D s hs n A
    ContMDiff 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E)) ∞
      (id : SphereBundleTotal Q → SphereBundleTotal Q) := by
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  let RX : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2))) (SphereBundleTotal Q) :=
    inferInstance
  let RY : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (SphereBundleTotal (rescaleMetric Q s hs)) := inferInstance
  have hInv :
      letI := RY
      letI := RX
      ContMDiff (RealModel (E := E)) (RealModel (E := E)) ∞ e.symm := by
    exact (sphereTotalDiffeomorph Q s hs).contMDiff
  exact HomeomorphPulledAtlasGeneralRealSmooth.smooth_to_old
    (RealModel (E := E)) e A.charts RX RY
    A.realManifold A.smoothToExisting hInv

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothTo
