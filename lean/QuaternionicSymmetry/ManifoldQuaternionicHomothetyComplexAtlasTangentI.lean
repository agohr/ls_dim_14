import QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasSmoothFrom
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyAtlasOldDerivative
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex
import QuaternionicSymmetry.HomeomorphPulledAtlasTangentLinear

/-! The pulled normalized complex atlas realizes the original twistor's
independently constructed almost-complex tensor on its real tangent bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasTangentI
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyComplexAtlasCharts
open ManifoldQuaternionicHomothetyAtlasOldDerivative
open ManifoldQuaternionicHomothetyPointwiseComplex
open ManifoldTwistorLeBrunComplexAtlas
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

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem tangentI (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    letI := charts Q D s hs n A
    ∀ (z : SphereBundleTotal Q)
      (v : TangentSpace 𝓘(ℝ,ComplexTwistorModel n) z),
      mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) z
          ((Complex.I : ℂ) • (show ComplexTwistorModel n from v)) =
      tangentComplex Q D z
        (mfderiv 𝓘(ℝ,ComplexTwistorModel n) (RealModel (E := E))
          (id : SphereBundleTotal Q → SphereBundleTotal Q) z v) := by
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
  have hOld :
      letI := RY
      letI := RX
      ∀ x : SphereBundleTotal Q,
        mfderiv (RealModel (E := E)) (RealModel (E := E)) e.symm (e x) =
          ContinuousLinearMap.id ℝ (E × EuclideanSpace ℝ (Fin 2)) := by
    intro x
    exact oldDerivative_eq_id Q s hs x
  have hJ : ∀ (y : SphereBundleTotal (rescaleMetric Q s hs))
      (u : E × EuclideanSpace ℝ (Fin 2)),
      tangentComplex (rescaleMetric Q s hs) (rescaleConnection Q D s hs) y u =
        tangentComplex Q D (e.symm y) u := by
    intro y u
    exact tangentComplex_at_homothety_point Q D s hs y u
  intro z v
  exact HomeomorphPulledAtlasTangentLinear.tangentI_pullback
    (RealModel (E := E)) e A.charts RX RY A.realManifold
    A.smoothToExisting hInv hOld
    (fun x => tangentComplex Q D x)
    (fun y => tangentComplex (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) y)
    hJ A.tangentI z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasTangentI
