import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorLocal
import QuaternionicSymmetry.ManifoldTwistorRawTransition

/-!
The smooth twistor homothety has identical raw base–sphere transitions.
The local almost-complex operator and horizontal contact-plane projector
agree in those coordinates. This formulation avoids elaborating two
dependent `TangentSpace` types with equal, but definitionally distinct,
bundle-core manifold structures.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCharts
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyTwistorLocal
open ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLocalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem rawSphereTransition_rescale (s : ℝ) (hs : s ≠ 0)
    (p q : M) (ys : E × ManifoldTwistorCoefficientSphere.geometricSphere) :
    rawSphereTransition (rescaleMetric Q s hs) p q ys =
      rawSphereTransition Q p q ys := by
  simp only [rawSphereTransition, sphereCore_rescale]

/-- The actual local geometric operators of the two twistor spaces agree in
every raw chart under the checked identity diffeomorphism. -/
theorem local_complex_and_horizontal_rescale
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (s : ℝ) (hs : s ≠ 0) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : ManifoldTwistorSphereBundle.coefficientSphere) :
    localTwistorComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) p y hy a =
        localTwistorComplex Q D p y hy a ∧
      localHorizontalPlaneProjection (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) p y hy a =
        localHorizontalPlaneProjection Q D p y hy a :=
  ⟨localTwistorComplex_rescale Q D s hs p y hy a,
    localHorizontalPlaneProjection_rescale Q D s hs p y hy a⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCharts
