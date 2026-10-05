import QuaternionicSymmetry.ComplexQuotientTransport
import QuaternionicSymmetry.ManifoldTwistorContactQuotientIMk
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalKernel
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex

/-! The identity on the common real tangent model induces a complex-linear
equivalence of homothetic contact quotients. Its geometric inputs are the
checked horizontal-kernel membership iff and pointwise twistor tensor law. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyContactQuotientComplexRaw
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyActualHorizontalKernel
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

private abbrev V := E × EuclideanSpace ℝ (Fin 2)

def quotientComplexEquiv (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    letI := contactQuotientComplexModule (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z
    letI := contactQuotientComplexModule Q D (sphereTotalDiffeomorph Q s hs z)
    (V (E := E) ⧸ horizontalTangentSubmodule (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z) ≃ₗ[ℂ]
    (V (E := E) ⧸ horizontalTangentSubmodule Q D
      (sphereTotalDiffeomorph Q s hs z)) := by
  let P := horizontalTangentSubmodule (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) z
  let R := horizontalTangentSubmodule Q D (sphereTotalDiffeomorph Q s hs z)
  letI := contactQuotientComplexModule (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) z
  letI := contactQuotientComplexModule Q D (sphereTotalDiffeomorph Q s hs z)
  let J := tangentComplex (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) z
  apply ComplexQuotientTransport.complexEquiv P R
    (horizontal_mem_iff_rescale Q D s hs z) J
  · intro v
    exact ManifoldTwistorContactQuotientIMk.i_smul_mk
      (rescaleMetric Q s hs) (rescaleConnection Q D s hs) z v
  · intro v
    rw [tangentComplex_at_homothety_point Q D s hs z v]
    exact ManifoldTwistorContactQuotientIMk.i_smul_mk Q D
      (sphereTotalDiffeomorph Q s hs z) v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyContactQuotientComplexRaw
