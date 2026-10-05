import QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualHorizontalKernel
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The real contact quotient transported along the actual homothety map,
defined by the identity tangent model and the proved horizontal membership
equivalence; no dependent submodule equality is exposed as an API. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyContactQuotientReal
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyActualHorizontalKernel
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

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

def contactQuotientRealEquiv (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    (TangentSpace (J (E := E)) z ⧸
      horizontalTangentSubmodule (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z) ≃ₗ[ℝ]
    (TangentSpace (J (E := E)) (sphereTotalDiffeomorph Q s hs z) ⧸
      horizontalTangentSubmodule Q D (sphereTotalDiffeomorph Q s hs z)) := by
  let P := horizontalTangentSubmodule (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) z
  let R := horizontalTangentSubmodule Q D (sphereTotalDiffeomorph Q s hs z)
  apply Submodule.Quotient.equiv P R (LinearEquiv.refl ℝ _)
  apply Submodule.ext
  intro v
  simpa only [P, R, Submodule.mem_map, LinearEquiv.coe_refl, id_eq] using
    horizontal_mem_iff_rescale Q D s hs z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyContactQuotientReal
