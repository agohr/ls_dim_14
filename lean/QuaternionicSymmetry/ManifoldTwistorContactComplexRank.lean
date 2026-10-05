import QuaternionicSymmetry.ManifoldTwistorContactFiberCharts
import QuaternionicSymmetry.ManifoldTwistorContactDistributionComplex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import QuaternionicSymmetry.QuaternionicAction

/-! The complex rank of the actual horizontal twistor contact plane.
This checks the exponent in the contact canonical-line formula against
the quaternionic dimension, rather than assuming it in a bundle label. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

theorem horizontalComplex_finrank (z : SphereBundleTotal Q)
    (n : ℕ) (hDim : Module.finrank ℝ E = 4 * n) :
    letI := horizontalComplexModule Q D z
    Module.finrank ℂ (horizontalTangentSubmodule Q D z) = 2 * n := by
  let realModule : Module ℝ (horizontalTangentSubmodule Q D z) := inferInstance
  letI : Module ℝ (horizontalTangentSubmodule Q D z) := realModule
  letI := horizontalComplexModule Q D z
  letI : IsScalarTower ℝ ℂ (horizontalTangentSubmodule Q D z) := ⟨by
    intro r c v
    change horizontalComplexSmul Q D z (r • c) v =
      r • horizontalComplexSmul Q D z c v
    rw [show r • c = (r : ℂ) * c by simp,
      horizontalComplexSmul_mul, horizontalComplexSmul_real]⟩
  have hmodule : Module.complexToReal (horizontalTangentSubmodule Q D z) =
      realModule := by
    apply Module.ext'
    intro r v
    change horizontalComplexSmul Q D z (r : ℂ) v = r • v
    exact horizontalComplexSmul_real Q D z r v
  have h := finrank_real_of_complex (horizontalTangentSubmodule Q D z)
  rw [hmodule] at h
  have hr : Module.finrank ℝ (horizontalTangentSubmodule Q D z) = 4 * n :=
    (horizontalFiber_finrank Q D z).trans hDim
  omega

theorem horizontalComplex_finrank_quaternionic (z : SphereBundleTotal Q)
    (S : QuaternionicStructure E) :
    letI := horizontalComplexModule Q D z
    Module.finrank ℂ (horizontalTangentSubmodule Q D z) =
      2 * S.quaternionicDimension :=
  horizontalComplex_finrank Q D z S.quaternionicDimension S.real_finrank

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
