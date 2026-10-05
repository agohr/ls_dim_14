import QuaternionicSymmetry.ManifoldTwistorContactPullbackBundle

/-! The actual smooth pullback bundle π*TM acquires the fiberwise twistor
complex structure through the connection horizontal lift. Its complex
action is checked against the globally defined twistor J on TZ. The
smoothness of this action as a bundle map is a separate local-chart proof. -/

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

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The complex scalar action on each fiber of the genuine smooth
pullback bundle, transported through the geometric horizontal lift. -/
def contactPullbackComplexModule (z : SphereBundleTotal Q) :
    Module ℂ (contactPullbackFiber Q z) := by
  letI := horizontalComplexModule Q D z
  exact (contactPullbackHorizontalEquiv Q D z).toAddEquiv.module ℂ

/-- Horizontal lift is complex linear for the induced action. -/
def contactPullbackHorizontalComplexEquiv (z : SphereBundleTotal Q) :
    letI := contactPullbackComplexModule Q D z
    letI := horizontalComplexModule Q D z
    contactPullbackFiber Q z ≃ₗ[ℂ] horizontalTangentSubmodule Q D z := by
  letI := horizontalComplexModule Q D z
  letI := contactPullbackComplexModule Q D z
  exact {
    contactPullbackHorizontalEquiv Q D z with
    map_smul' := by
      intro c u
      simp [contactPullbackComplexModule, Equiv.smul_def]
  }

/-- The fiberwise complex multiplication by i is precisely the restriction
of the global tangent J, seen through horizontal lift. -/
theorem contactPullback_i_eq_globalJ (z : SphereBundleTotal Q)
    (u : contactPullbackFiber Q z) :
    letI := contactPullbackComplexModule Q D z
    (contactPullbackHorizontalEquiv Q D z (Complex.I • u) :
      horizontalTangentSubmodule Q D z) =
      horizontalTangentComplex Q D z
        (contactPullbackHorizontalEquiv Q D z u) := by
  letI := contactPullbackComplexModule Q D z
  letI := horizontalComplexModule Q D z
  change contactPullbackHorizontalComplexEquiv Q D z (Complex.I • u) = _
  rw [map_smul]
  exact horizontalComplexSmul_i Q D z _

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
