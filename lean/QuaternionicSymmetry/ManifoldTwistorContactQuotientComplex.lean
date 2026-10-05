import QuaternionicSymmetry.ManifoldTwistorSmoothContactSubbundles
import QuaternionicSymmetry.ManifoldTwistorVerticalComplexLine

/-! The quotient of the actual twistor tangent space by the connection
horizontal contact plane is a complex line. Its complex structure is
transported from the genuine vertical kernel of the sphere projection.
The construction is fiberwise; a holomorphic contact-line bundle requires
the twistor integrability theorem. -/

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

/-- The quotient by the connection-horizontal plane has its natural
complex scalar action, identified with the vertical complex line. -/
def contactQuotientComplexModule (z : SphereBundleTotal Q) :
    Module ℂ (TangentSpace (I (E := E)) z ⧸
      horizontalTangentSubmodule Q D z) := by
  letI := verticalComplexModule Q D z
  exact (contactQuotientEquiv Q D z).toAddEquiv.module ℂ

/-- The vertical identification is complex linear for the transported
quotient structure. -/
def contactQuotientComplexEquiv (z : SphereBundleTotal Q) :
    letI := contactQuotientComplexModule Q D z
    letI := verticalComplexModule Q D z
    (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) ≃ₗ[ℂ]
      verticalTangentSubmodule Q z := by
  letI := verticalComplexModule Q D z
  letI := contactQuotientComplexModule Q D z
  exact {
    contactQuotientEquiv Q D z with
    map_smul' := by
      intro c v
      simp [contactQuotientComplexModule, Equiv.smul_def]
  }

theorem contactQuotient_complex_finrank (z : SphereBundleTotal Q) :
    letI := contactQuotientComplexModule Q D z
    Module.finrank ℂ
      (TangentSpace (I (E := E)) z ⧸ horizontalTangentSubmodule Q D z) = 1 := by
  letI := contactQuotientComplexModule Q D z
  letI := verticalComplexModule Q D z
  rw [(contactQuotientComplexEquiv Q D z).finrank_eq]
  exact verticalComplex_finrank Q D z

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
