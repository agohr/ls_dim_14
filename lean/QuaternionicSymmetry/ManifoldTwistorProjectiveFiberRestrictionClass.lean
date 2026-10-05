import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestriction
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The actual Picard restriction homomorphism sends the contact class to
the genuine tangent determinant class of CP¹. An integer degree computation
for that class is a separate remaining obligation. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestrictionClass

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorProjectiveFiberRestriction
open HolomorphicLineCoreClasses ProjectiveLineTangentDeterminant
open FourDimensionalHalfSpinProjective
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem restrictionHom_contactClass {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A)
    (p : M) :
    letI := A.charts
    restrictionHom Q D A p (contactClass Q D C.line) =
      (Quotient.mk _ tangentLineCore : CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model)) := by
  letI := A.charts
  letI := tangentLineCore.holomorphic
  letI := C.line.holomorphic
  apply Quotient.sound
  exact ⟨(contactRestrictionGauge Q D A C p).symm⟩

theorem restrictionHom_contactPower {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A)
    (p : M) (k : ℤ) :
    letI := A.charts
    restrictionHom Q D A p ((contactClass Q D C.line) ^ k) =
      (Quotient.mk _ tangentLineCore : CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model)) ^ k := by
  letI := A.charts
  rw [map_zpow, restrictionHom_contactClass Q D A C p]

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestrictionClass
