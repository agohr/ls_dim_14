import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestrictionClass
import QuaternionicSymmetry.ProjectiveLineTangentHyperplaneSquare
import QuaternionicSymmetry.HolomorphicLineCoreClassPowers

/-! The actual contact line restricts to the square of the standard
hyperplane line on a twistor CP¹ fiber. This is a holomorphic gauge and an
equality in the genuine represented Picard group, not a stipulated degree. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberO2

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorProjectiveFiberRestriction
open ManifoldTwistorProjectiveFiberRestrictionClass
open HolomorphicLineCoreClasses HolomorphicLineCoreClassPowers
open HolomorphicLineTensorPowerClasses HolomorphicLinePowers HolomorphicLineGauge
open ProjectiveLineTangentDeterminant ProjectiveLineHyperplaneCore
open ProjectiveLineTangentHyperplaneSquare FourDimensionalHalfSpinProjective
noncomputable section

theorem tangentClass_eq_hyperplane_squared :
    (Quotient.mk _ tangentLineCore : CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model)) =
      (Quotient.mk _ hyperplaneLineCore : CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model)) ^ 2 := by
  rw [← class_powerCoreRep]
  letI := tangentLineCore.holomorphic
  letI := hyperplaneLineCore.holomorphic
  apply Quotient.sound
  exact ⟨tangentHyperplaneSquareGauge⟩

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def contactFiberO2Gauge {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A) (p : M) :
    GaugeIso (IB := 𝓘(ℂ,Model)) (powerCore hyperplaneCore 2)
      (restrictedContactCore Q D A C.line p) := by
  letI := tangentLineCore.holomorphic
  exact tangentHyperplaneSquareGauge.symm.trans (contactRestrictionGauge Q D A C p)

theorem restrictionHom_contactClass_eq_O2 {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A) (p : M) :
    letI := A.charts
    restrictionHom Q D A p (contactClass Q D C.line) =
      (Quotient.mk _ hyperplaneLineCore : CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model)) ^ 2 := by
  letI := A.charts
  exact (restrictionHom_contactClass Q D A C p).trans tangentClass_eq_hyperplane_squared

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberO2
