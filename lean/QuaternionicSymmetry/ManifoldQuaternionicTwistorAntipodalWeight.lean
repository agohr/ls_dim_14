import QuaternionicSymmetry.ManifoldQuaternionicVerticalComplexCharacter
import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction

/-! The actual fiberwise twistor antipode and equivariance of its coefficient
map. Total-space equivariance and the comparison of contact/vertical
characters at antipodes remain separate obligations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalWeight

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def coefficientAntipodal (a : coefficientSphere) : coefficientSphere :=
  ⟨-a.1, by simpa only [squareNorm, Pi.neg_apply, neg_mul_neg] using a.2⟩

theorem coefficientAntipodal_apply (a : coefficientSphere) :
    (coefficientAntipodal a).1 = -a.1 := rfl

theorem coefficientAntipodal_involutive :
    Function.Involutive coefficientAntipodal := by
  intro a
  apply Subtype.ext
  simp [coefficientAntipodal]

theorem coefficientAntipodal_coefficientSphereAction
    (f : QuaternionicIsometries Q) (x : M) (a : coefficientSphere) :
    coefficientAntipodal (coefficientSphereAction Q f x a) =
      coefficientSphereAction Q f x (coefficientAntipodal a) := by
  apply Subtype.ext
  change -(coefficientAction Q f x a.1) = coefficientAction Q f x (-a.1)
  exact (map_neg _ _).symm

def sphereAntipodal (z : SphereBundleTotal Q) : SphereBundleTotal Q :=
  ⟨z.1, coefficientSphereHomeomorph
    (coefficientAntipodal (coefficientSphereHomeomorph.symm z.2))⟩

theorem sphereAntipodal_base (z : SphereBundleTotal Q) :
    (sphereAntipodal Q z).1 = z.1 := rfl

theorem sphereAntipodal_coefficient (z : SphereBundleTotal Q) :
    coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2 =
      coefficientAntipodal (coefficientSphereHomeomorph.symm z.2) := by
  simp [sphereAntipodal]

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalWeight
