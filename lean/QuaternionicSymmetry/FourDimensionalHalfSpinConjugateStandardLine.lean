import QuaternionicSymmetry.FourDimensionalHalfSpinConnectionHopfMatch
import QuaternionicSymmetry.QuaternionicManifoldStandardAffineOverlap

/-! Quaternionic conjugation identifies the already-checked right-line
standard representation with the genuine left half-spin representation.
This fixes the sign and supplies a route from the standard affine gauge law
to the independent left-spinor connection. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinConjugateStandardLine

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinLieProjection
  QuaternionicProjectiveStandardLie
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicConnection

noncomputable section

/-- The right quaternionic line Lie operator becomes literal left
multiplication by the imaginary spinor coefficient after conjugation. -/
theorem star_scalarLineLie (A : ℍ →L[ℝ] ℍ) (v : ℍ) :
    star (scalarLineLie leftLineStructure A (star v)) =
      leftLieProjection A * v := by
  let a := leftLieProjection A
  have ha : star a = -a := Quaternion.star_eq_neg.mpr (leftLieProjection_re A)
  change star ((star v) * -a) = a * v
  rw [star_mul, star_neg, ha, star_star]
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem star_standardLineForm (p : M) (y u v : ℍ) :
    star (scalarLineLie leftLineStructure
      (fixedTangentConjugation leftLineStructure Q p (D.form p y u))
      (star v)) =
      leftSpinorForm Q D p y u * v := by
  rw [leftSpinorForm_apply]
  exact star_scalarLineLie _ _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinConjugateStandardLine
