import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondMobiusPoint
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex

/-! The actual adapted-base complex operator transforms in the second
CP¹ affine chart, including the south pole.  The coefficient is the
antipodal Hopf point of the literal `[w:1]` spinor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondBaseComplex

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveActualBaseComplex
  FourDimensionalHalfSpinProjectiveActualSecondMobiusPoint
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinAntipodalVerticalSign
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem secondAffineSpinorPoint_hopf (w : ℂ) :
    projectiveHopf (secondAffineSpinorPoint w) =
      hopfSphere ![w,1] (by simp) := by
  rw [secondAffineSpinorPoint_mk]
  exact projectiveHopf_mk _ _

theorem actual_second_antipodal_baseComplex_mobius (p q : M)
    (lift : unitary ℍ) (y u : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : secondDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0) :
    let t := secondMobius
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w
    fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y
      (chartBaseComplex Q p y
        (antipodalCoefficient (hopfSphere ![w,1] (by simp))) u) =
      chartBaseComplex Q q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
        (antipodalCoefficient (hopfSphere ![t,1] (by simp)))
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) := by
  dsimp
  have h := actual_projective_antipodal_base_complex_overlap Q p q y hy
    hx.1.1 hx.1.2 (secondAffineSpinorPoint w) u
  rw [actualTransition_secondPoint Q p q lift y hx w hden] at h
  rw [secondAffineSpinorPoint_hopf,
    secondAffineSpinorPoint_hopf] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
