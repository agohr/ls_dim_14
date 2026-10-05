import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseHopfOverlap

/-! The actual raw-manifold base complex structure, including its smooth
adapted-frame conjugation, intertwines with the true projective half-spin
transition after antipodal Hopf identification. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinProjectiveBaseHopfOverlap
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actual_projective_antipodal_base_complex_overlap
    (p q : M) (y : ℍ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hi : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ p))
    (hj : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      Q.frames.adaptedCore.baseSet (achart ℍ q))
    (v : ProjectiveSpinor) (u : ℍ) :
    fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y
      (chartBaseComplex Q p y
        (antipodalCoefficient (projectiveHopf v)) u) =
      chartBaseComplex Q q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
        (antipodalCoefficient
          (projectiveHopf (spinorTransition Q (achart ℍ p) (achart ℍ q)
            ((extChartAt 𝓘(ℝ, ℍ) p).symm y) hi hj v)))
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) := by
  have h := chartBaseComplex_overlap Q p q y hy
    (antipodalCoefficient (projectiveHopf v)) u
  rw [rotatedCoefficient_antipodal_projectiveHopf Q p q y hy hi hj v] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseComplex
