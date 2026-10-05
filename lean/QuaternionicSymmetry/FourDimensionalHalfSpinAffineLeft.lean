import QuaternionicSymmetry.FourDimensionalHalfSpinAffineBlock

/-! Literal left-half-spin affine connection law on each actual refined
adapted-frame overlap. The local unit quaternion is a smooth lift, but the
formula is sign-invariant and therefore does not require a global spin lift. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinAffineLeft

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinAffineBlock
  FourDimensionalHalfSpinConjugateStandardLine
  FourDimensionalHalfSpinLieProjection
  QuaternionicProjectiveStandardLie
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicProjectiveLineMaurer
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldFixedConnectionOverlap
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem leftSpinorForm_affine_refined (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    leftSpinorForm Q D p y u =
      star (r y) *
        (leftSpinorForm Q D q
          (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u) * r y +
          fderiv ℝ r y u) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
  let v := fderiv ℝ φ y u
  let A := fixedForm leftLineStructure Q D q (φ y) v
  have hright := scalarLineForm_affine_refined Q D p q lift y u hy hx
  have h := congrArg
    (fun T : ℍ →L[ℝ] ℍ => star (T (star (1 : ℍ)))) hright
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  have hderiv := rightStar_fderiv r y hr u
  have hp : fixedForm leftLineStructure Q D p y u =
      fixedTangentConjugation leftLineStructure Q p (D.form p y u) :=
    fixedForm_apply leftLineStructure Q D p y u
  rw [hp] at h
  rw [fixedForm_apply leftLineStructure Q D q _ _] at h
  have hD0 :
      (fderiv ℝ (fun z => rightStar (r z)) y u) 1 =
        star (fderiv ℝ r y u) := by
    rw [hderiv]
    simp
  simp only [star_one, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.add_apply] at h
  rw [show rightStar (r y) 1 = star (r y) by simp [rightStar], hD0] at h
  have hK (w : ℍ) : rightStar (star (r y)) w = w * r y := by
    simp [rightStar]
  rw [hK] at h
  change star
      (scalarLineLie leftLineStructure
        (fixedTangentConjugation leftLineStructure Q p (D.form p y u)) 1) =
    star ((scalarLineLie leftLineStructure
      (fixedTangentConjugation leftLineStructure Q q (D.form q (φ y) v))
        (star (r y)) + star (fderiv ℝ r y u)) * r y) at h
  rw [star_mul, star_add, star_star,
    star_scalarLineLie] at h
  have hP := star_scalarLineLie
    (fixedTangentConjugation leftLineStructure Q p (D.form p y u)) 1
  simp only [star_one, mul_one] at hP
  rw [hP] at h
  simpa [leftSpinorForm_apply, φ, v, r] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinAffineLeft
