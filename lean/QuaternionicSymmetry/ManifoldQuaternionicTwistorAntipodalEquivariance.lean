import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalWeight

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalEquivariance

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicTwistorAntipodalWeight
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem sphereAntipodal_commutes_coefficient
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    coefficientSphereHomeomorph.symm
      (sphereAntipodal Q (sphereTotalMap Q f z)).2 =
    coefficientSphereHomeomorph.symm
      (sphereTotalMap Q f (sphereAntipodal Q z)).2 := by
  calc
    _ = coefficientAntipodal
          (coefficientSphereHomeomorph.symm (sphereTotalMap Q f z).2) :=
      sphereAntipodal_coefficient Q _
    _ = coefficientAntipodal
          (coefficientSphereAction Q f z.1
            (coefficientSphereHomeomorph.symm z.2)) := by
      rw [sphereTotalMap_coefficient]
    _ = coefficientSphereAction Q f z.1
          (coefficientAntipodal (coefficientSphereHomeomorph.symm z.2)) :=
      coefficientAntipodal_coefficientSphereAction Q f z.1 _
    _ = _ := by
      rw [sphereTotalMap_coefficient, sphereAntipodal_base,
        sphereAntipodal_coefficient]

private theorem total_eq_of_base_and_coefficient
    {u v : SphereBundleTotal Q} (hb : u.1 = v.1)
    (hc : coefficientSphereHomeomorph.symm u.2 =
      coefficientSphereHomeomorph.symm v.2) : u = v := by
  cases u with
  | mk x a =>
    cases v with
    | mk y b =>
      dsimp at hb hc
      cases hb
      have hab : a = b := coefficientSphereHomeomorph.symm.injective hc
      cases hab
      rfl

/-- The antipode commutes with the actual lifted isometry on the total space. -/
theorem sphereAntipodal_commutes
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    sphereAntipodal Q (sphereTotalMap Q f z) =
      sphereTotalMap Q f (sphereAntipodal Q z) := by
  apply total_eq_of_base_and_coefficient Q
  · simp only [sphereAntipodal_base, sphereTotalMap_base]
  · exact sphereAntipodal_commutes_coefficient Q f z

/-- Applying the fiberwise antipode twice returns the original point. -/
theorem sphereAntipodal_involutive :
    Function.Involutive (sphereAntipodal Q) := by
  intro z
  apply total_eq_of_base_and_coefficient Q
  · rfl
  · simpa only [sphereAntipodal_coefficient] using
      coefficientAntipodal_involutive
        (coefficientSphereHomeomorph.symm z.2)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalEquivariance
