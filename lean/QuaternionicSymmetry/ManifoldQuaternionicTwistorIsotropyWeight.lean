import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction

/-! The derivative of an actual quaternionic isometry fixing a twistor point
acts on its vertical complex line. This is the geometric isotropy weight;
identifying the line with the contact quotient is a separate theorem. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorIsotropyWeight

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryOrientation
open ManifoldQuaternionicRankThreeOrientation
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorCoefficientSphere
open ManifoldQuaternionicConnection
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev Isotropy (z : SphereBundleTotal Q) :=
  MulAction.stabilizer (QuaternionicIsometries Q) z

/-- A stabilizer of an actual twistor point also fixes its base point. -/
theorem isotropy_fixes_base (z : SphereBundleTotal Q)
    (f : Isotropy Q z) : f.1 • z.1 = z.1 := by
  have h := congrArg (fun w : SphereBundleTotal Q => w.1) f.2
  simpa only [smul_sphereTotal_base] using h

/-- The same stabilizer fixes the twistor point's preferred coefficient. -/
theorem isotropy_fixes_coefficient (z : SphereBundleTotal Q)
    (f : Isotropy Q z) :
    coefficientSphereAction Q f.1 z.1
      (coefficientSphereHomeomorph.symm z.2) =
        coefficientSphereHomeomorph.symm z.2 := by
  have h := congrArg (fun w : SphereBundleTotal Q =>
    coefficientSphereHomeomorph.symm w.2) f.2
  exact (sphereTotalMap_coefficient Q f.1 z).symm.trans h

/-- The actual twistor stabilizer acts linearly on the vertical coefficient
plane at its fixed twistor point. -/
def isotropyVerticalRepresentation (z : SphereBundleTotal Q) :
    Isotropy Q z →* Module.End ℝ
      (verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) where
  toFun f := {
    toFun := fun v => ⟨coefficientAction Q f.1 z.1 v.1, by
      change (coefficientSphereHomeomorph.symm z.2).1 ⬝ᵥ
        coefficientAction Q f.1 z.1 v.1 = 0
      have hfix := congrArg Subtype.val (isotropy_fixes_coefficient Q z f)
      change coefficientAction Q f.1 z.1
        (coefficientSphereHomeomorph.symm z.2).1 =
          (coefficientSphereHomeomorph.symm z.2).1 at hfix
      calc
        _ = (coefficientAction Q f.1 z.1
            (coefficientSphereHomeomorph.symm z.2).1) ⬝ᵥ
              coefficientAction Q f.1 z.1 v.1 := by rw [hfix]
        _ = (coefficientSphereHomeomorph.symm z.2).1 ⬝ᵥ v.1 :=
          coefficientAction_dot Q f.1 z.1 _ _
        _ = 0 := v.2⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      exact (coefficientAction Q f.1 z.1).map_add u.1 v.1
    map_smul' := by
      intro r v
      apply Subtype.ext
      exact (coefficientAction Q f.1 z.1).map_smul r v.1 }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact coefficientAction_one Q z.1 v.1
  map_mul' f g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change coefficientAction Q (f.1 * g.1) z.1 v.1 =
      coefficientAction Q f.1 z.1 (coefficientAction Q g.1 z.1 v.1)
    rw [coefficientAction_mul, isotropy_fixes_base Q z g]

/-- Every isotropy weight is complex-linear for the canonical vertical
complex structure; this is the SO(2) character on the actual twistor fiber. -/
theorem isotropyVerticalRepresentation_complex
    (z : SphereBundleTotal Q) (f : Isotropy Q z)
    (v : verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) :
    isotropyVerticalRepresentation Q z f
      (verticalComplex (coefficientSphereHomeomorph.symm z.2) v) =
    verticalComplex (coefficientSphereHomeomorph.symm z.2)
      (isotropyVerticalRepresentation Q z f v) := by
  apply Subtype.ext
  change coefficientAction Q f.1 z.1
      ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃ v.1) =
    (coefficientSphereHomeomorph.symm z.2).1 ⨯₃
      coefficientAction Q f.1 z.1 v.1
  rw [coefficientAction_cross]
  exact congrArg (fun a : Fin 3 → ℝ => a ⨯₃ coefficientAction Q f.1 z.1 v.1)
    (congrArg Subtype.val (isotropy_fixes_coefficient Q z f))

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorIsotropyWeight
