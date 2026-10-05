import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison
import QuaternionicSymmetry.ManifoldTwistorSphereCore

/-! The derivative action of quaternionic isometries transported through the
proved pointwise equivalence to the existing twistor sphere bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual derivative-induced map on the original twistor sphere bundle.
The point is reconstructed in the preferred chart of its image base point. -/
def twistorMap (f : QuaternionicIsometries Q) (z : TwistorSphere Q) :
    TwistorSphere Q :=
  preferredPoint Q (f • projection Q z)
    ((preferredFiberEquiv Q (f • projection Q z)).symm
      (intrinsicTwistorFiberAction Q f (projection Q z)
        (toIntrinsicFiber Q z)))

theorem projection_twistorMap (f : QuaternionicIsometries Q)
    (z : TwistorSphere Q) :
    projection Q (twistorMap Q f z) = f • projection Q z := rfl

theorem toIntrinsic_twistorMap (f : QuaternionicIsometries Q)
    (z : TwistorSphere Q) :
    toIntrinsicFiber Q (twistorMap Q f z) =
      intrinsicTwistorFiberAction Q f (projection Q z)
        (toIntrinsicFiber Q z) := by
  change preferredToIntrinsic Q (f • projection Q z)
      ((preferredFiberEquiv Q (f • projection Q z)).symm
        (intrinsicTwistorFiberAction Q f (projection Q z)
          (toIntrinsicFiber Q z))) = _
  exact (preferredFiberEquiv Q (f • projection Q z)).apply_symm_apply _

theorem twistorMap_one (z : TwistorSphere Q) :
    twistorMap Q 1 z = z := by
  simpa only [twistorMap, one_smul, intrinsicTwistorFiberAction_one]
    using preferredPoint_intrinsic_roundtrip Q z

theorem twistorMap_mul (f g : QuaternionicIsometries Q)
    (z : TwistorSphere Q) :
    twistorMap Q (f * g) z = twistorMap Q f (twistorMap Q g z) := by
  calc
    twistorMap Q (f * g) z =
        preferredPoint Q (f • (g • projection Q z))
          ((preferredFiberEquiv Q (f • (g • projection Q z))).symm
            (intrinsicTwistorFiberAction Q f (g • projection Q z)
              (intrinsicTwistorFiberAction Q g (projection Q z)
                (toIntrinsicFiber Q z)))) := by
      exact congrArg
        (fun A : IntrinsicTwistorFiber Q (f • (g • projection Q z)) =>
          preferredPoint Q (f • (g • projection Q z))
            ((preferredFiberEquiv Q (f • (g • projection Q z))).symm A))
        (intrinsicTwistorFiberAction_mul Q f g (projection Q z)
          (toIntrinsicFiber Q z))
    _ = twistorMap Q f (twistorMap Q g z) := by
      change preferredPoint Q (f • (g • projection Q z))
          ((preferredFiberEquiv Q (f • (g • projection Q z))).symm
            (intrinsicTwistorFiberAction Q f (g • projection Q z)
              (intrinsicTwistorFiberAction Q g (projection Q z)
                (toIntrinsicFiber Q z)))) =
        preferredPoint Q (f • (g • projection Q z))
          ((preferredFiberEquiv Q (f • (g • projection Q z))).symm
            (intrinsicTwistorFiberAction Q f (g • projection Q z)
              (toIntrinsicFiber Q (twistorMap Q g z))))
      rw [toIntrinsic_twistorMap]

instance : MulAction (QuaternionicIsometries Q) (TwistorSphere Q) where
  smul := twistorMap Q
  one_smul := twistorMap_one Q
  mul_smul := twistorMap_mul Q

/-- The corresponding map on the smooth Euclidean-sphere bundle's points. -/
def sphereTotalMap (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) : SphereBundleTotal Q :=
  (sphereTotalEquiv Q).symm (twistorMap Q f ((sphereTotalEquiv Q) z))

theorem sphereTotalMap_base (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    (sphereTotalMap Q f z).1 = f • z.1 := by
  change projection Q (twistorMap Q f (toOriginalSphere Q z)) = f • z.1
  rw [projection_twistorMap]
  rfl

instance : MulAction (QuaternionicIsometries Q) (SphereBundleTotal Q) where
  smul := sphereTotalMap Q
  one_smul z := by
    change (sphereTotalEquiv Q).symm
      (twistorMap Q 1 ((sphereTotalEquiv Q) z)) = z
    rw [twistorMap_one]
    exact (sphereTotalEquiv Q).symm_apply_apply z
  mul_smul f g z := by
    change (sphereTotalEquiv Q).symm
      (twistorMap Q (f * g) ((sphereTotalEquiv Q) z)) =
      (sphereTotalEquiv Q).symm
        (twistorMap Q f ((sphereTotalEquiv Q)
          ((sphereTotalEquiv Q).symm
            (twistorMap Q g ((sphereTotalEquiv Q) z)))))
    rw [twistorMap_mul, (sphereTotalEquiv Q).apply_symm_apply]

theorem smul_sphereTotal_base (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    (f • z).1 = f • z.1 := sphereTotalMap_base Q f z

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction
