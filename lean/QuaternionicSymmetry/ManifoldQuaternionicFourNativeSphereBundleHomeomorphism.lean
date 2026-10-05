import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereForwardContinuous
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseContinuous

/-! The original quaternionic twistor sphere is genuinely homeomorphic to
the negative-Hodge unit sphere subset of an independently topologized smooth
native alternating-two-form bundle. Both total-space continuities are proved
locally from actual bundle trivializations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleHomeomorphism

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereForwardContinuous
open ManifoldQuaternionicFourNativeSphereInverseContinuous
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance

def twistorNativeSphereHomeomorph :
    TwistorSphere Q ≃ₜ NativeSphereBundleTotal Q where
  toEquiv := twistorNativeSphereEquiv Q hdim
  continuous_toFun := twistorToNativeSphere_continuous Q hdim
  continuous_invFun := nativeSphereToTwistor_continuous Q hdim

theorem twistorNativeSphereHomeomorph_projection (z : TwistorSphere Q) :
    (twistorNativeSphereHomeomorph Q hdim z).1.1 = projection Q z := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereBundleHomeomorphism
