import QuaternionicSymmetry.LocalOrderedPrimitiveGauge
import QuaternionicSymmetry.LocalConnectionCoordinatePullback

/-!
Combined gauge and coordinate descent for the integrated ordered
Chern--Simons primitive. The affine connection law and homogeneous path
direction law imply the exact chart transition of the scalar primitive.
-/

namespace QuaternionicSymmetry.LocalOrderedPrimitiveGaugeCoordinate

open Filter QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalOrderedPrimitiveGauge
  QuaternionicSymmetry.LocalConnectionCoordinatePullback
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

noncomputable section

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

theorem traceOrderedTransgressionForm_gauge_coordinate
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj θi θj : Form (E := E) (A := R))
    (φ : E → E) (g h : E → R) (x : E)
    (hΓpatch : Γi =ᶠ[𝓝 x]
      transform (pullback Γj φ) g h)
    (hθpatch : θi =ᶠ[𝓝 x]
      adjointForm (pullback θj φ) g h)
    (hΓj : DifferentiableAt ℝ Γj (φ x))
    (hθj : DifferentiableAt ℝ θj (φ x))
    (hφ : ContDiffAt ℝ 2 φ x)
    (hg : ContDiffAt ℝ 2 g x) (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    traceOrderedTransgressionForm T Γi θi k x =
      (traceOrderedTransgressionForm T Γj θj k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  calc
    traceOrderedTransgressionForm T Γi θi k x =
        traceOrderedTransgressionForm T
          (pullback Γj φ) (pullback θj φ) k x := by
      exact traceOrderedTransgressionForm_transition T hT
        (pullback Γj φ) Γi (pullback θj φ) θi g h x
        hΓpatch hθpatch
        (differentiableAt_pullback Γj φ x hΓj hφ)
        (differentiableAt_pullback θj φ x hθj hφ)
        hg hh hleft hright k
    _ = _ := traceOrderedTransgressionForm_pullback
      T Γj θj φ x hΓj hθj hφ k

end
end QuaternionicSymmetry.LocalOrderedPrimitiveGaugeCoordinate
