import QuaternionicSymmetry.LocalChernWeilOrderedExact
import QuaternionicSymmetry.LocalTracePowerGauge

/-!
Gauge covariance of the complete ordered Chern--Simons primitive. This
covers all inserted path-direction terms, not just one chosen ordering.
-/

namespace QuaternionicSymmetry.LocalOrderedPrimitiveGauge

open Filter QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalTracePowerGauge
  QuaternionicSymmetry.LocalContinuousWedgeGauge
  QuaternionicSymmetry.ContinuousWedge
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

noncomputable section

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

private theorem conjugateForm_add {m : ℕ} (g h : R)
    (a b : E [⋀^Fin m]→L[ℝ] R) :
    conjugateForm g h (a + b) =
      conjugateForm g h a + conjugateForm g h b := by
  ext v
  simp only [conjugateForm_apply, ContinuousAlternatingMap.add_apply,
    mul_add, add_mul]

private theorem conjugateForm_degreeCast {m n : ℕ} (e : m = n)
    (g h : R) (a : E [⋀^Fin m]→L[ℝ] R) :
    conjugateForm g h (degreeCast e a) =
      degreeCast e (conjugateForm g h a) := by
  cases e
  rfl

/-- An affine gauge law for the connection and homogeneous adjoint law for
its path direction conjugate every ordered primitive word. -/
theorem orderedPrimitive_transition
    (Γi Γj θi θj : Form (E := E) (A := R))
    (g h : E → R) (x : E)
    (hΓpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hθpatch : θj =ᶠ[𝓝 x] adjointForm θi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    orderedPrimitive Γj θj k x =
      conjugateForm (g x) (h x) (orderedPrimitive Γi θi k x) := by
  have hθ : connectionForm θj x =
      conjugateForm (g x) (h x) (connectionForm θi x) := by
    ext v
    have hp := hθpatch.eq_of_nhds
    have hv := congrArg (fun f : E →L[ℝ] R => f (v 0)) hp
    simpa only [connectionForm, oneFormMap_apply, adjointForm_apply,
      conjugateForm_apply] using hv
  have hF : curvatureForm Γj x =
      conjugateForm (g x) (h x) (curvatureForm Γi x) := by
    exact curvaturePowerForm_transition Γi Γj g h x hΓpatch
      hΓ hg hh hleft hright 0
  induction k with
  | zero => exact hθ
  | succ k ih =>
      have hpow := curvaturePowerForm_transition Γi Γj g h x hΓpatch
        hΓ hg hh hleft hright k
      change degreeCast
          (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl)
          (wedge (ContinuousLinearMap.mul ℝ R)
            (connectionForm θj x) (curvaturePowerForm Γj k x)) +
        degreeCast (primitiveDegree_succ_cast k)
          (wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureForm Γj x) (orderedPrimitive Γj θj k x)) = _
      rw [hθ, hpow, hF, ih]
      rw [← conjugateForm_wedge_mul (g x) (h x) hright,
        ← conjugateForm_wedge_mul (g x) (h x) hright]
      rw [← conjugateForm_degreeCast, ← conjugateForm_degreeCast]
      exact (conjugateForm_add (g x) (h x) _ _).symm

/-- A cyclic trace removes gauge conjugation from the ordered primitive. -/
theorem traceOrderedPrimitive_transition
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj θi θj : Form (E := E) (A := R))
    (g h : E → R) (x : E)
    (hΓpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hθpatch : θj =ᶠ[𝓝 x] adjointForm θi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    T.compContinuousAlternatingMap (orderedPrimitive Γj θj k x) =
      T.compContinuousAlternatingMap (orderedPrimitive Γi θi k x) := by
  rw [orderedPrimitive_transition Γi Γj θi θj g h x
    hΓpatch hθpatch hΓ hg hh hleft hright k]
  exact cyclic_conjugateForm T hT (g x) (h x) hright _

/-- The complete integrated ordered Chern--Simons primitive is invariant
under a fixed gauge change along the affine connection path. -/
theorem traceOrderedTransgressionForm_transition [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj θi θj : Form (E := E) (A := R))
    (g h : E → R) (x : E)
    (hΓpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hθpatch : θj =ᶠ[𝓝 x] adjointForm θi g h)
    (hΓ : DifferentiableAt ℝ Γi x)
    (hθ : DifferentiableAt ℝ θi x)
    (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    traceOrderedTransgressionForm T Γj θj k x =
      traceOrderedTransgressionForm T Γi θi k x := by
  change (∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γj + t • θj) θj k x)) =
    ∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γi + t • θi) θi k x)
  apply intervalIntegral.integral_congr
  intro t _
  have hpath : Γj + t • θj =ᶠ[𝓝 x]
      transform (Γi + t • θi) g h := by
    filter_upwards [hΓpatch, hθpatch] with y hgy hty
    rw [Pi.add_apply, Pi.smul_apply, hgy, hty]
    exact (congrFun (transform_path Γi θi g h t) y).symm
  exact traceOrderedPrimitive_transition T hT
    (Γi + t • θi) (Γj + t • θj) θi θj g h x
    hpath hθpatch (hΓ.add (hθ.const_smul t))
    hg hh hleft hright k

end
end QuaternionicSymmetry.LocalOrderedPrimitiveGauge
