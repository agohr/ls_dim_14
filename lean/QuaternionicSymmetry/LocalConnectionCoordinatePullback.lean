import QuaternionicSymmetry.LocalChernWeilTracePowers
import QuaternionicSymmetry.LocalTracePowerGauge
import QuaternionicSymmetry.LocalChernWeilOrderedExact

/-!
Coordinate naturality of local curvature and all normalized trace powers.
The coordinate map acts by its actual Fréchet derivative on every tangent
argument. This is the coordinate half of a manifold gauge descent proof.
-/

namespace QuaternionicSymmetry.LocalConnectionCoordinatePullback

open Filter
open scoped Topology
open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalChernWeilOrderedPolynomial
  QuaternionicSymmetry.ContinuousWedge

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

noncomputable section

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- Pullback of a local connection one-form along a chart transition. -/
def pullback (Γ : Form (E := E) (A := R)) (φ : E → E) :
    Form (E := E) (A := R) :=
  fun y => (Γ (φ y)).comp (fderiv ℝ φ y)

theorem connectionForm_pullback (Γ : Form (E := E) (A := R))
    (φ : E → E) :
    connectionForm (pullback Γ φ) =
      fun y => (connectionForm Γ (φ y)).compContinuousLinearMap
        (fderiv ℝ φ y) := by
  funext y
  ext v
  rfl

theorem differentiableAt_pullback (Γ : Form (E := E) (A := R))
    (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x)) (hφ : ContDiffAt ℝ 2 φ x) :
    DifferentiableAt ℝ (pullback Γ φ) x := by
  have hcoeff := hΓ.comp x (hφ.differentiableAt (by norm_num))
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hcoeff.clm_comp hD

theorem wedgeSquareForm_pullback (Γ : Form (E := E) (A := R))
    (φ : E → E) (x : E) :
    wedgeSquareForm (pullback Γ φ) x =
      (wedgeSquareForm Γ (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  ext v
  simp only [wedgeSquareForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    QuaternionicSymmetry.LocalConnection.wedgeSquare_apply,
    pullback, ContinuousLinearMap.comp_apply, Function.comp_def]

theorem curvatureForm_pullback (Γ : Form (E := E) (A := R))
    (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x)) (hφ : ContDiffAt ℝ 2 φ x) :
    curvatureForm (pullback Γ φ) x =
      (curvatureForm Γ (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  rw [curvatureForm_eq_extDeriv_add (pullback Γ φ) x
    (differentiableAt_pullback Γ φ x hΓ hφ)]
  rw [curvatureForm_eq_extDeriv_add Γ (φ x) hΓ]
  rw [connectionForm_pullback Γ φ]
  rw [extDeriv_pullback (by
      exact ((oneFormMap (E := E) (A := R)).differentiableAt.comp (φ x) hΓ))
      hφ (by norm_num)]
  rw [wedgeSquareForm_pullback]
  ext v
  simp only [ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]

private theorem wedge_compContinuousLinearMap {p q : ℕ}
    (L : E →L[ℝ] E)
    (a : E [⋀^Fin p]→L[ℝ] R) (b : E [⋀^Fin q]→L[ℝ] R) :
    ContinuousAlternatingMap.compContinuousLinearMap
      (wedge (ContinuousLinearMap.mul ℝ R) a b) L =
      wedge (ContinuousLinearMap.mul ℝ R)
        (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [wedge_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

private theorem degreeCast_compContinuousLinearMap {a b : ℕ}
    (h : a = b) (eta : E [⋀^Fin a]→L[ℝ] R)
    (L : E →L[ℝ] E) :
    (degreeCast h eta).compContinuousLinearMap L =
      degreeCast h (eta.compContinuousLinearMap L) := by
  cases h
  rfl

/-- Every ordered curvature wedge power commutes with a genuine coordinate
pullback. -/
theorem curvaturePowerForm_pullback (Γ : Form (E := E) (A := R))
    (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (k : ℕ) :
    curvaturePowerForm (pullback Γ φ) k x =
      (curvaturePowerForm Γ k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  induction k with
  | zero => exact curvatureForm_pullback Γ φ x hΓ hφ
  | succ k ih =>
      change wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm (pullback Γ φ) x)
        (curvaturePowerForm (pullback Γ φ) k x) = _
      rw [curvatureForm_pullback Γ φ x hΓ hφ, ih]
      exact (wedge_compContinuousLinearMap (fderiv ℝ φ x)
        (curvatureForm Γ (φ x)) (curvaturePowerForm Γ k (φ x))).symm

/-- A continuous coefficient trace preserves coordinate pullback of all
positive curvature powers. -/
theorem tracePowerForm_pullback {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R))
    (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    (k : ℕ) :
    tracePowerForm T (pullback Γ φ) k x =
      (tracePowerForm T Γ k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  change T.compContinuousAlternatingMap
    (curvaturePowerForm (pullback Γ φ) k x) =
      (T.compContinuousAlternatingMap
        (curvaturePowerForm Γ k (φ x))).compContinuousLinearMap
          (fderiv ℝ φ x)
  rw [curvaturePowerForm_pullback Γ φ x hΓ hφ k]
  ext v
  rfl

/-- Ordered Chern--Simons words respect genuine coordinate pullback,
including every occurrence of the path direction one-form. -/
theorem orderedPrimitive_pullback
    (Γ θ : Form (E := E) (A := R)) (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x))
    (hφ : ContDiffAt ℝ 2 φ x) (k : ℕ) :
    orderedPrimitive (pullback Γ φ) (pullback θ φ) k x =
      (orderedPrimitive Γ θ k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  induction k with
  | zero =>
      exact congrFun (connectionForm_pullback θ φ) x
  | succ k ih =>
      change degreeCast
          (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl)
          (wedge (ContinuousLinearMap.mul ℝ R)
            (connectionForm (pullback θ φ) x)
            (curvaturePowerForm (pullback Γ φ) k x)) +
        degreeCast (primitiveDegree_succ_cast k)
          (wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureForm (pullback Γ φ) x)
            (orderedPrimitive (pullback Γ φ) (pullback θ φ) k x)) = _
      rw [congrFun (connectionForm_pullback θ φ) x,
        curvaturePowerForm_pullback Γ φ x hΓ hφ k,
        curvatureForm_pullback Γ φ x hΓ hφ, ih]
      rw [← wedge_compContinuousLinearMap,
        ← wedge_compContinuousLinearMap]
      rw [← degreeCast_compContinuousLinearMap,
        ← degreeCast_compContinuousLinearMap]
      ext v
      rfl

theorem pullback_path (Γ θ : Form (E := E) (A := R))
    (φ : E → E) (t : ℝ) :
    pullback (Γ + t • θ) φ = pullback Γ φ + t • pullback θ φ := by
  funext x
  ext v
  simp only [pullback, Pi.add_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]

private theorem traceOrdered_path_intervalIntegrable {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (x : E) (hΓ : DifferentiableAt ℝ Γ x)
    (hθ : DifferentiableAt ℝ θ x) (k : ℕ) :
    IntervalIntegrable
      (fun t : ℝ => T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k x))
      MeasureTheory.volume 0 1 := by
  have hpath : (fun t : ℝ => T.compContinuousAlternatingMap
      (orderedPrimitive (Γ + t • θ) θ k x)) =
    fun t => T.compContinuousAlternatingMap
      (∑ w : PrimitiveWordIndex k,
        t ^ primitiveWordExponent k w • primitivePathCoeff Γ θ k w x) := by
    funext t
    rw [orderedPrimitive_path_sum Γ θ x hΓ hθ t k]
  rw [hpath]
  apply Continuous.intervalIntegrable
  let F := ContinuousLinearMap.compContinuousAlternatingMapCLM
    (ι := Fin (primitiveDegree k)) ℝ E R B T
  change Continuous (fun t : ℝ => F
    (∑ w : PrimitiveWordIndex k,
      t ^ primitiveWordExponent k w • primitivePathCoeff Γ θ k w x))
  apply F.continuous.comp
  fun_prop

/-- Coordinate pullback commutes with the integrated ordered primitive. -/
theorem traceOrderedTransgressionForm_pullback {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (φ : E → E) (x : E)
    (hΓ : DifferentiableAt ℝ Γ (φ x))
    (hθ : DifferentiableAt ℝ θ (φ x))
    (hφ : ContDiffAt ℝ 2 φ x) (k : ℕ) :
    traceOrderedTransgressionForm T (pullback Γ φ)
        (pullback θ φ) k x =
      (traceOrderedTransgressionForm T Γ θ k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  let L := ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ι := Fin (primitiveDegree k)) (G := B) (fderiv ℝ φ x)
  have hInt := traceOrdered_path_intervalIntegrable T Γ θ (φ x) hΓ hθ k
  change (∫ t in (0 : ℝ)..1,
    T.compContinuousAlternatingMap
      (orderedPrimitive
        (pullback Γ φ + t • pullback θ φ) (pullback θ φ) k x)) =
    L (∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k (φ x)))
  rw [← L.intervalIntegral_comp_comm hInt]
  apply intervalIntegral.integral_congr
  intro t _
  change T.compContinuousAlternatingMap
    (orderedPrimitive
      (pullback Γ φ + t • pullback θ φ) (pullback θ φ) k x) =
    L (T.compContinuousAlternatingMap
      (orderedPrimitive (Γ + t • θ) θ k (φ x)))
  rw [← pullback_path Γ θ φ t,
    orderedPrimitive_pullback (Γ + t • θ) θ φ x
      (hΓ.add (hθ.const_smul t)) hφ k]
  ext v
  rfl

/-- The chart-transition law for Chern--Weil trace powers follows from an
actual affine gauge law for local connections and the chart derivative.
Here `g,h` form inverse gauge lifts near the point. -/
theorem tracePowerForm_gauge_coordinate {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj : Form (E := E) (A := R))
    (φ : E → E) (g h : E → R) (x : E)
    (hpatch : Γi =ᶠ[𝓝 x]
      QuaternionicSymmetry.LocalConnectionGauge.transform
        (pullback Γj φ) g h)
    (hΓj : DifferentiableAt ℝ Γj (φ x))
    (hφ : ContDiffAt ℝ 2 φ x)
    (hg : ContDiffAt ℝ 2 g x) (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    tracePowerForm T Γi k x =
      (tracePowerForm T Γj k (φ x)).compContinuousLinearMap
        (fderiv ℝ φ x) := by
  calc
    tracePowerForm T Γi k x =
        tracePowerForm T (pullback Γj φ) k x := by
      exact QuaternionicSymmetry.LocalTracePowerGauge.tracePowerForm_transition
        T hT (pullback Γj φ) Γi g h x hpatch
        (differentiableAt_pullback Γj φ x hΓj hφ)
        hg hh hleft hright k
    _ = _ := tracePowerForm_pullback T Γj φ x hΓj hφ k

end
end QuaternionicSymmetry.LocalConnectionCoordinatePullback
