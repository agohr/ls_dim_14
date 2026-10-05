import QuaternionicSymmetry.LocalChernWeilOrderedDerivative
import QuaternionicSymmetry.LocalChernWeilOrderedPolynomial

/-!
# Exact local trace-power transgression in every positive degree

The ordered Chern--Simons primitive inserts the path direction in every
noncommutative curvature word. Its exterior derivative is the actual endpoint
difference, with no pointwise positivity or classification assumptions.
-/

namespace QuaternionicSymmetry.LocalChernWeilOrderedExact

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerVariation
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedPolynomial
  QuaternionicSymmetry.DifferentialFormCoefficient

noncomputable section
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

private theorem traceDegreeCast_integral [CompleteSpace B]
    {m n : ℕ} (h : m = n) (f : ℝ → E [⋀^Fin m]→L[ℝ] B) :
    traceDegreeCast h (∫ t in (0 : ℝ)..1, f t) =
      ∫ t in (0 : ℝ)..1, traceDegreeCast h (f t) := by
  cases h
  rfl

/-- The path integral of the traced ordered primitive. Its degree is one
less than the corresponding positive curvature trace power. -/
def traceOrderedTransgressionForm [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) (k : ℕ) :
    E → E [⋀^Fin (primitiveDegree k)]→L[ℝ] B := fun y =>
  ∫ t in (0 : ℝ)..1,
    T.compContinuousAlternatingMap (orderedPrimitive (Γ + t • θ) θ k y)

/-- Every positive trace power has a genuine local exact transgression
between the two endpoint connections. -/
theorem tracePowerForm_sub_eq_extDeriv_ordered [CompleteSpace B]
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    tracePowerForm T (Γ + θ) k x - tracePowerForm T Γ k x =
      traceDegreeCast (primitiveDegree_add_one k)
        (extDeriv (traceOrderedTransgressionForm T Γ θ k) x) := by
  change tracePowerForm T (Γ + θ) k x - tracePowerForm T Γ k x =
    traceDegreeCast (primitiveDegree_add_one k)
      (extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        T.compContinuousAlternatingMap
          (orderedPrimitive (Γ + t • θ) θ k y)) x)
  rw [extDeriv_integral_traceOrderedPrimitive T Γ θ k x hΓ hθ,
    traceDegreeCast_integral]
  calc
    tracePowerForm T (Γ + θ) k x - tracePowerForm T Γ k x =
      ∫ t in (0 : ℝ)..1,
        T.compContinuousAlternatingMap
          (curvaturePowerPathVariation Γ θ x t k) := by
            exact tracePowerForm_sub_eq_integral_variation T Γ θ x
              (hΓ.differentiableAt (by norm_num))
              (hθ.differentiableAt (by norm_num)) k
    _ = ∫ t in (0 : ℝ)..1,
        traceDegreeCast (primitiveDegree_add_one k)
          (extDeriv (fun y => T.compContinuousAlternatingMap
            (orderedPrimitive (Γ + t • θ) θ k y)) x) := by
          apply intervalIntegral.integral_congr
          intro t _
          have hpoint := extDeriv_traceOrderedPrimitive T hT
            (Γ + t • θ) θ k x (hΓ.add (hθ.const_smul t)) hθ
          change traceDegreeCast (primitiveDegree_add_one k)
              (extDeriv (fun y => T.compContinuousAlternatingMap
                (orderedPrimitive (Γ + t • θ) θ k y)) x) =
            T.compContinuousAlternatingMap
              (orderedCurvatureVariation (Γ + t • θ) θ x k) at hpoint
          change T.compContinuousAlternatingMap
              (curvaturePowerPathVariation Γ θ x t k) =
            traceDegreeCast (primitiveDegree_add_one k)
              (extDeriv (fun y => T.compContinuousAlternatingMap
                (orderedPrimitive (Γ + t • θ) θ k y)) x)
          rw [curvaturePowerPathVariation_eq_orderedCurvatureVariation]
          exact hpoint.symm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Specialization to the actual finite-dimensional real endomorphism trace. -/
theorem traceCurvaturePowerForm_sub_eq_extDeriv_ordered
    (Γ θ : Form (E := E) (A := V →L[ℝ] V)) (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceCurvaturePowerForm (Γ + θ) k x - traceCurvaturePowerForm Γ k x =
      traceDegreeCast (primitiveDegree_add_one k)
        (extDeriv (traceOrderedTransgressionForm
          LocalEndomorphismTrace.traceCLM Γ θ k) x) :=
  tracePowerForm_sub_eq_extDeriv_ordered
    LocalEndomorphismTrace.traceCLM
    LocalEndomorphismTrace.traceCLM_cyclic Γ θ k x hΓ hθ

end
end QuaternionicSymmetry.LocalChernWeilOrderedExact
