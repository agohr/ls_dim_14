import QuaternionicSymmetry.LocalChernWeilCubicForm
import QuaternionicSymmetry.LocalChernWeilQuadraticVariation
import QuaternionicSymmetry.LocalChernWeilQuadraticFTC

/-!
# First variation and endpoint of the local cubic trace form

This proves the actual time derivative of the normalized six-form
`T(F ∧ F ∧ F)` along an affine path of local connections.  The three ordered
terms are retained, so no cyclicity or graded commutativity is assumed.
The endpoint identity follows by the Banach-valued fundamental theorem of
calculus.  Exterior exactness is a separate Chern--Weil argument.
-/

namespace QuaternionicSymmetry.LocalChernWeilCubicVariation

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticVariation
  QuaternionicSymmetry.LocalChernWeilQuadraticFTC
  QuaternionicSymmetry.LocalChernWeilCubicForm

noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 6]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 6]→L[ℝ] B) := inferInstance

/-- The ordered three-term first variation of the normalized cubic trace form. -/
def traceCubePathIntegrand (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E) (t : ℝ) :
    E [⋀^Fin 6]→L[ℝ] B :=
  let F := curvatureForm (Γ + t • θ) x
  let D := covariantDerivativeForm (Γ + t • θ) θ x
  wedge24 (traceProduct T) D (wedge22 (ContinuousLinearMap.mul ℝ R) F F) +
    wedge24 (traceProduct T) F
      (wedge22 (ContinuousLinearMap.mul ℝ R) D F +
        wedge22 (ContinuousLinearMap.mul ℝ R) F D)

/-- Actual time derivative of `T(F ∧ F ∧ F)`.  The spatial connection forms
need only be differentiable at the fixed point for this path derivative. -/
theorem traceCubeForm_path_hasDerivAt (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => traceCubeForm T (Γ + s • θ) x)
      (traceCubePathIntegrand T Γ θ x t) t := by
  let F : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun s => curvatureForm (Γ + s • θ) x
  let D : E [⋀^Fin 2]→L[ℝ] R :=
    covariantDerivativeForm (Γ + t • θ) θ x
  let G : ℝ → E [⋀^Fin 4]→L[ℝ] R :=
    fun s => wedge22 (ContinuousLinearMap.mul ℝ R) (F s) (F s)
  let W := wedge24CLM (E := E) (A := R) (B := R) (C := B) (traceProduct T)
  have hF : HasDerivAt F D t :=
    curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t
  have hG : HasDerivAt G
      (wedge22 (ContinuousLinearMap.mul ℝ R) D (F t) +
        wedge22 (ContinuousLinearMap.mul ℝ R) (F t) D) t := by
    simpa only [G, F, D] using
      wedge22_curvature_path_hasDerivAt (ContinuousLinearMap.mul ℝ R)
        Γ θ x hΓ hθ t
  have hW : HasDerivAt (fun _ : ℝ => W) 0 t := hasDerivAt_const t W
  have hfirst : HasDerivAt (fun s => W (F s)) (W D) t := by
    simpa using (HasDerivAt.clm_apply
      (F := E [⋀^Fin 2]→L[ℝ] R)
      (G := (E [⋀^Fin 4]→L[ℝ] R) →L[ℝ] E [⋀^Fin 6]→L[ℝ] B)
      hW hF)
  have hsecond := HasDerivAt.clm_apply
    (F := E [⋀^Fin 4]→L[ℝ] R)
    (G := E [⋀^Fin 6]→L[ℝ] B) hfirst hG
  change HasDerivAt
      (fun s => wedge24 (traceProduct T) (F s) (G s))
      (wedge24 (traceProduct T) D (G t) +
        wedge24 (traceProduct T) (F t)
          (wedge22 (ContinuousLinearMap.mul ℝ R) D (F t) +
            wedge22 (ContinuousLinearMap.mul ℝ R) (F t) D)) t at hsecond
  have htrace (s : ℝ) :
      traceCubeForm T (Γ + s • θ) x =
        wedge24 (traceProduct T) (F s) (G s) := rfl
  have hint :
      traceCubePathIntegrand T Γ θ x t =
        wedge24 (traceProduct T) D (G t) +
          wedge24 (traceProduct T) (F t)
            (wedge22 (ContinuousLinearMap.mul ℝ R) D (F t) +
              wedge22 (ContinuousLinearMap.mul ℝ R) (F t) D) := by
    simp only [traceCubePathIntegrand, F, D, G]
  simpa only [htrace, hint] using hsecond

theorem traceCubeForm_path_deriv (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceCubeForm T (Γ + s • θ) x) t =
      traceCubePathIntegrand T Γ θ x t :=
  (traceCubeForm_path_hasDerivAt T Γ θ x hΓ hθ t).deriv

theorem continuous_traceCubePathIntegrand (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    Continuous (traceCubePathIntegrand T Γ θ x) := by
  let F : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun t => curvatureForm (Γ + t • θ) x
  let D : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun t => covariantDerivativeForm (Γ + t • θ) θ x
  let G : ℝ → E [⋀^Fin 4]→L[ℝ] R :=
    fun t => wedge22 (ContinuousLinearMap.mul ℝ R) (F t) (F t)
  let W := wedge24CLM (E := E) (A := R) (B := R) (C := B) (traceProduct T)
  let U := wedge22CLM (E := E) (A := R) (B := R) (C := R)
    (ContinuousLinearMap.mul ℝ R)
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun t =>
    (curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t).continuousAt
  have hscalar : Continuous (fun t : ℝ => 2 * t) :=
    continuous_const.mul continuous_id
  have hD : Continuous D := by
    have h : Continuous (fun t : ℝ =>
        covariantDerivativeForm Γ θ x + (2 * t) • wedgeSquareForm θ x) :=
      continuous_const.add (hscalar.smul continuous_const)
    simpa only [D, covariantDerivativeForm_path] using h
  have hG : Continuous G := by
    simpa only [G, U, wedge22CLM_apply] using
      ((continuous_const.clm_apply hF).clm_apply hF :
        Continuous (fun t => U (F t) (F t)))
  have hleft : Continuous (fun t => W (D t) (G t)) :=
    (continuous_const.clm_apply hD).clm_apply hG
  have hright : Continuous (fun t =>
      W (F t) (U (D t) (F t) + U (F t) (D t))) :=
    (continuous_const.clm_apply hF).clm_apply
      (((continuous_const.clm_apply hD).clm_apply hF).add
        ((continuous_const.clm_apply hF).clm_apply hD))
  have h := hleft.add hright
  have hint (t : ℝ) :
      traceCubePathIntegrand T Γ θ x t =
        W (D t) (G t) + W (F t)
          (U (D t) (F t) + U (F t) (D t)) := by
    simp only [traceCubePathIntegrand, W, U, F, D, G,
      wedge24CLM_apply, wedge22CLM_apply]
  have hfun : traceCubePathIntegrand T Γ θ x =
      (fun t => W (D t) (G t) + W (F t)
        (U (D t) (F t) + U (F t) (D t))) :=
    funext hint
  rw [hfun]
  exact h

/-- Banach-valued endpoint identity for the actual cubic characteristic
six-form.  The integrand is the proved three-term variation above. -/
theorem traceCubeForm_path_integral [CompleteSpace B] (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    traceCubeForm T (Γ + θ) x - traceCubeForm T Γ x =
      ∫ t in (0 : ℝ)..1, traceCubePathIntegrand T Γ θ x t := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s => traceCubeForm T (Γ + s • θ) x)
        (traceCubePathIntegrand T Γ θ x t) t :=
    traceCubeForm_path_hasDerivAt T Γ θ x hΓ hθ
  have h := endpoint_sub_eq_integral
    (fun s : ℝ => traceCubeForm T (Γ + s • θ) x)
    (traceCubePathIntegrand T Γ θ x) hderiv
    (continuous_traceCubePathIntegrand T Γ θ x hΓ hθ)
  have hz : Γ + (0 : ℝ) • θ = Γ := by
    ext y v
    simp [Pi.smul_apply]
  have ho : Γ + (1 : ℝ) • θ = Γ + θ := by simp
  simpa only [hz, ho] using h

end
end QuaternionicSymmetry.LocalChernWeilCubicVariation
