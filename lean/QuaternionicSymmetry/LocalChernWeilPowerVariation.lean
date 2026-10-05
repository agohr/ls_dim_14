import QuaternionicSymmetry.LocalChernWeilTracePowers
import QuaternionicSymmetry.LocalConnectionVariation
import QuaternionicSymmetry.LocalChernWeilQuadraticFTC

/-! Ordered affine-path variation and Banach-valued endpoints for every
positive normalized curvature trace power. -/

namespace QuaternionicSymmetry.LocalChernWeilPowerVariation

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilQuadraticFTC
  QuaternionicSymmetry.ContinuousWedge

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The ordered derivative of a curvature wedge power along the affine
connection path. The recursion keeps all noncommutative coefficient terms. -/
def curvaturePowerPathVariation (Γ θ : Form (E := E) (A := R)) (x : E) (t : ℝ) :
    (k : ℕ) → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0 => covariantDerivativeForm (Γ + t • θ) θ x
  | k + 1 =>
      wedge (ContinuousLinearMap.mul ℝ R)
        (covariantDerivativeForm (Γ + t • θ) θ x)
        (curvaturePowerForm (Γ + t • θ) k x) +
      wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm (Γ + t • θ) x)
        (curvaturePowerPathVariation Γ θ x t k)

theorem curvaturePowerForm_path_hasDerivAt
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (t : ℝ) (k : ℕ) :
    HasDerivAt (fun s : ℝ => curvaturePowerForm (Γ + s • θ) k x)
      (curvaturePowerPathVariation Γ θ x t k) t := by
  induction k with
  | zero => exact curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t
  | succ k ih =>
      letI : NormedAddCommGroup
          ((E [⋀^Fin (powerDegree k)]→L[ℝ] R) →L[ℝ]
            E [⋀^Fin (2 + powerDegree k)]→L[ℝ] R) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI : NormedSpace ℝ
          ((E [⋀^Fin (powerDegree k)]→L[ℝ] R) →L[ℝ]
            E [⋀^Fin (2 + powerDegree k)]→L[ℝ] R) :=
        ContinuousLinearMap.toNormedSpace
      letI : NormedAddCommGroup
          ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ]
            (E [⋀^Fin (powerDegree k)]→L[ℝ] R) →L[ℝ]
              E [⋀^Fin (2 + powerDegree k)]→L[ℝ] R) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI : NormedSpace ℝ
          ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ]
            (E [⋀^Fin (powerDegree k)]→L[ℝ] R) →L[ℝ]
              E [⋀^Fin (2 + powerDegree k)]→L[ℝ] R) :=
        ContinuousLinearMap.toNormedSpace
      let P := ContinuousLinearMap.mul ℝ R
      let F : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
        fun s => curvatureForm (Γ + s • θ) x
      let Q : ℝ → E [⋀^Fin (powerDegree k)]→L[ℝ] R :=
        fun s => curvaturePowerForm (Γ + s • θ) k x
      let D : E [⋀^Fin 2]→L[ℝ] R :=
        covariantDerivativeForm (Γ + t • θ) θ x
      let V : E [⋀^Fin (powerDegree k)]→L[ℝ] R :=
        curvaturePowerPathVariation Γ θ x t k
      let W := wedgeCLM (E := E) (A := R) (B := R) (C := R)
        (p := 2) (q := powerDegree k) P
      have hF : HasDerivAt F D t := curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t
      have hQ : HasDerivAt Q V t := ih
      have hW : HasDerivAt (fun _ : ℝ => W) 0 t := hasDerivAt_const t W
      have hfirst : HasDerivAt (fun s => W (F s)) (W D) t := by
        simpa using (HasDerivAt.clm_apply hW hF)
      have hsecond := HasDerivAt.clm_apply hfirst hQ
      simpa only [F, Q, D, V, W, P, wedgeCLM_apply,
        curvaturePowerForm, curvaturePowerPathVariation] using hsecond

theorem continuous_curvaturePowerPathVariation
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (k : ℕ) :
    Continuous (fun t : ℝ => curvaturePowerPathVariation Γ θ x t k) := by
  have hF : Continuous (fun t : ℝ => curvatureForm (Γ + t • θ) x) :=
    continuous_iff_continuousAt.mpr fun t =>
      (curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t).continuousAt
  have hD : Continuous (fun t : ℝ => covariantDerivativeForm (Γ + t • θ) θ x) := by
    have hscalar : Continuous (fun t : ℝ => 2 * t) :=
      continuous_const.mul continuous_id
    simpa only [covariantDerivativeForm_path] using
      (continuous_const.add (hscalar.smul continuous_const))
  induction k with
  | zero => exact hD
  | succ k ih =>
      have hQ : Continuous (fun t : ℝ => curvaturePowerForm (Γ + t • θ) k x) :=
        continuous_iff_continuousAt.mpr fun t =>
          (curvaturePowerForm_path_hasDerivAt Γ θ x hΓ hθ t k).continuousAt
      let W := wedgeCLM (E := E) (A := R) (B := R) (C := R)
        (p := 2) (q := powerDegree k) (ContinuousLinearMap.mul ℝ R)
      have hW : Continuous (fun _ : ℝ => W) := continuous_const
      have hleft : Continuous (fun t => W
          (covariantDerivativeForm (Γ + t • θ) θ x)
          (curvaturePowerForm (Γ + t • θ) k x)) :=
        (hW.clm_apply hD).clm_apply hQ
      have hright : Continuous (fun t => W
          (curvatureForm (Γ + t • θ) x)
          (curvaturePowerPathVariation Γ θ x t k)) :=
        (hW.clm_apply hF).clm_apply ih
      simpa only [curvaturePowerPathVariation, W, wedgeCLM_apply] using
        hleft.add hright

/-- The path derivative after applying an arbitrary continuous coefficient
functional. Cyclicity is only needed later, when ordered terms are combined. -/
theorem tracePowerForm_path_hasDerivAt (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (t : ℝ) (k : ℕ) :
    HasDerivAt (fun s : ℝ => tracePowerForm T (Γ + s • θ) k x)
      (T.compContinuousAlternatingMap (curvaturePowerPathVariation Γ θ x t k)) t := by
  let L := (ContinuousLinearMap.compContinuousAlternatingMapCLM
    (ι := Fin (powerDegree k)) ℝ E R B) T
  have hL : HasDerivAt (fun _ : ℝ => L) 0 t := hasDerivAt_const t L
  have hP := curvaturePowerForm_path_hasDerivAt Γ θ x hΓ hθ t k
  simpa [tracePowerForm, DifferentialFormCoefficient.mapForm, L] using
    (HasDerivAt.clm_apply hL hP)

/-- The actual local endpoint difference is the time integral of its
ordered first variation in every positive degree. -/
theorem tracePowerForm_sub_eq_integral_variation [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x)
    (k : ℕ) :
    tracePowerForm T (Γ + θ) k x - tracePowerForm T Γ k x =
      ∫ t in (0 : ℝ)..1,
        T.compContinuousAlternatingMap (curvaturePowerPathVariation Γ θ x t k) := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ => tracePowerForm T (Γ + s • θ) k x)
        (T.compContinuousAlternatingMap (curvaturePowerPathVariation Γ θ x t k)) t :=
    tracePowerForm_path_hasDerivAt T Γ θ x hΓ hθ t k
  have hcont : Continuous (fun t : ℝ =>
      T.compContinuousAlternatingMap (curvaturePowerPathVariation Γ θ x t k)) := by
    exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM
      (ι := Fin (powerDegree k)) ℝ E R B) T).continuous.comp
        (continuous_curvaturePowerPathVariation Γ θ x hΓ hθ k)
  have h := endpoint_sub_eq_integral
    (fun s : ℝ => tracePowerForm T (Γ + s • θ) k x)
    (fun t : ℝ => T.compContinuousAlternatingMap
      (curvaturePowerPathVariation Γ θ x t k)) hderiv hcont
  have hz : Γ + (0 : ℝ) • θ = Γ := by
    ext y v
    simp [Pi.smul_apply]
  have ho : Γ + (1 : ℝ) • θ = Γ + θ := by simp
  simpa only [hz, ho] using h

end
end QuaternionicSymmetry.LocalChernWeilPowerVariation
