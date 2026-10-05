import QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
import QuaternionicSymmetry.LocalPolynomialTransgressionIntegral

/-!
# Finite polynomial structure of affine curvature powers

The curvature of `Γ + t θ` is quadratic in time.  Repeated normalized wedges
therefore give finite time polynomials in every curvature degree.  This file
keeps the index of each ordered coefficient explicit, so noncommutative
products are never silently collected or reordered.
-/

namespace QuaternionicSymmetry.LocalChernWeilPowerPolynomial

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalPolynomialTransgressionIntegral
  QuaternionicSymmetry.ContinuousWedge

noncomputable section
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedSpace

/-- The three ordered coefficients of affine-path curvature. -/
def curvatureBaseCoeff (Γ θ : Form (E := E) (A := R))
    (i : Fin 3) : E → E [⋀^Fin 2]→L[ℝ] R :=
  if i = 0 then curvatureForm Γ
  else if i = 1 then covariantDerivativeForm Γ θ
  else wedgeSquareForm θ

theorem curvatureForm_path_sum (Γ θ : Form (E := E) (A := R))
    (y : E) (hΓ : DifferentiableAt ℝ Γ y)
    (hθ : DifferentiableAt ℝ θ y) (t : ℝ) :
    curvatureForm (Γ + t • θ) y =
      ∑ i : Fin 3, t ^ i.val • curvatureBaseCoeff Γ θ i y := by
  rw [curvatureForm_path Γ θ y hΓ hθ t]
  simp [Fin.sum_univ_succ, curvatureBaseCoeff]
  abel

/-- All three coefficient fields are differentiable from local C² data. -/
theorem differentiableAt_curvatureBaseCoeff
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x)
    (i : Fin 3) :
    DifferentiableAt ℝ (curvatureBaseCoeff Γ θ i) x := by
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hθ₁ : DifferentiableAt ℝ θ x := hθ.differentiableAt (by norm_num)
  have hDΓ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDθ : DifferentiableAt ℝ (fderiv ℝ θ) x :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  fin_cases i
  · simpa [curvatureBaseCoeff] using
      differentiableAt_curvatureForm Γ x hΓ₁ hDΓ
  · change DifferentiableAt ℝ (covariantDerivativeForm Γ θ) x
    exact (alternatingPartCLM (E := E) (A := R)).differentiableAt.comp x
      ((hDθ.add (differentiableAt_product Γ θ x hΓ₁ hθ₁)).add
        (differentiableAt_product θ Γ x hθ₁ hΓ₁))
  · change DifferentiableAt ℝ (wedgeSquareForm θ) x
    exact (alternatingPartCLM (E := E) (A := R)).differentiableAt.comp x
      (differentiableAt_product θ θ x hθ₁ hθ₁)

/-- Bilinearity expands two finite time polynomials without reordering any
coefficient products. -/
theorem wedge_sum_sum {p q : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (P : R →L[ℝ] R →L[ℝ] R)
    (a : ι → ℝ) (b : κ → ℝ)
    (α : ι → E [⋀^Fin p]→L[ℝ] R)
    (β : κ → E [⋀^Fin q]→L[ℝ] R) :
    wedge P (∑ i, a i • α i) (∑ j, b j • β j) =
      ∑ i, ∑ j, (a i * b j) • wedge P (α i) (β j) := by
  let W := wedgeCLM (E := E) (A := R) (B := R) (C := R)
    (p := p) (q := q) P
  change W (∑ i, a i • α i) (∑ j, b j • β j) = _
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [W, wedgeCLM_apply, mul_comm]

/-- An ordered word of quadratic affine-path coefficient choices. -/
def TimeWordIndex : ℕ → Type
  | 0 => Fin 3
  | k + 1 => Fin 3 × TimeWordIndex k

instance timeWordIndexFintype : (k : ℕ) → Fintype (TimeWordIndex k)
  | 0 => by
      change Fintype (Fin 3)
      infer_instance
  | k + 1 => by
      letI := timeWordIndexFintype k
      dsimp [TimeWordIndex]
      infer_instance

/-- The time exponent of one ordered coefficient word. -/
def timeWordExponent : (k : ℕ) → TimeWordIndex k → ℕ
  | 0, i => i.val
  | k + 1, (i, w) => i.val + timeWordExponent k w

/-- Its ordered coefficient in the normalized curvature wedge power. -/
def curvaturePowerPathCoeff (Γ θ : Form (E := E) (A := R)) :
    (k : ℕ) → TimeWordIndex k →
      E → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0, i => curvatureBaseCoeff Γ θ i
  | k + 1, (i, w) => fun y =>
      wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureBaseCoeff Γ θ i y)
        (curvaturePowerPathCoeff Γ θ k w y)

theorem differentiableAt_curvaturePowerPathCoeff
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x)
    (k : ℕ) (w : TimeWordIndex k) :
    DifferentiableAt ℝ (curvaturePowerPathCoeff Γ θ k w) x := by
  induction k with
  | zero =>
      exact differentiableAt_curvatureBaseCoeff Γ θ x hΓ hθ w
  | succ k ih =>
      obtain ⟨i, w⟩ := w
      exact differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureBaseCoeff Γ θ i)
        (curvaturePowerPathCoeff Γ θ k w) x
        (differentiableAt_curvatureBaseCoeff Γ θ x hΓ hθ i) (ih w)

/-- Every ordered curvature power is a finite time polynomial.  Duplicate
exponents are deliberately retained as separate coefficient words. -/
theorem curvaturePowerForm_path_sum (Γ θ : Form (E := E) (A := R))
    (y : E) (hΓ : DifferentiableAt ℝ Γ y)
    (hθ : DifferentiableAt ℝ θ y) (t : ℝ) (k : ℕ) :
    curvaturePowerForm (Γ + t • θ) k y =
      ∑ w : TimeWordIndex k,
        t ^ timeWordExponent k w • curvaturePowerPathCoeff Γ θ k w y := by
  induction k with
  | zero =>
      simpa only [curvaturePowerForm, TimeWordIndex,
        timeWordExponent, curvaturePowerPathCoeff] using
        curvatureForm_path_sum Γ θ y hΓ hθ t
  | succ k ih =>
      change wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm (Γ + t • θ) y)
        (curvaturePowerForm (Γ + t • θ) k y) = _
      rw [curvatureForm_path_sum Γ θ y hΓ hθ t, ih]
      rw [wedge_sum_sum]
      simp only [TimeWordIndex, Fintype.sum_prod_type,
        timeWordExponent, curvaturePowerPathCoeff, pow_add]

/-- A scalar transgression coefficient for each ordered curvature word. -/
def transgressionPathCoeff (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (w : TimeWordIndex k) :
    E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B := fun y =>
  wedge (traceProduct T) (connectionForm θ y)
    (curvaturePowerPathCoeff Γ θ k w y)

theorem differentiableAt_transgressionPathCoeff
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (x : E) (hΓ : ContDiffAt ℝ 2 Γ x)
    (hθ : ContDiffAt ℝ 2 θ x) (k : ℕ) (w : TimeWordIndex k) :
    DifferentiableAt ℝ (transgressionPathCoeff T Γ θ k w) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x
      (hθ.differentiableAt (by norm_num))
  exact differentiableAt_wedge (traceProduct T)
    (connectionForm θ) (curvaturePowerPathCoeff Γ θ k w)
    x hθform
    (differentiableAt_curvaturePowerPathCoeff Γ θ x hΓ hθ k w)

/-- The normalized all-degree transgression integrand has an explicit finite
time-polynomial expansion at every point of spatial differentiability. -/
theorem traceConnectionCurvaturePower_path_sum
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (y : E) (hΓ : DifferentiableAt ℝ Γ y)
    (hθ : DifferentiableAt ℝ θ y) (t : ℝ) (k : ℕ) :
    traceConnectionCurvaturePower T (Γ + t • θ) θ k y =
      ∑ w : TimeWordIndex k,
        t ^ timeWordExponent k w • transgressionPathCoeff T Γ θ k w y := by
  let W := wedgeCLM (E := E) (A := R) (B := R) (C := B)
    (p := 1) (q := powerDegree k) (traceProduct T)
      (connectionForm θ y)
  change W (curvaturePowerForm (Γ + t • θ) k y) = _
  rw [curvaturePowerForm_path_sum Γ θ y hΓ hθ t k]
  simp only [map_sum, map_smul, W, wedgeCLM_apply,
    transgressionPathCoeff]

private theorem extDeriv_congr_eventually {p : ℕ}
    (ω η : E → E [⋀^Fin p]→L[ℝ] B) (x : E)
    (h : ω =ᶠ[𝓝 x] η) : extDeriv ω x = extDeriv η x := by
  simp only [extDeriv]
  rw [h.fderiv_eq]

/-- For every ordered curvature power, spatial exterior differentiation
commutes with the time integral of its actual transgression form.  The proof
uses the finite time-polynomial expansion and local C² regularity, not a
general differentiation-under-integral assumption. -/
theorem extDeriv_integral_traceConnectionCurvaturePower [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      traceConnectionCurvaturePower T (Γ + t • θ) θ k y) x =
    ∫ t in (0 : ℝ)..1,
      extDeriv (traceConnectionCurvaturePower T (Γ + t • θ) θ k) x := by
  let A : TimeWordIndex k →
      E → E [⋀^Fin (1 + powerDegree k)]→L[ℝ] B :=
    transgressionPathCoeff T Γ θ k
  let degree : TimeWordIndex k → ℕ := timeWordExponent k
  have hA : ∀ w ∈ (Finset.univ : Finset (TimeWordIndex k)),
      DifferentiableAt ℝ (A w) x := by
    intro w _
    exact differentiableAt_transgressionPathCoeff T Γ θ x hΓ hθ k w
  have hpoly :=
    LocalPolynomialTransgressionIntegral.extDeriv_integral_weighted_polynomial
      (Finset.univ : Finset (TimeWordIndex k)) degree A x hA
  have hdiff : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y := by
    filter_upwards [hΓ.eventually (by norm_num), hθ.eventually (by norm_num)]
      with y hΓy hθy
    exact ⟨hΓy.differentiableAt (by norm_num),
      hθy.differentiableAt (by norm_num)⟩
  have hpath (y : E) (hy : DifferentiableAt ℝ Γ y ∧
      DifferentiableAt ℝ θ y) (t : ℝ) :
      traceConnectionCurvaturePower T (Γ + t • θ) θ k y =
        ∑ w : TimeWordIndex k, t ^ degree w • A w y :=
    traceConnectionCurvaturePower_path_sum T Γ θ y hy.1 hy.2 t k
  have hleft : (fun y => ∫ t in (0 : ℝ)..1,
      traceConnectionCurvaturePower T (Γ + t • θ) θ k y) =ᶠ[𝓝 x]
      (fun y => ∫ t in (0 : ℝ)..1,
        ∑ w : TimeWordIndex k, t ^ degree w • A w y) := by
    filter_upwards [hdiff] with y hy
    apply intervalIntegral.integral_congr
    intro t _
    exact hpath y hy t
  have hright (t : ℝ) :
      extDeriv (traceConnectionCurvaturePower T (Γ + t • θ) θ k) x =
        extDeriv (fun y =>
          ∑ w : TimeWordIndex k, t ^ degree w • A w y) x := by
    apply extDeriv_congr_eventually
    exact hdiff.mono (fun y hy => hpath y hy t)
  calc
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        traceConnectionCurvaturePower T (Γ + t • θ) θ k y) x =
      extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        ∑ w : TimeWordIndex k, t ^ degree w • A w y) x :=
        extDeriv_congr_eventually _ _ x hleft
    _ = ∫ t in (0 : ℝ)..1,
        extDeriv (fun y =>
          ∑ w : TimeWordIndex k, t ^ degree w • A w y) x := hpoly
    _ = ∫ t in (0 : ℝ)..1,
        extDeriv (traceConnectionCurvaturePower T (Γ + t • θ) θ k) x := by
      congr 1
      funext t
      exact (hright t).symm

end
end QuaternionicSymmetry.LocalChernWeilPowerPolynomial
