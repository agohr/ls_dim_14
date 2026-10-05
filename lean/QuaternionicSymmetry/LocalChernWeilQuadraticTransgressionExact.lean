import QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Polynomial time integration gives an exact local quadratic transgression. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionExact

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgression
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionFTC
  QuaternionicSymmetry.LocalEndomorphismTrace
open scoped Topology

noncomputable section

private theorem integral_quadratic {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A B C : V) :
    (∫ t in (0 : ℝ)..1, A + t • B + t ^ 2 • C) =
      A + (1 / 2 : ℝ) • B + (1 / 3 : ℝ) • C := by
  have hA : IntervalIntegrable (fun _ : ℝ => A) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun t : ℝ => t • B) MeasureTheory.volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable 0 1
  have hC : IntervalIntegrable (fun t : ℝ => t ^ 2 • C) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow 2).smul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    _root_.integral_id, _root_.integral_pow]
  norm_num

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

local instance : NormedAddCommGroup (E [⋀^Fin 3]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 3]→L[ℝ] B) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance

private theorem extDeriv_integral_quadratic
    (A B₁ C : E → E [⋀^Fin 3]→L[ℝ] B) (x : E)
    (hA : DifferentiableAt ℝ A x) (hB₁ : DifferentiableAt ℝ B₁ x)
    (hC : DifferentiableAt ℝ C x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      A y + t • B₁ y + t ^ 2 • C y) x =
    ∫ t in (0 : ℝ)..1,
      extDeriv (fun y => A y + t • B₁ y + t ^ 2 • C y) x := by
  have htime : (fun y => ∫ t in (0 : ℝ)..1,
      A y + t • B₁ y + t ^ 2 • C y) =
      (fun y => A y + (1 / 2 : ℝ) • B₁ y + (1 / 3 : ℝ) • C y) := by
    funext y
    exact integral_quadratic (A y) (B₁ y) (C y)
  have htimeDeriv : (fun t : ℝ => extDeriv
      (fun y => A y + t • B₁ y + t ^ 2 • C y) x) =
      (fun t : ℝ => extDeriv A x + t • extDeriv B₁ x +
        t ^ 2 • extDeriv C x) := by
    funext t
    change extDeriv (A + t • B₁ + t ^ 2 • C) x = _
    rw [extDeriv_add (hA.add (hB₁.const_smul t))
      (hC.const_smul (t ^ 2)),
      extDeriv_add hA (hB₁.const_smul t),
      extDeriv_smul, extDeriv_smul]
  rw [htime, htimeDeriv, integral_quadratic]
  change extDeriv (A + (1 / 2 : ℝ) • B₁ + (1 / 3 : ℝ) • C) x = _
  rw [extDeriv_add (hA.add (hB₁.const_smul (1 / 2)))
    (hC.const_smul (1 / 3)),
    extDeriv_add hA (hB₁.const_smul (1 / 2)),
    extDeriv_smul, extDeriv_smul]

omit [CompleteSpace B] in
private theorem extDeriv_congr_eventually
    (ω η : E → E [⋀^Fin 3]→L[ℝ] B) (x : E)
    (h : ω =ᶠ[𝓝 x] η) : extDeriv ω x = extDeriv η x := by
  simp only [extDeriv]
  rw [h.fderiv_eq]

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance

private def transgressionA (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (y : E) : E [⋀^Fin 3]→L[ℝ] B :=
  (2 : ℝ) • wedge12 (traceProduct T) (connectionForm θ y) (curvatureForm Γ y)

private def transgressionB (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (y : E) : E [⋀^Fin 3]→L[ℝ] B :=
  (2 : ℝ) • wedge12 (traceProduct T) (connectionForm θ y)
    (covariantDerivativeForm Γ θ y)

private def transgressionC (T : R →L[ℝ] B)
    (θ : Form (E := E) (A := R)) (y : E) : E [⋀^Fin 3]→L[ℝ] B :=
  (2 : ℝ) • wedge12 (traceProduct T) (connectionForm θ y)
    (wedgeSquareForm θ y)

omit [CompleteSpace B] in
private theorem transgression_path_quadratic (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (y : E)
    (hΓ : DifferentiableAt ℝ Γ y) (hθ : DifferentiableAt ℝ θ y) (t : ℝ) :
    (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y =
      transgressionA T Γ θ y + t • transgressionB T Γ θ y +
        t ^ 2 • transgressionC T θ y := by
  ext v
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [traceConnectionCurvature, curvatureForm_path Γ θ y hΓ hθ t]
  simp only [transgressionA, transgressionB, transgressionC,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    wedge12_apply, traceProduct_apply]
  simp only [mul_add, mul_smul_comm, map_add, map_smul,
    smul_add, smul_sub]
  module

omit [CompleteSpace B] in
private theorem transgression_coeff_differentiableAt (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    DifferentiableAt ℝ (transgressionA T Γ θ) x ∧
      DifferentiableAt ℝ (transgressionB T Γ θ) x ∧
      DifferentiableAt ℝ (transgressionC T θ) x := by
  let G : ℝ → E → E [⋀^Fin 3]→L[ℝ] B := fun t y =>
    (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y
  have hG (t : ℝ) : DifferentiableAt ℝ (G t) x :=
    by
      have heq : (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ = G t := by
        funext y
        rfl
      rw [← heq]
      exact (differentiableAt_traceConnectionCurvature T (Γ + t • θ) θ x
        (hΓ.add (hθ.const_smul t))
        (hθ.differentiableAt (by norm_num))).const_smul 2
  have hdiff : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y := by
    filter_upwards [hΓ.eventually (by norm_num), hθ.eventually (by norm_num)]
      with y hΓy hθy
    exact ⟨hΓy.differentiableAt (by norm_num),
      hθy.differentiableAt (by norm_num)⟩
  have hpath (y : E) (hy : DifferentiableAt ℝ Γ y ∧
      DifferentiableAt ℝ θ y) (t : ℝ) : G t y =
      transgressionA T Γ θ y + t • transgressionB T Γ θ y +
        t ^ 2 • transgressionC T θ y :=
    transgression_path_quadratic T Γ θ y hy.1 hy.2 t
  have h0 (y : E) (hy : DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y) :
      G 0 y = transgressionA T Γ θ y := by
    simpa using hpath y hy 0
  have h1 (y : E) (hy : DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y) : G 1 y =
      transgressionA T Γ θ y + transgressionB T Γ θ y +
        transgressionC T θ y := by
    simpa using hpath y hy 1
  have hm (y : E) (hy : DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y) : G (-1) y =
      transgressionA T Γ θ y - transgressionB T Γ θ y +
        transgressionC T θ y := by
    simpa [sub_eq_add_neg] using hpath y hy (-1)
  have hA : transgressionA T Γ θ =ᶠ[𝓝 x] G 0 :=
    hdiff.mono (fun y hy => (h0 y hy).symm)
  have hB : transgressionB T Γ θ =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) • (G 1 y - G (-1) y)) := by
    filter_upwards [hdiff] with y hy
    rw [h1 y hy, hm y hy]
    module
  have hC : transgressionC T θ =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) • (G 1 y + G (-1) y) - G 0 y) := by
    filter_upwards [hdiff] with y hy
    rw [h1 y hy, hm y hy, h0 y hy]
    module
  constructor
  · exact (hG 0).congr_of_eventuallyEq hA
  constructor
  · have hh : DifferentiableAt ℝ
        (fun y => (1 / 2 : ℝ) • (G 1 y - G (-1) y)) x := by
        have heq : (1 / 2 : ℝ) • (G 1 - G (-1)) =
            (fun y => (1 / 2 : ℝ) • (G 1 y - G (-1) y)) := by
          funext y
          rfl
        rw [← heq]
        exact ((hG 1).sub (hG (-1))).const_smul (1 / 2)
    exact hh.congr_of_eventuallyEq hB
  · have hh : DifferentiableAt ℝ
        (fun y => (1 / 2 : ℝ) • (G 1 y + G (-1) y) - G 0 y) x := by
        have heq : (1 / 2 : ℝ) • (G 1 + G (-1)) - G 0 =
            (fun y => (1 / 2 : ℝ) • (G 1 y + G (-1) y) - G 0 y) := by
          funext y
          rfl
        rw [← heq]
        exact (((hG 1).add (hG (-1))).const_smul (1 / 2)).sub (hG 0)
    exact hh.congr_of_eventuallyEq hC

/-- For the affine quadratic transgression path, spatial exterior
differentiation commutes with time integration. The path is polynomial in
time, so the proof integrates its three coefficients separately. -/
theorem extDeriv_integral_traceConnectionCurvature (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y) x =
    ∫ t in (0 : ℝ)..1, (2 : ℝ) •
      extDeriv (traceConnectionCurvature T (Γ + t • θ) θ) x := by
  have hdiff : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y := by
    filter_upwards [hΓ.eventually (by norm_num), hθ.eventually (by norm_num)]
      with y hΓy hθy
    exact ⟨hΓy.differentiableAt (by norm_num),
      hθy.differentiableAt (by norm_num)⟩
  have hpath (y : E) (hy : DifferentiableAt ℝ Γ y ∧
      DifferentiableAt ℝ θ y) (t : ℝ) :
      (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y =
      transgressionA T Γ θ y + t • transgressionB T Γ θ y +
        t ^ 2 • transgressionC T θ y :=
    transgression_path_quadratic T Γ θ y hy.1 hy.2 t
  have hleft : (fun y => ∫ t in (0 : ℝ)..1,
      (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y) =ᶠ[𝓝 x]
      (fun y => ∫ t in (0 : ℝ)..1,
        transgressionA T Γ θ y + t • transgressionB T Γ θ y +
          t ^ 2 • transgressionC T θ y) := by
    filter_upwards [hdiff] with y hy
    apply intervalIntegral.integral_congr
    intro t _
    exact hpath y hy t
  have hright : (fun t : ℝ => (2 : ℝ) •
      extDeriv (traceConnectionCurvature T (Γ + t • θ) θ) x) =
      (fun t : ℝ => extDeriv (fun y =>
        transgressionA T Γ θ y + t • transgressionB T Γ θ y +
          t ^ 2 • transgressionC T θ y) x) := by
    funext t
    have hfun : (fun y =>
        transgressionA T Γ θ y + t • transgressionB T Γ θ y +
          t ^ 2 • transgressionC T θ y) =ᶠ[𝓝 x]
        (fun y => (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y) := by
      exact hdiff.mono (fun y hy => (hpath y hy t).symm)
    calc
      (2 : ℝ) • extDeriv (traceConnectionCurvature T (Γ + t • θ) θ) x =
          extDeriv (fun y => (2 : ℝ) •
            traceConnectionCurvature T (Γ + t • θ) θ y) x :=
        (extDeriv_const_smul (2 : ℝ) _ x
          (differentiableAt_traceConnectionCurvature T (Γ + t • θ) θ x
            (hΓ.add (hθ.const_smul t))
            (hθ.differentiableAt (by norm_num)))).symm
      _ = extDeriv (fun y =>
            transgressionA T Γ θ y + t • transgressionB T Γ θ y +
              t ^ 2 • transgressionC T θ y) x :=
        (extDeriv_congr_eventually _ _ x hfun).symm
  rw [hright]
  exact (extDeriv_congr_eventually _ _ x hleft).trans <|
    extDeriv_integral_quadratic
    (transgressionA T Γ θ) (transgressionB T Γ θ) (transgressionC T θ) x
    (transgression_coeff_differentiableAt T Γ θ x hΓ hθ).1
    (transgression_coeff_differentiableAt T Γ θ x hΓ hθ).2.1
    (transgression_coeff_differentiableAt T Γ θ x hΓ hθ).2.2

/-- The endpoint difference of local quadratic Chern--Weil forms is exact.
The displayed three-form is the time integral of the normalized affine
transgression integrand. -/
theorem traceSquareForm_sub_eq_extDeriv_integral (T : R →L[ℝ] B)
    (hT : ∀ p q : R, T (p * q) = T (q * p))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceSquareForm T (Γ + θ) x - traceSquareForm T Γ x =
      extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        (2 : ℝ) • traceConnectionCurvature T (Γ + t • θ) θ y) x := by
  rw [traceSquareForm_sub_eq_integral_extDeriv T hT Γ θ x hΓ hθ]
  exact (extDeriv_integral_traceConnectionCurvature T Γ θ x
    hΓ hθ).symm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Exact endpoint transgression for the actual trace of real
finite-dimensional endomorphisms. -/
theorem traceCurvatureSquare_sub_eq_extDeriv_integral
    (Γ θ : Form (E := E) (A := V →L[ℝ] V)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    traceCurvatureSquare (Γ + θ) x - traceCurvatureSquare Γ x =
      extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        (2 : ℝ) • traceConnectionCurvature traceCLM (Γ + t • θ) θ y) x :=
  traceSquareForm_sub_eq_extDeriv_integral traceCLM traceCLM_cyclic Γ θ x
    hΓ hθ

end
end QuaternionicSymmetry.LocalChernWeilQuadraticTransgressionExact
