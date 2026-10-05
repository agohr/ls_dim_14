import QuaternionicSymmetry.LocalChernWeilQuadratic
import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.LocalProjectiveGauge

/-! Gauge invariance of the normalized local quadratic Chern–Weil form.
The proof uses the actual curvature gauge law and cyclicity of the coefficient
functional; it does not assume that the quadratic characteristic form glues. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticGauge

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalProjectiveGauge
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalTraceSquareAlgebra
  QuaternionicSymmetry.LocalEndomorphismTrace
open scoped Topology

noncomputable section

variable {E A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

private theorem cyclic_conjugated_product
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (g h u v : A) (hgh : g * h = 1) :
    T ((h * u * g) * (h * v * g)) = T (u * v) := by
  calc
    T ((h * u * g) * (h * v * g))
        = T (h * ((u * v) * g)) := by
            congr 1
            calc
              (h * u * g) * (h * v * g) = h * u * (g * h) * v * g := by
                noncomm_ring
              _ = h * u * 1 * v * g := by rw [hgh]
              _ = h * ((u * v) * g) := by simp only [mul_one]; noncomm_ring
    _ = T (((u * v) * g) * h) := hT h _
    _ = T (u * v) := by rw [mul_assoc (u * v) g h, hgh, mul_one]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem traceSquare4_conjugation
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (F : E → E → A) (g h : A) (hgh : g * h = 1)
    (a b c d : E) :
    traceSquare4 T (fun v w => h * F v w * g) a b c d =
      traceSquare4 T F a b c d := by
  simp only [traceSquare4, map_add, map_sub]
  rw [cyclic_conjugated_product T hT g h (F a b) (F c d) hgh,
    cyclic_conjugated_product T hT g h (F a c) (F b d) hgh,
    cyclic_conjugated_product T hT g h (F a d) (F b c) hgh]

/-- The actual degree-four form is invariant under a regular local gauge
transformation with inverse lifts. -/
theorem traceSquareForm_gauge_invariant
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) :
    traceSquareForm T (transform Γ g h) x = traceSquareForm T Γ x := by
  ext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, traceSquareForm_apply T hT, traceSquareForm_apply T hT]
  have hF :
      (fun a b => curvature (transform Γ g h) x a b) =
        (fun a b => h x * curvature Γ x a b * g x) := by
    funext a b
    exact curvature_transform Γ g h x hΓ hg hh hleft hright a b
  rw [hF, traceSquare4_conjugation T hT (fun a b => curvature Γ x a b)
    (g x) (h x) hright]

/-- A local projective connection transition identifies the quadratic scalar
forms on the overlap. The transition is a germ, so no global bundle is
assumed. -/
theorem traceSquareForm_transition
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (Γi Γj : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) :
    traceSquareForm T Γj x = traceSquareForm T Γi x := by
  have hcurv : curvatureForm Γj x = curvatureForm (transform Γi g h) x := by
    ext v
    simpa only [curvatureForm_apply] using
      curvature_congr_of_germ Γj (transform Γi g h) x (v 0) (v 1) hpatch
  change wedge22 (traceProduct T) (curvatureForm Γj x) (curvatureForm Γj x) =
    traceSquareForm T Γi x
  rw [hcurv]
  exact traceSquareForm_gauge_invariant T hT Γi g h x hΓ hg hh hleft hright

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem traceCurvatureSquare_gauge_invariant
    (Γ : Form (E := E) (A := V →L[ℝ] V))
    (g h : E → V →L[ℝ] V) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) :
    traceCurvatureSquare (transform Γ g h) x =
      traceCurvatureSquare Γ x :=
  traceSquareForm_gauge_invariant traceCLM traceCLM_cyclic
    Γ g h x hΓ hg hh hleft hright

theorem traceCurvatureSquare_transition
    (Γi Γj : Form (E := E) (A := V →L[ℝ] V))
    (g h : E → V →L[ℝ] V) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) :
    traceCurvatureSquare Γj x = traceCurvatureSquare Γi x :=
  traceSquareForm_transition traceCLM traceCLM_cyclic Γi Γj
    g h x hpatch hΓ hg hh hleft hright

end
end QuaternionicSymmetry.LocalChernWeilQuadraticGauge
