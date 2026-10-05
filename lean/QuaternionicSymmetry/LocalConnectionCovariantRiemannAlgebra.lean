import QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi

/-! Algebraic symmetries retained by the covariant derivative of a genuine
torsion-free connection curvature tensor. -/
namespace QuaternionicSymmetry.LocalConnectionCovariantRiemannAlgebra
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

theorem covariantCurvatureDerivative_antisymm
    (Γ : Form (E := E) (A := E →L[ℝ] E)) (x a u v : E) :
    covariantCurvatureDerivative Γ x a u v =
      -covariantCurvatureDerivative Γ x a v u := by
  have hEq : (fun y => curvature Γ y v u) =
      fun y => -curvature Γ y u v := by
    funext y
    exact curvature_antisymm Γ y v u
  simp only [covariantCurvatureDerivative, hEq, fderiv_fun_neg,
    ContinuousLinearMap.neg_apply, curvature_antisymm Γ x v u]
  noncomm_ring

theorem covariantRiemannDerivative_antisymm
    (Γ : Form (E := E) (A := E →L[ℝ] E)) (x : E)
    (hsym : ∀ u v : E, Γ x u v = Γ x v u)
    (a u v z : E) :
    covariantRiemannDerivative Γ x a u v z =
      -covariantRiemannDerivative Γ x a v u z := by
  simp only [covariantRiemannDerivative]
  rw [covariantCurvatureDerivative_antisymm Γ x a v u,
    hsym a u, hsym a v,
    curvature_antisymm Γ x v (Γ x u a),
    curvature_antisymm Γ x (Γ x v a) u]
  simp only [ContinuousLinearMap.neg_apply]
  abel

private theorem curvature_differentiableAt
    (Γ : Form (E := E) (A := E →L[ℝ] E)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (u v : E) :
    DifferentiableAt ℝ (fun y => curvature Γ y u v) x := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have huv : DifferentiableAt ℝ (fun y => fderiv ℝ Γ y u v) x :=
    (h₂.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hvu : DifferentiableAt ℝ (fun y => fderiv ℝ Γ y v u) x :=
    (h₂.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hu : DifferentiableAt ℝ (fun y => Γ y u) x :=
    h₁.clm_apply (differentiableAt_const _)
  have hv : DifferentiableAt ℝ (fun y => Γ y v) x :=
    h₁.clm_apply (differentiableAt_const _)
  simpa only [curvature_apply] using
    ((huv.sub hvu).add ((hu.hasFDerivAt.mul' hv.hasFDerivAt).differentiableAt)).sub
      ((hv.hasFDerivAt.mul' hu.hasFDerivAt).differentiableAt)

/-- Covariant differentiation preserves the algebraic first Bianchi
identity. The local premise is only first Bianchi for the actual curvature
on a neighborhood of the point. -/
theorem covariantRiemannDerivative_first_bianchi
    (Γ : Form (E := E) (A := E →L[ℝ] E)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x)
    (hB : ∀ u v w : E,
      (fun y => curvature Γ y u v w + curvature Γ y v w u +
        curvature Γ y w u v) =ᶠ[𝓝 x] fun _ => 0)
    (a u v w : E) :
    covariantRiemannDerivative Γ x a u v w +
      covariantRiemannDerivative Γ x a v w u +
        covariantRiemannDerivative Γ x a w u v = 0 := by
  have hRuv := curvature_differentiableAt Γ x hΓ u v
  have hRvw := curvature_differentiableAt Γ x hΓ v w
  have hRwu := curvature_differentiableAt Γ x hΓ w u
  have hd := (hB u v w).fderiv_eq (𝕜 := ℝ)
  have hd₁ := hRuv.clm_apply (differentiableAt_const w)
  have hd₂ := hRvw.clm_apply (differentiableAt_const u)
  have hd₃ := hRwu.clm_apply (differentiableAt_const v)
  change fderiv ℝ
    ((fun y => curvature Γ y u v w + curvature Γ y v w u) +
      fun y => curvature Γ y w u v) x = _ at hd
  have h12 : DifferentiableAt ℝ
      (fun y => curvature Γ y u v w + curvature Γ y v w u) x :=
    hd₁.add hd₂
  rw [fderiv_add h12 hd₃] at hd
  rw [fderiv_fun_add hd₁ hd₂] at hd
  have hdA := congrArg (fun L : E →L[ℝ] E => L a) hd
  simp only [ContinuousLinearMap.add_apply] at hdA
  rw [fderiv_eval_const hRuv w a,
    fderiv_eval_const hRvw u a,
    fderiv_eval_const hRwu v a] at hdA
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply] at hdA
  -- The remaining terms are the three first-Bianchi identities with one
  -- argument replaced by the Christoffel correction.
  have hBu := (hB (Γ x a u) v w).self_of_nhds
  have hBv := (hB u (Γ x a v) w).self_of_nhds
  have hBw := (hB u v (Γ x a w)).self_of_nhds
  have hB0 := (hB u v w).self_of_nhds
  have hΓB := congrArg (Γ x a) hB0
  simp only [map_add, map_zero] at hΓB
  simp only [covariantRiemannDerivative, covariantCurvatureDerivative,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply] at *
  calc
    _ = ((fderiv ℝ (fun y => curvature Γ y u v) x a) w +
          (fderiv ℝ (fun y => curvature Γ y v w) x a) u +
          (fderiv ℝ (fun y => curvature Γ y w u) x a) v) +
        ((Γ x a) (curvature Γ x u v w) +
          (Γ x a) (curvature Γ x v w u) +
          (Γ x a) (curvature Γ x w u v)) -
        ((curvature Γ x (Γ x a u) v w +
          curvature Γ x v w (Γ x a u) +
          curvature Γ x w (Γ x a u) v) +
         (curvature Γ x u (Γ x a v) w +
          curvature Γ x (Γ x a v) w u +
          curvature Γ x w u (Γ x a v)) +
         (curvature Γ x u v (Γ x a w) +
          curvature Γ x v (Γ x a w) u +
          curvature Γ x (Γ x a w) u v)) := by abel
    _ = 0 := by rw [hdA, hΓB, hBu, hBv, hBw]; abel

end
end QuaternionicSymmetry.LocalConnectionCovariantRiemannAlgebra
