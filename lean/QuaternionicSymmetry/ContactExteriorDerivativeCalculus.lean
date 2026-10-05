import QuaternionicSymmetry.ContactDeterminantAlgebra
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Coordinate exterior differentiation of a contact one-form. The formulas
include changes of coordinates and of local line trivialization. -/
namespace QuaternionicSymmetry.ContactExteriorDerivativeCalculus
open Filter
open scoped Topology ContDiff
noncomputable section
variable {K V : Type*} [RCLike K] [NormedAddCommGroup V] [NormedSpace K V]

/-- Antisymmetrization of the derivative of a local one-form. -/
def exteriorDerivative (a : V → V →L[K] K) (x : V) : LinearMap.BilinForm K V :=
  LinearMap.mk₂ K (fun u v => fderiv K a x u v - fderiv K a x v u)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (by intros; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)

@[simp] theorem exteriorDerivative_apply (a : V → V →L[K] K) (x u v : V) :
    exteriorDerivative a x u v = fderiv K a x u v - fderiv K a x v u := rfl

theorem exteriorDerivative_alt (a : V → V →L[K] K) (x : V) :
    (exteriorDerivative a x).IsAlt := by intro u; simp

/-- The Levi form agrees, up to sign, with the exterior derivative on
horizontal vector fields. -/
theorem exteriorDerivative_horizontal (a : V → V →L[K] K) (X Y : V → V) (x : V)
    (ha : DifferentiableAt K a x) (hX : DifferentiableAt K X x)
    (hY : DifferentiableAt K Y x)
    (haX : (fun y => a y (X y)) =ᶠ[𝓝 x] fun _ => 0)
    (haY : (fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0) :
    exteriorDerivative a x (X x) (Y x) = -a x (VectorField.lieBracket K X Y x) := by
  have hx := congrArg (fun T : V →L[K] K => T (Y x)) haX.fderiv_eq
  have hy := congrArg (fun T : V →L[K] K => T (X x)) haY.fderiv_eq
  rw [fderiv_clm_apply ha hX, fderiv_const_apply] at hx
  rw [fderiv_clm_apply ha hY, fderiv_const_apply] at hy
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hx hy
  simp only [exteriorDerivative_apply, VectorField.lieBracket, map_sub]
  linear_combination hy - hx

/-- Differentiating the local contact-form transformation law. -/
theorem oneForm_covariance_derivative
    (a c : V → V →L[K] K) (G : V → V) (g : V → K) (x : V)
    (ha : DifferentiableAt K a x) (hc : DifferentiableAt K c (G x))
    (hG : ContDiffAt K 2 G x) (hg : DifferentiableAt K g x)
    (hcov : (fun y => (c (G y)).comp (fderiv K G y)) =ᶠ[𝓝 x]
      fun y => g y • a y) (u v : V) :
    fderiv K c (G x) (fderiv K G x u) (fderiv K G x v) +
      c (G x) (fderiv K (fderiv K G) x u v) =
      fderiv K g x u * a x v + g x * fderiv K a x u v := by
  have hG₁ := hG.differentiableAt (by norm_num)
  have hG₂ := (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcG : DifferentiableAt K (fun y => c (G y)) x := hc.comp x hG₁
  have hd := congrArg (fun T : V →L[K] (V →L[K] K) => T u v) hcov.fderiv_eq
  have hcomp : fderiv K (fun y => c (G y)) x =
      (fderiv K c (G x)).comp (fderiv K G x) := fderiv_comp x hc hG₁
  rw [fderiv_clm_comp hcG hG₂, fderiv_fun_smul hg ha, hcomp] at hd
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, add_comm] using hd

/-- The symmetric Hessian cancels, leaving precisely the line-gauge term. -/
theorem exteriorDerivative_covariance
    (a c : V → V →L[K] K) (G : V → V) (g : V → K) (x : V)
    (ha : DifferentiableAt K a x) (hc : DifferentiableAt K c (G x))
    (hG : ContDiffAt K 2 G x) (hg : DifferentiableAt K g x)
    (hcov : (fun y => (c (G y)).comp (fderiv K G y)) =ᶠ[𝓝 x]
      fun y => g y • a y) (u v : V) :
    exteriorDerivative c (G x) (fderiv K G x u) (fderiv K G x v) =
      g x * exteriorDerivative a x u v +
        (fderiv K g x u * a x v - fderiv K g x v * a x u) := by
  have huv := oneForm_covariance_derivative a c G g x ha hc hG hg hcov u v
  have hvu := oneForm_covariance_derivative a c G g x ha hc hG hg hcov v u
  have hsym := hG.isSymmSndFDerivAt (by norm_num)
  rw [hsym.eq v u] at hvu
  simp only [exteriorDerivative_apply]
  linear_combination huv - hvu

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A polynomial local density, free of any choice of a symplectic basis. -/
def determinantDensity (e : Module.Basis ι K V) (a : V → V →L[K] K) (x : V) : K :=
  (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
    (ContactDeterminantAlgebra.border (a x).toLinearMap (exteriorDerivative a x))).det

theorem determinantDensity_contDiffAt (e : Module.Basis ι K V)
    (a : V → V →L[K] K) (x : V) (ha : ContDiffAt K ∞ a x) :
    ContDiffAt K ∞ (determinantDensity e a) x := by
  classical
  let b := e.prod (Module.Basis.singleton Unit K)
  let A := fun y => LinearMap.BilinForm.toMatrix b
    (ContactDeterminantAlgebra.border (a y).toLinearMap (exteriorDerivative a y))
  have hd : ContDiffAt K ∞ (fderiv K a) x := ha.fderiv_right (by simp)
  have hentry (i j : ι ⊕ Unit) : ContDiffAt K ∞ (fun y => A y i j) x := by
    simp only [A, LinearMap.BilinForm.toMatrix_apply,
      ContactDeterminantAlgebra.border_apply, exteriorDerivative_apply]
    change ContDiffAt K ∞ (fun y =>
      fderiv K a y (b i).1 (b j).1 - fderiv K a y (b j).1 (b i).1 +
        (b i).2 * a y (b j).1 - (b j).2 * a y (b i).1) x
    exact (((hd.clm_apply contDiffAt_const).clm_apply contDiffAt_const).sub
      ((hd.clm_apply contDiffAt_const).clm_apply contDiffAt_const)).add
      (contDiffAt_const.mul (ha.clm_apply contDiffAt_const)) |>.sub
      (contDiffAt_const.mul (ha.clm_apply contDiffAt_const))
  have hprod (σ : Equiv.Perm (ι ⊕ Unit)) (s : Finset (ι ⊕ Unit)) :
      ContDiffAt K ∞ (fun y => ∏ i ∈ s, A y (σ i) i) x := by
    induction s using Finset.induction with
    | empty => simpa using (contDiffAt_const : ContDiffAt K ∞ (fun _ : V => (1 : K)) x)
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using (hentry (σ i) i).mul ih
  change ContDiffAt K ∞ (fun y => (A y).det) x
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun σ _ => contDiffAt_const.mul (hprod σ Finset.univ))

/-- The determinant density is a section of the squared contact canonical
relation: the tangent Jacobian occurs squared. -/
theorem determinantDensity_covariance [FiniteDimensional K V]
    (e : Module.Basis ι K V) (a c : V → V →L[K] K)
    (G : V → V) (g : V → K) (x : V)
    (ha : DifferentiableAt K a x) (hc : DifferentiableAt K c (G x))
    (hG : ContDiffAt K 2 G x) (hg : DifferentiableAt K g x) (hg0 : g x ≠ 0)
    (hcov : (fun y => (c (G y)).comp (fderiv K G y)) =ᶠ[𝓝 x]
      fun y => g y • a y) :
    (fderiv K G x).det ^ 2 * determinantDensity e c (G x) =
      g x ^ (Fintype.card ι + 1) * determinantDensity e a x := by
  apply ContactDeterminantAlgebra.border_det_covariance e
    (a x).toLinearMap (c (G x)).toLinearMap (fderiv K g x).toLinearMap
    (exteriorDerivative a x) (exteriorDerivative c (G x))
    (fderiv K G x).toLinearMap (g x) hg0
  · exact congrArg ContinuousLinearMap.toLinearMap hcov.self_of_nhds
  · apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact exteriorDerivative_covariance a c G g x ha hc hG hg hcov u v

end
end QuaternionicSymmetry.ContactExteriorDerivativeCalculus
