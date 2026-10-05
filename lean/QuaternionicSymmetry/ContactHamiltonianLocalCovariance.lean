import QuaternionicSymmetry.ContactHamiltonianLocalSmooth

/-! Local Hamiltonian fields glue under the actual tangent and contact-line
cocycles, and their Lie brackets preserve the contact hyperplane. -/
namespace QuaternionicSymmetry.ContactHamiltonianLocalCovariance
open ContactDeterminantAlgebra ContactExteriorDerivativeCalculus
open ContactHamiltonianAlgebra ContactHamiltonianLocalSmooth Filter
open scoped ContDiff Topology
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem section_derivative_covariance (f h : V → ℂ) (G : V → V) (g : V → ℂ) (x v : V)
    (hf : DifferentiableAt ℂ f x) (hh : DifferentiableAt ℂ h (G x))
    (hG : DifferentiableAt ℂ G x) (hg : DifferentiableAt ℂ g x)
    (he : (fun y => h (G y)) =ᶠ[𝓝 x] fun y => g y * f y) :
    fderiv ℂ h (G x) (fderiv ℂ G x v) = fderiv ℂ g x v * f x + g x * fderiv ℂ f x v := by
  have hc : fderiv ℂ (fun y => h (G y)) x = (fderiv ℂ h (G x)).comp (fderiv ℂ G x) := fderiv_comp x hh hG
  have he' := congrArg (fun A : V →L[ℂ] ℂ => A v) he.fderiv_eq
  rw [hc,fderiv_fun_mul hg hf] at he'
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,mul_comm,add_comm] using he'

theorem localSolution_covariance
    (a c : V → V →L[ℂ] ℂ) (f h : V → ℂ) (G : V → V) (g : V → ℂ) (x : V)
    (ha : DifferentiableAt ℂ a x) (hc : DifferentiableAt ℂ c (G x))
    (hf : DifferentiableAt ℂ f x) (hh : DifferentiableAt ℂ h (G x))
    (hG : ContDiffAt ℂ 2 G x) (hg : DifferentiableAt ℂ g x) (hg0 : g x ≠ 0)
    (hform : (fun y => (c (G y)).comp (fderiv ℂ G y)) =ᶠ[𝓝 x] fun y => g y • a y)
    (hsection : (fun y => h (G y)) =ᶠ[𝓝 x] fun y => g y * f y)
    (haN : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate)
    (hcN : (border (c (G x)).toLinearMap (exteriorDerivative c (G x))).Nondegenerate)
    (hInv : (fderiv ℂ G x).IsInvertible) :
    (localSolution c h (G x)).1 = fderiv ℂ G x (localSolution a f x).1 := by
  obtain ⟨T,hT⟩ := hInv
  have hTe (v : V) : T.toLinearEquiv v = fderiv ℂ G x v := congrArg (fun A : V →L[ℂ] V => A v) hT
  rw [localSolution_eq a f x haN,localSolution_eq c h (G x) hcN]
  rw [← hT]
  apply solution_covariance (a x).toLinearMap (exteriorDerivative a x) haN
    (c (G x)).toLinearMap (exteriorDerivative c (G x)) hcN T.toLinearEquiv
    (g x) (fderiv ℂ g x).toLinearMap
  · intro v
    rw [hTe]
    exact congrArg (fun A : V →L[ℂ] ℂ => A v) hform.self_of_nhds
  · intro u v
    rw [hTe,hTe]
    have h := exteriorDerivative_covariance a c G g x ha hc hG hg hform u v
    simpa only [add_sub_assoc] using h
  · exact hsection.self_of_nhds
  · intro v
    rw [hTe]
    exact section_derivative_covariance f h G g x v hf hh (hG.differentiableAt (by norm_num)) hg hsection
  · exact hg0

theorem lieBracket_horizontal
    (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (X Y : V → V) (c : ℂ) (x : V)
    (ha : DifferentiableAt ℂ a x) (hf : DifferentiableAt ℂ f x)
    (hX : DifferentiableAt ℂ X x) (hY : DifferentiableAt ℂ Y x)
    (hvalue : (fun y => a y (X y)) =ᶠ[𝓝 x] f)
    (hlevi : ∀ v, exteriorDerivative a x (X x) v + c * a x v = -fderiv ℂ f x v)
    (hYker : (fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0) :
    a x (VectorField.lieBracket ℂ X Y x) = 0 := by
  have hx := congrArg (fun T : V →L[ℂ] ℂ => T (Y x)) hvalue.fderiv_eq
  have hy := congrArg (fun T : V →L[ℂ] ℂ => T (X x)) hYker.fderiv_eq
  rw [fderiv_clm_apply ha hX] at hx
  rw [fderiv_clm_apply ha hY,fderiv_const_apply] at hy
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply] at hx hy
  have hh := hlevi (Y x)
  have hzero : a x (Y x) = 0 := hYker.self_of_nhds
  rw [hzero,mul_zero,add_zero] at hh
  simp only [exteriorDerivative_apply] at hh
  simp only [VectorField.lieBracket,map_sub]
  linear_combination hy - hx - hh

end
end QuaternionicSymmetry.ContactHamiltonianLocalCovariance
