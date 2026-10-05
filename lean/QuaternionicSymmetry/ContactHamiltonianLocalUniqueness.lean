import QuaternionicSymmetry.ContactHamiltonianLocalCovariance

/-! A local vector field preserving the contact hyperplane is uniquely
determined by its contraction. The proof tests its bracket against explicit
local horizontal extensions of every vector in the contact kernel. -/
namespace QuaternionicSymmetry.ContactHamiltonianLocalUniqueness
open ContactDeterminantAlgebra ContactExteriorDerivativeCalculus
open ContactHamiltonianAlgebra ContactHamiltonianLocalSmooth Filter
open scoped ContDiff Topology
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem horizontal_extension (a : V → V →L[ℂ] ℂ) (x v w : V)
    (ha : DifferentiableAt ℂ a x) (hv : a x v = 0) (hw : a x w = 1) :
    ∃ Y : V → V, DifferentiableAt ℂ Y x ∧ Y x = v ∧
      (fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0 := by
  let Y : V → V := fun y => v - ((a y v) / (a y w)) • w
  have hden : a x w ≠ 0 := by rw [hw]; exact one_ne_zero
  refine ⟨Y,?_,?_,?_⟩
  · dsimp only [Y]
    simp only [div_eq_mul_inv]
    exact (differentiableAt_const v).sub
      (show DifferentiableAt ℂ (fun y => ((a y v)/(a y w)) • w) x from
        (((ha.clm_apply (differentiableAt_const v)).mul
          (differentiableAt_inv hden |>.comp x (ha.clm_apply (differentiableAt_const w)))).smul
            (differentiableAt_const w)))
  · simp [Y,hv]
  · have he : ∀ᶠ y in 𝓝 x, a y w ≠ 0 :=
      ((ha.clm_apply (differentiableAt_const w)).continuousAt).eventually_ne hden
    filter_upwards [he] with y hy
    simp [Y,map_sub,map_smul,smul_eq_mul,div_mul_cancel₀ _ hy]

theorem levi_equation_on_kernel
    (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (X : V → V) (x : V)
    (ha : DifferentiableAt ℂ a x) (hX : DifferentiableAt ℂ X x)
    (hvalue : (fun y => a y (X y)) =ᶠ[𝓝 x] f)
    (hN : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate)
    (hcontact : ∀ Y : V → V, DifferentiableAt ℂ Y x →
      ((fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0) →
      a x (VectorField.lieBracket ℂ X Y x) = 0)
    (v : V) (hv : a x v = 0) :
    exteriorDerivative a x (X x) v = -fderiv ℂ f x v := by
  let w := (solution (a x).toLinearMap (exteriorDerivative a x) hN 1 0).1
  have hw : a x w = 1 := solution_value _ _ hN 1 0
  obtain ⟨Y,hY,hYx,hYzero⟩ := horizontal_extension a x v w ha hv hw
  have hh := hcontact Y hY hYzero
  have hx := congrArg (fun A : V →L[ℂ] ℂ => A v) hvalue.fderiv_eq
  have hy := congrArg (fun A : V →L[ℂ] ℂ => A (X x)) hYzero.fderiv_eq
  rw [fderiv_clm_apply ha hX] at hx
  rw [fderiv_clm_apply ha hY,fderiv_const_apply] at hy
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,hYx] at hx hy
  simp only [VectorField.lieBracket,map_sub,hYx] at hh
  simp only [exteriorDerivative_apply]
  linear_combination hy - hx - hh

/-- Every differentiable contact field is the constructed local Hamiltonian
of its contraction. -/
theorem eq_localSolution
    (a : V → V →L[ℂ] ℂ) (f : V → ℂ) (X : V → V) (x : V)
    (ha : DifferentiableAt ℂ a x) (hX : DifferentiableAt ℂ X x)
    (hvalue : (fun y => a y (X y)) =ᶠ[𝓝 x] f)
    (hN : (border (a x).toLinearMap (exteriorDerivative a x)).Nondegenerate)
    (hcontact : ∀ Y : V → V, DifferentiableAt ℂ Y x →
      ((fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0) →
      a x (VectorField.lieBracket ℂ X Y x) = 0) :
    X x = (localSolution a f x).1 := by
  let b := exteriorDerivative a x
  let d := fderiv ℂ f x
  let w := (solution (a x).toLinearMap b hN 1 0).1
  have hw : a x w = 1 := solution_value _ _ hN 1 0
  let c := -b (X x) w - d w
  have hEq (v : V) : b (X x) v + c * a x v = -d v := by
    have hv : a x (v - (a x v) • w) = 0 := by simp [hw]
    have hh := levi_equation_on_kernel a f X x ha hX hvalue hN hcontact _ hv
    change b (X x) (v-(a x v) • w) = -d (v-(a x v) • w) at hh
    simp only [map_sub,map_smul,smul_eq_mul] at hh
    dsimp only [c]
    linear_combination hh
  rw [localSolution_eq a f x hN]
  exact congrArg Prod.fst (solution_unique (a x).toLinearMap b hN (f x) d.toLinearMap
    (X x) c hvalue.self_of_nhds hEq)

end
end QuaternionicSymmetry.ContactHamiltonianLocalUniqueness
