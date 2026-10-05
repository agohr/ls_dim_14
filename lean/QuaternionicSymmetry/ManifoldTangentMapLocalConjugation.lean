import QuaternionicSymmetry.ManifoldJointSpatialTangentContinuousAt

/-! An eventual local factorization transfers exactly to bundled
derivatives at the base point. -/
namespace QuaternionicSymmetry.ManifoldTangentMapLocalConjugation

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {F₀ H₀ X₀ F₁ H₁ X₁ F₂ H₂ X₂ F₃ H₃ X₃ : Type*}
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
  [TopologicalSpace H₀] [TopologicalSpace X₀] [ChartedSpace H₀ X₀]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [TopologicalSpace H₁] [TopologicalSpace X₁] [ChartedSpace H₁ X₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [TopologicalSpace H₂] [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [TopologicalSpace H₃] [TopologicalSpace X₃] [ChartedSpace H₃ X₃]
  {I₀ : ModelWithCorners ℝ F₀ H₀}
  {I₁ : ModelWithCorners ℝ F₁ H₁}
  {I₂ : ModelWithCorners ℝ F₂ H₂}
  {I₃ : ModelWithCorners ℝ F₃ H₃}

theorem tangentMap_eq_of_eventually_conjugate
    {a : X₀ → X₁} {b : X₁ → X₂} {c : X₂ → X₃}
    {f : X₀ → X₃} (v : TangentBundle I₀ X₀)
    (heq : f =ᶠ[nhds v.1] c ∘ b ∘ a)
    (ha : MDifferentiableAt I₀ I₁ a v.1)
    (hb : MDifferentiableAt I₁ I₂ b (a v.1))
    (hc : MDifferentiableAt I₂ I₃ c (b (a v.1))) :
    tangentMap I₀ I₃ f v =
      tangentMap I₂ I₃ c (tangentMap I₁ I₂ b (tangentMap I₀ I₁ a v)) := by
  have hpoint : f v.1 = (c ∘ b ∘ a) v.1 := heq.eq_of_nhds
  have hderiv : mfderiv I₀ I₃ f v.1 =
      mfderiv I₀ I₃ (c ∘ b ∘ a) v.1 := heq.mfderiv_eq
  have hmap : tangentMap I₀ I₃ f v =
      tangentMap I₀ I₃ (c ∘ b ∘ a) v := by
    apply Bundle.TotalSpace.ext hpoint
    exact heq_of_eq (congrArg (fun L => L v.2) hderiv)
  rw [hmap]
  have hba : MDifferentiableAt I₀ I₂ (b ∘ a) v.1 := hb.comp v.1 ha
  have houter := tangentMap_comp_at (I := I₀) (I' := I₂) (I'' := I₃)
    (f := b ∘ a) (g := c) v hc hba
  have hinner := tangentMap_comp_at (I := I₀) (I' := I₁) (I'' := I₂)
    (f := a) (g := b) v hb ha
  exact houter.trans (congrArg (tangentMap I₂ I₃ c) hinner)

end
end QuaternionicSymmetry.ManifoldTangentMapLocalConjugation
