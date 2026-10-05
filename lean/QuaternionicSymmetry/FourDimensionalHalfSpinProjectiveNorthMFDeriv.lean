import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartAt
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! The actual manifold derivatives of the projective Hopf map and of the
geometric sphere inclusion recover the checked north affine Fréchet
derivative. The source chart is the genuine independent CP¹ atlas chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthMFDeriv

open scoped Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveNorthChartAt
  FourDimensionalHalfSpinProjectiveNorthChartDerivative
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveNormalizerTransitive
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinProjectiveMobiusAction
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ComplexProjectiveTopology

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def northEuclideanDifferential : (Fin 1 → ℂ) →L[ℝ] EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    northChartDifferential

theorem north_mfderiv_chain :
    (sphereTangentMap (projectiveHopfGeometric
      ((projectiveChart 1 0).symm (0 : Fin 1 → ℂ)))).comp
      ((mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
        ((projectiveChart 1 0).symm (0 : Fin 1 → ℂ))).comp
        (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
          (projectiveChart 1 0).symm (0 : Fin 1 → ℂ))) =
      northEuclideanDifferential := by
  have hchart : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ)
      𝓘(ℝ, Fin 1 → ℂ) (projectiveChart 1 0).symm 0 := by
    rw [← north_chartAt]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Fin 1 → ℂ))
      (affineSpinorPoint 0)).mdifferentiableAt_symm (by
        rw [north_chartAt, projectiveChart_target]
        trivial)
  have hhopf : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      projectiveHopfGeometric (affineSpinorPoint 0) :=
    projectiveHopfGeometric_contMDiff.mdifferentiableAt (by simp)
  have hcoe : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanThree)
      ((↑) : geometricSphere → EuclideanThree)
      (projectiveHopfGeometric (affineSpinorPoint 0)) :=
    (contMDiff_coe_sphere (m := ∞) (n := 2)
      (E := EuclideanThree)).mdifferentiableAt (by simp)
  have hp0 : (projectiveChart 1 0).symm (0 : Fin 1 → ℂ) =
      affineSpinorPoint 0 := by
    rw [affineSpinorPoint_eq_projectiveChart]
    congr 1
    funext i
    fin_cases i
    simp
  have hhopfAt : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      projectiveHopfGeometric ((projectiveChart 1 0).symm 0) := by
    rw [hp0]
    exact hhopf
  have hcomp : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2)
      (projectiveHopfGeometric ∘ (projectiveChart 1 0).symm) 0 :=
    hhopfAt.comp 0 hchart
  have hfirst := mfderiv_comp (I := 𝓘(ℝ, Fin 1 → ℂ))
    (I' := 𝓘(ℝ, Fin 1 → ℂ)) (I'' := 𝓡 2)
    (0 : Fin 1 → ℂ) hhopfAt hchart
  have hsecond := mfderiv_comp
    (f := projectiveHopfGeometric ∘ (projectiveChart 1 0).symm)
    (g := (Subtype.val : geometricSphere → EuclideanThree))
    (I := 𝓘(ℝ, Fin 1 → ℂ))
    (I' := 𝓡 2) (I'' := 𝓘(ℝ, EuclideanThree))
    (0 : Fin 1 → ℂ) (by simpa only [Function.comp_apply, hp0] using hcoe)
      hcomp
  -- The remaining self-model derivative is exactly the chart computation.
  have hcoord :
      (fun w : Fin 1 → ℂ =>
        ((projectiveHopfGeometric ((projectiveChart 1 0).symm w) :
          geometricSphere) : EuclideanThree)) =
      (fun w => toEuclidean
        ((projectiveHopf ((projectiveChart 1 0).symm w)).1)) := rfl
  have hderiv : HasFDerivAt
      (fun w : Fin 1 → ℂ =>
        ((projectiveHopfGeometric ((projectiveChart 1 0).symm w) :
          geometricSphere) : EuclideanThree))
      northEuclideanDifferential 0 := by
    rw [hcoord]
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp
      0 projectiveHopf_chart_hasFDerivAt_north
  rw [hfirst] at hsecond
  simp only [Function.comp_apply] at hsecond
  have hleft : mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, EuclideanThree)
      (Subtype.val ∘ projectiveHopfGeometric ∘
        (projectiveChart 1 0).symm) 0 = northEuclideanDifferential := by
    rw [mfderiv_eq_fderiv]
    exact hderiv.fderiv
  simpa only [sphereTangentMap] using hsecond.symm.trans hleft

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthMFDeriv
