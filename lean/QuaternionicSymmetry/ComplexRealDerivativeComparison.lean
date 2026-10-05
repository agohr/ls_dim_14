import QuaternionicSymmetry.ComplexRealTangentAction

/-! Scalar restriction of an actual complex manifold derivative agrees with
the real manifold derivative for maps between different complex self-model
atlases. -/

namespace QuaternionicSymmetry.ComplexRealDerivativeComparison

open scoped Manifold ContDiff
noncomputable section

variable {E V M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace E M] [ChartedSpace V P]
  [IsManifold 𝓘(ℂ,E) 1 M] [IsManifold 𝓘(ℝ,E) 1 M]
  [IsManifold 𝓘(ℂ,V) 1 P] [IsManifold 𝓘(ℝ,V) 1 P]

theorem mfderiv_real_complex {f : M → P} {x : M}
    (hR : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,V) f x)
    (hC : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,V) f x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x =
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,V) f x).restrictScalars ℝ := by
  rw [hR.mfderiv, hC.mfderiv]
  simp only [modelWithCornersSelf_coe]
  rw [show writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,V) x f =
    writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,V) x f from rfl]
  simp only [Set.range_id, fderivWithin_univ]
  have hc : DifferentiableAt ℂ
      (writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,V) x f)
      ((extChartAt 𝓘(ℂ,E) x) x) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using
      hC.differentiableWithinAt_writtenInExtChartAt
  exact hc.fderiv_restrictScalars ℝ

theorem real_mfderiv_injective_of_complex {f : M → P}
    (hC : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,V) ∞ f)
    (hR : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hInj : ∀ x : M, Function.Injective
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,V) f x)) :
    ∀ x : M, Function.Injective
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x) := by
  intro x
  rw [mfderiv_real_complex
    (hR.mdifferentiable (by simp) x)
    (hC.mdifferentiable (by simp) x)]
  exact hInj x

end
end QuaternionicSymmetry.ComplexRealDerivativeComparison
