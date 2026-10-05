import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic

/-! The real and complex manifold derivatives of the same map agree after
scalar restriction when its self-model charts are unchanged. -/

namespace QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction

open scoped Manifold
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem mfderiv_real_eq_complex {f : M → N} {x : M}
    (hr : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x)
    (hc : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) f x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x =
      (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x).restrictScalars ℝ := by
  rw [hr.mfderiv, hc.mfderiv]
  simp only [modelWithCornersSelf_coe]
  rw [show writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x f =
    writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,F) x f from rfl]
  simp only [Set.range_id, fderivWithin_univ]
  have hd : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,F) x f)
      ((extChartAt 𝓘(ℂ,E) x) x) := by
    simpa [modelWithCornersSelf_coe, Set.range_id, differentiableWithinAt_univ]
      using hc.differentiableWithinAt_writtenInExtChartAt
  exact hd.fderiv_restrictScalars ℝ

end
end QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction
