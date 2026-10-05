import QuaternionicSymmetry.ComplexSmoothRealDerivativeField
import QuaternionicSymmetry.ComplexSmoothRealInfinity
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! A real-smooth map between complex manifold atlases is holomorphic
when its actual real manifold derivative commutes with multiplication by i.
The proof uses true chart derivatives, not a supplied holomorphic map. -/

namespace QuaternionicSymmetry.ComplexManifoldRealSmoothCriterion

open scoped Manifold ContDiff
open ComplexSmoothRealDerivativeField ComplexSmoothRealInfinity
noncomputable section

variable {E F : Type} {M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [IsManifold 𝓘(ℝ,F) ∞ N] [IsManifold 𝓘(ℂ,F) ∞ N]

theorem mdifferentiable_of_real_complex_derivative (f : M → N)
    (hReal : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) f)
    (hI : ∀ (x : M) (v : E),
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v)) :
    MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) f := by
  intro x
  let g := writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x f
  let c := (extChartAt 𝓘(ℝ,E) x) x
  have hDiff : DifferentiableAt ℝ g c := by
    simpa [g,c,modelWithCornersSelf_coe,differentiableWithinAt_univ] using
      (hReal x).differentiableWithinAt_writtenInExtChartAt
  have hDeriv : fderiv ℝ g c = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x := by
    simpa [g,c,modelWithCornersSelf_coe,fderivWithin_univ] using
      (hReal x).mfderiv.symm
  have hIg (v : E) : fderiv ℝ g c (Complex.I • v) =
      Complex.I • fderiv ℝ g c v := by
    rw [hDeriv]
    exact hI x v
  have hC : DifferentiableAt ℂ g c :=
    (differentiableAt_iff_restrictScalars ℝ hDiff).2
      ⟨complexifyCommutingMap (fderiv ℝ g c) hIg,
        complexifyCommutingMap_restrictScalars (fderiv ℝ g c) hIg⟩
  apply (mdifferentiableAt_iff (I := 𝓘(ℂ,E)) (I' := 𝓘(ℂ,F)) f x).2
  refine ⟨(hReal x).continuousAt, ?_⟩
  have heq : writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x f =
      writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,F) x f := rfl
  simpa [g,c,heq,modelWithCornersSelf_coe,differentiableWithinAt_univ] using hC

theorem contMDiff_of_real_complex_derivative (f : M → N)
    (hReal : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hI : ∀ (x : M) (v : E),
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v)) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f := by
  have hC := mdifferentiable_of_real_complex_derivative f
    (hReal.mdifferentiable (by simp)) hI
  obtain ⟨hcont,hRealCharts⟩ := contMDiff_iff.mp hReal
  obtain ⟨_,hComplexCharts⟩ := mdifferentiable_iff.mp hC
  apply contMDiff_iff.mpr
  refine ⟨hcont, ?_⟩
  intro x y
  let s : Set E := (extChartAt 𝓘(ℂ,E) x).target ∩
    (extChartAt 𝓘(ℂ,E) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ,F) y).source)
  have hs : IsOpen s := by
    apply (continuousOn_extChartAt_symm (I := 𝓘(ℂ,E)) x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℂ,E)) x)
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ,F)) y).preimage hcont
  exact contDiffOn_infty_of_real_complex hs (hRealCharts x y) (hComplexCharts x y)

end
end QuaternionicSymmetry.ComplexManifoldRealSmoothCriterion
