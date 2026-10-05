import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartCoefficientSmooth
import QuaternionicSymmetry.ManifoldTwistorLocalComplexSmoothness
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor

/-! Joint smoothness of the horizontal base endomorphism in both actual
projective affine coordinates, via the ambient adapted-frame calculation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseTensorSmooth

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveChartCoefficientSmooth
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorGlobalAlmostComplex
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorSphereBundle

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private def chartSet (p : M) : Set (ℍ × ℂ) :=
  (extChartAt 𝓘(ℝ, ℍ) p).target ×ˢ Set.univ

theorem ambient_affine_base_smooth (p : M) (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun yz : ℍ × ℂ =>
        ambientBaseComplex Q p yz.1 (chartAntipodalVector i yz.2))
      (chartSet p) := by
  have hfirst : ContDiffOn ℝ ∞ (fun yz : ℍ × ℂ => yz.1) (chartSet p) :=
    contDiff_fst.contDiffOn
  have hsecond : ContDiffOn ℝ ∞
      (fun yz : ℍ × ℂ => chartAntipodalVector i yz.2) (chartSet p) :=
    (chartAntipodalVector_smooth i).contDiffOn.comp
      contDiff_snd.contDiffOn (by intro yz hyz; exact Set.mem_univ _)
  exact (ambientBaseComplex_smooth Q p).comp
    (hfirst.prodMk hsecond) (by
      intro yz hyz
      exact ⟨hyz.1, Set.mem_univ _⟩)

theorem first_base_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun yz : ℍ × ℂ => chartBaseComplex Q p yz.1
        (antipodalCoefficient (hopfSphere ![1,yz.2] (by simp))))
      (chartSet p) := by
  convert ambient_affine_base_smooth Q p 0 using 1
  funext yz
  rw [chartAntipodalVector_zero]
  rfl

theorem second_base_smooth (p : M) :
    ContDiffOn ℝ ∞
      (fun yz : ℍ × ℂ => chartBaseComplex Q p yz.1
        (antipodalCoefficient (hopfSphere ![yz.2,1] (by simp))))
      (chartSet p) := by
  convert ambient_affine_base_smooth Q p 1 using 1
  funext yz
  rw [chartAntipodalVector_one]
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBaseTensorSmooth
