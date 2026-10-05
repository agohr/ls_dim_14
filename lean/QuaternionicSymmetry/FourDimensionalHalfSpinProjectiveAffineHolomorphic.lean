import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedHorizontal
import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic
import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction

/-! The literal first affine projective inclusion is holomorphic by
projectivizing its nonzero homogeneous lift.  Hence its actual real
manifold derivative is complex-linear, even where the atlas selector
chooses the other affine chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineHolomorphic

open scoped Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfAffineDerivative
  ComplexProjectiveTopology
  ManifoldComplexHolomorphicFactorization
  ComplexManifoldDerivativeScalarRestriction

noncomputable section

private theorem affineSpinorPoint_eq_projectivize (z : ℂ) :
    affineSpinorPoint z = projectivize 1 ![1,z] := by
  rw [projectivize_of_ne_zero 1 ![1,z] (by simp)]
  rfl

theorem affineSpinorPoint_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ) ∞ affineSpinorPoint := by
  have hLift : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 2 → ℂ) ∞
      (fun z : ℂ => ![1,z]) := by
    have h : ContDiff ℂ ∞ (fun z : ℂ => ![1,z]) := by
      apply contDiff_pi.mpr
      intro j
      fin_cases j
      · simpa using (contDiff_const : ContDiff ℂ ∞
          (fun _ : ℂ => (1 : ℂ)))
      · simpa using (contDiff_id : ContDiff ℂ ∞ (id : ℂ → ℂ))
    exact h.contMDiff
  have hcomp : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ) ∞
      (fun z : ℂ => projectivize 1 ![1,z]) := by
    apply contMDiffOn_univ.mp
    exact (contMDiffOn_projectivize_nonzero 1).comp
      hLift.contMDiffOn (by
        intro z hz
        simp)
  exact hcomp.congr (fun z => affineSpinorPoint_eq_projectivize z)

theorem affineSpinorPoint_real_mfderiv_complex (z w : ℂ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) affineSpinorPoint z
      (show ℂ from Complex.I • w) =
      Complex.I • (show Fin 1 → ℂ from
        mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
          affineSpinorPoint z w) := by
  have hc := affineSpinorPoint_holomorphic.mdifferentiableAt (x := z) (by simp)
  have hr := (holomorphic_is_real_smooth
    affineSpinorPoint_holomorphic).mdifferentiableAt (x := z) (by simp)
  rw [mfderiv_real_eq_complex hr hc]
  change (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ)
      affineSpinorPoint z) (Complex.I • (w : TangentSpace 𝓘(ℂ,ℂ) z)) =
    Complex.I • (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ)
      affineSpinorPoint z w)
  exact map_smul _ _ _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineHolomorphic
