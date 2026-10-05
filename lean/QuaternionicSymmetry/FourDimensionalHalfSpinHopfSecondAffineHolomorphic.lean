import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondIndexedHorizontal
import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic
import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction

/-! The literal second affine projective inclusion is holomorphic,
including at the first-chart pole. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondAffineHolomorphic

open scoped Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  ComplexProjectiveTopology
  ManifoldComplexHolomorphicFactorization
  ComplexManifoldDerivativeScalarRestriction

noncomputable section

private theorem secondAffineSpinorPoint_eq_projectivize (z : ℂ) :
    secondAffineSpinorPoint z = projectivize 1 ![z,1] := by
  rw [projectivize_of_ne_zero 1 ![z,1] (by simp)]
  exact secondAffineSpinorPoint_mk z

theorem secondAffineSpinorPoint_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ) ∞ secondAffineSpinorPoint := by
  have hLift : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 2 → ℂ) ∞
      (fun z : ℂ => ![z,1]) := by
    have h : ContDiff ℂ ∞ (fun z : ℂ => ![z,1]) := by
      apply contDiff_pi.mpr
      intro j
      fin_cases j
      · simpa using (contDiff_id : ContDiff ℂ ∞ (id : ℂ → ℂ))
      · simpa using (contDiff_const : ContDiff ℂ ∞
          (fun _ : ℂ => (1 : ℂ)))
    exact h.contMDiff
  have hcomp : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ) ∞
      (fun z : ℂ => projectivize 1 ![z,1]) := by
    apply contMDiffOn_univ.mp
    exact (contMDiffOn_projectivize_nonzero 1).comp
      hLift.contMDiffOn (by
        intro z hz
        simp)
  exact hcomp.congr (fun z => secondAffineSpinorPoint_eq_projectivize z)

theorem secondAffineSpinorPoint_real_mfderiv_complex (z w : ℂ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) secondAffineSpinorPoint z
      (show ℂ from Complex.I • w) =
      Complex.I • (show Fin 1 → ℂ from
        mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
          secondAffineSpinorPoint z w) := by
  have hc := secondAffineSpinorPoint_holomorphic.mdifferentiableAt
    (x := z) (by simp)
  have hr := (holomorphic_is_real_smooth
    secondAffineSpinorPoint_holomorphic).mdifferentiableAt
    (x := z) (by simp)
  rw [mfderiv_real_eq_complex hr hc]
  change (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ)
      secondAffineSpinorPoint z) (Complex.I • (w : TangentSpace 𝓘(ℂ,ℂ) z)) =
    Complex.I • (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin 1 → ℂ)
      secondAffineSpinorPoint z w)
  exact map_smul _ _ _

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondAffineHolomorphic
