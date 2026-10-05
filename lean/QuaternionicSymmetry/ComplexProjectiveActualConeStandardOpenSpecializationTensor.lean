import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCounit
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula

/-! Identifies the transported homogeneous standard-open specialization with
literal torus evaluation on pure tensors. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSpecializationTensor

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartFamilyTensorFormula
open ComplexProjectiveDiagonalChartFamilySpecialization
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCounit
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem specializeStandardOpen_tmul
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (t : TorusCoordinateRing r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    specializeStandardOpen (r := r) A hA hNonempty i z (t ⊗ₜ[ℂ] x) =
      (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i)) (evalTorus z t)) * x := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((standardOpenEquiv A hA hNonempty i) x)
  have hx : x = (standardOpenEquiv A hA hNonempty i).symm
      (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
    rw [hp]
    exact ((standardOpenEquiv A hA hNonempty i).symm_apply_apply x).symm
  rw [hx]
  have hfam :
      baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
      Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) := by
    apply (chartFamilyProductRingEquiv (r := r) A i).injective
    rw [chartFamilyProductRingEquiv_baseChanged]
    simp only [baseChangedStandardOpenFamilyEquiv, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply]
    change baseChangedStandardOpenEquiv (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
      t ⊗ₜ[ℂ] Ideal.Quotient.mk (chartVanishingIdeal A i) p
    simp [baseChangedStandardOpenEquiv, standardOpenAlgEquiv,
      Algebra.TensorProduct.congr_apply]
  change (standardOpenEquiv A hA hNonempty i).symm
    (specializeChartQuotient A i z
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p)))) = _
  rw [hfam, specializeChartQuotient_mk]
  have hmap :
      ((MvPolynomial.map (evalTorus z)).comp
        (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)))) =
      RingHom.id (MvPolynomial (Fin d) ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [evalTorus]
    · intro k
      simp
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  have hpmap := congrArg (fun f : MvPolynomial (Fin d) ℂ →+* _ => f p) hmap
  simp only [RingHom.comp_apply, RingHom.id_apply] at hpmap
  rw [hpmap, MvPolynomial.C_mul']
  rw [Algebra.smul_def, map_mul]
  change (standardOpenEquiv A hA hNonempty i).symm
      ((algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)
        (evalTorus z t)) * Ideal.Quotient.mk (chartVanishingIdeal A i) p) = _
  rw [map_mul]
  change (standardOpenAlgEquiv A hA hNonempty i).symm
        (algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)
          (evalTorus z t)) *
      (standardOpenAlgEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p) = _
  rw [(standardOpenAlgEquiv A hA hNonempty i).symm.commutes]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSpecializationTensor
