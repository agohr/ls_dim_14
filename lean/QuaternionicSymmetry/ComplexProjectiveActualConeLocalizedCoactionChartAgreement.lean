import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionScalars
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoordinates

/-! The two actual overlap localization lifts agree on the entire
restricted left chart algebra, by quotient-polynomial generator extensionality. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionChartAgreement

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCoordinates
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeLocalizedCoactionLeft
open ComplexProjectiveActualConeLocalizedCoactionRight
open ComplexProjectiveActualConeLocalizedCoactionGeneratorAgreement
open ComplexProjectiveActualConeLocalizedCoactionScalars
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localizedCoactions_agree_on_left_chart
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    ∀ a : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i),
      localizedCoactionRight μ A hA hNonempty hCompact i j
        ((overlapRestrictionLeft A hA hNonempty i j) a) =
      localizedCoactionLeft μ A hA hNonempty hCompact i j
        ((overlapRestrictionLeft A hA hNonempty i j) a) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
  let e := standardOpenAlgEquiv A hA hNonempty i
  let F : (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →+*
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j) :=
    ((localizedCoactionRight μ A hA hNonempty hCompact i j).comp
      (overlapRestrictionLeft A hA hNonempty i j).toRingHom).comp e.symm.toRingHom
  let G : (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →+*
      TorusCoordinateRing r ⊗[ℂ]
        HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j) :=
    ((localizedCoactionLeft μ A hA hNonempty hCompact i j).comp
      (overlapRestrictionLeft A hA hNonempty i j).toRingHom).comp e.symm.toRingHom
  have hpoly : F.comp (Ideal.Quotient.mk (chartVanishingIdeal A i)) =
      G.comp (Ideal.Quotient.mk (chartVanishingIdeal A i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i)
          (MvPolynomial.C c)) = algebraMap ℂ _ c := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (e.commutes c).symm
      change (localizedCoactionRight μ A hA hNonempty hCompact i j)
          ((overlapRestrictionLeft A hA hNonempty i j)
            (e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c)))) =
        (localizedCoactionLeft μ A hA hNonempty hCompact i j)
          ((overlapRestrictionLeft A hA hNonempty i j)
            (e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c))))
      rw [hc, (overlapRestrictionLeft A hA hNonempty i j).commutes c]
      exact (localizedCoactions_agree_on_scalar μ A hA hNonempty hCompact i j c).symm
    · intro k
      have hk : e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i)
          (MvPolynomial.X k)) =
          coordinateFraction A hA hNonempty i (i.succAbove k) := by
        apply e.injective
        symm
        simpa [e, standardOpenAlgEquiv, coordinateFraction,
          ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv_apply] using
          standardOpenToChart_coordinate A hA hNonempty i k
      change (localizedCoactionRight μ A hA hNonempty hCompact i j)
          ((overlapRestrictionLeft A hA hNonempty i j)
            (e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.X k)))) =
        (localizedCoactionLeft μ A hA hNonempty hCompact i j)
          ((overlapRestrictionLeft A hA hNonempty i j)
            (e.symm (Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.X k))))
      rw [hk]
      exact
        localizedCoactions_agree_on_coordinateFraction
          μ A hA hNonempty hCompact i j (i.succAbove k)
  have hFG : F = G := by
    apply RingHom.ext
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact congrArg (fun h : MvPolynomial (Fin d) ℂ →+* _ => h p) hpoly
  intro a
  have h := congrArg (fun h : (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) →+* _ =>
      h (e a)) hFG
  change (localizedCoactionRight μ A hA hNonempty hCompact i j)
      ((overlapRestrictionLeft A hA hNonempty i j) (e.symm (e a))) =
    (localizedCoactionLeft μ A hA hNonempty hCompact i j)
      ((overlapRestrictionLeft A hA hNonempty i j) (e.symm (e a))) at h
  rw [e.symm_apply_apply] at h
  exact h

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedCoactionChartAgreement
