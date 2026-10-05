import QuaternionicSymmetry.ComplexProjectiveActualConeProjLocalAction

/-! The local regular action with domain literally the scheme-theoretic
product of the torus and each standard open of the actual cone Proj. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjProductAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjChartIso
open ComplexProjectiveActualConeProjLocalAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def chartStructureMap (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme ⟶
      Spec (CommRingCat.of ℂ) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (actualProjChartIso A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap ℂ
        (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))

def actualProjChartProductIso (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (chartStructureMap A hA hNonempty i) ≅
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ
          (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i)))
  let e := actualProjChartIso A hA hNonempty i
  let m := pullback.map f (e.hom ≫ g) f g (𝟙 _) e.hom (𝟙 _)
    (by simp) (by simp)
  exact asIso m

def actualProjChartProductAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (chartStructureMap A hA hNonempty i) ⟶
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (actualProjChartProductIso (r := r) A hA hNonempty i).hom ≫
    chartProductActionToActualProj μ A hA hNonempty hCompact i

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjProductAction
