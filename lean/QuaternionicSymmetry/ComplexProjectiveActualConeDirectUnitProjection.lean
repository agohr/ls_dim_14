import QuaternionicSymmetry.ComplexProjectiveActualConeLocalUnitLaw
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeSpecializationProjections
import QuaternionicSymmetry.ComplexTorusSchemeUnit

/-! The local specialization-based identity section projects to the identity
on the genuine basic-open scheme factor of the literal product pullback. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDirectUnitProjection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeLocalUnitLaw
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeSpecializationProjections
open ComplexProjectiveActualConeBasicOpenComplexStructure
open ComplexProjectiveActualConeComplexStructure
open ComplexTorusSchemeUnit
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem specializeStandardOpen_comp_includeRight
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (specializeStandardOpen (r := r) A hA hNonempty i 1).comp
      (Algebra.TensorProduct.includeRight.toRingHom :
        HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
        TorusCoordinateRing r ⊗[ℂ]
          HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
      RingHom.id _ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  exact specializeStandardOpen_right A hA hNonempty i 1 x

theorem specializeStandardOpen_comp_includeLeft
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (specializeStandardOpen (r := r) A hA hNonempty i 1).comp
      (Algebra.TensorProduct.includeLeftRingHom :
        TorusCoordinateRing r →+*
        TorusCoordinateRing r ⊗[ℂ]
          HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) =
      (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i))).comp (evalTorus (1 : ComplexTorus r)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro t
  exact specializeStandardOpen_left A hA hNonempty i 1 t

theorem directBasicOpenUnit_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    directBasicOpenUnit (r := r) A hA hNonempty i ≫ pullback.snd _ _ =
      𝟙 (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).toScheme := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let e := directBasicOpenProductIso (r := r) A hA hNonempty i
  let k := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  have hs := directBasicOpenProductIso_hom_snd (r := r) A hA hNonempty i
  have hr := specializeStandardOpen_comp_includeRight (r := r) A hA hNonempty i
  have hs' : e.inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) ≫
        k.inv := by
    rw [← cancel_epi e.hom]
    simp only [Iso.hom_inv_id_assoc]
    simp only [← Category.assoc]
    rw [hs]
    change pullback.snd _ _ = pullback.snd _ _ ≫ k.hom ≫ k.inv
    simp
  simp only [directBasicOpenUnit, ← Category.assoc]
  rw [Category.assoc (f := k.hom ≫
    Spec.map (CommRingCat.ofHom (specializeStandardOpen (r := r) A hA hNonempty i 1)))
    (g := e.inv) (h := pullback.snd _ _), hs']
  simp only [Category.assoc]
  rw [← Category.assoc (f := Spec.map (CommRingCat.ofHom
    (specializeStandardOpen (r := r) A hA hNonempty i 1)))
    (g := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
    (h := k.inv)]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  simp

theorem directBasicOpenUnit_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    directBasicOpenUnit (r := r) A hA hNonempty i ≫ pullback.fst _ _ =
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ≫ torusUnitSpec r := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let e := directBasicOpenProductIso (r := r) A hA hNonempty i
  let k := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  have hs := directBasicOpenProductIso_hom_fst (r := r) A hA hNonempty i
  have hr := specializeStandardOpen_comp_includeLeft (r := r) A hA hNonempty i
  have hs' : e.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))) := by
    rw [← cancel_epi e.hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs.symm
  simp only [directBasicOpenUnit, ← Category.assoc]
  rw [Category.assoc (f := k.hom ≫
    Spec.map (CommRingCat.ofHom (specializeStandardOpen (r := r) A hA hNonempty i 1)))
    (g := e.inv) (h := pullback.fst _ _), hs']
  simp only [Category.assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  calc
    k.hom ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i))).comp (evalTorus (1 : ComplexTorus r)))) =
      (k.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i))))) ≫ torusUnitSpec r := by
            simp [torusUnitSpec, Category.assoc, ← Spec.map_comp,
              ← CommRingCat.ofHom_comp]
    _ = ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty) ≫ torusUnitSpec r := by
          rw [basicOpenIsoSpec_complexStructure A hA hNonempty i]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDirectUnitProjection
