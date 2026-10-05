import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensor

/-! The two transported parameter inclusions are the canonical maps on
the entire tensor product, hence genuinely the affine scheme projections. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensorMap

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def firstParameterAlgHom :
    TorusCoordinateRing r →ₐ[ℂ] DoubleTorusCoordinateRing r :=
  AlgHom.mk' (firstParameter (r := r)) (by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    rw [show firstParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
      algebraMap ℂ (DoubleTorusCoordinateRing r) c from
      congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
        firstParameter_comp_algebraMap])

def secondParameterAlgHom :
    TorusCoordinateRing r →ₐ[ℂ] DoubleTorusCoordinateRing r :=
  AlgHom.mk' (secondParameter (r := r)) (by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    rw [show secondParameter (algebraMap ℂ (TorusCoordinateRing r) c) =
      algebraMap ℂ (DoubleTorusCoordinateRing r) c from
      congrArg (fun f : ℂ →+* DoubleTorusCoordinateRing r => f c)
        secondParameter_comp_algebraMap])

theorem firstParameterStandardOpen_tmul
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstParameterStandardOpen (r := r) A hA hNonempty i (t ⊗ₜ[ℂ] x) =
      (firstParameter t) ⊗ₜ[ℂ] x := by
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
  exact firstParameterStandardOpen_tmul_rep A hA hNonempty i t p

theorem secondParameterStandardOpen_tmul
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r)
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondParameterStandardOpen (r := r) A hA hNonempty i (t ⊗ₜ[ℂ] x) =
      (secondParameter t) ⊗ₜ[ℂ] x := by
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
  exact secondParameterStandardOpen_tmul_rep A hA hNonempty i t p

set_option maxRecDepth 2048 in
theorem firstParameterStandardOpen_eq_tensorMap
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstParameterStandardOpen (r := r) A hA hNonempty i =
      (Algebra.TensorProduct.map (firstParameterAlgHom (r := r))
        (AlgHom.id ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i)))).toRingHom := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro q
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => simpa using firstParameterStandardOpen_tmul A hA hNonempty i t x
  | add x y hx hy => simp [hx, hy]

set_option maxRecDepth 2048 in
theorem secondParameterStandardOpen_eq_tensorMap
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondParameterStandardOpen (r := r) A hA hNonempty i =
      (Algebra.TensorProduct.map (secondParameterAlgHom (r := r))
        (AlgHom.id ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i)))).toRingHom := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro q
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => simpa using secondParameterStandardOpen_tmul A hA hNonempty i t x
  | add x y hx hy => simp [hx, hy]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensorMap
