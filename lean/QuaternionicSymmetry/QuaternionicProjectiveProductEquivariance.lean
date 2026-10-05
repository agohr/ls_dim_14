import QuaternionicSymmetry.QuaternionicProjectiveScalarEquivariance
import QuaternionicSymmetry.QuaternionicProjectiveProductMaurer

/-! Equivariance of the infinitesimal standard action under the genuine
compact product representation. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveProductEquivariance

open scoped Quaternion
open QuaternionicIsometryNormalizer
open QuaternionicUnitScalarIsometries
open QuaternionicLieAlgebraProjection
open QuaternionicProjectiveScalarEquivariance
open QuaternionicProjectiveKernelEquivariance
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardL2
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S : QuaternionicStructure E)

theorem scalar_conjugation_fixed_of_commutes (q : unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a : Fin 3 → ℝ, A * synth S a = synth S a * A) :
    conjugation (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q)) A = A := by
  let T := QuaternionicManifoldSmoothProductLifts.scalarActionLinear S (q : ℍ)
  let U := QuaternionicManifoldSmoothProductLifts.scalarActionLinear S (star (q : ℍ))
  have hcomm : A * T = T * A :=
    commutes_scalarAction_of_commutes_synth S A hA (q : ℍ)
  have hright : T * U = 1 := by
    rw [← QuaternionicProjectiveProductMaurer.scalarAction_mul,
      Quaternion.self_mul_star, normSq_one_of_unitary]
    exact QuaternionicProjectiveProductMaurer.scalarAction_one S
  change T * A * U = A
  rw [← hcomm, mul_assoc, hright, mul_one]

theorem symplecticProjection_conjugation_product
    (p : symplecticKernel S × unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    symplecticProjection S
      (conjugation (symplecticProductAction S p).1 A) =
      conjugation p.1.1.1 (symplecticProjection S A) := by
  rw [symplecticProjection_conjugation S (symplecticProductAction S p) A hA]
  change conjugation (p.1.1.1 *
      unitScalarIsometry S (p.2 : ℍ) (normSq_one_of_unitary p.2))
        (symplecticProjection S A) = _
  rw [conjugation_mul,
    scalar_conjugation_fixed_of_commutes S p.2 _ hA]

theorem scalarLineLie_conjugation_product
    (p : symplecticKernel S × unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    scalarLineLie S (conjugation (symplecticProductAction S p).1 A) =
      QuaternionicProjectiveLineMaurer.rightStar (p.2 : ℍ) *
        scalarLineLie S A *
        QuaternionicProjectiveLineMaurer.rightStar (star (p.2 : ℍ)) := by
  change scalarLineLie S (conjugation
    (p.1.1.1 * unitScalarIsometry S (p.2 : ℍ) (normSq_one_of_unitary p.2)) A) = _
  rw [conjugation_mul]
  have hAq : ∀ a, symplecticProjection S
        (conjugation (unitScalarIsometry S (p.2 : ℍ)
          (normSq_one_of_unitary p.2)) A) * synth S a =
      synth S a * symplecticProjection S
        (conjugation (unitScalarIsometry S (p.2 : ℍ)
          (normSq_one_of_unitary p.2)) A) := by
    intro a
    change symplecticProjection S
        (conjugation (unitQuaternionNormalizerAction S p.2).1 A) * synth S a =
      synth S a * symplecticProjection S
        (conjugation (unitQuaternionNormalizerAction S p.2).1 A)
    rw [symplecticProjection_conjugation S
      (unitQuaternionNormalizerAction S p.2) A hA]
    exact conjugation_commutes_synth S (unitQuaternionNormalizerAction S p.2)
      (symplecticProjection S A) hA a
  rw [scalarLineLie_conjugation_kernel S p.1 _ hAq,
    scalarLineLie_conjugation_scalar S p.2 A hA]

set_option maxHeartbeats 800000 in
theorem standardLie_conjugation_product
    (p : symplecticKernel S × unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    standardLie S (conjugation (symplecticProductAction S p).1 A) =
      (standardActionL2 S p).toContinuousLinearMap *
        standardLie S A *
        (standardActionL2 S p).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change symplecticProjection S
        (conjugation (symplecticProductAction S p).1 A) z.fst =
        p.1.1.1 (symplecticProjection S A (p.1.1.1.symm z.fst))
    rw [symplecticProjection_conjugation_product S p A hA]
    rfl
  · change scalarLineLie S
        (conjugation (symplecticProductAction S p).1 A) z.snd =
        (z.snd * (p.2 : ℍ)) *
          (-(QuaternionicProjectiveStandardLie.imaginary
            (QuaternionicLieAlgebraProjection.axialProjection
              (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))) *
            star (p.2 : ℍ)
    rw [scalarLineLie_conjugation_product S p A hA]
    simp [QuaternionicProjectiveLineMaurer.rightStar, mul_assoc,
      QuaternionicProjectiveStandardLie.scalarLineLie]

theorem standardLie_conjugation_product_inv
    (p : symplecticKernel S × unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    standardLie S (conjugation (symplecticProductAction S p).1.symm A) =
      (standardActionL2 S p).symm.toContinuousLinearMap *
        standardLie S A *
        (standardActionL2 S p).toContinuousLinearMap := by
  have h := standardLie_conjugation_product S p⁻¹ A hA
  simpa only [map_inv, Subgroup.coe_inv,
    LinearIsometryEquiv.inv_def, standardActionL2] using h

end
end QuaternionicSymmetry.QuaternionicProjectiveProductEquivariance
