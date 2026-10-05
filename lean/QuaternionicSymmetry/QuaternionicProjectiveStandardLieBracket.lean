import QuaternionicSymmetry.QuaternionicProjectiveStandardLie
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionBracket

/-! The quaternionic-line part of the standard infinitesimal action obeys
the Lie bracket with the right-action sign dictated by the group action. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket

open QuaternionicProjectiveStandardLie
  QuaternionicLieAlgebraProjection
  ManifoldQuaternionicRankThreeOrientation
  ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Quaternion
noncomputable section

theorem imaginary_cross (a b : Fin 3 → ℝ) :
    imaginary ((2 : ℝ) • crossProduct a b) =
      imaginary a * imaginary b - imaginary b * imaginary a := by
  ext <;> simp [
    crossProduct, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem axial_synth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (S : QuaternionicStructure E) (a : Fin 3 → ℝ) :
    axialProjection (adjointRepresentation S (synth S a)) = a := by
  ext i
  fin_cases i <;>
    simp [axialProjection, axialLinear,
      QuaternionicLieAlgebraProjection.adjointRepresentation_synth,
      crossProduct, Pi.basisFun_apply]

theorem scalarLineLie_synth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (S : QuaternionicStructure E) (a : Fin 3 → ℝ) (w : ℍ) :
    scalarLineLie S (synth S a) w = w * -(imaginary a) := by
  simp [scalarLineLie, axial_synth]

theorem scalarLineLie_bracket_synth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (S : QuaternionicStructure E) (a b : Fin 3 → ℝ) :
    scalarLineLie S (synth S a * synth S b - synth S b * synth S a) =
      scalarLineLie S (synth S a) * scalarLineLie S (synth S b) -
        scalarLineLie S (synth S b) * scalarLineLie S (synth S a) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [synth_commutator_cross]
  rw [← map_smul (synth S)]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    scalarLineLie_synth]
  rw [imaginary_cross]
  noncomm_ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem scalarLineLie_scalarProjection (S : QuaternionicStructure E)
    (A : E →L[ℝ] E) :
    scalarLineLie S (scalarProjection S A) = scalarLineLie S A := by
  apply ContinuousLinearMap.ext
  intro w
  simp [scalarLineLie, scalarProjection, axial_synth]

theorem scalarLineLie_bracket (S : QuaternionicStructure E)
    (A B : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A)
    (hB : ∀ a, symplecticProjection S B * synth S a =
      synth S a * symplecticProjection S B) :
    scalarLineLie S (A * B - B * A) =
      scalarLineLie S A * scalarLineLie S B -
        scalarLineLie S B * scalarLineLie S A := by
  rw [← scalarLineLie_scalarProjection S (A * B - B * A),
    scalarProjection_commutator S A B hA hB]
  change scalarLineLie S (synth S _ * synth S _ - synth S _ * synth S _) = _
  rw [scalarLineLie_bracket_synth]
  change scalarLineLie S (scalarProjection S A) *
      scalarLineLie S (scalarProjection S B) -
    scalarLineLie S (scalarProjection S B) *
      scalarLineLie S (scalarProjection S A) = _
  rw [scalarLineLie_scalarProjection, scalarLineLie_scalarProjection]

theorem symplecticProjection_bracket (S : QuaternionicStructure E)
    (A B : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A)
    (hB : ∀ a, symplecticProjection S B * synth S a =
      synth S a * symplecticProjection S B) :
    symplecticProjection S (A * B - B * A) =
      symplecticProjection S A * symplecticProjection S B -
        symplecticProjection S B * symplecticProjection S A := by
  have hAB : symplecticProjection S A * scalarProjection S B =
      scalarProjection S B * symplecticProjection S A := hA _
  have hBA : symplecticProjection S B * scalarProjection S A =
      scalarProjection S A * symplecticProjection S B := hB _
  have heqA : A = symplecticProjection S A + scalarProjection S A :=
    (projection_sum S A).symm
  have heqB : B = symplecticProjection S B + scalarProjection S B :=
    (projection_sum S B).symm
  have hcomm : A * B - B * A =
      (symplecticProjection S A * symplecticProjection S B -
        symplecticProjection S B * symplecticProjection S A) +
      (scalarProjection S A * scalarProjection S B -
        scalarProjection S B * scalarProjection S A) := by
    have h1 := congrArg₂ (fun X Y : E →L[ℝ] E => X * Y) heqA heqB
    have h2 := congrArg₂ (fun X Y : E →L[ℝ] E => X * Y) heqB heqA
    change A * B = _ at h1
    change B * A = _ at h2
    rw [h1, h2]
    simp only [add_mul, mul_add]
    rw [hAB, hBA]
    abel
  change A * B - B * A - scalarProjection S (A * B - B * A) = _
  rw [scalarProjection_commutator S A B hA hB, hcomm]
  abel

theorem standardLie_bracket (S : QuaternionicStructure E)
    (A B : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A)
    (hB : ∀ a, symplecticProjection S B * synth S a =
      synth S a * symplecticProjection S B) :
    standardLie S (A * B - B * A) =
      standardLie S A * standardLie S B -
        standardLie S B * standardLie S A := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change symplecticProjection S (A * B - B * A) z.fst =
      (symplecticProjection S A * symplecticProjection S B -
        symplecticProjection S B * symplecticProjection S A) z.fst
    exact congrArg (fun T : E →L[ℝ] E => T z.fst)
      (symplecticProjection_bracket S A B hA hB)
  · change scalarLineLie S (A * B - B * A) z.snd =
      (scalarLineLie S A * scalarLineLie S B -
        scalarLineLie S B * scalarLineLie S A) z.snd
    exact congrArg (fun T : ℍ →L[ℝ] ℍ => T z.snd)
      (scalarLineLie_bracket S A B hA hB)

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket
