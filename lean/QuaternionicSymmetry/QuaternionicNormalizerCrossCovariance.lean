import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthMFDeriv
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation

/-! The fixed-model orthogonal normalizer preserves the quaternionic
coefficient cross product, not just the Euclidean dot product. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerCrossCovariance

open QuaternionicIsometryNormalizer
  ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

theorem rotation_cross (g : normalizer S) (a b : Fin 3 → ℝ) :
    rotationLinear S g (crossProduct a b) =
      crossProduct (rotationLinear S g a) (rotationLinear S g b) := by
  let R := rotationLinear S g
  have h : (2 : ℝ) • synth S (R (crossProduct a b)) =
      (2 : ℝ) • synth S (crossProduct (R a) (R b)) := by
    calc
      _ = conjugation g.1 ((2 : ℝ) • synth S (crossProduct a b)) := by
        rw [map_smul, synth_rotationLinear]
      _ = conjugation g.1
          (synth S a * synth S b - synth S b * synth S a) := by
        rw [synth_commutator_cross]
      _ = conjugation g.1 (synth S a) * conjugation g.1 (synth S b) -
          conjugation g.1 (synth S b) * conjugation g.1 (synth S a) := by
        ext v
        simp [conjugation_apply, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.sub_apply]
      _ = synth S (R a) * synth S (R b) -
          synth S (R b) * synth S (R a) := by
        rw [synth_rotationLinear, synth_rotationLinear]
      _ = _ := synth_commutator_cross S (R a) (R b)
  have h' := (smul_right_injective (E →L[ℝ] E)
    (by norm_num : (2 : ℝ) ≠ 0)) h
  have hc := congrArg (coeff S) h'
  simpa only [coeff_synth] using hc

end
end QuaternionicSymmetry.QuaternionicNormalizerCrossCovariance
