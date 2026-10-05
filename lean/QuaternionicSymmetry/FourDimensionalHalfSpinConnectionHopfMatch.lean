import QuaternionicSymmetry.FourDimensionalHalfSpinHopfInfinitesimal
import QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace
import QuaternionicSymmetry.ManifoldQuaternionicFourFormConnection

/-! The independent left-spinor connection extracted from the actual
adapted tangent connection has exactly the same infinitesimal Hopf action
as the actual induced rank-three connection.  Projective descent and the
affine overlap law are handled separately. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinConnectionHopfMatch

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinLieProjection
  FourDimensionalHalfSpinHopfInfinitesimal
  QuaternionicUnitScalarIsometries
  QuaternionicLieAlgebraProjection
  QuaternionicInfinitesimalSplitting
  QuaternionicFixedModelAdjointTrace
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicLeftLineAction
  ManifoldQuaternionicRankThreeOrientation
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicFourFormConnection
  ManifoldQuaternionicConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

private theorem synth_left_one (a : Fin 3 → ℝ) :
    synth leftLineStructure a 1 = pureScalar a := by
  have h := action_pureScalar leftLineStructure a (1 : ℍ)
  rw [action_eq_mul] at h
  simpa using h.symm

theorem pureScalar_cross (a b : Fin 3 → ℝ) :
    pureScalar ((2 : ℝ) • crossProduct a b) =
      pureScalar a * pureScalar b - pureScalar b * pureScalar a := by
  have h := congrArg (fun T : ℍ →L[ℝ] ℍ => T 1)
    (synth_commutator_cross leftLineStructure a b)
  change synth leftLineStructure a (synth leftLineStructure b 1) -
      synth leftLineStructure b (synth leftLineStructure a 1) =
    ((2 : ℝ) • synth leftLineStructure
      (crossProduct a b)) 1 at h
  rw [synth_left_one, synth_left_one] at h
  have ha := action_pureScalar leftLineStructure a (pureScalar b)
  have hb := action_pureScalar leftLineStructure b (pureScalar a)
  rw [action_eq_mul] at ha hb
  rw [← ha, ← hb] at h
  rw [← map_smul] at h
  change pureScalar a * pureScalar b - pureScalar b * pureScalar a =
      synth leftLineStructure
      ((2 : ℝ) • crossProduct a b) 1 at h
  rw [synth_left_one] at h
  exact h.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The fixed-model left-spinor coefficient is literally the imaginary
quaternion encoding the actual induced rank-three connection matrix. -/
theorem leftSpinorForm_eq_inducedMatrix (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) :
    leftSpinorForm Q D p y u =
      pureScalar (scalarCoefficients (inducedMatrix Q D p y u)) := by
  let T := Q.reduction.Q (achart ℍ p)
  have hA := tangentForm_preservesSpan Q D p y u hy
  have hfixed := adjointRepresentation_fixedConjugation
    leftLineStructure T (D.form p y u) hA
  rw [leftSpinorForm_apply]
  change pureScalar (axialProjection
    (adjointRepresentation leftLineStructure
      (fixedTangentConjugation leftLineStructure Q p (D.form p y u)))) = _
  rw [show adjointRepresentation leftLineStructure
    (fixedTangentConjugation leftLineStructure Q p (D.form p y u)) =
      adjointRepresentation T (D.form p y u) from hfixed]
  rfl

theorem leftSpinorForm_hopf_commutator (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (a : Fin 3 → ℝ) :
    pureScalar (inducedForm Q D p y u a) =
      leftSpinorForm Q D p y u * pureScalar a -
        pureScalar a * leftSpinorForm Q D p y u := by
  rw [leftSpinorForm_eq_inducedMatrix Q D p y u hy]
  rw [← inducedMatrix_mulVec Q D p y u a]
  rw [← cross_scalarCoefficients (inducedMatrix Q D p y u)
    (inducedMatrix_skew Q D p y u hy) a]
  exact pureScalar_cross _ _

/-- The actual spinor connection and rank-three sphere connection have
identical infinitesimal action under the literal Hopf map.  The spinor-side
horizontal direction is defined from the tangent connection projection,
not transported from the sphere connection. -/
theorem leftSpinorForm_hopf_derivative (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target)
    (v : ℍ) (a : Fin 3 → ℝ)
    (hv : quaternionHopf v = pureScalar a) :
    fderiv ℝ quaternionHopf v (leftSpinorForm Q D p y u * v) =
      pureScalar (inducedForm Q D p y u a) := by
  rw [quaternionHopf_left_infinitesimal _ _
    (leftSpinorForm_re Q D p y u), hv]
  exact (leftSpinorForm_hopf_commutator Q D p y u hy a).symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinConnectionHopfMatch
