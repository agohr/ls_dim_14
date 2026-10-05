import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport
import QuaternionicSymmetry.QuaternionicNormalizerProductSurjective
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

/-! The actual orthogonal quaternionic normalizer acts transitively on its
unit complex-structure sphere.  Its isotropy is the orthogonal commutant of
the chosen complex structure.  In real dimension four this gives a normalizer
quotient presentation; identifying the normalizer with `SO(4)`, its stabilizer
with `U(2)`, and the source projective half-spin action remains separate. -/

namespace QuaternionicSymmetry.FourDimensionalTwistorHomogeneousFiber

open scoped Quaternion
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionTransport
open ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

/-- The coefficient of the first quaternionic complex structure. -/
def north : coefficientSphere :=
  ⟨Pi.basisFun ℝ (Fin 3) 0, by
    simp [squareNorm, Fin.sum_univ_succ, Pi.basisFun_apply]⟩

omit [FiniteDimensional ℝ E] in
private theorem north_synth : synth S (north).1 = S.I := by
  change synth S (Pi.basisFun ℝ (Fin 3) 0) = S.I
  rw [synth_basis]
  rfl

/-- Orthogonal normalizer elements fixing the selected complex structure. -/
def complexStabilizer : Subgroup (normalizer S) where
  carrier := {g | rotationLinear S g (north).1 = (north).1}
  one_mem' := by
    change rotationLinear S 1 (north).1 = (north).1
    change rotationEquiv S 1 (north).1 = (north).1
    rw [show rotationEquiv S 1 = 1 from map_one (rotationHom S)]
    rfl
  mul_mem' := by
    intro g h hg hh
    change rotationLinear S (g * h) (north).1 = (north).1
    rw [rotationLinear_mul, hh, hg]
  inv_mem' := by
    intro g hg
    change rotationLinear S g⁻¹ (north).1 = (north).1
    calc
      _ = rotationLinear S g⁻¹ (rotationLinear S g (north).1) := by rw [hg]
      _ = (north).1 := rotationLinear_inv S g (north).1

/-- The stabilizer is precisely the orthogonal subgroup commuting with `I`.
This is the intrinsic `U(2)` stabilizer when `E` has real dimension four. -/
theorem mem_complexStabilizer_iff_commutes_I (g : normalizer S) :
    g ∈ complexStabilizer S ↔
      ∀ v : E, g.1 (S.I v) = S.I (g.1 v) := by
  change rotationLinear S g (north).1 = (north).1 ↔ _
  constructor
  · intro hg v
    have hs := synth_rotationLinear S g (north).1
    rw [hg, north_synth S] at hs
    have he := congrArg (fun A : E →L[ℝ] E => A (g.1 v)) hs
    simpa [conjugation_apply] using he.symm
  · intro hg
    apply (show Function.Injective (synth S) from
      Function.LeftInverse.injective (coeff_synth S))
    rw [synth_rotationLinear, north_synth S]
    ext v
    simpa [conjugation_apply] using
      (hg (g.1.symm v))

private theorem pureScalar_normSq (a : coefficientSphere) :
    Quaternion.normSq (pureScalar a.1) = 1 := by
  simpa [pureScalar, Quaternion.normSq_def', squareNorm,
    Fin.sum_univ_succ, pow_two, add_assoc] using a.2

/-- Every point of the coefficient sphere is in the orbit of the first
quaternionic complex structure under the actual orthogonal normalizer. -/
theorem exists_normalizer_maps_north (a : coefficientSphere) :
    ∃ g : normalizer S, rotationLinear S g (north).1 = a.1 := by
  obtain ⟨q,hq⟩ := exists_unitTransport basisI (pureScalar a.1)
    basisI_unit.1 (pureScalar_re a.1) basisI_unit.2
    (pureScalar_normSq a)
  refine ⟨unitQuaternionNormalizerAction S q, ?_⟩
  apply (show Function.Injective (synth S) from
    Function.LeftInverse.injective (coeff_synth S))
  rw [synth_rotationLinear]
  have hqa : (q : ℍ) * basisI * star (q : ℍ) = pureScalar a.1 := by
    rw [hq, mul_assoc, q.property.2, mul_one]
  change conjugation (unitScalarIsometry S (q : ℍ)
      (normSq_one_of_unitary q)) (synth S (north).1) = synth S a.1
  rw [unitScalar_conjugation]
  have hn : pureScalar (north).1 = basisI := by
    ext <;> simp [north, pureScalar, basisI, Pi.basisFun_apply]
  rw [hn, hqa]
  ext v
  exact action_pureScalar S a.1 v

end
end QuaternionicSymmetry.FourDimensionalTwistorHomogeneousFiber
