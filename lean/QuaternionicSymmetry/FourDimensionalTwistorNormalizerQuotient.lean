import QuaternionicSymmetry.FourDimensionalTwistorHomogeneousFiber
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A genuine homogeneous-space presentation of the quaternionic
complex-structure sphere by the orthogonal normalizer and its complex
stabilizer.  This does not yet identify the normalizer with the entire
orientation-preserving orthogonal group in real dimension four, nor with
Hitchin's projective negative-half-spin representation. -/

namespace QuaternionicSymmetry.FourDimensionalTwistorNormalizerQuotient

open VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicIsometryNormalizer QuaternionicNormalizerRotationAxes
open FourDimensionalTwistorHomogeneousFiber
open ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

private theorem rotation_squareNorm (g : normalizer S) (a : Fin 3 → ℝ) :
    squareNorm (rotationLinear S g a) = squareNorm a := by
  exact rotation_dot S g a a

/-- The actual adjoint action of the quaternionic orthogonal normalizer on
the unit complex-structure sphere. -/
def act (g : normalizer S) (a : coefficientSphere) : coefficientSphere :=
  ⟨rotationLinear S g a.1,
    (rotation_squareNorm S g a.1).trans a.2⟩

@[simp] theorem act_val (g : normalizer S) (a : coefficientSphere) :
    (act S g a).1 = rotationLinear S g a.1 := rfl

instance : MulAction (normalizer S) coefficientSphere where
  smul := act S
  one_smul a := by
    apply Subtype.ext
    change rotationLinear S 1 a.1 = a.1
    change rotationEquiv S 1 a.1 = a.1
    rw [show rotationEquiv S 1 = 1 from map_one (rotationHom S)]
    rfl
  mul_smul g h a := by
    apply Subtype.ext
    exact rotationLinear_mul S g h a.1

theorem stabilizer_eq_complexStabilizer :
    MulAction.stabilizer (normalizer S) (north) = complexStabilizer S := by
  ext g
  change act S g (north) = north ↔ g ∈ complexStabilizer S
  rw [Subtype.ext_iff]
  rfl

/-- The stabilizer coset space is bijective to the actual sphere.  The
stabilizer is the commuting orthogonal subgroup by the preceding leaf. -/
def quotientEquivSphere :
    (normalizer S ⧸ complexStabilizer S) ≃ coefficientSphere := by
  let e := MulAction.orbitEquivQuotientStabilizer
    (normalizer S) (north : coefficientSphere)
  have horbit : MulAction.orbit (normalizer S) (north : coefficientSphere) = Set.univ := by
    ext a
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨g,hg⟩ := exists_normalizer_maps_north S a
      refine ⟨g, ?_⟩
      apply Subtype.ext
      exact hg
  let all : MulAction.orbit (normalizer S) (north : coefficientSphere) ≃
      coefficientSphere := {
    toFun := Subtype.val
    invFun := fun a => ⟨a, by rw [horbit]; trivial⟩
    left_inv := fun a => Subtype.ext rfl
    right_inv := fun a => rfl }
  exact (Equiv.cast (congrArg (fun H : Subgroup (normalizer S) =>
    normalizer S ⧸ H) (stabilizer_eq_complexStabilizer S))).symm.trans
    (e.symm.trans all)

end
end QuaternionicSymmetry.FourDimensionalTwistorNormalizerQuotient
