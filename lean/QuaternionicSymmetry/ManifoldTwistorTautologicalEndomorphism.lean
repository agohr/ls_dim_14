import QuaternionicSymmetry.ManifoldTwistorSphereBundle
import QuaternionicSymmetry.QuaternionicAction

/-! The tautological unit quaternionic endomorphism at a twistor point.
The local expressions square to minus the identity and transform by the
actual adapted tangent-frame transition. -/

namespace QuaternionicSymmetry.ManifoldTwistorTautologicalEndomorphism

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.VectorBundleFrameTransitions
open QuaternionicSymmetry.VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff Quaternion

noncomputable section

def imaginaryQuaternion (a : Fin 3 → ℝ) : ℍ :=
  ⟨0, a 0, a 1, a 2⟩

theorem imaginaryQuaternion_normSq (a : Fin 3 → ℝ) :
    Quaternion.normSq (imaginaryQuaternion a) = squareNorm a := by
  simp [imaginaryQuaternion, Quaternion.normSq_def', squareNorm, Fin.sum_univ_three]
  ring

theorem imaginaryQuaternion_sq (a : coefficientSphere) :
    imaginaryQuaternion a.1 * imaginaryQuaternion a.1 = -1 := by
  rw [← pow_two, Quaternion.sq_eq_neg_normSq.mpr rfl,
    imaginaryQuaternion_normSq, a.2]
  simp

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The selected imaginary unit in one adapted tangent frame. -/
def localComplexStructure (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    E →L[ℝ] E :=
  synth (Q.reduction.Q i) (localCoordinate Q i z hi).1

omit [FiniteDimensional ℝ E] in
private theorem synth_eq_action (S : QuaternionicStructure E)
    (a : Fin 3 → ℝ) (v : E) :
    synth S a v = S.action (imaginaryQuaternion a) v := by
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_eval, S.action_apply]
  simp [imaginaryQuaternion, Fin.sum_univ_three,
    QuaternionicStructure.frame, QuaternionicStructure.K_apply]

theorem localComplexStructure_sq (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) (v : E) :
    localComplexStructure Q i z hi (localComplexStructure Q i z hi v) = -v := by
  let a := localCoordinate Q i z hi
  change synth (Q.reduction.Q i) a.1 (synth (Q.reduction.Q i) a.1 v) = -v
  rw [synth_eq_action, synth_eq_action]
  change (((Q.reduction.Q i).action (imaginaryQuaternion a.1) *
    (Q.reduction.Q i).action (imaginaryQuaternion a.1)) : Module.End ℝ E) v = -v
  calc
    _ = (Q.reduction.Q i).action
        (imaginaryQuaternion a.1 * imaginaryQuaternion a.1) v := by
      exact congrArg (fun f : Module.End ℝ E => f v)
        ((Q.reduction.Q i).action.map_mul _ _).symm
    _ = -v := by rw [imaginaryQuaternion_sq a]; simp

/-- The same tautological endomorphism in two frames differs precisely by
the genuine adapted tangent-frame change. -/
theorem localComplexStructure_transition (i j : atlas E M)
    (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i)
    (hj : projection Q z ∈ Q.frames.adaptedCore.baseSet j) (v : E) :
    localComplexStructure Q j z hj (Q.frames.coordChange i j (projection Q z) v) =
      Q.frames.coordChange i j (projection Q z) (localComplexStructure Q i z hi v) := by
  rw [localComplexStructure, localComplexStructure,
    localTrivialization_transition Q i j z hi hj]
  exact ManifoldQuaternionicRankThreeOrthogonal.synth_rankThreeCoordChange_eval
    Q i j (projection Q z) hi hj (localCoordinate Q i z hi).1 v

/-- The tautological endomorphism on the genuine tangent fiber. It is
constructed in the preferred adapted frame at the twistor point's base. -/
def tautologicalTangent (z : TwistorSphere Q) :
    TangentSpace 𝓘(ℝ, E) (projection Q z) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (projection Q z) :=
  let x := projection Q z
  let i := Q.frames.adaptedCore.indexAt x
  ((Q.frames.fromFrame i x).comp
    (localComplexStructure Q i z (Q.frames.adaptedCore.mem_baseSet_at x))).comp
      (Q.frames.toFrame i x)

/-- Express the same tangent-fiber endomorphism through any adapted chart.
The actual tangent-core change transports preferred tangent coordinates to
that chart before applying the local quaternionic endomorphism. -/
def tautologicalTangentInChart (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    TangentSpace 𝓘(ℝ, E) (projection Q z) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (projection Q z) :=
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  ((((tangentBundleCore 𝓘(ℝ, E) M).coordChange i k x).comp
    (Q.frames.fromFrame i x)).comp (localComplexStructure Q i z hi)).comp
      ((Q.frames.toFrame i x).comp
        ((tangentBundleCore 𝓘(ℝ, E) M).coordChange k i x))

theorem tautologicalTangentInChart_eq (i : atlas E M) (z : TwistorSphere Q)
    (hi : projection Q z ∈ Q.frames.adaptedCore.baseSet i) :
    tautologicalTangentInChart Q i z hi = tautologicalTangent Q z := by
  let x := projection Q z
  let k := Q.frames.adaptedCore.indexAt x
  have hk := Q.frames.adaptedCore.mem_baseSet_at x
  ext v
  change (tangentBundleCore 𝓘(ℝ, E) M).coordChange i k x
      (Q.frames.fromFrame i x
        (localComplexStructure Q i z hi
          (Q.frames.toFrame i x
            ((tangentBundleCore 𝓘(ℝ, E) M).coordChange k i x v)))) =
    Q.frames.fromFrame k x
      (localComplexStructure Q k z hk (Q.frames.toFrame k x v))
  have hright (w : E) :
      Q.frames.toFrame i x
        ((tangentBundleCore 𝓘(ℝ, E) M).coordChange k i x w) =
      Q.frames.coordChange k i x (Q.frames.toFrame k x w) := by
    rw [Q.frames.coordChange_apply, Q.frames.from_to k x hk]
  rw [hright]
  rw [localComplexStructure_transition Q k i z hk hi]
  have hleft (w : E) :
      (tangentBundleCore 𝓘(ℝ, E) M).coordChange i k x
        (Q.frames.fromFrame i x (Q.frames.coordChange k i x w)) =
      Q.frames.fromFrame k x w := by
    rw [Q.frames.coordChange_apply]
    rw [Q.frames.from_to i x hi]
    rw [(tangentBundleCore 𝓘(ℝ, E) M).coordChange_comp k i k x
      ⟨⟨hk, hi⟩, hk⟩]
    rw [(tangentBundleCore 𝓘(ℝ, E) M).coordChange_self k x hk]
  exact hleft _

theorem tautologicalTangent_sq (z : TwistorSphere Q)
    (v : TangentSpace 𝓘(ℝ, E) (projection Q z)) :
    tautologicalTangent Q z (tautologicalTangent Q z v) = -v := by
  let x := projection Q z
  let i := Q.frames.adaptedCore.indexAt x
  have hi := Q.frames.adaptedCore.mem_baseSet_at x
  change Q.frames.fromFrame i x
      (localComplexStructure Q i z hi
        (Q.frames.toFrame i x
          (Q.frames.fromFrame i x (localComplexStructure Q i z hi
            (Q.frames.toFrame i x v))))) = -v
  rw [Q.frames.to_from i x hi]
  rw [localComplexStructure_sq Q i z hi]
  rw [map_neg, Q.frames.from_to i x hi]

end
end QuaternionicSymmetry.ManifoldTwistorTautologicalEndomorphism
