import QuaternionicSymmetry.ProjectiveAdjointBaseBundle
import QuaternionicSymmetry.QuaternionicFrame
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Coordinate changes of an actual `VectorBundleCore` give an exact (and hence
signed) cocycle in the algebra of continuous endomorphisms of its model fiber.
The second part records how local quaternionic structures agree under those
coordinate changes. A PQK projective standard bundle requires further geometry.
-/

namespace QuaternionicSymmetry.VectorBundleFrameTransitions

open TopologicalSpace
open scoped Topology Bundle

noncomputable section

variable {ι B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bundle core supplies genuine frame changes, with the direction reversed
to match the gauge convention `g i j * g j k = g i k`. -/
def transitionAtlas (Z : VectorBundleCore ℝ B V ι) :
    ProjectiveAdjointBaseBundle.TransitionAtlas ι B (V →L[ℝ] V) where
  U i := ⟨Z.baseSet i, Z.isOpen_baseSet i⟩
  cover := by
    apply IsOpenCover.of_sets Z.isOpen_baseSet
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩
  g i j x := Z.coordChange j i x
  diag i x hx := by
    ext v
    exact Z.coordChange_self i x hx v
  inverse i j x hi hj := by
    ext v
    exact (Z.coordChange_comp i j i x ⟨⟨hi, hj⟩, hi⟩ v).trans
      (Z.coordChange_self i x hi v)
  continuous i j := by
    simpa only [Set.inter_comm] using Z.continuousOn_coordChange j i
  cocycle i j k x hi hj hk := by
    left
    constructor
    · ext v
      exact Z.coordChange_comp k j i x ⟨⟨hk, hj⟩, hi⟩ v
    · ext v
      exact Z.coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩ v

/-- The adjoint coordinate change obtained from the real bundle core. -/
theorem adjointCoordChange_apply (Z : VectorBundleCore ℝ B V ι)
    (i j : ι) (x : B) (a : V →L[ℝ] V) :
    (transitionAtlas Z).adjointCoordChange i j x a =
      Z.coordChange i j x * a * Z.coordChange j i x := by
  exact (transitionAtlas Z).adjointCoordChange_apply i j x a

/-- A change of frame acts by an algebra homomorphism on endomorphisms
where both frames are defined. -/
theorem adjointCoordChange_mul (Z : VectorBundleCore ℝ B V ι)
    (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j)
    (a b : V →L[ℝ] V) :
    (transitionAtlas Z).adjointCoordChange i j x (a * b) =
      (transitionAtlas Z).adjointCoordChange i j x a *
        (transitionAtlas Z).adjointCoordChange i j x b := by
  simp only [adjointCoordChange_apply]
  have hinv : Z.coordChange j i x * Z.coordChange i j x = 1 :=
    (transitionAtlas Z).inverse i j x hi hj
  calc
    Z.coordChange i j x * (a * b) * Z.coordChange j i x =
        Z.coordChange i j x * a * (Z.coordChange j i x * Z.coordChange i j x) *
          b * Z.coordChange j i x := by rw [hinv]; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem adjointCoordChange_one (Z : VectorBundleCore ℝ B V ι)
    (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    (transitionAtlas Z).adjointCoordChange i j x (1 : V →L[ℝ] V) = 1 := by
  rw [adjointCoordChange_apply, mul_one]
  exact (transitionAtlas Z).inverse j i x hj hi

end

noncomputable section

variable {ι B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Quaternion relations survive frame transport even when the frame change
is not orthogonal. This is the algebraic part of gluing a quaternionic
endomorphism subspace. -/
theorem transport_quaternion_relations (Z : VectorBundleCore ℝ B V ι)
    (Q : QuaternionicStructure V) (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    let T := (transitionAtlas Z).adjointCoordChange i j x
    T (Q.I : V →L[ℝ] V) * T (Q.I : V →L[ℝ] V) = -1 ∧
    T (Q.J : V →L[ℝ] V) * T (Q.J : V →L[ℝ] V) = -1 ∧
    T (Q.I : V →L[ℝ] V) * T (Q.J : V →L[ℝ] V) =
      -(T (Q.J : V →L[ℝ] V) * T (Q.I : V →L[ℝ] V)) := by
  dsimp
  have hI : (Q.I : V →L[ℝ] V) * (Q.I : V →L[ℝ] V) =
      (-1 : V →L[ℝ] V) := by
    ext v
    exact Q.I_sq v
  have hJ : (Q.J : V →L[ℝ] V) * (Q.J : V →L[ℝ] V) =
      (-1 : V →L[ℝ] V) := by
    ext v
    exact Q.J_sq v
  have hIJ : (Q.I : V →L[ℝ] V) * (Q.J : V →L[ℝ] V) =
      -((Q.J : V →L[ℝ] V) * (Q.I : V →L[ℝ] V)) := by
    ext v
    exact Q.I_J_anti v
  refine ⟨?_, ?_, ?_⟩
  · rw [← adjointCoordChange_mul Z i j x hi hj, hI]
    simp [adjointCoordChange_one Z i j x hi hj]
  · rw [← adjointCoordChange_mul Z i j x hi hj, hJ]
    simp [adjointCoordChange_one Z i j x hi hj]
  · rw [← adjointCoordChange_mul Z i j x hi hj,
      ← adjointCoordChange_mul Z i j x hi hj, hIJ]
    simp

/-- The three local quaternionic endomorphisms in one frame. -/
def quaternionicGenerator (Q : QuaternionicStructure V) : Fin 3 → V →L[ℝ] V :=
  ![(Q.I : V →L[ℝ] V), (Q.J : V →L[ℝ] V), (Q.K : V →L[ℝ] V)]

/-- The span of the quaternionic endomorphisms attached to a local frame. -/
def quaternionicSpan (Q : QuaternionicStructure V) :
    Submodule ℝ (V →L[ℝ] V) :=
  Submodule.span ℝ (Set.range (quaternionicGenerator Q))

theorem generator_mem_span (Q : QuaternionicStructure V) (t : Fin 3) :
    quaternionicGenerator Q t ∈ quaternionicSpan Q :=
  Submodule.subset_span ⟨t, rfl⟩

/-- Evaluation of a continuous endomorphism at a fixed vector. -/
def evalAt (v : V) : (V →L[ℝ] V) →ₗ[ℝ] V where
  toFun f := f v
  map_add' f g := by simp
  map_smul' c f := by simp

/-- On a nonzero quaternionic Hermitian space, the three endomorphisms are
linearly independent. This rules out the zero-fiber degeneracy. -/
theorem quaternionicGenerator_linearIndependent [Nontrivial V]
    (Q : QuaternionicStructure V) :
    LinearIndependent ℝ (quaternionicGenerator Q) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w : V := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
  have hframe := Q.frame_linearIndependent w hw
  have htail := hframe.comp Fin.succ (Fin.succ_injective 3)
  apply LinearIndependent.of_comp (evalAt w)
  convert htail using 1
  funext t
  fin_cases t <;> rfl

theorem finrank_quaternionicSpan [Nontrivial V]
    (Q : QuaternionicStructure V) :
    Module.finrank ℝ (quaternionicSpan Q) = 3 := by
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (quaternionicGenerator Q))) = 3
  simpa using finrank_span_eq_card (quaternionicGenerator_linearIndependent Q)

/-- A local quaternionic reduction of an actual vector-bundle core. It asks
only that the transported generators belong to the next chart's quaternionic
span; they may rotate rather than remain fixed individually. -/
structure QuaternionicFrameReduction (Z : VectorBundleCore ℝ B V ι) where
  Q : ι → QuaternionicStructure V
  generator_transport : ∀ i j x, x ∈ Z.baseSet i → x ∈ Z.baseSet j →
    ∀ t : Fin 3,
      (transitionAtlas Z).adjointCoordChange i j x (quaternionicGenerator (Q i) t) ∈
        quaternionicSpan (Q j)

namespace QuaternionicFrameReduction

variable {Z : VectorBundleCore ℝ B V ι} (R : QuaternionicFrameReduction Z)

theorem map_span_le (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Submodule.map ((transitionAtlas Z).adjointCoordChange i j x).toLinearMap
      (quaternionicSpan (R.Q i)) ≤ quaternionicSpan (R.Q j) := by
  rw [quaternionicSpan, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact R.generator_transport i j x hi hj t

/-- Inverse frame changes upgrade generator preservation to equality of the
local quaternionic spans. This is the fiberwise gluing law for the reduction. -/
theorem map_span_eq (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Submodule.map ((transitionAtlas Z).adjointCoordChange i j x).toLinearMap
      (quaternionicSpan (R.Q i)) = quaternionicSpan (R.Q j) := by
  apply le_antisymm (R.map_span_le i j x hi hj)
  intro a ha
  have hback : (transitionAtlas Z).adjointCoordChange j i x a ∈
      quaternionicSpan (R.Q i) := by
    apply R.map_span_le j i x hj hi
    exact ⟨a, ha, rfl⟩
  refine ⟨(transitionAtlas Z).adjointCoordChange j i x a, hback, ?_⟩
  calc
    (transitionAtlas Z).adjointCoordChange i j x
        ((transitionAtlas Z).adjointCoordChange j i x a) =
      (transitionAtlas Z).adjointCoordChange j j x a :=
        (transitionAtlas Z).adjointCoordChange_comp j i j x hj hi hj a
    _ = a := (transitionAtlas Z).adjointCoordChange_self j x hj a

/-- The quaternionic subspace in the adjoint fiber, expressed in the adjoint
core's preferred frame at each base point. -/
def quaternionicFiber (x : B) :
    Submodule ℝ ((transitionAtlas Z).vectorCore.Fiber x) :=
  quaternionicSpan (R.Q ((transitionAtlas Z).vectorCore.indexAt x))

/-- Membership in the quaternionic endomorphism span is independent of the
chosen local frame. -/
theorem coord_mem_quaternionicSpan_iff (i : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (a : V →L[ℝ] V) :
    (transitionAtlas Z).adjointCoordChange ((transitionAtlas Z).vectorCore.indexAt x) i x a ∈
        quaternionicSpan (R.Q i) ↔ a ∈ R.quaternionicFiber x := by
  let P := transitionAtlas Z
  have hidx : x ∈ Z.baseSet (P.vectorCore.indexAt x) :=
    P.vectorCore.mem_baseSet_at x
  constructor
  · intro ha
    have hback : P.adjointCoordChange i (P.vectorCore.indexAt x) x
        (P.adjointCoordChange (P.vectorCore.indexAt x) i x a) ∈
        quaternionicSpan (R.Q (P.vectorCore.indexAt x)) := by
      apply R.map_span_le i (P.vectorCore.indexAt x) x hi hidx
      exact ⟨_, ha, rfl⟩
    have hid : P.adjointCoordChange i (P.vectorCore.indexAt x) x
        (P.adjointCoordChange (P.vectorCore.indexAt x) i x a) = a := by
      calc
        _ = P.adjointCoordChange (P.vectorCore.indexAt x) (P.vectorCore.indexAt x) x a :=
          P.adjointCoordChange_comp (P.vectorCore.indexAt x) i (P.vectorCore.indexAt x)
            x hidx hi hidx a
        _ = a := P.adjointCoordChange_self (P.vectorCore.indexAt x) x hidx a
    simpa only [quaternionicFiber, hid] using hback
  · intro ha
    apply R.map_span_le (P.vectorCore.indexAt x) i x hidx hi
    exact ⟨a, ha, rfl⟩

/-- The adjoint bundle's actual local trivialization recognizes the same
quaternionic subspace in every chart. -/
theorem localTriv_mem_quaternionicSpan_iff (i : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (a : V →L[ℝ] V) :
    ((transitionAtlas Z).vectorCore.localTriv i
      (⟨x, a⟩ : (transitionAtlas Z).vectorCore.TotalSpace)).2 ∈
        quaternionicSpan (R.Q i) ↔ a ∈ R.quaternionicFiber x := by
  exact R.coord_mem_quaternionicSpan_iff i x hi a

section RankThreeBundle

variable [Nontrivial V] [FiniteDimensional ℝ V]

/-- Coordinates on the quaternionic span in a local frame. -/
def spanBasis (Q : QuaternionicStructure V) :
    Module.Basis (Fin 3) ℝ (quaternionicSpan Q) :=
  Module.Basis.span (quaternionicGenerator_linearIndependent Q)

private def spanComplement (Q : QuaternionicStructure V) :
    Submodule ℝ (V →L[ℝ] V) :=
  Classical.choose (quaternionicSpan Q).exists_isCompl

omit [Nontrivial V] [FiniteDimensional ℝ V] in
private theorem spanComplement_isCompl (Q : QuaternionicStructure V) :
    IsCompl (quaternionicSpan Q) (spanComplement Q) :=
  Classical.choose_spec (quaternionicSpan Q).exists_isCompl

/-- Synthesize a quaternionic endomorphism from its three local coordinates. -/
def synth (Q : QuaternionicStructure V) :
    (Fin 3 → ℝ) →L[ℝ] (V →L[ℝ] V) :=
  ((quaternionicSpan Q).subtype.comp
    (spanBasis Q).equivFun.symm.toLinearMap).toContinuousLinearMap

/-- Extract local coordinates after projection to the quaternionic span. The
projection is only used outside the span; bundle transitions land inside it. -/
def coeff (Q : QuaternionicStructure V) :
    (V →L[ℝ] V) →L[ℝ] (Fin 3 → ℝ) :=
  ((spanBasis Q).equivFun.toLinearMap.comp
    ((quaternionicSpan Q).linearProjOfIsCompl
      (spanComplement Q) (spanComplement_isCompl Q))).toContinuousLinearMap

omit [FiniteDimensional ℝ V] in
theorem synth_mem (Q : QuaternionicStructure V) (a : Fin 3 → ℝ) :
    synth Q a ∈ quaternionicSpan Q := by
  change (((quaternionicSpan Q).subtype : _ →ₗ[ℝ] _) _ ) ∈ _
  exact Subtype.property _

theorem coeff_synth (Q : QuaternionicStructure V) (a : Fin 3 → ℝ) :
    coeff Q (synth Q a) = a := by
  change (spanBasis Q).equivFun
    ((quaternionicSpan Q).linearProjOfIsCompl
      (spanComplement Q) (spanComplement_isCompl Q)
      ((quaternionicSpan Q).subtype ((spanBasis Q).equivFun.symm a))) = a
  simpa only [Submodule.subtype_apply] using
    congrArg (spanBasis Q).equivFun
      (Submodule.linearProjOfIsCompl_apply_left (spanComplement_isCompl Q)
        ((spanBasis Q).equivFun.symm a)) |>.trans
      ((spanBasis Q).equivFun.apply_symm_apply a)

theorem synth_coeff_of_mem (Q : QuaternionicStructure V) (a : V →L[ℝ] V)
    (ha : a ∈ quaternionicSpan Q) : synth Q (coeff Q a) = a := by
  change ((quaternionicSpan Q).subtype
      ((spanBasis Q).equivFun.symm
        ((spanBasis Q).equivFun
          ((quaternionicSpan Q).linearProjOfIsCompl
            (spanComplement Q) (spanComplement_isCompl Q) a)))) = a
  have hp := (Submodule.linearProjOfIsCompl_apply_left
    (spanComplement_isCompl Q) (⟨a, ha⟩ : quaternionicSpan Q))
  simp only at hp
  rw [show (quaternionicSpan Q).linearProjOfIsCompl
      (spanComplement Q) (spanComplement_isCompl Q) a = ⟨a, ha⟩ from hp]
  exact congrArg Subtype.val ((spanBasis Q).equivFun.symm_apply_apply ⟨a, ha⟩)

/-- Coordinate change on the three real coefficients of the quaternionic
endomorphism span. -/
def rankThreeCoordChange (i j : ι) (x : B) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (coeff (R.Q j)).comp
    (((transitionAtlas Z).adjointCoordChange i j x).comp (synth (R.Q i)))

theorem rankThreeCoordChange_apply (i j : ι) (x : B) (a : Fin 3 → ℝ) :
    R.rankThreeCoordChange i j x a =
      coeff (R.Q j) ((transitionAtlas Z).adjointCoordChange i j x
        (synth (R.Q i) a)) := rfl

theorem rankThreeCoordChange_self (i : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (a : Fin 3 → ℝ) :
    R.rankThreeCoordChange i i x a = a := by
  rw [rankThreeCoordChange_apply]
  rw [(transitionAtlas Z).adjointCoordChange_self i x hi]
  exact coeff_synth (R.Q i) a

theorem rankThreeCoordChange_comp (i j k : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j)
    (hk : x ∈ Z.baseSet k) (a : Fin 3 → ℝ) :
    R.rankThreeCoordChange j k x (R.rankThreeCoordChange i j x a) =
      R.rankThreeCoordChange i k x a := by
  let P := transitionAtlas Z
  have hmem : P.adjointCoordChange i j x (synth (R.Q i) a) ∈
      quaternionicSpan (R.Q j) := by
    apply R.map_span_le i j x hi hj
    exact ⟨_, synth_mem (R.Q i) a, rfl⟩
  simp only [rankThreeCoordChange_apply]
  rw [synth_coeff_of_mem (R.Q j) _ hmem]
  exact congrArg (coeff (R.Q k))
    (P.adjointCoordChange_comp i j k x hi hj hk (synth (R.Q i) a))

theorem continuousOn_rankThreeCoordChange (i j : ι) :
    ContinuousOn (R.rankThreeCoordChange i j)
      (Z.baseSet i ∩ Z.baseSet j) := by
  let P := transitionAtlas Z
  have h := P.continuousOn_adjointCoordChange i j
  have hright : ContinuousOn
      (fun x => (P.adjointCoordChange i j x).comp (synth (R.Q i)))
      (Z.baseSet i ∩ Z.baseSet j) := by
    exact ((ContinuousLinearMap.compL ℝ (Fin 3 → ℝ)
      (V →L[ℝ] V) (V →L[ℝ] V)).flip (synth (R.Q i))).continuous.comp_continuousOn h
  exact ((ContinuousLinearMap.compL ℝ (Fin 3 → ℝ)
    (V →L[ℝ] V) (Fin 3 → ℝ)) (coeff (R.Q j))).continuous.comp_continuousOn hright

/-- The quaternionic reduction of a genuine vector-bundle core yields a
continuous rank-three vector-bundle core with real coefficient fiber. -/
def rankThreeCore : VectorBundleCore ℝ B (Fin 3 → ℝ) ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange := R.rankThreeCoordChange
  coordChange_self := R.rankThreeCoordChange_self
  continuousOn_coordChange := R.continuousOn_rankThreeCoordChange
  coordChange_comp i j k x hx a :=
    R.rankThreeCoordChange_comp i j k x hx.1.1 hx.1.2 hx.2 a

/-- The associated continuous rank-three vector-bundle structure. -/
def rankThreeVectorBundle :
    VectorBundle ℝ (Fin 3 → ℝ) R.rankThreeCore.Fiber :=
  R.rankThreeCore.vectorBundle

theorem rankThree_localTriv_coordChange (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) (a : Fin 3 → ℝ) :
    (Trivialization.coordChangeL ℝ (R.rankThreeCore.localTriv i)
      (R.rankThreeCore.localTriv j) x) a =
      R.rankThreeCoordChange i j x a := by
  exact R.rankThreeCore.localTriv_coordChange_eq i j ⟨hi, hj⟩ a

end RankThreeBundle

end QuaternionicFrameReduction

end
end QuaternionicSymmetry.VectorBundleFrameTransitions
