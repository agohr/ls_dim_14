import QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance

/-! The actual rank-three coefficient representation of a subgroup fixing
an actual connected component. Its algebraic homomorphism law comes from
the genuine isometry derivative; local joint continuity is proved using
adapted frames in a later bridge, not assumed in this definition. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedCoefficientRepresentation
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicLocalDerivativeEquivariance
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldRiemannianFixedComponentInput
open scoped Manifold ContDiff
noncomputable section
set_option maxRecDepth 2048

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (S : Subgroup (QuaternionicIsometries Q)) (x : M)

theorem fixedComponent_mem_fixedPoints
    (y : FixedComponent Q S x) : y.1 ∈ fixedPoints Q S :=
  connectedComponentIn_subset _ _ y.2

/-- The actual pointwise coefficient representation of `S` on the
quaternionic three-plane at a point of its fixed component. -/
def coefficientRepresentation (y : FixedComponent Q S x) :
    S →* Module.End ℝ (Fin 3 → ℝ) where
  toFun f := coefficientAction Q f.1 y.1
  map_one' := by
    apply LinearMap.ext
    intro a
    exact coefficientAction_one Q y.1 a
  map_mul' f g := by
    apply LinearMap.ext
    intro a
    change coefficientAction Q (f.1 * g.1) y.1 a =
      coefficientAction Q f.1 y.1 (coefficientAction Q g.1 y.1 a)
    rw [coefficientAction_mul, (fixedComponent_mem_fixedPoints Q S x y) g.1 g.2]

/-- Intrinsic triviality does not depend on a chosen local frame: it says
each actual isometry derivative acts identically on the rank-three
coefficient plane at this fixed point. -/
def TrivialQuaternionicIsotropy (y : FixedComponent Q S x) : Prop :=
  ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f y.1 a = a

theorem trivial_iff_representation_one (y : FixedComponent Q S x) :
    TrivialQuaternionicIsotropy Q S x y ↔
      ∀ f : S, coefficientRepresentation Q S x y f = 1 := by
  constructor
  · intro h f
    apply LinearMap.ext
    intro a
    exact h f.1 f.2 a
  · intro h f hf a
    have he := congrArg (fun T : Module.End ℝ (Fin 3 → ℝ) => T a)
      (h ⟨f,hf⟩)
    simpa [coefficientRepresentation] using he

/-- Conjugate the intrinsic coefficient action into one fixed local adapted
frame. The varying preferred `indexAt` appears only in the algebraic
comparison; this definition is the geometric local frame presentation. -/
def fixedChartCoefficientRepresentation (i : atlas E M)
    (y : FixedComponent Q S x)
    (hi : y.1 ∈ Q.frames.adaptedCore.baseSet i) :
    S →* Module.End ℝ (Fin 3 → ℝ) where
  toFun f := (Q.reduction.rankThreeCoordChange (achart E y.1) i y.1).toLinearMap.comp
    ((coefficientAction Q f.1 y.1).comp
      (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1).toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro a
    change Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
      (coefficientAction Q 1 y.1
        (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1 a)) = a
    rw [coefficientAction_one]
    rw [Q.reduction.rankThreeCoordChange_comp i (achart E y.1) i y.1
      hi (Q.frames.adaptedCore.mem_baseSet_at y.1) hi,
      Q.reduction.rankThreeCoordChange_self i y.1 hi]
  map_mul' f g := by
    apply LinearMap.ext
    intro a
    change Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
      (coefficientAction Q (f.1 * g.1) y.1
        (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1 a)) =
      Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
        (coefficientAction Q f.1 y.1
          (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1
            (Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
              (coefficientAction Q g.1 y.1
                (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1 a)))))
    rw [coefficientAction_mul,
      (fixedComponent_mem_fixedPoints Q S x y) g.1 g.2]
    rw [Q.reduction.rankThreeCoordChange_comp
      (achart E y.1) i (achart E y.1) y.1
      (Q.frames.adaptedCore.mem_baseSet_at y.1) hi
      (Q.frames.adaptedCore.mem_baseSet_at y.1),
      Q.reduction.rankThreeCoordChange_self (achart E y.1) y.1
        (Q.frames.adaptedCore.mem_baseSet_at y.1)]

theorem trivial_iff_fixedChartRepresentation_one (i : atlas E M)
    (y : FixedComponent Q S x)
    (hi : y.1 ∈ Q.frames.adaptedCore.baseSet i) :
    TrivialQuaternionicIsotropy Q S x y ↔
      ∀ f : S, fixedChartCoefficientRepresentation Q S x i y hi f = 1 := by
  constructor
  · intro h f
    apply LinearMap.ext
    intro a
    change Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
      (coefficientAction Q f.1 y.1
        (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1 a)) = a
    rw [h f.1 f.2,
      Q.reduction.rankThreeCoordChange_comp i (achart E y.1) i y.1
        hi (Q.frames.adaptedCore.mem_baseSet_at y.1) hi,
      Q.reduction.rankThreeCoordChange_self i y.1 hi]
  · intro h f hf a
    let b := Q.reduction.rankThreeCoordChange (achart E y.1) i y.1 a
    have he := congrArg (fun T : Module.End ℝ (Fin 3 → ℝ) => T b)
      (h ⟨f,hf⟩)
    change Q.reduction.rankThreeCoordChange (achart E y.1) i y.1
      (coefficientAction Q f y.1
        (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1 b)) = b at he
    rw [Q.reduction.rankThreeCoordChange_comp
      (achart E y.1) i (achart E y.1) y.1
      (Q.frames.adaptedCore.mem_baseSet_at y.1) hi
      (Q.frames.adaptedCore.mem_baseSet_at y.1),
      Q.reduction.rankThreeCoordChange_self (achart E y.1) y.1
        (Q.frames.adaptedCore.mem_baseSet_at y.1)] at he
    have hinj : Function.Injective
        (Q.reduction.rankThreeCoordChange (achart E y.1) i y.1) := by
      intro u v huv
      have hu := congrArg
        (Q.reduction.rankThreeCoordChange i (achart E y.1) y.1) huv
      change Q.reduction.rankThreeCoordChange i (achart E y.1) y.1
          (Q.reduction.rankThreeCoordChange (achart E y.1) i y.1 u) =
        Q.reduction.rankThreeCoordChange i (achart E y.1) y.1
          (Q.reduction.rankThreeCoordChange (achart E y.1) i y.1 v) at hu
      rw [Q.reduction.rankThreeCoordChange_comp
        (achart E y.1) i (achart E y.1) y.1
        (Q.frames.adaptedCore.mem_baseSet_at y.1) hi
        (Q.frames.adaptedCore.mem_baseSet_at y.1),
        Q.reduction.rankThreeCoordChange_comp
        (achart E y.1) i (achart E y.1) y.1
        (Q.frames.adaptedCore.mem_baseSet_at y.1) hi
        (Q.frames.adaptedCore.mem_baseSet_at y.1)] at hu
      simpa only [Q.reduction.rankThreeCoordChange_self
        (achart E y.1) y.1 (Q.frames.adaptedCore.mem_baseSet_at y.1)] using hu
    exact hinj he

/-- The overlap of two actual adapted frames along the connected fixed
component. It uses an open chart domain, never the discontinuous `indexAt`. -/
def fixedChartOverlap (i j : atlas E M) : Set (FixedComponent Q S x) :=
  {y | y.1 ∈ Q.frames.adaptedCore.baseSet i ∩
    Q.frames.adaptedCore.baseSet j}

/-- The actual rank-three conjugating matrix between any two local frame
presentations varies continuously along their fixed-component overlap. -/
theorem continuous_fixedChartTransition (i j : atlas E M) :
    Continuous (fun y : fixedChartOverlap Q S x i j =>
      Q.reduction.rankThreeCoordChange i j y.1.1) := by
  have hval : Continuous
      (fun y : fixedChartOverlap Q S x i j => (y.1 : FixedComponent Q S x).1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmem : ∀ y : fixedChartOverlap Q S x i j,
      y.1.1 ∈ Q.frames.adaptedCore.baseSet i ∩
        Q.frames.adaptedCore.baseSet j := fun y => y.2
  exact (Q.reduction.continuousOn_rankThreeCoordChange i j).comp_continuous
    hval hmem

/-- Two fixed-chart representations differ by exactly the actual continuous
rank-three frame transition. Hence their triviality predicates agree on an
overlap, with no distinguished global adapted frame. -/
theorem fixedChartRepresentation_transition (i j : atlas E M)
    (y : FixedComponent Q S x)
    (hi : y.1 ∈ Q.frames.adaptedCore.baseSet i)
    (hj : y.1 ∈ Q.frames.adaptedCore.baseSet j)
    (f : S) (a : Fin 3 → ℝ) :
    fixedChartCoefficientRepresentation Q S x j y hj f a =
      Q.reduction.rankThreeCoordChange i j y.1
        (fixedChartCoefficientRepresentation Q S x i y hi f
          (Q.reduction.rankThreeCoordChange j i y.1 a)) := by
  let k := achart E y.1
  have hk : y.1 ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at y.1
  change Q.reduction.rankThreeCoordChange k j y.1
      (coefficientAction Q f.1 y.1
        (Q.reduction.rankThreeCoordChange j k y.1 a)) =
    Q.reduction.rankThreeCoordChange i j y.1
      (Q.reduction.rankThreeCoordChange k i y.1
        (coefficientAction Q f.1 y.1
          (Q.reduction.rankThreeCoordChange i k y.1
            (Q.reduction.rankThreeCoordChange j i y.1 a))))
  rw [Q.reduction.rankThreeCoordChange_comp j i k y.1 hj hi hk,
    Q.reduction.rankThreeCoordChange_comp k i j y.1 hk hi hj]

/-- On a fixed component, the fixed-chart representation is exactly the
coefficient extracted from the actual adapted derivative in that chart.
The equality is on the genuine chart overlap and uses no global frame. -/
theorem fixedChartRepresentation_eq_localCoefficientRotation
    (c : M) (hc : c ∈ fixedPoints Q S) (y : FixedComponent Q S x)
    (hy : y.1 ∈ (chartAt E c).source)
    (hi : y.1 ∈ Q.frames.adaptedCore.baseSet (achart E c))
    (f : S) (a : Fin 3 → ℝ) :
    fixedChartCoefficientRepresentation Q S x (achart E c) y hi f a =
      ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
        Q f.1 c y.1 a := by
  have hfc : f.1 • c = c := hc f.1 f.2
  have hfy : f.1 • y.1 = y.1 :=
    (fixedComponent_mem_fixedPoints Q S x y) f.1 f.2
  have hloc := localCoefficientRotation_eq_true_on_overlap Q f.1 c y.1
    hy (by simpa only [hfc,hfy] using hy) a
  change Q.reduction.rankThreeCoordChange (achart E y.1) (achart E c) y.1
      (coefficientAction Q f.1 y.1
        (Q.reduction.rankThreeCoordChange (achart E c) (achart E y.1) y.1 a)) = _
  simpa only [localTrueCoefficientAction, hfc, hfy] using hloc.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedCoefficientRepresentation
