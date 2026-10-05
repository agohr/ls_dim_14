import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry

/-! The actual geometric input for the complete Stage 2 dimension range.
In quaternionic dimension one the Einstein and oriented Weyl equations are
part of the geometric input. In higher dimensions the ordinary positive
quaternionic-Kähler package suffices. No classification, torus, contact
generation, or fixed-component property is a field. -/

namespace QuaternionicSymmetry.Stage2IntrinsicGeometry

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicScalarCurvature
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A uniform positive input with the precise four-dimensional convention. -/
structure CompactConnectedPositiveTwistorGeometry (n : ℕ) extends
    CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  positiveDimension : 1 ≤ n
  realDimension : Module.finrank ℝ E = 4*n
  einstein_four : n = 1 → ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E),
      localRicci tangent connection p y hy v w =
        (localScalarCurvature tangent connection p y hy / 4) * inner ℝ v w
  oppositeWeyl_four : n = 1 → ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E)
      (a : Fin 3 → ℝ) (w : E),
      correctedWeylVector toPositiveQuaternionicKahlerGeometry p y hy u v
          (synth (tangent.reduction.Q (achart E p)) a w) =
        synth (tangent.reduction.Q (achart E p)) a
          (correctedWeylVector toPositiveQuaternionicKahlerGeometry p y hy u v w)

/-- Every existing actual four-dimensional input gives the uniform input. -/
def ofFour
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    CompactConnectedPositiveTwistorGeometry (E := E) (M := M) 1 where
  toPositiveQuaternionicKahlerGeometry := P.toPositiveQuaternionicKahlerGeometry
  compact := P.compact
  connected := P.connected
  positiveDimension := by omega
  realDimension := by simpa using P.realDimension
  einstein_four := fun _ => P.einstein
  oppositeWeyl_four := fun _ => P.oppositeWeyl

/-- No extra tensor hypotheses are imposed on a higher-dimensional input. -/
def ofHigher {n : ℕ} (hn : 2 ≤ n)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n) :
    CompactConnectedPositiveTwistorGeometry (E := E) (M := M) n where
  toCompactConnectedPositiveQuaternionicKahlerGeometry := P
  positiveDimension := by omega
  realDimension := hDim
  einstein_four := by intro h; omega
  oppositeWeyl_four := by intro h; omega

/-- Extract the four-dimensional package without changing metric or connection. -/
def toFour (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) 1) :
    CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M) where
  toPositiveQuaternionicKahlerGeometry := P.toPositiveQuaternionicKahlerGeometry
  compact := P.compact
  connected := P.connected
  realDimension := by simpa using P.realDimension
  einstein := P.einstein_four rfl
  oppositeWeyl := P.oppositeWeyl_four rfl

@[simp] theorem ofFour_tangent
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    (ofFour P).tangent = P.tangent := rfl

@[simp] theorem ofHigher_tangent {n : ℕ} (hn : 2 ≤ n)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n) :
    (ofHigher hn P hDim).tangent = P.tangent := rfl

@[simp] theorem toFour_tangent
    (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) 1) :
    (toFour P).tangent = P.tangent := rfl

end
end QuaternionicSymmetry.Stage2IntrinsicGeometry
