import QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex
import QuaternionicSymmetry.ManifoldQuaternionicConnection

/-! The covariant Hessian of an actual quaternionic isometric immersion in
fixed adapted orthonormal tangent gauges. Vanishing is the coordinate
total-geodesy condition, not a twistor/contact naturality assumption. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)

/-- The immersion written from a fixed source chart to a fixed target
chart, with values in the target model space. -/
def localBaseMap (q : N) (p : M) (y : F) : E :=
  extChartAt 𝓘(ℝ,E) p (ι ((extChartAt 𝓘(ℝ,F) q).symm y))

/-- The rectangular tangent derivative in the source and target adapted
orthonormal frames. Both frame changes are actual bundle-gauge maps. -/
def adaptedRectangularDerivative (q : N) (p : M) (y : F) :
    F →L[ℝ] E :=
  let x := (extChartAt 𝓘(ℝ,F) q).symm y
  (P.tangent.frames.toFrame (achart E p) (ι x)).comp
    ((localDerivative ι (achart F q) (achart E p) x).comp
      (R.tangent.frames.fromFrame (achart F q) x))

/-- The rectangular adapted-frame derivative intertwines the actual
quaternionic generators through the locally extracted coefficient map. -/
theorem adaptedRectangularDerivative_intertwines
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hR : IsInducedQuaternionicGeometry P R ι)
    (q : N) (p : M) (y : F)
    (hi : (extChartAt 𝓘(ℝ,F) q).symm y ∈
      R.tangent.frames.adaptedCore.baseSet (achart F q))
    (hj : ι ((extChartAt 𝓘(ℝ,F) q).symm y) ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p))
    (a : Fin 3 → ℝ) (v : F) :
    adaptedRectangularDerivative P R ι q p y
        (synth (R.tangent.reduction.Q (achart F q)) a v) =
      synth (P.tangent.reduction.Q (achart E p))
        (localCoefficientMap P R ι hι hR (achart F q) (achart E p)
          ((extChartAt 𝓘(ℝ,F) q).symm y) a)
        (adaptedRectangularDerivative P R ι q p y v) := by
  let x := (extChartAt 𝓘(ℝ,F) q).symm y
  let i := achart F q
  let j := achart E p
  let T := localDerivative ι i j x
  let C := localCoefficientMap P R ι hι hR i j x
  let Fi := R.tangent.frames.fromFrame i x
  let Ti := R.tangent.frames.toFrame i x
  let Tj := P.tangent.frames.toFrame j (ι x)
  let Fj := P.tangent.frames.fromFrame j (ι x)
  have hlocal := localDerivative_intertwines P R ι hι hR i j x hi hj a (Fi v)
  change T (Fi (synth (R.tangent.reduction.Q i) a (Ti (Fi v)))) =
    Fj (synth (P.tangent.reduction.Q j) (C a) (Tj (T (Fi v)))) at hlocal
  rw [R.tangent.frames.to_from i x hi] at hlocal
  have h := congrArg Tj hlocal
  rw [P.tangent.frames.to_from j (ι x) hj] at h
  exact h

/-- Actual source/target chart overlap on which the rectangular
derivative and the two connection one-forms have geometric meaning. -/
def immersionChartOverlap (q : N) (p : M) : Set F :=
  {y | y ∈ (extChartAt 𝓘(ℝ,F) q).target ∧
    ι ((extChartAt 𝓘(ℝ,F) q).symm y) ∈
      (extChartAt 𝓘(ℝ,E) p).source}

theorem adaptedRectangularDerivative_intertwines_on_overlap
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hR : IsInducedQuaternionicGeometry P R ι)
    (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) (M := M) (N := N)
      ι q p)
    (a : Fin 3 → ℝ) (v : F) :
    adaptedRectangularDerivative P R ι q p y
        (synth (R.tangent.reduction.Q (achart F q)) a v) =
      synth (P.tangent.reduction.Q (achart E p))
        (localCoefficientMap P R ι hι hR (achart F q) (achart E p)
          ((extChartAt 𝓘(ℝ,F) q).symm y) a)
        (adaptedRectangularDerivative P R ι q p y v) := by
  have hi : (extChartAt 𝓘(ℝ,F) q).symm y ∈
      R.tangent.frames.adaptedCore.baseSet (achart F q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,F)] using
      (extChartAt 𝓘(ℝ,F) q).map_target hy.1
  have hj : ι ((extChartAt 𝓘(ℝ,F) q).symm y) ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  exact adaptedRectangularDerivative_intertwines P R ι hι hR q p y hi hj a v

theorem adaptedRectangularDerivative_injective
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (q : N) (p : M) (y : F)
    (hi : (extChartAt 𝓘(ℝ,F) q).symm y ∈
      R.tangent.frames.adaptedCore.baseSet (achart F q))
    (hj : ι ((extChartAt 𝓘(ℝ,F) q).symm y) ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p)) :
    Function.Injective (adaptedRectangularDerivative P R ι q p y) := by
  let x := (extChartAt 𝓘(ℝ,F) q).symm y
  let i := achart F q
  let j := achart E p
  let T := localDerivative ι i j x
  let Fi := R.tangent.frames.fromFrame i x
  let Ti := R.tangent.frames.toFrame i x
  let Tj := P.tangent.frames.toFrame j (ι x)
  let Fj := P.tangent.frames.fromFrame j (ι x)
  intro u v huv
  change Tj (T (Fi u)) = Tj (T (Fi v)) at huv
  have hT : T (Fi u) = T (Fi v) := by
    have h := congrArg Fj huv
    rw [P.tangent.frames.from_to j (ι x) hj,
      P.tangent.frames.from_to j (ι x) hj] at h
    exact h
  have hF := (localDerivative_injective P R ι hι i j x hi hj) hT
  have h := congrArg Ti hF
  rw [R.tangent.frames.to_from i x hi,
    R.tangent.frames.to_from i x hi] at h
  exact h

theorem adaptedRectangularDerivative_injective_on_overlap
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) (M := M) (N := N)
      ι q p) :
    Function.Injective (adaptedRectangularDerivative P R ι q p y) := by
  have hi : (extChartAt 𝓘(ℝ,F) q).symm y ∈
      R.tangent.frames.adaptedCore.baseSet (achart F q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,F)] using
      (extChartAt 𝓘(ℝ,F) q).map_target hy.1
  have hj : ι ((extChartAt 𝓘(ℝ,F) q).symm y) ∈
      P.tangent.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  exact adaptedRectangularDerivative_injective P R ι hι q p y hi hj

/-- Covariant Hessian of the adapted rectangular derivative. Directions
`u` live in source chart coordinates and `v` in its adapted orthonormal
frame; the target connection is evaluated on the actual chart derivative
`dG_y u`. -/
def covariantHessian
    (DP : CompatibleTangentConnection P.tangent)
    (DR : CompatibleTangentConnection R.tangent)
    (q : N) (p : M) (y u v : F) : E :=
  let A := adaptedRectangularDerivative P R ι q p
  let G := localBaseMap ι q p
  (fderiv ℝ A y u) v +
    (DP.form p (G y) (fderiv ℝ G y u)) (A y v) -
      A y ((DR.form q y u) v)

/-- Explicit total-geodesy condition in all actual adapted chart pairs.
This is a narrow geometric input: it states only vanishing of the
covariant Hessian, with no twistor or contact conclusion. -/
def IsTotallyGeodesic
    (DP : CompatibleTangentConnection P.tangent)
    (DR : CompatibleTangentConnection R.tangent) : Prop :=
  ∀ (q : N) (p : M) (y : F),
    y ∈ immersionChartOverlap (E := E) (F := F) (M := M) (N := N) ι q p →
    ∀ u v, covariantHessian P R ι DP DR q p y u v = 0

omit [Nontrivial E] [Nontrivial F] in
theorem covariantHessian_eq_derivative_of_adapted
    (DP : CompatibleTangentConnection P.tangent)
    (DR : CompatibleTangentConnection R.tangent)
    (q : N) (p : M) (y u v : F) :
    (fderiv ℝ (adaptedRectangularDerivative P R ι q p) y u) v =
      covariantHessian P R ι DP DR q p y u v -
        (DP.form p (localBaseMap ι q p y)
          (fderiv ℝ (localBaseMap ι q p) y u))
          (adaptedRectangularDerivative P R ι q p y v) +
        adaptedRectangularDerivative P R ι q p y ((DR.form q y u) v) := by
  dsimp [covariantHessian]
  abel

theorem derivative_of_totallyGeodesic
    (DP : CompatibleTangentConnection P.tangent)
    (DR : CompatibleTangentConnection R.tangent)
    (hTot : IsTotallyGeodesic P R ι DP DR)
    (q : N) (p : M) (y : F)
    (hy : y ∈ immersionChartOverlap (E := E) (F := F) (M := M) (N := N)
      ι q p) (u v : F) :
    (fderiv ℝ (adaptedRectangularDerivative P R ι q p) y u) v =
      - (DP.form p (localBaseMap ι q p y)
          (fderiv ℝ (localBaseMap ι q p) y u))
          (adaptedRectangularDerivative P R ι q p y v) +
        adaptedRectangularDerivative P R ι q p y ((DR.form q y u) v) := by
  rw [covariantHessian_eq_derivative_of_adapted P R ι DP DR,
    hTot q p y hy u v]
  simp

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
