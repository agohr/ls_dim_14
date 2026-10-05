import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylPairSymmetry
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge

/-! The genuine corrected Weyl tensor annihilates the Q-positive input
half. Both output Hodge sign and pair symmetry are proved from the actual
connection. After reversing orientation, this is the source's W⁻=0. -/

namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylBlock

open Module FourDimensionalExteriorHodge FourDimensionalCoordinateHodge
open FourDimensionalQuaternionicHodgeFrame
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourWeylPairSymmetry
open ManifoldPositiveTwistorCompatibleFourWeylExteriorHodge
open scoped Manifold ContDiff BigOperators
noncomputable section

def pairFirst : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def pairSecond : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

private theorem coordinates_apply_pair
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : Basis (Fin 4) ℝ V) (α : TwoForm V) (j : Fin 6) :
    coordinates b α j =
      BilinearExterior.evaluate (b (pairFirst j)) (b (pairSecond j)) α := by
  fin_cases j <;> rfl

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def weylColumn
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : E) (hz : ‖z‖ = 1) (i : Fin 6) : Two :=
  let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
  coordinates b.toBasis (HyperholomorphicExterior.form b.toBasis
    (correctedWeylOperator P p y hy
      (b (pairFirst i)) (b (pairSecond i))).toLinearMap)

theorem weylColumn_pair_symmetry
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : E) (hz : ‖z‖ = 1) (i j : Fin 6) :
    weylColumn P p y hy z hz i j = weylColumn P p y hy z hz j i := by
  dsimp only [weylColumn]
  rw [coordinates_apply_pair, coordinates_apply_pair]
  rw [HyperholomorphicExterior.evaluate_form _ _
      (correctedWeylOperator_skew P p y hy _ _),
    HyperholomorphicExterior.evaluate_form _ _
      (correctedWeylOperator_skew P p y hy _ _)]
  exact correctedWeylOperator_pair_symmetry P p y hy _ _ _ _

theorem weylColumn_negative
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : E) (hz : ‖z‖ = 1) (i : Fin 6) :
    FourDimensionalCoordinateHodge.star (weylColumn P p y hy z hz i) = -weylColumn P p y hy z hz i := by
  let b := frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz
  have h := correctedWeyl_negative_exteriorHodge P p y hy
    (b (pairFirst i)) (b (pairSecond i)) z hz
  have hc := congrArg (coordinates b.toBasis) h
  rw [coordinates_frameStar, map_neg] at hc
  exact hc

/-- Actual corrected Weyl curvature operator in an orthonormal exterior
basis. The six columns are evaluations on the six basis bivectors. -/
def coordinateWeyl
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : E) (hz : ‖z‖ = 1) (α : Two) : Two :=
  fun j => α 0 * weylColumn P p y hy z hz 0 j +
    α 1 * weylColumn P p y hy z hz 1 j +
    α 2 * weylColumn P p y hy z hz 2 j +
    α 3 * weylColumn P p y hy z hz 3 j +
    α 4 * weylColumn P p y hy z hz 4 j +
    α 5 * weylColumn P p y hy z hz 5 j

theorem coordinateWeyl_annihilates_positive
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : E) (hz : ‖z‖ = 1) (α : Two) (hα : FourDimensionalCoordinateHodge.star α = α) :
    coordinateWeyl P p y hy z hz α = 0 := by
  have ha0 := congrFun hα 0
  have ha1 := congrFun hα 1
  have ha2 := congrFun hα 2
  change α 5 = α 0 at ha0
  change -α 4 = α 1 at ha1
  change α 3 = α 2 at ha2
  funext j
  have hc := weylColumn_negative P p y hy z hz j
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  have hc2 := congrFun hc 2
  change weylColumn P p y hy z hz j 5 = -weylColumn P p y hy z hz j 0 at hc0
  change -weylColumn P p y hy z hz j 4 = -weylColumn P p y hy z hz j 1 at hc1
  change weylColumn P p y hy z hz j 3 = -weylColumn P p y hy z hz j 2 at hc2
  simp only [coordinateWeyl, Pi.zero_apply]
  rw [weylColumn_pair_symmetry P p y hy z hz 0 j,
    weylColumn_pair_symmetry P p y hy z hz 1 j,
    weylColumn_pair_symmetry P p y hy z hz 2 j,
    weylColumn_pair_symmetry P p y hy z hz 3 j,
    weylColumn_pair_symmetry P p y hy z hz 4 j,
    weylColumn_pair_symmetry P p y hy z hz 5 j]
  rw [ha0, ha2, hc0, hc2]
  have ha4 : α 4 = -α 1 := by linarith [ha1]
  have hc4 : weylColumn P p y hy z hz j 4 = weylColumn P p y hy z hz j 1 :=
    neg_injective hc1
  rw [ha4, hc4]
  ring

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylBlock
