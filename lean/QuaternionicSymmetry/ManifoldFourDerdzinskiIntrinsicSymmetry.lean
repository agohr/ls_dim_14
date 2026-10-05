import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourCanonicalHodge
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylPairSymmetry
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourWeylBlock
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGlobalWeylHodge
import QuaternionicSymmetry.FourDimensionalExteriorHodgeReversedHalves
import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

/-! A tensor-level, source-relative application of Derdzinski's metric
classification, separate from Hitchin's conformal twistor theorem.

Source: A. Derdzinski, *Einstein Metrics in Dimension Four*, Handbook of
Differential Geometry I (2000), 419–707, DOI 10.1016/S1874-5741(00)80007-2.
Author PDF https://people.math.osu.edu/derdzinski.1/courses/7711/em.pdf,
Theorem 33.4(a), printed p.186 (PDF index 185); the self-duality convention
is W⁻=0, §6, printed p.47 (PDF index 46). It concludes isometry to S⁴ or
CP² with a multiple of its standard metric, rather than conformal equivalence.

The explicit general corollary below uses a Q-oriented orthonormal frame.
Its corrected Weyl OUTPUT has negative Hodge sign. Reversing the orientation
changes the Hodge star's sign, so that output has positive sign in the
source's orientation. Pair symmetry identifies the corresponding negative
INPUT block with zero; the actual six-column curvature operator proves this
internally in `coordinateWeyl_annihilates_positive`. The Q orientation is
global, by the determinant-one adapted transition law and
`tangentHodgeStar_local`; `tangentCorrectedWeylForm_negative` transports the
actual Weyl output to the genuine tangent fiber. These are equations on the actual metric curvature,
not a classification flag. Metric compatibility and zero torsion identify
the given connection with Levi-Civita. The source corollary also includes
global point symmetry of the two standard metrics and its preservation
under isometry and positive scaling. Those literature/standard-model facts
remain an explicit premise; this file introduces no axiom.

Curvature normalization: source (4.23), printed p.27, uses
R_s(u,v)=∇v∇u−∇u∇v+∇[u,v], opposite the project's curvature. Its Ricci
contraction (4.34), printed p.28, uses Trace[w↦R_s(u,w)v], agreeing with the
project's Trace[w↦R_project(w,u)v]. Source (5.10), printed p.36, and (10.2),
printed p.62, give W_s=−W_project for an Einstein four-metric; the scalar
correction is exactly s/12, not s/24. Negating W leaves its zero block and
its Hodge output sign unchanged. The source Hodge convention (6.1), printed
p.40, and the
project's `(01,02,03,12,13,23)` coefficients agree in an oriented orthonormal
frame. Reversing that orientation therefore yields W_s⁻=0.

The standard-model point symmetries in the derived corollary can be seen
directly from the models in source Examples 10.4 and 10.6 (printed pp.63–65):
on the unit sphere, the orthogonal map 2 proj_x−id fixes x and restricts to
−id on its tangent hyperplane; on CP², the unitary map 2 proj_ℓ−id fixes the
line ℓ and induces −id on Hom_C(ℓ,ℓ⊥). Orthogonal/unitary actions preserve
the respective induced/quotient metrics. These model constructions and
transport through the classified isometry are external elementary geometry
in the explicit corollary, not kernel-formalized model declarations.
-/

namespace QuaternionicSymmetry.ManifoldFourDerdzinskiIntrinsicSymmetry

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourWeylOperator
open ManifoldPositiveTwistorCompatibleFourCanonicalHodge
open ManifoldQuaternionicScalarCurvature
open ManifoldRiemannianIntrinsicSymmetry
open FourDimensionalExteriorHodge FourDimensionalExteriorCanonicalHodge
open FourDimensionalQuaternionicHodgeFrame
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The scalar-corrected actual curvature, without any self-duality or
four-dimensional classification hypothesis. -/
def metricCorrectedWeylOperator
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) : E →L[ℝ] E :=
  P.connection.curvature P.tangent p y
    ((solderEquiv P.tangent p y hy).symm u)
    ((solderEquiv P.tangent p y hy).symm v) -
  (localScalarCurvature P.tangent P.connection p y hy / 12) •
    (wedgeLinear u v).toContinuousLinearMap

/-- The general metric corollary of Derdzinski 33.4(a), with every local
Einstein and oriented Weyl equation visible. In dimension four a quaternionic
frame supplies the orientation only; no holonomy classification is invoked. -/
def DerdzinskiFourSymmetrySource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hdim : Module.finrank ℝ E = 4),
    IsCompact (Set.univ : Set M) → IsPreconnected (Set.univ : Set M) →
    (∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) v w,
      localRicci P.tangent P.connection p y hy v w =
        (localScalarCurvature P.tangent P.connection p y hy / 4) * inner ℝ v w) →
    (∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) u v z (hz : ‖z‖ = 1),
      let Q := P.tangent.reduction.Q (achart E p)
      let b := frameBasis Q hdim z hz
      let β := HyperholomorphicExterior.form b.toBasis
        (metricCorrectedWeylOperator P p y hy u v).toLinearMap;
      -(canonicalStar Q hdim β) = β) →
    IsRiemannianSymmetric P.tangent

/-- Apply the general metric theorem to the actual four-dimensional input.
The corrected-Weyl orientation equation is proved internally. -/
theorem symmetric_of_derdzinskiFour
    (hSource : DerdzinskiFourSymmetrySource)
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    IsRiemannianSymmetric P.tangent := by
  apply hSource P.toPositiveQuaternionicKahlerGeometry P.realDimension
    P.compact P.connected P.einstein
  intro p y hy u v z hz
  change -(canonicalStar (P.tangent.reduction.Q (achart E p)) P.realDimension
    (HyperholomorphicExterior.form
      (frameBasis (P.tangent.reduction.Q (achart E p)) P.realDimension z hz).toBasis
      (correctedWeylOperator P.toPositiveTwistorCompatibleFourGeometry
        p y hy u v).toLinearMap)) = _
  rw [correctedWeyl_canonicalStar_negative
    P.toPositiveTwistorCompatibleFourGeometry p y hy u v z hz]
  exact neg_neg _

end
end QuaternionicSymmetry.ManifoldFourDerdzinskiIntrinsicSymmetry
