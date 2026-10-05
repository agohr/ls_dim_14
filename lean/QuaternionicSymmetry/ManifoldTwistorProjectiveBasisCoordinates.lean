import QuaternionicSymmetry.ManifoldTwistorProjectiveEvaluation
import QuaternionicSymmetry.ComplexProjectiveManifold
import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic
import Mathlib.LinearAlgebra.Dual.Basis

/-! Finite-basis coordinates for the actual twistor section-evaluation map. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveBasisCoordinates

open ManifoldTwistorProjectiveEvaluation ManifoldTwistorLinearSystem
open HolomorphicLinePowers
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)
variable (d : ℕ)
  (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections Q D L r))

/-- The canonical coordinate map on duals induced by a chosen basis. -/
def dualCoordinates :
    Module.Dual ℂ (GlobalSections Q D L r) →ₗ[ℂ] Coord d where
  toFun f := fun k => f (b k)
  map_add' _ _ := by funext k; rfl
  map_smul' _ _ := by funext k; rfl

theorem dualCoordinates_injective :
    Function.Injective (dualCoordinates Q D L r d b) := by
  intro f g h
  apply b.ext
  intro k
  exact congrFun h k

/-- The same coordinate map is a genuine complex-linear equivalence, not
just an injective coordinate presentation. -/
def dualCoordinatesEquiv :
    Module.Dual ℂ (GlobalSections Q D L r) ≃ₗ[ℂ] Coord d :=
  b.dualBasis.equivFun

theorem dualCoordinates_eq_equiv :
    dualCoordinates Q D L r d b =
      (dualCoordinatesEquiv Q D L r d b).toLinearMap := by
  ext f k
  simp [dualCoordinates, dualCoordinatesEquiv]

/-- Coordinates of the actual evaluation functional in a chosen section basis. -/
def basisEvaluation (x : SphereBundleTotal Q) : Coord d :=
  fun k => evaluationDual Q D L r x (b k)

theorem basisEvaluation_ne_zero (x : SphereBundleTotal Q)
    (hx : x ∉ baseLocus Q D L r) : basisEvaluation Q D L r d b x ≠ 0 := by
  intro hz
  apply hx
  apply (mem_baseLocus_iff_basis Q D L r b x).2
  intro k
  have hk := congrFun hz k
  exact hk

/-- The complete linear system, expressed in homogeneous coordinates of
an actual finite basis; no finite-dimensionality value is assumed. -/
def basisProjectiveEvaluation :
    {x : SphereBundleTotal Q // x ∉ baseLocus Q D L r} → Space d :=
  fun x => Projectivization.mk ℂ (basisEvaluation Q D L r d b x.1)
    (basisEvaluation_ne_zero Q D L r d b x.1 x.2)

/-- A total extension of the basis evaluation map; its values on the base
locus are immaterial, and it agrees with the actual projective evaluation
outside that locus. -/
def basisProjectiveEvaluationTotal (x : SphereBundleTotal Q) : Space d :=
  projectivize d (basisEvaluation Q D L r d b x)

theorem basisProjectiveEvaluationTotal_eq (x : SphereBundleTotal Q)
    (hx : x ∉ baseLocus Q D L r) :
    basisProjectiveEvaluationTotal Q D L r d b x =
      basisProjectiveEvaluation Q D L r d b ⟨x, hx⟩ := by
  exact projectivize_of_ne_zero d _
    (basisEvaluation_ne_zero Q D L r d b x hx)

theorem basisProjectiveEvaluation_eq_projective_map
    (x : {x : SphereBundleTotal Q // x ∉ baseLocus Q D L r}) :
    basisProjectiveEvaluation Q D L r d b x =
      Projectivization.map (dualCoordinates Q D L r d b)
        (dualCoordinates_injective Q D L r d b)
        (projectiveEvaluation Q D L r x) := by
  rfl

/-- Evaluation in an arbitrary holomorphic line-bundle chart has the same
projective coordinates, since it rescales every basis coefficient together. -/
def basisChartEvaluation (i : L.Index) (x : SphereBundleTotal Q) : Coord d :=
  fun k => chartEvaluation Q D L r i x (b k)

theorem basisChartEvaluation_eq_smul (i : L.Index) (x : SphereBundleTotal Q) :
    basisChartEvaluation Q D L r d b i x =
      transitionScalar (L.integerTwistCore Q D r)
        ((L.integerTwistCore Q D r).indexAt x) i x •
          basisEvaluation Q D L r d b x := by
  funext k
  change chartEvaluation Q D L r i x (b k) =
    (transitionScalar (L.integerTwistCore Q D r)
      ((L.integerTwistCore Q D r).indexAt x) i x •
        evaluationDual Q D L r x) (b k)
  rw [chartEvaluation_eq_smul]

theorem basisChartEvaluation_ne_zero (i : L.Index) (x : SphereBundleTotal Q)
    (hx : x ∉ baseLocus Q D L r)
    (hi : x ∈ (L.integerTwistCore Q D r).baseSet i) :
    basisChartEvaluation Q D L r d b i x ≠ 0 := by
  intro hz
  apply chartEvaluation_ne_zero_of_not_mem_baseLocus Q D L r i x hx hi
  apply b.ext
  intro k
  exact congrFun hz k

theorem basisProjectiveEvaluation_eq_chart
    (x : {x : SphereBundleTotal Q // x ∉ baseLocus Q D L r})
    (i : L.Index) (hi : x.1 ∈ (L.integerTwistCore Q D r).baseSet i) :
    basisProjectiveEvaluation Q D L r d b x =
      Projectivization.mk ℂ (basisChartEvaluation Q D L r d b i x.1)
        (basisChartEvaluation_ne_zero Q D L r d b i x.1 x.2 hi) := by
  change Projectivization.mk ℂ (basisEvaluation Q D L r d b x.1) _ =
    Projectivization.mk ℂ (basisChartEvaluation Q D L r d b i x.1) _
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (basisChartEvaluation Q D L r d b i x.1)
    (basisEvaluation Q D L r d b x.1) _ _).2
  exact ⟨transitionScalar (L.integerTwistCore Q D r)
    ((L.integerTwistCore Q D r).indexAt x.1) i x.1,
    (basisChartEvaluation_eq_smul Q D L r d b i x.1).symm⟩

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveBasisCoordinates
