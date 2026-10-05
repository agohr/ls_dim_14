import QuaternionicSymmetry.ManifoldTwistorLinearSystem
import QuaternionicSymmetry.HolomorphicLineGauge
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The actual section-evaluation map to the projectivization of the dual
section space, defined exactly off the genuine base locus. This is only a
set map at this stage; holomorphicity/embedding and positivity are separate
geometric statements. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveEvaluation

open QuaternionicSymmetry.ManifoldTwistorLinearSystem
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)

/-- The evaluation functional in the standard one-dimensional complex
fiber underlying the actual bundle core. -/
def evaluationDual (x : SphereBundleTotal Q) :
    Module.Dual ℂ (GlobalSections Q D L r) := by
  exact evaluation Q D L r x

/-- Evaluation expressed in any specified line-bundle chart, by
transporting the actual fiber value from the preferred core chart. -/
def chartEvaluation (i : L.Index) (x : SphereBundleTotal Q) :
    Module.Dual ℂ (GlobalSections Q D L r) :=
  ((L.integerTwistCore Q D r).coordChange
    ((L.integerTwistCore Q D r).indexAt x) i x).toLinearMap.comp
      (evaluation Q D L r x)

theorem chartEvaluation_eq_smul (i : L.Index) (x : SphereBundleTotal Q) :
    chartEvaluation Q D L r i x =
      transitionScalar (L.integerTwistCore Q D r)
        ((L.integerTwistCore Q D r).indexAt x) i x •
          evaluationDual Q D L r x := by
  ext s
  exact linear_apply_one
    ((L.integerTwistCore Q D r).coordChange
      ((L.integerTwistCore Q D r).indexAt x) i x)
    (evaluation Q D L r x s)

theorem chartTransition_ne_zero (i : L.Index) (x : SphereBundleTotal Q)
    (hx : x ∈ (L.integerTwistCore Q D r).baseSet i) :
    transitionScalar (L.integerTwistCore Q D r)
      ((L.integerTwistCore Q D r).indexAt x) i x ≠ 0 := by
  let Z := L.integerTwistCore Q D r
  have hs : transitionScalar Z (Z.indexAt x) (Z.indexAt x) x = 1 :=
    Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) 1
  have h := scalar_comp Z (Z.indexAt x) i (Z.indexAt x) x
    ⟨⟨Z.mem_baseSet_at x, hx⟩, Z.mem_baseSet_at x⟩
  rw [hs] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem evaluationDual_ne_zero_of_not_mem_baseLocus
    (x : SphereBundleTotal Q) (hx : x ∉ baseLocus Q D L r) :
    evaluationDual Q D L r x ≠ 0 := by
  intro h
  apply hx
  intro s
  have hs := congrArg (fun f : Module.Dual ℂ (GlobalSections Q D L r) => f s) h
  simpa only [evaluationDual, LinearMap.zero_apply] using hs

theorem chartEvaluation_ne_zero_of_not_mem_baseLocus
    (i : L.Index) (x : SphereBundleTotal Q)
    (hx : x ∉ baseLocus Q D L r)
    (hi : x ∈ (L.integerTwistCore Q D r).baseSet i) :
    chartEvaluation Q D L r i x ≠ 0 := by
  rw [chartEvaluation_eq_smul]
  exact smul_ne_zero (chartTransition_ne_zero Q D L r i x hi)
    (evaluationDual_ne_zero_of_not_mem_baseLocus Q D L r x hx)

/-- The complete linear system maps its actual base-locus complement to
projective dual space. No basepoint-freeness or ampleness is postulated. -/
def projectiveEvaluation :
    {x : SphereBundleTotal Q // x ∉ baseLocus Q D L r} →
      ℙ ℂ (Module.Dual ℂ (GlobalSections Q D L r)) :=
  fun x => Projectivization.mk ℂ (evaluationDual Q D L r x.1)
    (evaluationDual_ne_zero_of_not_mem_baseLocus Q D L r x.1 x.2)

/-- The projective evaluation point is independent of the local
trivialization: changing charts rescales its nonzero dual functional
by the actual nonzero line transition scalar. -/
theorem projectiveEvaluation_eq_chart
    (x : {x : SphereBundleTotal Q // x ∉ baseLocus Q D L r})
    (i : L.Index) (hi : x.1 ∈ (L.integerTwistCore Q D r).baseSet i) :
    projectiveEvaluation Q D L r x =
      Projectivization.mk ℂ (chartEvaluation Q D L r i x.1)
        (chartEvaluation_ne_zero_of_not_mem_baseLocus Q D L r i x.1 x.2 hi) := by
  change Projectivization.mk ℂ (evaluationDual Q D L r x.1) _ =
    Projectivization.mk ℂ (chartEvaluation Q D L r i x.1) _
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (chartEvaluation Q D L r i x.1)
    (evaluationDual Q D L r x.1) _ _).2
  exact ⟨transitionScalar (L.integerTwistCore Q D r)
    ((L.integerTwistCore Q D r).indexAt x.1) i x.1,
    (chartEvaluation_eq_smul Q D L r i x.1).symm⟩

/-- If the actual complete linear system has empty base locus, its
projective evaluation is defined at every twistor point. -/
def projectiveEvaluationOfBasepointFree
    (h : baseLocus Q D L r = ∅) :
    SphereBundleTotal Q → ℙ ℂ (Module.Dual ℂ (GlobalSections Q D L r)) :=
  fun x => projectiveEvaluation Q D L r
    ⟨x, by simp [h]⟩

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveEvaluation
