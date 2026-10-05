import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
import QuaternionicSymmetry.ManifoldRiemannianOneJetInput

/-! The standard involutivity of a Riemannian point symmetry follows from
the already registered one-jet rigidity theorem on a connected manifold.
No model classification or second symmetry premise is needed. -/

namespace QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry

open ManifoldQuaternionicMetric ManifoldQuaternionicFundamentalSymmetry
open ManifoldRiemannianOneJetInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M]
  {Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞)}
  {x : M}

/-- The square of the point isometry has the same value and differential
as the identity at its center, hence is the identity globally. -/
theorem PointSymmetry.trans_self_eq_refl
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (s : PointSymmetry Q x) :
    s.map.map.trans s.map.map = Diffeomorph.refl 𝓘(ℝ,E) M ∞ := by
  apply hjet Q _ _
    (metric_trans Q (s.metric_invariant) (s.metric_invariant))
    (metric_refl Q) x
  · change s.map.map (s.map.map x) = x
    rw [s.fixed]
    exact s.fixed
  · intro v
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      ((s.map.map : M → M) ∘ (s.map.map : M → M)) x v =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (id : M → M) x v
    rw [mfderiv_comp x
      (s.map.map.contMDiff.mdifferentiable (by simp) (s.map.map x))
      (s.map.map.contMDiff.mdifferentiable (by simp) x)]
    rw [s.fixed]
    rw [mfderiv_id]
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (s.map.map : M → M) x
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (s.map.map : M → M) x v) = v
    rw [s.deriv_neg v, map_neg, s.deriv_neg v, neg_neg]

/-- Every actual point symmetry is involutive, as in the conventional
definition of a globally Riemannian symmetric space. -/
theorem PointSymmetry.involutive
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (s : PointSymmetry Q x) (y : M) :
    s.map.map (s.map.map y) = y := by
  have h := congrArg (fun f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞ => f y)
    (s.trans_self_eq_refl hjet)
  simpa using h

end
end QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
