import QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! The spatial tangent action supplied by BG-R3, restricted to actual
quaternionic isometries. This is a joint statement on the entire tangent
bundle, not merely at fixed points. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointTangentAction

open Manifold
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryTopology
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A smooth joint action has a continuous spatial tangent action when
restricted along any continuously parametrized family of group elements. -/
theorem continuous_spatialTangentAction
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2)) :
    Continuous (fun p : QuaternionicIsometries Q × TangentBundle 𝓘(ℝ,E) M =>
      (⟨(toFullMetricIsometry Q p.1) p.2.1,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (p.1.1 : M → M) p.2.1 p.2.2⟩ :
        TangentBundle 𝓘(ℝ,E) M)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  let a : (M ≃ᵢ M) × M → M := fun p => p.1 p.2
  let F₁ : QuaternionicIsometries Q × TangentBundle 𝓘(ℝ,E) M →
      TangentBundle 𝓘(ℝ,V) (M ≃ᵢ M) × TangentBundle 𝓘(ℝ,E) M :=
    fun p => (⟨toFullMetricIsometry Q p.1, 0⟩, p.2)
  have h₁ : Continuous F₁ := by
    have hg : Continuous (fun f : QuaternionicIsometries Q =>
        (⟨toFullMetricIsometry Q f, 0⟩ : TangentBundle 𝓘(ℝ,V) (M ≃ᵢ M))) := by
      exact (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ,V)) (n := ∞) ℝ (TangentSpace 𝓘(ℝ,V) :
        (M ≃ᵢ M) → Type _)).continuous.comp (toFullMetricIsometry_continuous Q)
    exact (hg.comp continuous_fst).prodMk continuous_snd
  let F₂ := (equivTangentBundleProd 𝓘(ℝ,V) (M ≃ᵢ M) 𝓘(ℝ,E) M).symm
  have h₂ : Continuous F₂ :=
    (contMDiff_equivTangentBundleProd_symm (n := ∞)
      (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,E))).continuous
  have h₃ : Continuous (tangentMap (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) a) :=
    continuous_tangentAction Q hChart hManifold hAction
  have h := h₃.comp (h₂.comp h₁)
  convert h using 1
  funext p
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (p.1.1 : M → M) p.2.1 p.2.2 =
    mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) a
      (toFullMetricIsometry Q p.1, p.2.1) (0,p.2.2)
  have hc : a ∘ (fun x : M => (toFullMetricIsometry Q p.1, x)) =
      (p.1.1 : M → M) := rfl
  have hright : MDifferentiableAt 𝓘(ℝ,E) (𝓘(ℝ,V).prod 𝓘(ℝ,E))
      (fun x : M => (toFullMetricIsometry Q p.1, x)) p.2.1 :=
    ((contMDiff_const.prodMk contMDiff_id :
      ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,V).prod 𝓘(ℝ,E)) ∞
        (fun x : M => (toFullMetricIsometry Q p.1, x))).mdifferentiableAt (by simp))
  have hcomp := tangentMap_comp_at (I := 𝓘(ℝ,E))
    (I' := 𝓘(ℝ,V).prod 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := fun x : M => (toFullMetricIsometry Q p.1, x))
    (g := a) p.2 (hAction.mdifferentiableAt (by simp)) hright
  rw [hc, tangentMap_prod_right] at hcomp
  exact congrArg Bundle.TotalSpace.snd hcomp

/-- BG-R3 gives joint continuity of the actual derivative action on the
whole tangent bundle. No fixed-point or isotropy hypothesis is needed. -/
theorem continuous_jointTangentAction (hR3 : IsometryLieSource.{0,0}) :
    Continuous (fun p : QuaternionicIsometries Q × TangentBundle 𝓘(ℝ,E) M =>
      (⟨p.1 • p.2.1,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (p.1.1 : M → M) p.2.1 p.2.2⟩ :
        TangentBundle 𝓘(ℝ,E) M)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  exact continuous_spatialTangentAction Q hChart hManifold hAction

/-- The inverse differential also varies continuously, with its tangent
input based at the moving image point. -/
theorem continuous_jointInverseTangentAction (hR3 : IsometryLieSource.{0,0}) :
    Continuous (fun p : QuaternionicIsometries Q × TangentBundle 𝓘(ℝ,E) M =>
      (⟨p.1⁻¹ • p.2.1,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((p.1⁻¹).1 : M → M) p.2.1 p.2.2⟩ :
        TangentBundle 𝓘(ℝ,E) M)) := by
  exact (continuous_jointTangentAction Q hR3).comp
    (continuous_inv.comp continuous_fst |>.prodMk continuous_snd)

end
end QuaternionicSymmetry.ManifoldQuaternionicJointTangentAction
