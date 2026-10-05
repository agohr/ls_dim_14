import QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeTransition

/-! Internally constructed quaternionic Hermitian tangent geometry of a
quaternionic immersion on a compatible refined atlas. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionHermitianTangent
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicImmersionGaugeAtlas
open ManifoldQuaternionicImmersionGaugeTransition ManifoldPositiveQuaternionicKahlerGeometry
open VectorBundleFrameTransitions ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [old : ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)} {ι : N → M}
  (G : ∀ c, LocalGauge (F := F) P ι c)

def tangent : letI := charts G; letI := charts_manifold (old := old) G
    SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,F)) (M := N) (n := ∞) := by
  let S : Index G → QuaternionicStructure F := fun i => (G (chartCenter G i)).Q
  let T : Index G → Index G → N → F →L[ℝ] F := fun i j =>
    transition G (chartCenter G i) (chartCenter G j)
  have hT (i j : Index G) (x : N) :
      letI := charts G; letI := charts_manifold (old := old) G
      (frames (old := old) G).coordChange i j x = T i j x := frameTransition_eq G i j x
  have hmetric (i j : Index G) (x : N) (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) :
      ∀ v w, inner ℝ (T i j x v) (T i j x w) = inner ℝ v w :=
    transition_inner G _ _ x (mem_domain G i x hi) (mem_domain G j x hj)
  have hspan (i j : Index G) (x : N) (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (t : Fin 3) :
      (T i j x).comp ((quaternionicGenerator (S i) t).comp (T j i x)) ∈ quaternionicSpan (S j) :=
    generator_transition G _ _ x (mem_domain G i x hi) (mem_domain G j x hj) t
  letI := charts G
  letI := charts_manifold (old := old) G
  exact {
    frames := frames (old := old) G
    reduction := {
      Q := S
      generator_transport := by
        intro i j x hi hj t
        rw [adjointCoordChange_apply]
        change ((frames (old := old) G).coordChange i j x).comp
          ((quaternionicGenerator (S i) t).comp ((frames (old := old) G).coordChange j i x)) ∈ _
        rw [hT,hT]
        exact hspan i j x hi hj t }
    transition_inner := by
      intro i j x hi hj v w
      rw [hT]
      exact hmetric i j x hi hj v w }

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionHermitianTangent
