import QuaternionicSymmetry.ManifoldTwistorProjectiveHolomorphicMap
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Genuine geometric very-ampleness and ampleness criteria for the actual
twistor contact-line twists. These predicates are not established by their
definitions; their fields require real basepoint-freeness, embedding, and
injectivity of the actual manifold derivative. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness

open ManifoldTwistorProjectiveBasisCoordinates
open ManifoldTwistorProjectiveHolomorphicMap
open ManifoldTwistorLinearSystem
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open ComplexProjectiveTopology
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

/-- Global generation of the actual one-dimensional line fibers: at each
point, some global holomorphic section has a nonzero value. For a line fiber,
this is the usual generating condition and is separate from ampleness. -/
def GloballyGeneratedTwist (r : ℤ) : Prop :=
  ∀ x : SphereBundleTotal Q,
    ∃ s : GlobalSections Q D L r, evaluation Q D L r x s ≠ 0

theorem globallyGeneratedTwist_iff_baseLocus_empty (r : ℤ) :
    GloballyGeneratedTwist Q D L r ↔ baseLocus Q D L r = ∅ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := h x
      exact False.elim (hs (hx s))
    · intro hx
      simp at hx
  · intro h x
    have hx : x ∉ baseLocus Q D L r := by simp [h]
    have hex : ∃ s : GlobalSections Q D L r,
        evaluation Q D L r x s ≠ 0 := by
      by_contra hn
      apply hx
      intro s
      by_contra hs
      exact hn ⟨s, hs⟩
    exact hex

theorem basisProjectiveEvaluationTotal_contMDiff_of_basepointFree
    (r : ℤ) (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections Q D L r))
    (h : baseLocus Q D L r = ∅) :
    letI := A.charts
    ContMDiff 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ) ∞
      (basisProjectiveEvaluationTotal Q D L r d b) := by
  letI := A.charts
  rw [← contMDiffOn_univ]
  convert basisProjectiveEvaluationTotal_contMDiffOn Q D L r d b using 1
  simp [h]

/-- A positive twist has a genuine projective holomorphic embedding from
its full linear system if some finite basis makes the actual evaluation
basepoint-free, topologically embedded, and immersive in the differential
sense. No such basis or conclusion is assumed by the definition. -/
def VeryAmpleTwist (k : ℕ) : Prop :=
  letI := A.charts
  ∃ (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections Q D L (k : ℤ))),
    baseLocus Q D L (k : ℤ) = ∅ ∧
    Topology.IsEmbedding (basisProjectiveEvaluationTotal Q D L (k : ℤ) d b) ∧
    ∀ x : SphereBundleTotal Q,
      Function.Injective
        (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ)
          (basisProjectiveEvaluationTotal Q D L (k : ℤ) d b) x)

/-- The standard geometric ampleness criterion: an actual positive tensor
power yields a very ample complete linear system. -/
def AmpleContactLine : Prop :=
  ∃ k : ℕ, 0 < k ∧ VeryAmpleTwist Q D L k

theorem veryAmpleTwist_globallyGenerated (k : ℕ)
    (h : VeryAmpleTwist Q D L k) :
    GloballyGeneratedTwist Q D L (k : ℤ) := by
  rcases h with ⟨d, b, hbase, _hemb, _hdiff⟩
  exact (globallyGeneratedTwist_iff_baseLocus_empty Q D L (k : ℤ)).2 hbase

/-- The differential-injectivity clause alone forces the genuine section
space to have at least one more dimension than the complex twistor manifold.
This bound is not inferred from mere ampleness or a nonzero section. -/
theorem veryAmpleTwist_section_finrank_bound (k : ℕ)
    (h : VeryAmpleTwist Q D L k) (x : SphereBundleTotal Q) :
    2 * n + 2 ≤ Module.finrank ℂ (GlobalSections Q D L (k : ℤ)) := by
  letI := A.charts
  rcases h with ⟨d, b, _hbase, _hemb, hdiff⟩
  have hle : Module.finrank ℂ (ComplexTwistorModel n) ≤
      Module.finrank ℂ (Fin d → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective (hdiff x)
  have hdim : 2 * n + 1 ≤ d := by simpa [ComplexTwistorModel] using hle
  have hsections : Module.finrank ℂ (GlobalSections Q D L (k : ℤ)) = d + 1 := by
    simpa using Module.finrank_eq_card_basis b
  omega

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness
