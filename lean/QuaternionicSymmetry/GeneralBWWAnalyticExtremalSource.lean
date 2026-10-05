import QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness
import QuaternionicSymmetry.HolomorphicLineCoreClassGroup
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections
import QuaternionicSymmetry.TorusIntegralVertexExposure

/-! Reviewed derived general analytic BWW corollary. This is an explicitly passed
literature premise, not a kernel proof of BWW. The external derivation and actual applications remain separately disclosed. Accepted author manuscript
arXiv:1802.05002v3: Lemma 3.2 pp.23–24, Lemma 3.4 pp.24–25,
Lemma 3.6 p.25, Lemma 3.7 pp.25–26. The 1 October 2026 source review discloses Kodaira/Chow/GAGA and
algebraization of the SAME holomorphic torus map to the central Gm bundle
automorphism extension of Aut(X,[L]): Brion, Facets of Algebraic Geometry I
(2022), ch.3, §2 and Lemma 2.3; Conrad D.2.1. Two consecutive sufficiently
large tensor powers give a faithful linear representation of this extension.
The given line lift, characters, complete sections and actual smooth fixed
component are matched; no claim of an internal Lean proof of this chain is made. -/
namespace QuaternionicSymmetry.GeneralBWWAnalyticExtremalSource
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineComplexTorusLinearization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open TorusIntegralVertexExposure
open scoped Manifold ContDiff
noncomputable section

variable {X F : Type} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace F X]
  (L : LineCore.{0} (B := X) 𝓘(ℂ,F)) {r : ℕ}

/-- Full compact-torus fixed set of the very base action supplied by the
line linearization. -/
def fixedSet (a : ComplexTorusLineLinearization L (r := r)) : Set X :=
  {x | ∀ t : Torus r, a.baseAction (compactInclusion r t) x = x}

/-- A literal integral fiber weight, with no scalar gauge or character shift:
the total-space equation compares the same dependent fiber at a fixed point. -/
def HasFiberWeight (a : ComplexTorusLineLinearization L (r := r))
    (x : X) (ν : Fin r → ℤ) : Prop :=
  x ∈ fixedSet L a ∧ ∀ (t : Torus r) (v : L.core.Fiber x),
    lineTotalMap L a.baseAction a.fiberEquiv (compactInclusion r t) ⟨x,v⟩ =
      ⟨x,(weightCharacter ν t : ℂ) • v⟩

def fixedWeights (a : ComplexTorusLineLinearization L (r := r)) : Set (Fin r → ℝ) :=
  {w | ∃ x ν, HasFiberWeight L a x ν ∧ realWeight ν = w}

/-- Reviewed universally quantified BWW restriction and small-component
corollary. No quaternionic hypotheses or section-generation assumption occur.
Full Picard generation concerns all represented analytic line classes. -/
def AnalyticExtremalRestrictionAndSmallSections : Prop :=
  ∀ {X F : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]
    (L : LineCore.{0} (B := X) 𝓘(ℂ,F)) {r : ℕ},
    0 < r → AmpleCore 𝓘(ℂ,F) L →
    Function.Bijective (fun m : ℤ =>
      (Quotient.mk _ L : CoreClass.{0} (B := X) 𝓘(ℂ,F)) ^ m) →
    ∀ (a : ComplexTorusLineLinearization L (r := r)),
    Function.Injective a.baseAction →
    ∀ (x : X) (ν : Fin r → ℤ), HasFiberWeight L a x ν →
    realWeight ν ∈ (convexHull ℝ (fixedWeights L a)).extremePoints ℝ →
    ∀ (Y : Set X), Y = connectedComponentIn (fixedSet L a) x →
    ∀ {b : ℕ}
      (hChart : ChartedSpace (EuclideanSpace ℂ (Fin b))
        (↥Y))
      (hManifold : letI := hChart; IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
        (↥Y)),
      letI := hChart
      ∀ (hIncl : ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) 𝓘(ℂ,F) ∞
        (Subtype.val : ↥Y → X)),
    (∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin b)) 𝓘(ℝ,F)
      (Subtype.val : ↥Y → X) y)) →
    Function.Surjective (restrictionLinear 𝓘(ℂ,F)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b)) L Subtype.val hIncl) ∧
    (0 < b → b ≤ 3 → 2 ≤ Module.finrank ℂ
      (RestrictedGlobalSections 𝓘(ℂ,F) 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
        L Subtype.val hIncl))

end
end QuaternionicSymmetry.GeneralBWWAnalyticExtremalSource
