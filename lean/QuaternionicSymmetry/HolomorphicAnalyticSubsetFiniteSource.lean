import QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Published general analytic background: Grauert–Remmert, *Theory of
Stein Spaces* (1979), Introduction pp.XVII–XX and Chapter VI §4 pp.200–203.
Cartan–Serre finiteness makes H⁰(A,O_A) finite-dimensional for a compact
analytic subspace A. Separating ambient holomorphic functions yield, by
products, interpolation functions on every finite subset of A. Hence the
size of every finite subset is bounded by that dimension, so A is finite.
This disclosed corollary replaces the older unpublished Demailly locator.
The specialization to projective fibers below is a kernel proof. -/
namespace QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource
open HolomorphicSeparatedFiniteFibersSource ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe uB uF

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]

/-- A relatively closed subset of an open complex manifold, locally the
common zero locus of finitely many actual holomorphic scalar functions.
This is the standard local-equation definition of an analytic subset. -/
def AnalyticSubsetOn (U A : Set B) : Prop :=
  A ⊆ U ∧ IsClosed ((Subtype.val : U → B) ⁻¹' A) ∧
    ∀ x ∈ A, ∃ V : Set B, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ (d : ℕ) (h : B → Fin d → ℂ),
        ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) ∞ h V ∧
        A ∩ V = V ∩ h ⁻¹' {0}

/-- The Cartan–Serre finiteness corollary on a boundaryless complex manifold:
compact analytic subsets are finite when holomorphic functions separate
the ambient open complex manifold's points. -/
def SeparatedCompactAnalyticSubsetFiniteTheorem : Prop :=
  ∀ {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (U : Set B), IsOpen U →
    (∀ x y : B, x ∈ U → y ∈ U → x ≠ y →
      ∃ f : B → ℂ, ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f U ∧ f x ≠ f y) →
    ∀ A : Set B, AnalyticSubsetOn (F := F) U A → IsCompact A → A.Finite

variable [T2Space B] [IsManifold 𝓘(ℂ,F) ∞ B]

omit [IsManifold 𝓘(ℂ,F) ∞ B] in
/-- Compact projective fibers have the literal local analytic equations:
subtract the target point's holomorphic chart coordinates. Compactness
provides relative closedness without assuming a Hausdorff target here. -/
theorem analyticSubsetOn_projective_fiber
    (U : Set B) (hU : IsOpen U) (d : ℕ) (g : B → Space d)
    (hg : ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) ∞ g U)
    (p : Space d) (hCompact : IsCompact (U ∩ g ⁻¹' {p})) :
    AnalyticSubsetOn (F := F) U (U ∩ g ⁻¹' {p}) := by
  refine ⟨Set.inter_subset_left, hCompact.isClosed.preimage continuous_subtype_val, ?_⟩
  intro x hx
  let e := chartAt (Fin d → ℂ) p
  let V := U ∩ g ⁻¹' e.source
  have hp : p ∈ e.source := mem_chart_source (Fin d → ℂ) p
  have hV : IsOpen V :=
    hg.continuousOn.isOpen_inter_preimage hU e.open_source
  have hxV : x ∈ V := ⟨hx.1, by
    change g x ∈ e.source
    rw [show g x = p from hx.2]
    exact hp⟩
  refine ⟨V,hV,hxV,Set.inter_subset_left,d,
    (fun y => e (g y) - e p), ?_, ?_⟩
  · have he : ContMDiffOn 𝓘(ℂ,Fin d → ℂ) 𝓘(ℂ,Fin d → ℂ) ∞ e e.source :=
      contMDiffOn_chart
    exact (he.comp (hg.mono Set.inter_subset_left)
      (fun y hy => hy.2)).sub contMDiffOn_const
  · ext y
    constructor
    · intro hy
      refine ⟨hy.2, ?_⟩
      change e (g y) - e p = 0
      rw [show g y = p from hy.1.2, sub_self]
    · intro hy
      have hcoord : e (g y) = e p := sub_eq_zero.mp hy.2
      exact ⟨⟨hy.1.1, e.injOn hy.1.2 hp hcoord⟩,hy.1⟩

/-- The projective-fiber source interface is a checked consequence of the
literal analytic-subset theorem; its analytic equations are not assumed. -/
theorem separatedCompactProjectiveFiber_of_analyticSubset
    (hSource : SeparatedCompactAnalyticSubsetFiniteTheorem.{uB,uF}) :
    SeparatedCompactProjectiveFiberFiniteTheorem.{uB,uF} := by
  intro B F _ _ _ _ _ _ _ _ U hU hSep d g hg p hCompact
  exact hSource U hU hSep (U ∩ g ⁻¹' {p})
    (analyticSubsetOn_projective_fiber U hU d g hg p hCompact) hCompact

end
end QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource
