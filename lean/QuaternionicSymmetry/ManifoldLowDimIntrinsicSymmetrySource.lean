import QuaternionicSymmetry.ManifoldRiemannianIntrinsicSymmetry
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Source-faithful *derived classification corollary* contracts for the
intrinsic metric endpoint, without introducing types for Wolf models.

Poon–Salamon 1991, Theorem 1.1 classifies complete connected positive
eight-dimensional quaternionic-Kähler metrics up to isometry as three
symmetric metrics. BWW 2018, Theorem 1.1 classifies compact simply connected
positive quaternionic-Kähler metrics of dimensions twelve and sixteen up
to homothety as symmetric metrics. Both therefore imply genuine global
point symmetries. Applying the source theorems to the present `P` still
requires the geometric bridge from its preserved quaternionic reduction
to the source's Levi-Civita holonomy condition; compactness supplies
completeness in dimension eight. These contracts record the full derived
boundary and are not themselves proofs of the cited theorems.

The four-dimensional case is intentionally absent: Hitchin 1981 T6.1
requires an actual Kähler twistor and concludes conformal equivalence;
the Weyl-orientation and conformal-Einstein metric-rigidity chain remain
separate. -/

namespace QuaternionicSymmetry.ManifoldLowDimIntrinsicSymmetrySource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldRiemannianIntrinsicSymmetry
open scoped Manifold ContDiff

noncomputable section

/-- Poon–Salamon 1991, T1.1, after compactness-to-completeness,
quaternionic-reduction-to-holonomy, and symmetry of the three classified
metrics. This is a literature contract, not an axiom or a model catalog. -/
def PoonSalamon8SymmetrySource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M)),
    Module.finrank ℝ E = 8 → IsRiemannianSymmetric P.tangent

/-- BWW 2018, T1.1, after the quaternionic-reduction-to-holonomy bridge
and preservation of global point symmetries under positive homothety.
Unlike Poon–Salamon 1.1 this source requires *actual simple connectedness*. -/
def BWW34SymmetrySource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [Nonempty M] [SimplyConnectedSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), (n = 3 ∨ n = 4) → Module.finrank ℝ E = 4*n →
      IsRiemannianSymmetric P.tangent

/-- Apply the eight-dimensional literature corollary to exactly the actual
compact connected metric in `P`; no twistor or Wolf predicate is inserted. -/
theorem symmetric_of_poonSalamon8
    (hSource : PoonSalamon8SymmetrySource)
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 8) :
    IsRiemannianSymmetric P.tangent :=
  hSource P hDim

/-- Apply BWW's twelve/sixteen-dimensional metric result with its
simply-connected hypothesis still visible in the Lean type. -/
theorem symmetric_of_bww34
    (hSource : BWW34SymmetrySource)
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [Nonempty M] [SimplyConnectedSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : n = 3 ∨ n = 4)
    (hDim : Module.finrank ℝ E = 4*n) :
    IsRiemannianSymmetric P.tangent :=
  hSource P n hn hDim

end
end QuaternionicSymmetry.ManifoldLowDimIntrinsicSymmetrySource
