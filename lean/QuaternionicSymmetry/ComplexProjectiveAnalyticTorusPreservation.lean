import QuaternionicSymmetry.AnalyticSubsetContinuation
import QuaternionicSymmetry.ComplexProjectiveDiagonalJointHolomorphic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! A closed projective analytic subset invariant under a compact diagonal
torus is invariant under its complex torus. Analytic continuation of
exponential curves replaces an appeal to Chow and Laurent polynomial density. -/
namespace QuaternionicSymmetry.ComplexProjectiveAnalyticTorusPreservation
open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalJointHolomorphic ComplexTorusHolomorphicStructure
open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open HolomorphicEmbeddingLocalEquations AnalyticSubsetContinuation
open Filter Set
open scoped Manifold ContDiff Topology
noncomputable section

variable {r d : ℕ}

def expCurve (b : Fin r → ℝ) (w : ℂ) : ComplexTorus r :=
  fun i => Units.mk0 (Complex.exp (w * b i)) (Complex.exp_ne_zero _)

lemma expCurve_holomorphic (b : Fin r → ℝ) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin r → ℂ) ∞ (expCurve b) := by
  apply ContMDiff.of_comp_isOpenEmbedding (torusVal_isOpenEmbedding r)
  apply ContDiff.contMDiff
  apply contDiff_pi.mpr
  intro i
  exact Complex.contDiff_exp.comp (contDiff_id.mul contDiff_const)

lemma expCurve_zero (b : Fin r → ℝ) : expCurve b 0 = 1 := by
  ext i
  simp [expCurve]

lemma expCurve_imaginary (b : Fin r → ℝ) (t : ℝ) :
    expCurve b ((t : ℂ) * Complex.I) = compactInclusion r (fun i => Circle.exp (t*b i)) := by
  funext i
  apply Units.ext
  change Complex.exp ((t : ℂ) * Complex.I * (b i : ℂ)) =
    Complex.exp ((t*b i : ℝ) * Complex.I)
  congr 1
  push_cast
  ring

lemma tendsto_imaginary_punctured :
    Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.I) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

set_option maxHeartbeats 800000 in
theorem mapsTo_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : LocalHolomorphicEquations (F := Fin d → ℂ) A) (hClosed : IsClosed A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    ∀ z : ComplexTorus r, Set.MapsTo (projectiveAction μ z) A A := by
  have hExp (b : Fin r → ℝ) (w : ℂ) (x : Space d) (hx : x ∈ A) :
      projectiveAction μ (expCurve b w) x ∈ A := by
    let f : ℂ → Space d := fun w => projectiveAction μ (expCurve b w) x
    have hp : ContMDiff 𝓘(ℂ,ℂ) (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,Fin d → ℂ)) ∞
        (fun w => (expCurve b w,x)) := (expCurve_holomorphic b).prodMk contMDiff_const
    have hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin d → ℂ) ∞ f :=
      ContMDiff.comp (f := fun w : ℂ => (expCurve b w,x))
        (g := fun q : ComplexTorus r × Space d => projectiveAction μ q.1 q.2)
        (jointAction_contMDiff μ) hp
    have h0 : f 0 ∈ A := by simpa [f, expCurve_zero, projectiveAction_one] using hx
    apply mapsTo_of_frequently hA hClosed hf h0 (z := 0) _ w
    apply tendsto_imaginary_punctured.frequently
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro t
    change projectiveAction μ (expCurve b ((t : ℂ) * Complex.I)) x ∈ A
    rw [expCurve_imaginary]
    exact hCompact _ hx
  intro z x hx
  let b : Fin r → ℝ := fun i => (Complex.log (z i : ℂ)).re
  let t : Torus r := fun i => Circle.exp (Complex.log (z i : ℂ)).im
  have hz : z = compactInclusion r t * expCurve b 1 := by
    funext i
    apply Units.ext
    change (z i : ℂ) = Complex.exp ((Complex.log (z i : ℂ)).im * Complex.I) *
      Complex.exp (1 * (Complex.log (z i : ℂ)).re)
    rw [one_mul, ← Complex.exp_add, add_comm, Complex.re_add_im,
      Complex.exp_log (z i).ne_zero]
  rw [hz, projectiveAction_mul]
  exact hCompact t (hExp b 1 x hx)

end
end QuaternionicSymmetry.ComplexProjectiveAnalyticTorusPreservation
