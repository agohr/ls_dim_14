import QuaternionicSymmetry.HolomorphicLineHermitianPositiveRoot
import QuaternionicSymmetry.HolomorphicLineGauge
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Pullback of actual Hermitian line metrics along genuine holomorphic
gauges between arbitrary covers. -/

namespace QuaternionicSymmetry.HolomorphicLineHermitianGauge

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.HolomorphicLineHermitianMetric
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff Topology
noncomputable section
universe uB uF uI

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]

/-- Complex-smooth scalar maps are smooth for the underlying real
manifold structures. The identity model charts leave only restriction of
scalars in ordinary `ContDiffWithinAt`. -/
theorem holomorphicOn_realSmooth {f : B → ℂ} {s : Set B}
    (hf : ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f s) :
    ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,ℂ) ∞ f s := by
  intro x hx
  have hfx := hf x hx
  rw [contMDiffWithinAt_iff] at hfx ⊢
  refine ⟨hfx.1, ?_⟩
  exact hfx.2.restrict_scalars ℝ

/-- The real-smooth squared modulus of a complex-holomorphic scalar map. -/
theorem normSq_smoothOn {f : B → ℂ} {s : Set B}
    (hf : ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f s) :
    ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ (fun x => Complex.normSq (f x)) s := by
  have hr := holomorphicOn_realSmooth hf
  intro x hx
  simpa only [Complex.normSq_eq_norm_sq] using
    ((contDiff_norm_sq ℝ (n := ∞)).contDiffAt.contMDiffAt).comp_contMDiffWithinAt x
      (hr x hx)

variable (L M : LineCore.{uI} (B := B) 𝓘(ℂ,F))

def gaugeForward (h : Isomorphic 𝓘(ℂ,F) L M)
    (i : L.Index) (a : M.Index) (x : B) : ℂ := by
  letI := L.holomorphic
  letI := M.holomorphic
  exact (Classical.choice h).forward i a x

/-- Pull back a local frame norm along the gauge, using the distinguished
chart of the target core. The ensuing fixed-chart lemma removes any
dependence on this choice wherever another target chart is available. -/
def gaugePullbackWeight (h : Isomorphic 𝓘(ℂ,F) L M)
    (m : HermitianLineMetric M) (i : L.Index) (x : B) : ℝ := by
  letI := L.holomorphic
  letI := M.holomorphic
  let e := Classical.choice h
  exact Complex.normSq (e.forward i (M.core.indexAt x) x) *
    m.frameNormSq (M.core.indexAt x) x

/-- The pulled-back weight has the expected local formula on *every*
common source-target chart, not only the distinguished target chart. -/
theorem gaugePullbackWeight_eq_chart (h : Isomorphic 𝓘(ℂ,F) L M)
    (m : HermitianLineMetric M) (i : L.Index) (a : M.Index) (x : B)
    (hx : x ∈ L.core.baseSet i ∩ M.core.baseSet a) :
    gaugePullbackWeight L M h m i x =
      Complex.normSq (gaugeForward L M h i a x) * m.frameNormSq a x := by
  letI := L.holomorphic
  letI := M.holomorphic
  let e := Classical.choice h
  let b := M.core.indexAt x
  have hb : x ∈ M.core.baseSet b := M.core.mem_baseSet_at x
  have hself : transitionScalar L.core i i x = 1 :=
    L.core.coordChange_self i x hx.1 1
  have hc := e.forward_compat i i a b x
    ⟨⟨⟨hx.1, hx.1⟩, hx.2⟩, hb⟩
  rw [hself, mul_one] at hc
  have hm := m.overlap a b x ⟨hx.2, hb⟩
  change Complex.normSq (e.forward i b x) * m.frameNormSq b x =
    Complex.normSq (e.forward i a x) * m.frameNormSq a x
  rw [← hc, Complex.normSq_mul, hm]
  ring

/-- An actual holomorphic gauge pulls a Hermitian line metric back to the
source line, independent of either chosen cover. -/
def gaugePullbackMetric (h : Isomorphic 𝓘(ℂ,F) L M)
    (m : HermitianLineMetric M) : HermitianLineMetric L := by
  letI := L.holomorphic
  letI := M.holomorphic
  let e := Classical.choice h
  exact {
    frameNormSq := gaugePullbackWeight L M h m
    positive := by
      intro i x hx
      let a := M.core.indexAt x
      have ha : x ∈ M.core.baseSet a := M.core.mem_baseSet_at x
      change 0 < Complex.normSq (e.forward i a x) * m.frameNormSq a x
      exact mul_pos (Complex.normSq_pos.mpr
        (e.forward_ne_zero i a x ⟨hx, ha⟩)) (m.positive a x ha)
    smooth := by
      intro i
      apply contMDiffOn_of_locally_contMDiffOn
      intro x hx
      let a := M.core.indexAt x
      refine ⟨M.core.baseSet a, M.core.isOpen_baseSet a,
        M.core.mem_baseSet_at x, ?_⟩
      have hn := normSq_smoothOn (e.forward_holomorphic i a)
      have hm : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ (m.frameNormSq a)
          (L.core.baseSet i ∩ M.core.baseSet a) :=
        (m.smooth a).mono (Set.inter_subset_right)
      have hmul := hn.mul hm
      exact hmul.congr (by
        intro y hy
        exact gaugePullbackWeight_eq_chart L M h m i a y hy)
    overlap := by
      intro i j x hx
      let a := M.core.indexAt x
      have ha : x ∈ M.core.baseSet a := M.core.mem_baseSet_at x
      have hi := gaugePullbackWeight_eq_chart L M h m i a x ⟨hx.1, ha⟩
      have hj := gaugePullbackWeight_eq_chart L M h m j a x ⟨hx.2, ha⟩
      have hself : transitionScalar M.core a a x = 1 :=
        M.core.coordChange_self a x ha 1
      have hc := e.forward_compat i j a a x
        ⟨⟨⟨hx.1, hx.2⟩, ha⟩, ha⟩
      rw [hself, one_mul] at hc
      rw [hi, hj]
      change Complex.normSq (e.forward i a x) * m.frameNormSq a x =
        Complex.normSq (transitionScalar L.core i j x) *
          (Complex.normSq (e.forward j a x) * m.frameNormSq a x)
      rw [hc, Complex.normSq_mul]
      ring }

end
end QuaternionicSymmetry.HolomorphicLineHermitianGauge
