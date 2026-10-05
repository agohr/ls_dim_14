import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Holomorphicity of the generic complete-linear-system map on the genuine
base-locus complement. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation

open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  [IsManifold IB ∞ B]
  (L : LineCore.{u} (B := B) IB)

/-- One actual local scalar coefficient of a bundled holomorphic section. -/
def chartEvaluation (i : L.Index) (x : B) (s : GlobalSections IB L) : ℂ :=
  L.core.coordChange (L.core.indexAt x) i x (s x)

theorem contMDiffOn_chartEvaluation (i : L.Index)
    (s : GlobalSections IB L) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (fun x => chartEvaluation IB L i x s)
      (L.core.baseSet i) := by
  letI := L.holomorphic
  let Z := L.core
  letI (j : L.Index) : MemTrivializationAtlas (Z.localTriv j) := ⟨⟨j, rfl⟩⟩
  intro x hx
  have hsource : (⟨x, s x⟩ : Bundle.TotalSpace ℂ Z.Fiber) ∈
      (Z.localTriv i).source := (Z.mem_localTriv_source i _).mpr hx
  have h := ((Z.localTriv i).contMDiffAt_iff
    (f := fun z : B => (⟨z, s z⟩ : Bundle.TotalSpace ℂ Z.Fiber)) hsource).mp
      (s.contMDiff x)
  exact h.2.contMDiffWithinAt

variable (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))

def basisChartEvaluation (i : L.Index) (x : B) : Coord d :=
  fun k => chartEvaluation IB L i x (b k)

theorem contMDiffOn_basisChartEvaluation (i : L.Index) :
    ContMDiffOn IB 𝓘(ℂ, Coord d) ∞
      (basisChartEvaluation IB L d b i) (L.core.baseSet i) := by
  apply contMDiffOn_pi_space.mpr
  intro k
  exact contMDiffOn_chartEvaluation IB L i (b k)

theorem basisChartEvaluation_eq_smul (i : L.Index) (x : B) :
    basisChartEvaluation IB L d b i x =
      transitionScalar L.core (L.core.indexAt x) i x •
        basisEvaluation IB L d b x := by
  funext k
  exact linear_apply_one (L.core.coordChange (L.core.indexAt x) i x) (b k x)

theorem chartTransition_ne_zero (i : L.Index) (x : B)
    (hx : x ∈ L.core.baseSet i) :
    transitionScalar L.core (L.core.indexAt x) i x ≠ 0 := by
  have hs : transitionScalar L.core (L.core.indexAt x)
      (L.core.indexAt x) x = 1 :=
    L.core.coordChange_self (L.core.indexAt x) x
      (L.core.mem_baseSet_at x) 1
  have h := scalar_comp L.core (L.core.indexAt x) i
    (L.core.indexAt x) x
      ⟨⟨L.core.mem_baseSet_at x, hx⟩, L.core.mem_baseSet_at x⟩
  rw [hs] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem basisChartEvaluation_ne_zero (i : L.Index) (x : B)
    (hx : x ∉ baseLocus IB L) (hi : x ∈ L.core.baseSet i) :
    basisChartEvaluation IB L d b i x ≠ 0 := by
  rw [basisChartEvaluation_eq_smul]
  exact smul_ne_zero (chartTransition_ne_zero IB L i x hi)
    (basisEvaluation_ne_zero IB L d b hx)

/-- Total extension of the generic basis map, used only off the base locus. -/
def projectiveEvaluationTotal (x : B) : Space d :=
  projectivize d (basisEvaluation IB L d b x)

private def localDomain (i : L.Index) : Set B :=
  {x | x ∉ baseLocus IB L} ∩ L.core.baseSet i

private theorem localProjectiveEvaluation_contMDiffOn (i : L.Index) :
    ContMDiffOn IB 𝓘(ℂ, Fin d → ℂ) ∞
      (projectiveEvaluationTotal IB L d b) (localDomain IB L i) := by
  have hcoeff := (contMDiffOn_basisChartEvaluation IB L d b i).mono
    (Set.inter_subset_right : localDomain IB L i ⊆ L.core.baseSet i)
  have hcomp := (contMDiffOn_projectivize_nonzero d).comp hcoeff
    (by
      intro x hx
      exact basisChartEvaluation_ne_zero IB L d b i x hx.1 hx.2)
  apply hcomp.congr
  intro x hx
  change projectiveEvaluationTotal IB L d b x =
    projectivize d (basisChartEvaluation IB L d b i x)
  rw [projectiveEvaluationTotal,
    projectivize_of_ne_zero d _ (basisEvaluation_ne_zero IB L d b hx.1),
    projectivize_of_ne_zero d _
      (basisChartEvaluation_ne_zero IB L d b i x hx.1 hx.2)]
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (basisChartEvaluation IB L d b i x)
    (basisEvaluation IB L d b x) _ _).2
  exact ⟨transitionScalar L.core (L.core.indexAt x) i x,
    (basisChartEvaluation_eq_smul IB L d b i x).symm⟩

/-- The actual generic complete-linear-system map is holomorphic wherever
its basis evaluation is nonzero. In particular, it applies unchanged to a
restricted line on a lower-dimensional complex submanifold. -/
theorem projectiveEvaluationTotal_contMDiffOn :
    ContMDiffOn IB 𝓘(ℂ, Fin d → ℂ) ∞
      (projectiveEvaluationTotal IB L d b)
      {x : B | x ∉ baseLocus IB L} := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let i := L.core.indexAt x
  refine ⟨L.core.baseSet i, L.core.isOpen_baseSet i,
    L.core.mem_baseSet_at x, ?_⟩
  exact localProjectiveEvaluation_contMDiffOn IB L d b i

/-- A globally generated line's genuine complete-linear-system map is a
global holomorphic map. -/
theorem projectiveEvaluationOfGenerated_contMDiff
    (h : GloballyGenerated IB L) :
    ContMDiff IB 𝓘(ℂ, Fin d → ℂ) ∞
      (projectiveEvaluationOfGenerated IB L d b h) := by
  rw [← contMDiffOn_univ]
  convert projectiveEvaluationTotal_contMDiffOn IB L d b using 1
  · funext x
    exact (projectivize_of_ne_zero d _
      (basisEvaluation_ne_zero IB L d b
        (by simpa [(globallyGenerated_iff_baseLocus_empty IB L).1 h]))).symm
  · simp [(globallyGenerated_iff_baseLocus_empty IB L).1 h]

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
