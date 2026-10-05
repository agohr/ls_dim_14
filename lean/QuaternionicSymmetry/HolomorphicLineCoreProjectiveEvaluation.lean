import QuaternionicSymmetry.HolomorphicLineCorePullbackSections
import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic
import Mathlib.LinearAlgebra.Dual.Basis

/-! The complete linear system of a genuine represented holomorphic line
core on an arbitrary complex manifold, including a pulled-back restricted
line on a lower-dimensional complex submanifold. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation

open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

/-- Evaluation at a point as an actual complex-linear functional on the
holomorphic section space. -/
def evaluation (x : B) : Module.Dual ℂ (GlobalSections IB L) where
  toFun s := s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The real base locus of the complete linear system. -/
def baseLocus : Set B :=
  {x | ∀ s : GlobalSections IB L, s x = 0}

theorem globallyGenerated_iff_baseLocus_empty :
    GloballyGenerated IB L ↔ baseLocus IB L = ∅ := by
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
    have hx : x ∉ baseLocus IB L := by simp [h]
    by_contra hn
    apply hx
    intro s
    by_contra hs
    exact hn ⟨s, hs⟩

variable (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))

/-- Actual complete-linear-system coordinates in an arbitrary basis. -/
def basisEvaluation (x : B) : Fin (d + 1) → ℂ :=
  fun k => b k x

theorem basisEvaluation_ne_zero {x : B} (hx : x ∉ baseLocus IB L) :
    basisEvaluation IB L d b x ≠ 0 := by
  intro hz
  apply hx
  intro s
  have heval : evaluation IB L x = 0 := by
    apply b.ext
    intro k
    exact congrFun hz k
  exact congrArg (fun f : Module.Dual ℂ (GlobalSections IB L) => f s) heval

/-- The complete linear-system map to projective space, genuinely defined
outside its base locus. -/
def projectiveEvaluation :
    {x : B // x ∉ baseLocus IB L} → Space d :=
  fun x => Projectivization.mk ℂ (basisEvaluation IB L d b x.1)
    (basisEvaluation_ne_zero IB L d b x.2)

/-- A total map when the line is globally generated, using the same
complete linear system and no arbitrary values on a base locus. -/
def projectiveEvaluationOfGenerated (h : GloballyGenerated IB L) :
    B → Space d :=
  fun x => projectiveEvaluation IB L d b
    ⟨x, by simp [(globallyGenerated_iff_baseLocus_empty IB L).1 h]⟩

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
