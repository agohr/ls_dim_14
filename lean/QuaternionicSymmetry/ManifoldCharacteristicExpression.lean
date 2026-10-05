import QuaternionicSymmetry.ManifoldDeRhamAllDegreeClasses
import QuaternionicSymmetry.ManifoldQuaternionicChernWeilIndependence
import Mathlib.Algebra.MvPolynomial.Basic

/-!
Degree-checked finite rational characteristic expressions evaluated in actual
manifold de Rham classes. The degree-four quaternionic bundle variable stays
separate from the tangent trace-power classes.
-/

namespace QuaternionicSymmetry.ManifoldCharacteristicExpression

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamAllDegrees
  QuaternionicSymmetry.ManifoldQuaternionicChernWeilIndependence
  QuaternionicSymmetry.ManifoldQuaternionicChernWeil
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

noncomputable instance cohomologyByDegreeAddCommGroup (n : ℕ) :
    AddCommGroup (CohomologyByDegree (E := E) (M := M) n) := by
  cases n with
  | zero =>
      change AddCommGroup (QuaternionicSymmetry.ManifoldDeRhamDegreeZero.zeroDegreeCohomology
        (E := E) (M := M))
      infer_instance
  | succ k =>
      change AddCommGroup (positiveDegreeCohomology (E := E) (M₀ := M) k)
      infer_instance

noncomputable instance cohomologyByDegreeModule (n : ℕ) :
    Module ℝ (CohomologyByDegree (E := E) (M := M) n) := by
  cases n with
  | zero =>
      change Module ℝ (QuaternionicSymmetry.ManifoldDeRhamDegreeZero.zeroDegreeCohomology
        (E := E) (M := M))
      infer_instance
  | succ k =>
      change Module ℝ (positiveDegreeCohomology (E := E) (M₀ := M) k)
      infer_instance

/-- Finite rational characteristic expressions, indexed by their genuine
cohomological degree. `u` is the rank-three bundle slot, and the other
generators are raw tangent trace powers, with no Chern-class identification. -/
inductive CharacteristicExpr : ℕ → Type
  | coeff (q : ℚ) : CharacteristicExpr 0
  | u : CharacteristicExpr 4
  | trace₂ : CharacteristicExpr 4
  | trace₄ : CharacteristicExpr 8
  | trace₆ : CharacteristicExpr 12
  | add {n : ℕ} : CharacteristicExpr n → CharacteristicExpr n → CharacteristicExpr n
  | neg {n : ℕ} : CharacteristicExpr n → CharacteristicExpr n
  | mul {p q : ℕ} : CharacteristicExpr p → CharacteristicExpr q →
      CharacteristicExpr (p + q)
  | cast {p q : ℕ} (h : p = q) : CharacteristicExpr p → CharacteristicExpr q

namespace CharacteristicExpr

/-- The corresponding ordinary four-variable rational polynomial. -/
noncomputable def polynomial : {n : ℕ} → CharacteristicExpr n →
    MvPolynomial (Fin 4) ℚ
  | _, .coeff q => MvPolynomial.C q
  | _, .u => MvPolynomial.X 0
  | _, .trace₂ => MvPolynomial.X 1
  | _, .trace₄ => MvPolynomial.X 2
  | _, .trace₆ => MvPolynomial.X 3
  | _, .add a b => polynomial a + polynomial b
  | _, .neg a => -polynomial a
  | _, .mul a b => polynomial a * polynomial b
  | _, .cast _ a => polynomial a

/-- Evaluate using the genuine cohomology wedge and degree-zero unit. -/
noncomputable def evaluate
    (u t₂ : CohomologyByDegree (E := E) (M := M) 4)
    (t₄ : CohomologyByDegree (E := E) (M := M) 8)
    (t₆ : CohomologyByDegree (E := E) (M := M) 12) :
    {n : ℕ} → CharacteristicExpr n →
      CohomologyByDegree (E := E) (M := M) n
  | _, .coeff q => (q : ℝ) • unitDegree
  | _, .u => u
  | _, .trace₂ => t₂
  | _, .trace₄ => t₄
  | _, .trace₆ => t₆
  | _, .add a b => evaluate u t₂ t₄ t₆ a + evaluate u t₂ t₄ t₆ b
  | _, .neg a => -evaluate u t₂ t₄ t₆ a
  | _, .mul a b => wedgeDegree _ _ (evaluate u t₂ t₄ t₆ a)
      (evaluate u t₂ t₄ t₆ b)
  | _, .cast h a => castDegree h (evaluate u t₂ t₄ t₆ a)

theorem evaluate_congr
    {u u' t₂ t₂' : CohomologyByDegree (E := E) (M := M) 4}
    {t₄ t₄' : CohomologyByDegree (E := E) (M := M) 8}
    {t₆ t₆' : CohomologyByDegree (E := E) (M := M) 12}
    (hu : u = u') (h₂ : t₂ = t₂') (h₄ : t₄ = t₄') (h₆ : t₆ = t₆') :
    ∀ {n : ℕ} (P : CharacteristicExpr n),
      evaluate u t₂ t₄ t₆ P = evaluate u' t₂' t₄' t₆' P := by
  intro n P
  induction P with
  | coeff q => rfl
  | u => exact hu
  | trace₂ => exact h₂
  | trace₄ => exact h₄
  | trace₆ => exact h₆
  | add a b ha hb => exact congrArg₂ (· + ·) ha hb
  | neg a ha => exact congrArg Neg.neg ha
  | mul a b ha hb => exact congrArg₂ (wedgeDegree _ _) ha hb
  | cast h a ha => exact congrArg (castDegree h) ha

theorem evaluate_add
    (u t₂ : CohomologyByDegree (E := E) (M := M) 4)
    (t₄ : CohomologyByDegree (E := E) (M := M) 8)
    (t₆ : CohomologyByDegree (E := E) (M := M) 12)
    {n : ℕ} (P R : CharacteristicExpr n) :
    evaluate u t₂ t₄ t₆ (.add P R) =
      evaluate u t₂ t₄ t₆ P + evaluate u t₂ t₄ t₆ R := rfl

theorem evaluate_mul
    (u t₂ : CohomologyByDegree (E := E) (M := M) 4)
    (t₄ : CohomologyByDegree (E := E) (M := M) 8)
    (t₆ : CohomologyByDegree (E := E) (M := M) 12)
    {p q : ℕ} (P : CharacteristicExpr p) (R : CharacteristicExpr q) :
    evaluate u t₂ t₄ t₆ (.mul P R) =
      wedgeDegree p q (evaluate u t₂ t₄ t₆ P)
        (evaluate u t₂ t₄ t₆ R) := rfl

end CharacteristicExpr

variable [FiniteDimensional ℝ E]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The global `tr(F^(k+1))` tangent Chern--Weil class. -/
noncomputable def tangentTraceClass
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (k : ℕ) : positiveDegreeCohomology (E := E) (M₀ := M)
      (QuaternionicSymmetry.LocalChernWeilOrderedTransgression.primitiveDegree k) :=
  QuotientAddGroup.mk
    ((QuaternionicSymmetry.LocalChernWeilOrderedTransgression.primitiveDegree_add_one k).symm ▸
      ((gaugeAtlas (Q := Q) (D := D) k).toTracePowerAtlas.closedGlobalForm))

theorem tangentTraceClass_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (k : ℕ) : tangentTraceClass Q D₁ k = tangentTraceClass Q D₀ k :=
  tracePowerClass_eq Q D₀ D₁ k

/-- Evaluate a degree-checked expression on actual even tangent trace classes
and a separate degree-four class. The latter can later be instantiated from
the quaternionic rank-three bundle. -/
noncomputable def evaluateTangent
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (u : CohomologyByDegree (E := E) (M := M) 4)
    {n : ℕ} (P : CharacteristicExpr n) :
    CohomologyByDegree (E := E) (M := M) n :=
  CharacteristicExpr.evaluate u (tangentTraceClass Q D 1)
    (tangentTraceClass Q D 3) (tangentTraceClass Q D 5) P

theorem evaluateTangent_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (u : CohomologyByDegree (E := E) (M := M) 4)
    {n : ℕ} (P : CharacteristicExpr n) :
    evaluateTangent Q D₁ u P = evaluateTangent Q D₀ u P := by
  exact CharacteristicExpr.evaluate_congr rfl
    (tangentTraceClass_connection_independent Q D₀ D₁ 1)
    (tangentTraceClass_connection_independent Q D₀ D₁ 3)
    (tangentTraceClass_connection_independent Q D₀ D₁ 5) P

theorem evaluateTangent_connection_independent_of_u_eq
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (u₀ u₁ : CohomologyByDegree (E := E) (M := M) 4)
    (hu : u₁ = u₀)
    {n : ℕ} (P : CharacteristicExpr n) :
    evaluateTangent Q D₁ u₁ P = evaluateTangent Q D₀ u₀ P := by
  exact CharacteristicExpr.evaluate_congr hu
    (tangentTraceClass_connection_independent Q D₀ D₁ 1)
    (tangentTraceClass_connection_independent Q D₀ D₁ 3)
    (tangentTraceClass_connection_independent Q D₀ D₁ 5) P

end QuaternionicSymmetry.ManifoldCharacteristicExpression
