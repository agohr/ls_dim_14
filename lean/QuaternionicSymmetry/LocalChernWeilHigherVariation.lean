import QuaternionicSymmetry.LocalConnectionBianchi
import QuaternionicSymmetry.LocalChernWeilQuadratic

/-!
# Covariant variation of arbitrary curvature trace words

The quadratic Chern--Weil calculation uses cancellation of connection
commutators inside a cyclic trace.  The same cancellation is independent of
word length.  This file states it for actual Frechet derivatives of finite
products of normed-algebra-valued coefficient functions, then specializes to
curvature coefficients.  Exterior alternation and closure of the resulting
higher-degree forms are separate steps.
-/

namespace QuaternionicSymmetry.LocalChernWeilHigherVariation

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionBianchi

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The product of a finite list of algebra-valued coefficient functions. -/
def wordProduct (fs : List (E → R)) (x : E) : R :=
  (fs.map (fun f => f x)).prod

theorem differentiableAt_wordProduct (fs : List (E → R)) (x : E)
    (hfs : ∀ f ∈ fs, DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (wordProduct fs) x := by
  induction fs with
  | nil =>
      change DifferentiableAt ℝ (fun _ : E => (1 : R)) x
      exact differentiableAt_const _
  | cons f fs ih =>
      have hf : DifferentiableAt ℝ f x := hfs f (by simp)
      have htail : ∀ g ∈ fs, DifferentiableAt ℝ g x := by
        intro g hg
        exact hfs g (by simp [hg])
      simpa [wordProduct] using hf.mul (ih htail)

/-- Insert the covariant derivative into every slot of a finite ordered
product.  The recursion preserves multiplication order. -/
def covariantWordVariation (Γ : Form (E := E) (A := R))
    (fs : List (E → R)) (x u : E) : R :=
  match fs with
  | [] => 0
  | f :: tail =>
      (fderiv ℝ f x u + Γ x u * f x - f x * Γ x u) *
        wordProduct tail x + f x * covariantWordVariation Γ tail x u

/-- The connection commutators in all slots telescope to the commutator of
the whole product.  This is the noncommutative Leibniz rule at arbitrary word
length, using the actual Frechet derivative. -/
theorem fderiv_wordProduct_add_commutator
    (Γ : Form (E := E) (A := R)) (fs : List (E → R)) (x u : E)
    (hfs : ∀ f ∈ fs, DifferentiableAt ℝ f x) :
    fderiv ℝ (wordProduct fs) x u +
      Γ x u * wordProduct fs x - wordProduct fs x * Γ x u =
        covariantWordVariation Γ fs x u := by
  induction fs with
  | nil =>
      change (fderiv ℝ (fun _ : E => (1 : R)) x) u +
        Γ x u * 1 - 1 * Γ x u = 0
      simp
  | cons f fs ih =>
      have hf : DifferentiableAt ℝ f x := hfs f (by simp)
      have htail : ∀ g ∈ fs, DifferentiableAt ℝ g x := by
        intro g hg
        exact hfs g (by simp [hg])
      have hp := (hf.hasFDerivAt.mul'
        (differentiableAt_wordProduct fs x htail).hasFDerivAt).fderiv
      change fderiv ℝ (fun y => f y * wordProduct fs y) x = _ at hp
      rw [show wordProduct (f :: fs) =
          (fun y => f y * wordProduct fs y) by rfl, hp]
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, op_smul_eq_mul]
      change f x * (fderiv ℝ (wordProduct fs) x) u +
          (fderiv ℝ f x) u * wordProduct fs x +
          Γ x u * (f x * wordProduct fs x) -
          (f x * wordProduct fs x) * Γ x u =
        ((fderiv ℝ f x) u + Γ x u * f x - f x * Γ x u) *
          wordProduct fs x + f x * covariantWordVariation Γ fs x u
      rw [← ih htail]
      noncomm_ring

/-- A cyclic trace kills the commutator of a whole product, so its actual
directional derivative is the sum of covariant slot variations. -/
theorem fderiv_trace_wordProduct
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (fs : List (E → R)) (x u : E)
    (hfs : ∀ f ∈ fs, DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => T (wordProduct fs y)) x u =
      T (covariantWordVariation Γ fs x u) := by
  have hp := (T.hasFDerivAt.comp x
    (differentiableAt_wordProduct fs x hfs).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => T (wordProduct fs y)) x =
    T.comp (fderiv ℝ (wordProduct fs) x) at hp
  rw [hp]
  have hv := fderiv_wordProduct_add_commutator Γ fs x u hfs
  have hc : T (Γ x u * wordProduct fs x -
      wordProduct fs x * Γ x u) = 0 := by
    rw [map_sub, hT, sub_self]
  calc
    T (fderiv ℝ (wordProduct fs) x u) =
        T (fderiv ℝ (wordProduct fs) x u +
          (Γ x u * wordProduct fs x - wordProduct fs x * Γ x u)) := by
      rw [map_add, hc, add_zero]
    _ = T (covariantWordVariation Γ fs x u) := by
      convert congrArg T hv using 1
      abel

/-- The ordered product of curvature coefficients, with the same vector-word
type as `LocalTraceWordGauge.trace_curvature_word_transition`. -/
def curvatureWordProduct (Γ : Form (E := E) (A := R))
    (vs : List (Fin 2 → E)) (x : E) : R :=
  wordProduct (vs.map (fun v => fun y => curvature Γ y (v 0) (v 1))) x

/-- Covariant slot variation of a curvature word. -/
def curvatureWordVariation (Γ : Form (E := E) (A := R))
    (vs : List (Fin 2 → E)) (x u : E) : R :=
  covariantWordVariation Γ
    (vs.map (fun v => fun y => curvature Γ y (v 0) (v 1))) x u

theorem curvatureWordVariation_cons (Γ : Form (E := E) (A := R))
    (v : Fin 2 → E) (vs : List (Fin 2 → E)) (x u : E) :
    curvatureWordVariation Γ (v :: vs) x u =
      covariantCurvatureDerivative Γ x u (v 0) (v 1) *
        curvatureWordProduct Γ vs x +
      curvature Γ x (v 0) (v 1) * curvatureWordVariation Γ vs x u := rfl

theorem curvatureWordProduct_eq_formWord (Γ : Form (E := E) (A := R))
    (vs : List (Fin 2 → E)) (x : E) :
    curvatureWordProduct Γ vs x =
      (vs.map (fun v => LocalConnectionForms.curvatureForm Γ x v)).prod := by
  simp only [curvatureWordProduct, wordProduct, List.map_map, Function.comp_def,
    LocalConnectionForms.curvatureForm_apply]

/-- The all-length trace formula applied to actual curvature coefficients.
Each slot's covariant derivative is the Bianchi derivative of that curvature
coefficient.  Alternating these coefficients into a closed higher Chern--Weil
form is not asserted here. -/
theorem fderiv_trace_curvatureWordProduct
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (vs : List (Fin 2 → E)) (x u : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) :
    fderiv ℝ (fun y => T (curvatureWordProduct Γ vs y)) x u =
      T (curvatureWordVariation Γ vs x u) := by
  apply fderiv_trace_wordProduct T hT Γ _ x u
  intro f hf
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hf
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := LocalConnectionExterior.differentiableAt_curvatureForm Γ x h₁ h₂
  have hcoeff := hF.continuousAlternatingMap_apply_const ![v 0, v 1]
  simpa only [LocalConnectionForms.curvatureForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hcoeff

end
end QuaternionicSymmetry.LocalChernWeilHigherVariation
