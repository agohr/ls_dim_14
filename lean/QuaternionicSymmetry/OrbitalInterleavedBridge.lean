import QuaternionicSymmetry.ForresterDiagonalInput
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The explicit permutation between grouped and interleaved quaternionic
coordinates in the symplectic Harish--Chandra formula. -/

namespace QuaternionicSymmetry.OrbitalInterleavedBridge

open Matrix MeasureTheory CompactSymplecticHaar OrbitalDiagonalSpectra
  ForresterDiagonalInput

noncomputable section

def groupedToInterleaved (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin n × Fin 2 where
  toFun := fun i => match i with
    | Sum.inl j => (j, 0)
    | Sum.inr j => (j, 1)
  invFun := fun i => if i.2 = 0 then Sum.inl i.1 else Sum.inr i.1
  left_inv := by
    intro i
    cases i <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    fin_cases j <;> simp

/-- Reindex a square matrix from grouped to interleaved block coordinates. -/
def interleave {n : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  Matrix.reindex (groupedToInterleaved n) (groupedToInterleaved n) A

theorem interleave_apply {n : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (i j : Fin n × Fin 2) :
    interleave A i j = A ((groupedToInterleaved n).symm i)
      ((groupedToInterleaved n).symm j) := rfl

theorem interleave_mul {n : ℕ} (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    interleave (A * B) = interleave A * interleave B :=
  Matrix.reindexAlgEquiv_mul ℂ ℂ (groupedToInterleaved n) A B

theorem interleave_conjTranspose {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    (interleave A)ᴴ = interleave Aᴴ :=
  Matrix.conjTranspose_reindex _ _ A

theorem interleave_transpose {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    (interleave A)ᵀ = interleave Aᵀ := rfl

theorem interleave_trace {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    (interleave A).trace = A.trace := by
  simp [interleave, Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply,
    ← (groupedToInterleaved n).symm.sum_comp]

/-- The printed source's `I_n ⊗ [[0,1],[-1,0]]` in interleaved indices. -/
def interleavedJ (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  interleave (standardJ n)

theorem interleave_standardJ (n : ℕ) :
    interleave (standardJ n) = interleavedJ n := rfl

theorem interleavedJ_apply (n : ℕ) (a b : Fin n × Fin 2) :
    interleavedJ n a b = if a.1 = b.1 then
      if a.2 = 0 ∧ b.2 = 1 then 1 else if a.2 = 1 ∧ b.2 = 0 then -1 else 0
      else 0 := by
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [interleave_apply, groupedToInterleaved, interleavedJ,
      standardJ, Matrix.fromBlocks, Matrix.one_apply];
    split_ifs <;> simp_all

theorem interleavedJ_sq (n : ℕ) : interleavedJ n * interleavedJ n = -1 := by
  change interleave (standardJ n) * interleave (standardJ n) = -1
  rw [← interleave_mul, standardJ_sq]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (groupedToInterleaved n)).map_neg 1 |>.trans (by simp)

/-- The interleaved stabilizer's transpose-left equation is exactly the
printed source's transpose-right equation. -/
theorem interleaved_source_preservation (n : ℕ)
    (g : stabilizer (interleavedJ n)) :
    (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) * interleavedJ n *
      (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)ᵀ = interleavedJ n :=
  (OrbitalSourceConventions.transpose_preservation_iff _ _ (interleavedJ_sq n)).mp g.2

/-- The diagonal arguments become genuine interleaved quaternionic
`diag(i x_j,-i x_j)` blocks. -/
def interleavedAntiHermitianDiagonal {n : ℕ} (x : Fin n → ℝ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  Matrix.of fun i j => if i = j then
    if i.2 = 0 then Complex.I * (x i.1 : ℂ) else -Complex.I * (x i.1 : ℂ)
    else 0

theorem interleave_antiHermitianDiagonal {n : ℕ} (x : Fin n → ℝ) :
    interleave (antiHermitianDiagonal x) = interleavedAntiHermitianDiagonal x := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [interleave_apply, groupedToInterleaved, interleavedAntiHermitianDiagonal,
      antiHermitianDiagonal, hermitianDiagonal, Matrix.diagonal_apply,
      Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]

theorem interleavedAntiHermitianDiagonal_conjTranspose {n : ℕ} (x : Fin n → ℝ) :
    (interleavedAntiHermitianDiagonal x)ᴴ =
      -interleavedAntiHermitianDiagonal x := by
  rw [← interleave_antiHermitianDiagonal x, interleave_conjTranspose,
    antiHermitianDiagonal_conjTranspose]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (groupedToInterleaved n)).map_neg _

/-- Each literal 2-by-2 block is `diag(i x_j, -i x_j)`, a quaternionic
block of source form (1.7) with off-diagonal entry zero. -/
theorem interleavedAntiHermitianDiagonal_block {n : ℕ} (x : Fin n → ℝ)
    (i j : Fin n) (a b : Fin 2) :
    interleavedAntiHermitianDiagonal x (i, a) (j, b) =
      if i = j then
        Matrix.diagonal (fun c : Fin 2 =>
          if c = 0 then Complex.I * (x i : ℂ) else -Complex.I * (x i : ℂ)) a b
      else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [interleavedAntiHermitianDiagonal, Matrix.of_apply, Prod.mk.injEq]

/-- Reindexing gives a continuous equivalence of finite unitary groups. -/
def unitaryReindex {κ τ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] (e : κ ≃ τ) :
    Matrix.unitaryGroup κ ℂ ≃* Matrix.unitaryGroup τ ℂ where
  toFun u := ⟨Matrix.reindex e e u.1, by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := (Matrix.mem_unitaryGroup_iff').mp u.2
    rw [Matrix.star_eq_conjTranspose] at h ⊢
    calc
      (Matrix.reindex e e u.1)ᴴ * Matrix.reindex e e u.1 =
          Matrix.reindex e e (u.1ᴴ * u.1) := by
            rw [Matrix.conjTranspose_reindex]
            exact (Matrix.reindexAlgEquiv_mul ℂ ℂ e _ _).symm
      _ = 1 := by rw [h]; exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_one⟩
  invFun u := ⟨Matrix.reindex e.symm e.symm u.1, by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := (Matrix.mem_unitaryGroup_iff').mp u.2
    rw [Matrix.star_eq_conjTranspose] at h ⊢
    calc
      (Matrix.reindex e.symm e.symm u.1)ᴴ * Matrix.reindex e.symm e.symm u.1 =
          Matrix.reindex e.symm e.symm (u.1ᴴ * u.1) := by
            rw [Matrix.conjTranspose_reindex]
            exact (Matrix.reindexAlgEquiv_mul ℂ ℂ e.symm _ _).symm
      _ = 1 := by rw [h]; exact (Matrix.reindexAlgEquiv ℂ ℂ e.symm).map_one⟩
  left_inv u := by
    apply Subtype.ext
    simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  right_inv u := by
    apply Subtype.ext
    simp [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  map_mul' u v := by
    apply Subtype.ext
    exact Matrix.reindexAlgEquiv_mul ℂ ℂ e u.1 v.1

/-- Reindexing identifies the two compact unitary stabilizer groups. -/
def stabilizerReindex {κ τ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] (J : Matrix κ κ ℂ) (e : κ ≃ τ) :
    stabilizer J ≃* stabilizer (Matrix.reindex e e J) where
  toFun g := ⟨unitaryReindex e g.1, by
    change (Matrix.reindex e e g.1.1)ᵀ * Matrix.reindex e e J *
      Matrix.reindex e e g.1.1 = Matrix.reindex e e J
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) g.2
    simpa only [map_mul, Matrix.reindexAlgEquiv_apply,
      Matrix.transpose_reindex] using h⟩
  invFun g := ⟨(unitaryReindex e).symm g.1, by
    have hJ : Matrix.reindex e.symm e.symm (Matrix.reindex e e J) = J := by
      ext i j
      simp [Matrix.reindex_apply]
    change (Matrix.reindex e.symm e.symm g.1.1)ᵀ * J *
      Matrix.reindex e.symm e.symm g.1.1 = J
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e.symm) g.2
    simpa only [map_mul, Matrix.reindexAlgEquiv_apply,
      Matrix.transpose_reindex, hJ] using h⟩
  left_inv g := by
    apply Subtype.ext
    exact (unitaryReindex e).left_inv g.1
  right_inv g := by
    apply Subtype.ext
    exact (unitaryReindex e).right_inv g.1
  map_mul' g h := by
    apply Subtype.ext
    exact (unitaryReindex e).map_mul g.1 h.1

/-- The literal interleaved source group is isomorphic to the grouped
`CompactSymplecticHaar.Group`. -/
def groupInterleave (n : ℕ) : Group n ≃* stabilizer (interleavedJ n) := by
  exact stabilizerReindex (standardJ n) (groupedToInterleaved n)

theorem stabilizerReindex_continuous {κ τ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] (J : Matrix κ κ ℂ) (e : κ ≃ τ) :
    Continuous (stabilizerReindex J e) := by
  have hval : Continuous (fun g : stabilizer J => (g.1.1 : Matrix κ κ ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmatrix : Continuous (fun g : stabilizer J => Matrix.reindex e e g.1.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : stabilizer J => g.1.1 (e.symm i) (e.symm j))
    exact (continuous_apply _).comp ((continuous_apply _).comp hval)
  exact (hmatrix.subtype_mk _).subtype_mk _

theorem stabilizerReindex_symm_continuous {κ τ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] (J : Matrix κ κ ℂ) (e : κ ≃ τ) :
    Continuous (stabilizerReindex J e).symm := by
  have hJ : Matrix.reindex e.symm e.symm (Matrix.reindex e e J) = J := by
    ext i j
    simp [Matrix.reindex_apply]
  have hval : Continuous (fun g : stabilizer (Matrix.reindex e e J) =>
      (g.1.1 : Matrix τ τ ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmatrix : Continuous (fun g : stabilizer (Matrix.reindex e e J) =>
      Matrix.reindex e.symm e.symm g.1.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun g : stabilizer (Matrix.reindex e e J) =>
      g.1.1 (e i) (e j))
    exact (continuous_apply _).comp ((continuous_apply _).comp hval)
  exact (hmatrix.subtype_mk _).subtype_mk _

def groupInterleaveContinuous (n : ℕ) : Group n ≃ₜ* stabilizer (interleavedJ n) :=
  { groupInterleave n with
    continuous_toFun := stabilizerReindex_continuous _ _
    continuous_invFun := stabilizerReindex_symm_continuous _ _ }

/-- Normalized Haar measure is carried exactly by the basis permutation. -/
theorem probability_interleave (n : ℕ) :
    Measure.map (groupInterleaveContinuous n) (probability (standardJ n)) =
      probability (interleavedJ n) := by
  let e := groupInterleaveContinuous n
  haveI : Measure.IsHaarMeasure
      (Measure.map e (probability (standardJ n))) := by infer_instance
  haveI : IsProbabilityMeasure (Measure.map e (probability (standardJ n))) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The literal source trace is unchanged by the simultaneous permutation
of its two matrix arguments and symplectic group element. -/
theorem sourceTrace_interleave {n : ℕ} (x y : Fin n → ℝ) (g : Group n) :
    Matrix.trace (interleavedAntiHermitianDiagonal x *
      ((groupInterleave n g).1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) *
      (interleavedAntiHermitianDiagonal y)ᴴ *
      ((groupInterleave n g).1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)ᴴ) =
    Matrix.trace (antiHermitianDiagonal x *
      (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
      (antiHermitianDiagonal y)ᴴ *
      (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ) := by
  rw [← interleave_trace]
  congr 1
  have hg : ((groupInterleave n g).1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) =
      interleave (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := rfl
  rw [hg, ← interleave_antiHermitianDiagonal x,
    ← interleave_antiHermitianDiagonal y,
    interleave_conjTranspose, interleave_conjTranspose]
  simp only [interleave_mul]

/-- The literal printed complex trace is real, so the real-valued
exponential in the formal contract is the printed exponential. -/
theorem interleaved_sourceTrace_im_zero {n : ℕ} (x y : Fin n → ℝ)
    (g : stabilizer (interleavedJ n)) :
    (Matrix.trace (interleavedAntiHermitianDiagonal x *
      (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) *
      (interleavedAntiHermitianDiagonal y)ᴴ *
      (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)ᴴ)).im = 0 := by
  have hy := interleavedAntiHermitianDiagonal_conjTranspose y
  have hy' : ((interleavedAntiHermitianDiagonal y)ᴴ)ᴴ =
      -(interleavedAntiHermitianDiagonal y)ᴴ := by
    rw [Matrix.conjTranspose_conjTranspose, hy]
    simp
  exact trace_pairing_im_zero (interleavedJ n)
    (interleavedAntiHermitianDiagonal x)
    (interleavedAntiHermitianDiagonal y)ᴴ
    (interleavedAntiHermitianDiagonal_conjTranspose x) hy' g

/-- The literal interleaved-block specialization of Eq. (1.8). -/
def LiteralInterleavedFormula : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (x y : Fin n → ℝ),
    (∀ i, 0 < x i) → (∀ i, 0 < y i) →
    realOddVandermonde x * realOddVandermonde y ≠ 0 →
    (∫ g : stabilizer (interleavedJ n),
      Real.exp ((Matrix.trace (interleavedAntiHermitianDiagonal x *
        (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) *
        (interleavedAntiHermitianDiagonal y)ᴴ *
        (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)ᴴ)).re / 2)
      ∂probability (interleavedJ n)) =
      (OrbitalOddDeterminantBase.sourceConstant n : ℝ) *
        realSourceDeterminant x y /
        (realOddVandermonde x * realOddVandermonde y)

/-- The literal interleaved source formula implies the grouped contract used
by the existing positive-parameter and coefficient theorems. -/
theorem literal_implies_grouped (hsource : LiteralInterleavedFormula) :
    ForresterDiagonalFormula := by
  intro n hn x y hx hy hΔ
  let e := groupInterleaveContinuous n
  let f : stabilizer (interleavedJ n) → ℝ := fun g =>
    Real.exp ((Matrix.trace (interleavedAntiHermitianDiagonal x *
      (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) *
      (interleavedAntiHermitianDiagonal y)ᴴ *
      (g.1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)ᴴ)).re / 2)
  have hf : AEStronglyMeasurable f
      (Measure.map e (probability (standardJ n))) := by
    have hc := (continuous_halfTrace (interleavedJ n)
      (interleavedAntiHermitianDiagonal x)
      (interleavedAntiHermitianDiagonal y)ᴴ)
    have hc' : Continuous f := by
      change Continuous (fun g : stabilizer (interleavedJ n) =>
        Real.exp (halfTrace (interleavedJ n)
          (interleavedAntiHermitianDiagonal x)
          (interleavedAntiHermitianDiagonal y)ᴴ g))
      exact Real.continuous_exp.comp hc
    exact hc'.aestronglyMeasurable
  have h := hsource n hn x y hx hy hΔ
  change (∫ g, f g ∂probability (interleavedJ n)) = _ at h
  rw [← probability_interleave n] at h
  have hmap : (∫ g, f g ∂Measure.map (groupInterleaveContinuous n)
      (probability (standardJ n))) =
      ∫ g : Group n, f (groupInterleaveContinuous n g) ∂probability (standardJ n) := by
    exact integral_map (groupInterleaveContinuous n).continuous.measurable.aemeasurable hf
  rw [hmap] at h
  change (∫ g : Group n, f (e g) ∂probability (standardJ n)) = _ at h
  have hpoint (g : Group n) : f (e g) =
      Real.exp ((Matrix.trace (antiHermitianDiagonal x *
        (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
        (antiHermitianDiagonal y)ᴴ *
        (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ)).re / 2) := by
    exact congrArg (fun z : ℂ => Real.exp (z.re / 2))
      (sourceTrace_interleave x y g)
  simp_rw [hpoint] at h
  exact h

end
end QuaternionicSymmetry.OrbitalInterleavedBridge
