import QuaternionicSymmetry.ManifoldSixVariableDensityGrades

/-!
The existing actual-degree expression syntax and the newer four-variable
degree-in-units-of-four syntax compile to exactly the same polynomial.
The newer grade-zero piece is `ℝ`; its map to closed zero-forms sends a scalar
to the corresponding constant form. This map need not be injective on an
empty manifold.
-/

namespace QuaternionicSymmetry.ManifoldCharacteristicExpressionComparison

open QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness
  QuaternionicSymmetry.ManifoldCharacteristicExpression
  QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldDeRhamAllDegrees
  QuaternionicSymmetry.ManifoldDeRhamWedge
  QuaternionicSymmetry.ManifoldDeRhamRing
  QuaternionicSymmetry.ManifoldDeRhamDegreeZero
  QuaternionicSymmetry.ManifoldDifferentialForms
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Reindex an even expression from weight `n` to actual form degree `4*n`.
Every old expression constructor is represented. -/
noncomputable def toActualDegree : {n : ℕ} → EvenExpr n → CharacteristicExpr (4 * n)
  | _, .coeff q => .coeff q
  | _, .u => .cast (by decide) .u
  | _, .trace₂ => .cast (by decide) .trace₂
  | _, .trace₄ => .cast (by decide) .trace₄
  | _, .trace₆ => .cast (by decide) .trace₆
  | _, .add P R => .add (toActualDegree P) (toActualDegree R)
  | _, .neg P => .neg (toActualDegree P)
  | _, .mul P R => .cast (by omega) (.mul (toActualDegree P) (toActualDegree R))
  | _, .cast h P => .cast (congrArg (4 * ·) h) (toActualDegree P)

/-- The two syntaxes denote exactly the same rational polynomial. -/
theorem toActualDegree_polynomial : ∀ {n : ℕ} (P : EvenExpr n),
    (toActualDegree P).polynomial = P.polynomial := by
  intro n P
  induction P with
  | coeff q => rfl
  | u => rfl
  | trace₂ => rfl
  | trace₄ => rfl
  | trace₆ => rfl
  | add P R hP hR => simp [toActualDegree, CharacteristicExpr.polynomial,
      EvenExpr.polynomial, hP, hR]
  | neg P hP => simp [toActualDegree, CharacteristicExpr.polynomial,
      EvenExpr.polynomial, hP]
  | mul P R hP hR => simp [toActualDegree, CharacteristicExpr.polynomial,
      EvenExpr.polynomial, hP, hR]
  | cast h P hP => simp [toActualDegree, CharacteristicExpr.polynomial,
      EvenExpr.polynomial, hP]

/-- Map the constant-coefficient even de Rham algebra to the full
degree-indexed de Rham groups; injectivity in degree zero requires `M` to be
nonempty. -/
noncomputable def embedGrade : (n : ℕ) → Grade (E := E) (M := M) n →
    CohomologyByDegree (E := E) (M := M) (4 * n)
  | 0, a => by
      change ℝ at a
      exact a • unitDegree (E := E) (M := M)
  | n + 1, a => by
      change positiveDegreeCohomology (E := E) (M₀ := M) (4 * n + 3) at a
      exact castDegree (show 4 * n + 4 = 4 * (n + 1) by omega) a

theorem embedGrade_add (n : ℕ)
    (a b : Grade (E := E) (M := M) n) :
    embedGrade n (a + b) = embedGrade n a + embedGrade n b := by
  cases n with
  | zero =>
      change ℝ at a b
      exact add_smul a b (unitDegree (E := E) (M := M))
  | succ n => rfl

theorem embedGrade_neg (n : ℕ) (a : Grade (E := E) (M := M) n) :
    embedGrade n (-a) = -embedGrade n a := by
  cases n with
  | zero =>
      change ℝ at a
      exact neg_smul a (unitDegree (E := E) (M := M))
  | succ n => rfl

private theorem castDegree_heq {p q : ℕ} (h : p = q)
    (a : CohomologyByDegree (E := E) (M := M) p) : castDegree h a ≍ a := by
  cases h
  rfl

private theorem castGrade_heq {p q : ℕ} (h : p = q)
    (a : Grade (E := E) (M := M) p) : castGrade h a ≍ a := by
  cases h
  rfl

private theorem castClass_heq {p q : ℕ} (h : p = q)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) p) : castClass h a ≍ a := by
  cases h
  rfl

private theorem castDegree_eq_cast {p q : ℕ} (h : p = q)
    (a : CohomologyByDegree (E := E) (M := M) p) :
    castDegree h a = cast (congrArg (fun n => CohomologyByDegree (E := E) (M := M) n) h) a := by
  cases h
  rfl

private theorem castGrade_eq_cast {p q : ℕ} (h : p = q)
    (a : Grade (E := E) (M := M) p) :
    castGrade h a = cast (congrArg (fun n => Grade (E := E) (M := M) n) h) a := by
  cases h
  rfl

private theorem castClass_eq_cast {p q : ℕ} (h : p = q)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) p) :
    castClass h a = cast (congrArg (fun n => positiveDegreeCohomology (E := E) (M₀ := M) n) h) a := by
  cases h
  rfl

private theorem wedgeDegree_zero_succ (k : ℕ)
    (a : zeroDegreeCohomology (E := E) (M := M))
    (b : positiveDegreeCohomology (E := E) (M₀ := M) k) :
    wedgeDegree 0 (k + 1) a b =
      castDegree (Nat.zero_add (k + 1)).symm (zeroPositiveWedge k a b) := by
  have hL : HEq (wedgeDegree 0 (k + 1) a b) (zeroPositiveWedge k a b) := by
    simp [wedgeDegree]
  have hR : HEq (castDegree (Nat.zero_add (k + 1)).symm (zeroPositiveWedge k a b))
      (zeroPositiveWedge k a b) := castDegree_heq _ _
  exact eq_of_heq (hL.trans hR.symm)

private theorem wedgeDegree_positive_heq (k l : ℕ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    HEq (wedgeDegree (k + 1) (l + 1) a b) (cohomologyWedge k l a b) := by
  simpa only [wedgeDegree] using castClass_heq
    (show k + l + 1 = (k + 1) + l by omega) (cohomologyWedge k l a b)

private theorem closedWedgeAll_smul_left {p q : ℕ} (c : ℝ)
    (a : closedForms (E := E) (M₀ := M) p)
    (b : closedForms (E := E) (M₀ := M) q) :
    closedWedgeAll (c • a) b = c • closedWedgeAll a b := by
  apply Subtype.ext
  apply Subtype.ext
  exact formWedge_smul_left c a.1.1 b.1.1

private theorem closedWedgeAll_smul_right {p q : ℕ} (c : ℝ)
    (a : closedForms (E := E) (M₀ := M) p)
    (b : closedForms (E := E) (M₀ := M) q) :
    closedWedgeAll a (c • b) = c • closedWedgeAll a b := by
  apply Subtype.ext
  apply Subtype.ext
  exact formWedge_smul_right c a.1.1 b.1.1

private theorem castClosedDegree_smul {p q : ℕ} (h : p = q) (c : ℝ)
    (a : closedForms (E := E) (M₀ := M) p) :
    castClosedDegree h (c • a) = c • castClosedDegree h a := by
  cases h
  rfl

private theorem wedgeDegree_const_left (n : ℕ) (c : ℝ)
    (a : CohomologyByDegree (E := E) (M := M) n) :
    wedgeDegree 0 n (c • unitDegree) a =
      castDegree (Nat.zero_add n).symm (c • a) := by
  cases n with
  | zero =>
      change zeroZeroWedge (c • oneClass) a = c • a
      unfold zeroZeroWedge
      rw [closedWedgeAll_smul_left]
      rw [show closedWedgeAll (oneClass (E := E) (M := M)) a = a by
        simpa only [Nat.zero_add, castClosedDegree] using closedWedgeAll_one_left a]
  | succ k =>
      induction a using Quotient.inductionOn with
      | _ α =>
          have h : zeroPositiveWedge k (c • oneClass)
              (QuotientAddGroup.mk α) =
              c • (QuotientAddGroup.mk α : positiveDegreeCohomology
                (E := E) (M₀ := M) k) := by
            rw [zeroPositiveWedge_mk]
            change QuotientAddGroup.mk _ = QuotientAddGroup.mk (c • α)
            congr 1
            unfold zeroPositiveClosed
            rw [closedWedgeAll_smul_left, castClosedDegree_smul,
              closedWedgeAll_one_left]
          rw [wedgeDegree_zero_succ]
          change castDegree (Nat.zero_add (k + 1)).symm
            (zeroPositiveWedge k (c • oneClass) (QuotientAddGroup.mk α)) =
              castDegree (Nat.zero_add (k + 1)).symm (c • QuotientAddGroup.mk α)
          rw [h]

private theorem wedgeDegree_const_right (n : ℕ) (c : ℝ)
    (a : CohomologyByDegree (E := E) (M := M) n) :
    wedgeDegree n 0 a (c • unitDegree) = c • a := by
  cases n with
  | zero =>
      change zeroZeroWedge a (c • oneClass) = c • a
      unfold zeroZeroWedge
      rw [closedWedgeAll_smul_right, closedWedgeAll_one_right]
  | succ k =>
      induction a using Quotient.inductionOn with
      | _ α =>
          change positiveZeroWedge k (QuotientAddGroup.mk α) (c • oneClass) =
            c • (QuotientAddGroup.mk α : positiveDegreeCohomology (E := E) (M₀ := M) k)
          rw [positiveZeroWedge_mk]
          change QuotientAddGroup.mk _ = QuotientAddGroup.mk (c • α)
          congr 1
          unfold positiveZeroClosed
          rw [closedWedgeAll_smul_right, closedWedgeAll_one_right]

private theorem embedGrade_mul (p q : ℕ)
    (a : Grade (E := E) (M := M) p)
    (b : Grade (E := E) (M := M) q) :
    castDegree (show 4 * p + 4 * q = 4 * (p + q) by omega)
      (wedgeDegree (4 * p) (4 * q) (embedGrade p a) (embedGrade q b)) =
    embedGrade (p + q) (gradeMul p q a b) := by
  cases p with
  | zero =>
      cases q with
      | zero =>
          change ℝ at a b
          change wedgeDegree 0 0 (a • unitDegree) (b • unitDegree) =
            (a * b) • unitDegree
          rw [wedgeDegree_const_left]
          simp [smul_smul, castDegree_eq_cast]
      | succ q =>
          apply eq_of_heq
          simp [embedGrade, gradeMul, wedgeDegree_const_left,
            castDegree_eq_cast, castGrade_eq_cast, cast_cast]
  | succ p =>
      cases q with
      | zero =>
          apply eq_of_heq
          simp [embedGrade, gradeMul, wedgeDegree_const_right,
            castDegree_eq_cast]
      | succ q =>
          apply eq_of_heq
          have hW : HEq
              (wedgeDegree (4 * (p + 1)) (4 * (q + 1))
                (embedGrade (p + 1) a) (embedGrade (q + 1) b))
              (cohomologyWedge (4 * p + 3) (4 * q + 3) a b) := by
            convert wedgeDegree_positive_heq (4 * p + 3) (4 * q + 3) a b using 1
          have hR : HEq (embedGrade (p + 1 + (q + 1))
              (gradeMul (p + 1) (q + 1) a b))
              (cohomologyWedge (4 * p + 3) (4 * q + 3) a b) := by
            simp only [embedGrade, gradeMul]
            simp only [id_eq]
            exact (castDegree_heq _ _).trans (castClass_heq _ _)
          exact (castDegree_heq _ _).trans (hW.trans hR.symm)

/-- The two expression languages have identical meanings in actual de Rham
cohomology after the constant-class map in degree zero. -/
theorem evaluate_toActualDegree
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3) :
    ∀ {n : ℕ} (P : EvenExpr n),
      CharacteristicExpr.evaluate (embedGrade 1 u) (embedGrade 1 t₂)
        (embedGrade 2 t₄) (embedGrade 3 t₆) (toActualDegree P) =
      embedGrade n (EvenExpr.evaluate u t₂ t₄ t₆ P) := by
  intro n P
  induction P with
  | coeff q => rfl
  | u => rfl
  | trace₂ => rfl
  | trace₄ => rfl
  | trace₆ => rfl
  | add P R hP hR =>
      simpa [toActualDegree, CharacteristicExpr.evaluate, EvenExpr.evaluate,
        embedGrade_add] using congrArg₂ (· + ·) hP hR
  | neg P hP =>
      simpa [toActualDegree, CharacteristicExpr.evaluate, EvenExpr.evaluate,
        embedGrade_neg] using congrArg Neg.neg hP
  | mul P R hP hR =>
      simp only [toActualDegree, CharacteristicExpr.evaluate, EvenExpr.evaluate]
      rw [hP, hR]
      exact embedGrade_mul _ _ _ _
  | cast h P hP =>
      cases h
      exact hP

end QuaternionicSymmetry.ManifoldCharacteristicExpressionComparison
