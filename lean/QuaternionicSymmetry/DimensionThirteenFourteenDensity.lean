import QuaternionicSymmetry.DimensionElevenTwelveDensity
import QuaternionicSymmetry.WeightSixAhat
import QuaternionicSymmetry.QuarticOrbitalSeparators

/-! Exact universal density reconstruction in dimensions 13 and 14.
The quartic terms are the symbolic targets used by the orbital separators.
This remains an algebraic statement: the Stage 1/E14 positivity witness and
the links from forms to classes and numbers are separate obligations. -/

namespace QuaternionicSymmetry.DimensionThirteenFourteenDensity

open MvPolynomial

noncomputable section

abbrev P := MvPolynomial (Fin 7) ℚ
def u : P := X 0
def p1 : P := X 1
def p2 : P := X 2
def p3 : P := X 3
def p4 : P := X 4
def p5 : P := X 5
def p6 : P := X 6

/-- Reuse the exact first five coefficient polynomials in the enlarged ring. -/
def lift : DimensionElevenTwelveDensity.P →ₐ[ℚ] P :=
  MvPolynomial.aeval ![u, p1, p2, p3, p4, p5]

def b6 (n : ℚ) : P :=
  C (691 / 7846046208000 * (n - 2047)) * u ^ 6
    - C (691 / 118879488000) * u ^ 5 * p1
    + C (691 / 15850598400) * u ^ 4 * p2
    - C (691 / 8491392000) * u ^ 3 * p3
    + C (691 / 15850598400) * u ^ 2 * p4
    - C (691 / 118879488000) * u * p5
    + C (691 / 7846046208000) * p6

/-- Sixth exponential coefficient, using the already proved fifth
coefficient and the exact recurrence from `WeightSixAhat`. -/
def a6 (n : ℚ) : P :=
  C (1 / 6) *
    (lift (DimensionElevenTwelveDensity.b1 n) * lift (DimensionElevenTwelveDensity.a5 n) + C 2 * lift (DimensionElevenTwelveDensity.b2 n) * lift (DimensionElevenTwelveDensity.a4 n)
      + C 3 * lift (DimensionElevenTwelveDensity.b3 n) * lift (DimensionElevenTwelveDensity.a3 n)
      + C 4 * lift (DimensionElevenTwelveDensity.b4 n) * lift (DimensionElevenTwelveDensity.a2 n)
      + C 5 * lift (DimensionElevenTwelveDensity.b5 n) * lift (DimensionElevenTwelveDensity.a1 n) + C 6 * b6 n)

/-- The sixth coefficient obeys the same recurrence as `LogAhat.A6` in
the enlarged polynomial ring.  This connects the reused first five
coefficients with the independent expanded sixth coefficient. -/
theorem a6_recurrence (n : ℚ) :
    6 * a6 n =
      lift (DimensionElevenTwelveDensity.b1 n) * lift (DimensionElevenTwelveDensity.a5 n)
        + 2 * lift (DimensionElevenTwelveDensity.b2 n) * lift (DimensionElevenTwelveDensity.a4 n)
        + 3 * lift (DimensionElevenTwelveDensity.b3 n) * lift (DimensionElevenTwelveDensity.a3 n)
        + 4 * lift (DimensionElevenTwelveDensity.b4 n) * lift (DimensionElevenTwelveDensity.a2 n)
        + 5 * lift (DimensionElevenTwelveDensity.b5 n) * lift (DimensionElevenTwelveDensity.a1 n)
        + 6 * b6 n := by
  apply MvPolynomial.funext
  intro v
  simp [a6]

def density13 : P :=
  C 32768 * u ^ 7 * a6 13
    + C (278528 / 3) * u ^ 8 * lift (DimensionElevenTwelveDensity.a5 13)
    + C (5681152 / 45) * u ^ 9 * lift (DimensionElevenTwelveDensity.a4 13)
    + C (14870528 / 135) * u ^ 10 * lift (DimensionElevenTwelveDensity.a3 13)
    + C (985339136 / 14175) * u ^ 11 * lift (DimensionElevenTwelveDensity.a2 13)
    + C (70463872 / 2079) * u ^ 12 * lift (DimensionElevenTwelveDensity.a1 13)
    + C (134961308128 / 10135125) * u ^ 13

def density14 : P :=
  C 65536 * u ^ 8 * a6 14
    + C (524288 / 3) * u ^ 9 * lift (DimensionElevenTwelveDensity.a5 14)
    + C (3407872 / 15) * u ^ 10 * lift (DimensionElevenTwelveDensity.a4 14)
    + C (181403648 / 945) * u ^ 11 * lift (DimensionElevenTwelveDensity.a3 14)
    + C (2490368 / 21) * u ^ 12 * lift (DimensionElevenTwelveDensity.a2 14)
    + C (989855744 / 17325) * u ^ 13 * lift (DimensionElevenTwelveDensity.a1 14)
    + C (2855653081088 / 127702575) * u ^ 14

/-- The first seven coefficients of the A-hat factor.  Later coefficients
are unrestricted: in dimensions 13 and 14 their character multipliers
vanish. -/
def Aext6 (n : ℕ) (tail : ℕ → P) : ℕ → P
  | 0 => 1
  | 1 => lift (DimensionElevenTwelveDensity.a1 n)
  | 2 => lift (DimensionElevenTwelveDensity.a2 n)
  | 3 => lift (DimensionElevenTwelveDensity.a3 n)
  | 4 => lift (DimensionElevenTwelveDensity.a4 n)
  | 5 => lift (DimensionElevenTwelveDensity.a5 n)
  | 6 => a6 n
  | j + 7 => tail (j + 7)

/-- The same character convolution used by `AlgebraReconstruction`, now
extended to the sixth A-hat coefficient. -/
def characterConvolution (n : ℕ) (tail : ℕ → P) : P :=
  ∑ j ∈ Finset.range (n + 1),
    C (Characters.taylorCoefficient (n - j) (Characters.virtual n)) *
      u ^ (n - j) * Aext6 n tail j

theorem characterConvolution13 (tail : ℕ → P) :
    characterConvolution 13 tail = density13 := by
  have h := HigherCharacters.taylor_thirteen
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃⟩
  simp only [characterConvolution, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, Aext6]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃]
  simp [density13]
  ring

theorem characterConvolution14 (tail : ℕ → P) :
    characterConvolution 14 tail = density14 := by
  have h := HigherCharacters.taylor_fourteen
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄⟩
  simp only [characterConvolution, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, Aext6]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄]
  simp [density14]
  ring

def q13 : P :=
  C (9911 / 127575) * p1 ^ 4 + C (16042 / 212625) * p1 ^ 2 * p2
    + C (26423 / 4465125) * p2 ^ 2 + C (284456 / 16372125) * p1 * p3
    + C (8894 / 19348875) * p4

def q14 : P :=
  C (4904 / 42525) * p1 ^ 4 + C (23024 / 212625) * p1 ^ 2 * p2
    + C (36256 / 4465125) * p2 ^ 2 + C (1084576 / 49116375) * p1 * p3
    - C (170152 / 212837625) * p4

def printed13 : P :=
  C 392 * u ^ 13 + C (45727288 / 315315) * p1 * u ^ 12
    + (C (121006364 / 5457375) * p1 ^ 2 + C (1781548 / 716625) * p2) * u ^ 11
    + (C (3397924 / 1913625) * p1 ^ 3 + C (36184556 / 49116375) * p1 * p2
        + C (1323256 / 34827975) * p3) * u ^ 10
    + q13 * u ^ 9
    + (C (19 / 10935) * p1 ^ 5 + C (1214 / 382725) * p1 ^ 3 * p2
        + C (116 / 76545) * p1 ^ 2 * p3 + C (61 / 70875) * p1 * p2 ^ 2
        + C (1154 / 2338875) * p1 * p4 + C (3596 / 13395375) * p2 * p3
        + C (1168 / 19348875) * p5) * u ^ 8
    + (C (1 / 65610) * p1 ^ 6 + C (1 / 21870) * p1 ^ 4 * p2
        + C (8 / 229635) * p1 ^ 3 * p3 + C (1 / 36450) * p1 ^ 2 * p2 ^ 2
        + C (1 / 42525) * p1 ^ 2 * p4 + C (8 / 382725) * p1 * p2 * p3
        + C (16 / 1403325) * p1 * p5 + C (1 / 546750) * p2 ^ 3
        + C (1 / 212625) * p2 * p4 + C (16 / 8037225) * p3 ^ 2
        + C (5528 / 1915538625) * p6) * u ^ 7

def printed14 : P :=
  C 448 * u ^ 14 + C (816577408 / 4729725) * p1 * u ^ 13
    + (C (152085968 / 5457375) * p1 ^ 2 + C (620496752 / 212837625) * p2) * u ^ 12
    + (C (655424 / 273375) * p1 ^ 3 + C (46487872 / 49116375) * p1 * p2
        + C (10779136 / 383107725) * p3) * u ^ 11
    + q14 * u ^ 10
    + (C (32 / 10935) * p1 ^ 5 + C (2008 / 382725) * p1 ^ 3 * p2
        + C (184 / 76545) * p1 ^ 2 * p3 + C (296 / 212625) * p1 * p2 ^ 2
        + C (1648 / 2338875) * p1 * p4 + C (5512 / 13395375) * p2 * p3
        + C (3712 / 70945875) * p5) * u ^ 9
    + (C (1 / 32805) * p1 ^ 6 + C (1 / 10935) * p1 ^ 4 * p2
        + C (16 / 229635) * p1 ^ 3 * p3 + C (1 / 18225) * p1 ^ 2 * p2 ^ 2
        + C (2 / 42525) * p1 ^ 2 * p4 + C (16 / 382725) * p1 * p2 * p3
        + C (32 / 1403325) * p1 * p5 + C (1 / 273375) * p2 ^ 3
        + C (2 / 212625) * p2 * p4 + C (32 / 8037225) * p3 ^ 2
        + C (11056 / 1915538625) * p6) * u ^ 8

private theorem lift_eval (q : DimensionElevenTwelveDensity.P) (v : Fin 7 → ℚ) :
    MvPolynomial.eval v (lift q) =
      MvPolynomial.eval ![v 0, v 1, v 2, v 3, v 4, v 5] q := by
  change MvPolynomial.aeval v (lift q) =
    MvPolynomial.aeval ![v 0, v 1, v 2, v 3, v 4, v 5] q
  unfold lift
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun i : Fin 6 => (aeval v) (![u, p1, p2, p3, p4, p5] i)) =
      ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    funext i
    fin_cases i <;> simp [u, p1, p2, p3, p4, p5]
  rw [h]

private theorem old_eval (q : AlgebraCertificates.P) (v : Fin 7 → ℚ) :
    MvPolynomial.eval ![v 0, v 1, v 2, v 3, v 4, v 5]
      (DimensionElevenTwelveDensity.old q) =
      AlgebraCertificates.evaluate (v 0) (2 * v 1) (2 * v 2)
        (2 * v 3) (2 * v 4) q := by
  change MvPolynomial.aeval ![v 0, v 1, v 2, v 3, v 4, v 5]
      (DimensionElevenTwelveDensity.old q) = _
  unfold DimensionElevenTwelveDensity.old AlgebraCertificates.evaluate
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun i : Fin 5 =>
      (aeval ![v 0, v 1, v 2, v 3, v 4, v 5])
        (![DimensionElevenTwelveDensity.u, 2 * DimensionElevenTwelveDensity.p1,
          2 * DimensionElevenTwelveDensity.p2, 2 * DimensionElevenTwelveDensity.p3,
          2 * DimensionElevenTwelveDensity.p4] i)) =
      ![v 0, 2 * v 1, 2 * v 2, 2 * v 3, 2 * v 4] := by
    funext i
    fin_cases i <;> simp [DimensionElevenTwelveDensity.u,
      DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
      DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
  rw [h]

/-- The sixth polynomial coefficient is the Bernoulli root formula with
the required `z_j=2p_j` substitution and the full power of `u`. -/
theorem b6_evaluate (n : ℕ) (v : Fin 7 → ℚ) :
    MvPolynomial.eval v (b6 n) =
      LogAhat.B6 n (v 0) (2 * v 1) (2 * v 2) (2 * v 3)
        (2 * v 4) (2 * v 5) (2 * v 6) := by
  simp [b6, LogAhat.B6, u, p1, p2, p3, p4, p5, p6]
  ring

theorem density13_printed : density13 = printed13 := by
  apply MvPolynomial.funext
  intro v
  simp only [density13, printed13, q13, a6, b6,
    map_add, map_sub, map_mul, map_pow, lift_eval]
  simp [DimensionElevenTwelveDensity.a5, DimensionElevenTwelveDensity.a4,
    DimensionElevenTwelveDensity.a3, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.b5,
    DimensionElevenTwelveDensity.b4, DimensionElevenTwelveDensity.b3,
    DimensionElevenTwelveDensity.b2, DimensionElevenTwelveDensity.b1,
    old_eval, AlgebraCertificates.evaluate, AlgebraCertificates.A₄,
    AlgebraCertificates.A₃, AlgebraCertificates.A₂, AlgebraCertificates.A₁,
    AlgebraCertificates.b₄, AlgebraCertificates.b₃, AlgebraCertificates.b₂,
    AlgebraCertificates.b₁, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    AlgebraCertificates.Z₄,
    DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1,
    DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3,
    DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5,
    u, p1, p2, p3, p4, p5, p6]
  ring

theorem density14_printed : density14 = printed14 := by
  apply MvPolynomial.funext
  intro v
  simp only [density14, printed14, q14, a6, b6,
    map_add, map_sub, map_mul, map_pow, lift_eval]
  simp [DimensionElevenTwelveDensity.a5, DimensionElevenTwelveDensity.a4,
    DimensionElevenTwelveDensity.a3, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.b5,
    DimensionElevenTwelveDensity.b4, DimensionElevenTwelveDensity.b3,
    DimensionElevenTwelveDensity.b2, DimensionElevenTwelveDensity.b1,
    old_eval, AlgebraCertificates.evaluate, AlgebraCertificates.A₄,
    AlgebraCertificates.A₃, AlgebraCertificates.A₂, AlgebraCertificates.A₁,
    AlgebraCertificates.b₄, AlgebraCertificates.b₃, AlgebraCertificates.b₂,
    AlgebraCertificates.b₁, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.Z₁, AlgebraCertificates.Z₂, AlgebraCertificates.Z₃,
    AlgebraCertificates.Z₄,
    DimensionElevenTwelveDensity.u, DimensionElevenTwelveDensity.p1,
    DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3,
    DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5,
    u, p1, p2, p3, p4, p5, p6]
  ring

private theorem quartic_embed (c : Fin 5 → ℚ) :
    MvPolynomial.aeval ![p1, p2, p3, p4]
      (QuarticOrbitalSeparators.quartic c) =
      C (c 0) * p1 ^ 4 + C (c 1) * p1 ^ 2 * p2 + C (c 2) * p2 ^ 2
        + C (c 3) * p1 * p3 + C (c 4) * p4 := by
  change MvPolynomial.aeval ![p1, p2, p3, p4]
      (C (c 0) * (X 0) ^ 4 + C (c 1) * (X 0) ^ 2 * X 1 + C (c 2) * (X 1) ^ 2
        + C (c 3) * X 0 * X 2 + C (c 4) * X 3) = _
  simp

/-- The independently reconstructed quartic is exactly the target of the
symbolic dimension-thirteen separator. -/
theorem q13_target :
    q13 = MvPolynomial.aeval ![p1, p2, p3, p4]
      (QuarticOrbitalSeparators.quartic QuarticOrbitalSeparators.target13) := by
  rw [quartic_embed]
  simp [q13, QuarticOrbitalSeparators.target13]

theorem q14_target :
    q14 = MvPolynomial.aeval ![p1, p2, p3, p4]
      (QuarticOrbitalSeparators.quartic QuarticOrbitalSeparators.target14) := by
  rw [quartic_embed]
  simp [q14, QuarticOrbitalSeparators.target14]
  have hc : (C (-170152 / 212837625) : P) =
      - C (170152 / 212837625) := by norm_num
  rw [hc]
  ring

/-- Weighted homogeneity is checked before setting `u=1`. -/
theorem density13_homogeneous (t : P) :
    MvPolynomial.aeval ![t * u, t * p1, t ^ 2 * p2, t ^ 3 * p3,
      t ^ 4 * p4, t ^ 5 * p5, t ^ 6 * p6] density13 =
      t ^ 13 * density13 := by
  rw [density13_printed]
  simp [printed13, q13, u, p1, p2, p3, p4, p5, p6]
  ring

theorem density14_homogeneous (t : P) :
    MvPolynomial.aeval ![t * u, t * p1, t ^ 2 * p2, t ^ 3 * p3,
      t ^ 4 * p4, t ^ 5 * p5, t ^ 6 * p6] density14 =
      t ^ 14 * density14 := by
  rw [density14_printed]
  simp [printed14, q14, u, p1, p2, p3, p4, p5, p6]
  ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem density13_evaluate (v : Fin 7 → R) :
    MvPolynomial.aeval v density13 = MvPolynomial.aeval v printed13 := by
  rw [density13_printed]

theorem density14_evaluate (v : Fin 7 → R) :
    MvPolynomial.aeval v density14 = MvPolynomial.aeval v printed14 := by
  rw [density14_printed]

end
end QuaternionicSymmetry.DimensionThirteenFourteenDensity
