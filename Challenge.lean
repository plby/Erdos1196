import Mathlib

namespace Erdos1196

/-- The Erdős weight `1 / (n * log n)` of a natural number `n`.

Paper reference: Equation 1.1 (LaTeX label `nu-def`). -/
noncomputable def erdos_weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

/-- The sum of the Erdős weights of the elements of `A`.

Paper reference: the definition of `f(A)` preceding Equation 1.1
(LaTeX label `nu-def`). -/
noncomputable def erdos_sum (A : Set ℕ) : ℝ :=
  ∑' n : ℕ, A.indicator erdos_weight n

/-- A set of natural numbers whose distinct elements are incomparable under divisibility.

Paper reference: the discussion preceding Figure 1 (LaTeX label `fig-divis`). -/
abbrev primitive_set (A : Set ℕ) : Prop :=
  IsAntichain (fun a b : ℕ => a ∣ b) A

/-- The property that every element of `A` is at least `x`.

Paper reference: Theorem 1.1 (LaTeX label `conj:1196`). -/
abbrev supported_above (A : Set ℕ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ)

/-- A nonnegative constant giving the asserted Erdős-sum bound for primitive sets.

Paper reference: Theorem 1.1 (LaTeX label `conj:1196`). -/
structure erdos1196_bound (C : ℝ) : Prop where
  /-- The bound constant is nonnegative.

  Paper reference: Theorem 1.1 (LaTeX label `conj:1196`). -/
  nonneg : 0 ≤ C
  /-- The quantitative Erdős-sum bound for primitive sets supported above `x`.

  Paper reference: Theorem 1.1 (LaTeX label `conj:1196`). -/
  bound :
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ 1 + C / Real.log x

/-- Erdős problem 1196: primitive sets supported above `x` have Erdős sum at most
`1 + O(1 / log x)`.

Paper reference: Theorem 1.1 (LaTeX label `conj:1196`). -/
theorem theorem_1196 :
    ∃ C : ℝ, erdos1196_bound C := by
  sorry

/-- The property that `p` is the least prime factor of the nonzero natural number `n`.

Paper reference: the discussion preceding Theorem 1.4 (LaTeX label `2-strong`). -/
abbrev IsLeastPrimeFactor (p n : ℕ) : Prop :=
  n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q -> q ∣ n -> p ≤ q

/-- The property that primitive sets with least prime factor `p` have sum at most its weight.

Paper reference: the definition preceding Theorem 1.4 (LaTeX label `2-strong`). -/
abbrev erdos_strong (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∀ A : Set ℕ, primitive_set A ->
      (∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_weight p

/-- The prime `2` is Erdős-strong.

Paper reference: Theorem 1.4 (LaTeX label `2-strong`). -/
theorem theorem_2_strong : erdos_strong 2 := by
  sorry

/-- The set of all prime natural numbers.

Paper reference: Theorem 1.2 (LaTeX label `conj:EPS`). -/
def prime_layer : Set ℕ :=
  {n : ℕ | Nat.Prime n}

/-- Erdős problem 164: the prime layer maximizes the Erdős sum among primitive sets.

Paper reference: Theorem 1.2 (LaTeX label `conj:EPS`). -/
theorem theorem_164 :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer := by
  sorry

/-- The positive natural numbers at most the real number `x`.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
def real_initial_segment (x : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x}

/-- The Erdős sum of the elements of `A` at most `x`.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
noncomputable def erdos_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  erdos_sum (A ∩ real_initial_segment x)

/-- The upper doubly logarithmic density of a set of natural numbers.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
noncomputable def upper_doubly_log_density (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => erdos_sum_up_to A x / Real.log (Real.log x))
    Filter.atTop

/-- A strictly increasing sequence in which every term divides its successor.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
abbrev strictly_increasing_divisibility_chain (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∀ i : ℕ, n i ∣ n (i + 1)

/-- The property that every term of the sequence `n` belongs to `A`.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
abbrev chain_in_set (n : ℕ → ℕ) (A : Set ℕ) : Prop :=
  ∀ i : ℕ, n i ∈ A

/-- The number of indices whose term in the sequence `n` is at most `x`.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
noncomputable def chain_count_up_to (n : ℕ → ℕ) (x : ℝ) : ℕ :=
  Set.ncard {i : ℕ | (n i : ℝ) ≤ x}

/-- The upper doubly logarithmic density of a sequence of natural numbers.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
noncomputable def upper_chain_density (n : ℕ → ℕ) : ENNReal :=
  Filter.limsup
    (fun x : ℝ => ENNReal.ofReal
      ((chain_count_up_to n x : ℝ) / Real.log (Real.log x)))
    Filter.atTop

/-- The property that the upper chain density of `n` is at least `Delta`.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
abbrev upper_chain_density_at_least (n : ℕ → ℕ) (Delta : ℝ) : Prop :=
  ENNReal.ofReal Delta ≤ upper_chain_density n

/-- Erdős problem 1217: positive upper doubly logarithmic density yields an
infinite divisibility chain with at least that upper density.

Paper reference: Theorem 1.6 (LaTeX label `conj:1217`). -/
theorem theorem_1217 :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_in_set n A ∧
        upper_chain_density_at_least n (upper_doubly_log_density A) := by
  sorry

/-- The natural numbers with exactly `k` prime factors, counted with multiplicity.

Paper reference: the layer definition preceding Figure 1 (LaTeX label `fig-divis`). -/
def omega_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | ArithmeticFunction.cardFactors n = k}

/-- The natural numbers with at least `k` prime factors, counted with multiplicity.

Paper reference: the layer definition preceding Figure 1 (LaTeX label `fig-divis`). -/
def omega_ge_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | k ≤ ArithmeticFunction.cardFactors n}

/-- The elements of `A` all of whose prime divisors belong to `Q`.

Paper reference: Theorem 1.3 (LaTeX label `conj:oddBM`). -/
def restrict_to_primes (A Q : Set ℕ) : Set ℕ :=
  {n : ℕ | n ∈ A ∧ ∀ p : ℕ, Nat.Prime p -> p ∣ n -> p ∈ Q}

/-- The property that every element of `Q` is an odd prime.

Paper reference: Theorem 1.3 (LaTeX label `conj:oddBM`). -/
abbrev IsSetOfOddPrimes (Q : Set ℕ) : Prop :=
  ∀ p : ℕ, p ∈ Q -> Nat.Prime p ∧ p ≠ 2

/-- The `k`th omega layer restricted to numbers whose prime divisors lie in `Q`.

Paper reference: Theorem 1.3 (LaTeX label `conj:oddBM`). -/
def oddBM_terminal (k : ℕ) (Q : Set ℕ) : Set ℕ :=
  restrict_to_primes (omega_layer k) Q

/-- Odd Banks--Martin: restricting a primitive set to odd primes is bounded by
the corresponding omega layer.

Paper reference: Theorem 1.3 (LaTeX label `conj:oddBM`). -/
theorem theorem_odd_banks_martin {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hA : primitive_set A)
    (hAk : A ⊆ omega_ge_layer k) :
    erdos_sum (restrict_to_primes A Q) ≤ erdos_sum (oddBM_terminal k Q) := by
  sorry

/-- The sum of the reciprocals of the elements of `A` in the interval `[y / x, y]`.

Paper reference: Theorem 1.5 (LaTeX label `AKS-thm`). -/
noncomputable def reciprocal_dyadic_interval_sum (A : Set ℕ) (x y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (A ∩ {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}).indicator
      (fun n : ℕ => 1 / (n : ℝ)) n

/-- Ahlswede--Khachatrian--Sárközy: reciprocal mass in a dyadic interval has
the standard primitive-set upper bound.

Paper reference: Theorem 1.5 (LaTeX label `AKS-thm`). -/
theorem theorem_AKS :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        reciprocal_dyadic_interval_sum A x y ≤
          C * Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  sorry

/-- The property that `q` is a positive power of a prime at most `x`.

Paper reference: Section 8 (LaTeX label `AKS-sec`). -/
abbrev IsSmallPrimePower (x : ℝ) (q : ℕ) : Prop :=
  ∃ p j : ℕ, Nat.Prime p ∧ 1 ≤ j ∧ (p : ℝ) ≤ x ∧ q = p ^ j

/-- The exponent `1 - 1 / (10 * log x)` used in the AKS partition function.

Paper reference: Section 8 (LaTeX label `AKS-sec`). -/
noncomputable def aksExponent (x : ℝ) : ℝ :=
  1 - 1 / (10 * Real.log x)

/-- The sum of `q⁻ˢ` over prime powers `q` whose underlying prime is at most `x`.

Paper reference: the definition of `Z` in Section 8 (LaTeX label `AKS-sec`). -/
noncomputable def aksPartitionFunction (x s : ℝ) : ℝ :=
  by
    classical
    exact ∑' q : ℕ, if IsSmallPrimePower x q then 1 / Real.rpow (q : ℝ) s else 0

/-- The natural numbers lying in the real interval `[y / x, y]`.

Paper reference: Theorem 1.5 (LaTeX label `AKS-thm`). -/
def aksInterval (x y : ℝ) : Set ℕ :=
  {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}

/-- The prime factors of `n` that are at most `x`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
noncomputable def aksSmallPrimeSupport (x : ℝ) (n : ℕ) : Finset ℕ :=
  n.factorization.support.filter fun p => (p : ℝ) ≤ x

/-- The number of distinct prime factors of `n` that are at most `x`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
noncomputable def aksSmallPrimeFactorCount (x : ℝ) (n : ℕ) : ℕ :=
  (aksSmallPrimeSupport x n).card

/-- The Poisson mass with parameter `Z` at the natural number `k`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
noncomputable def aksPoissonMass (Z : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-Z) * Z ^ k / (Nat.factorial k : ℝ)

/-- The reciprocal AKS LYM weight of `n` with cutoff `x` and parameter `Z`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
noncomputable def aksLYMWeight (x Z : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * aksPoissonMass Z (aksSmallPrimeFactorCount x n))

/-- The AKS LYM-weighted sum of the elements of `A` in `[y / x, y]`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
noncomputable def aksLYMSum (A : Set ℕ) (x y Z : ℝ) : ℝ :=
  ∑' n : ℕ, (A ∩ aksInterval x y).indicator (aksLYMWeight x Z) n

/-- LYM refinement: the AKS weighted sum is bounded by a constant times `log x`.

Paper reference: Remark 8.1 (LaTeX label `lym-rem`). -/
theorem aks_LYM_refinement :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        aksLYMSum A x y (aksPartitionFunction x (aksExponent x)) ≤
          C * Real.log x := by
  sorry

end Erdos1196
