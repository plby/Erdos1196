import Mathlib

namespace Erdos1196

noncomputable def erdos_weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

noncomputable def erdos_sum (A : Set ℕ) : ℝ :=
  ∑' n : ℕ, A.indicator erdos_weight n

abbrev primitive_set (A : Set ℕ) : Prop :=
  IsAntichain (fun a b : ℕ => a ∣ b) A

abbrev supported_above (A : Set ℕ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ)

structure erdos1196_bound (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound :
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ 1 + C / Real.log x

/-- Erdős problem 1196: primitive sets supported above `x` have Erdős sum at most
`1 + O(1 / log x)`. -/
theorem theorem_1196 :
    ∃ C : ℝ, erdos1196_bound C := by
  sorry

abbrev IsLeastPrimeFactor (p n : ℕ) : Prop :=
  n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q -> q ∣ n -> p ≤ q

abbrev erdos_strong (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∀ A : Set ℕ, primitive_set A ->
      (∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_weight p

/-- The prime `2` is Erdős-strong. -/
theorem theorem_2_strong : erdos_strong 2 := by
  sorry

def prime_layer : Set ℕ :=
  {n : ℕ | Nat.Prime n}

/-- Erdős problem 164: the prime layer maximizes the Erdős sum among primitive sets. -/
theorem theorem_164 :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer := by
  sorry

def real_initial_segment (x : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x}

noncomputable def erdos_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  erdos_sum (A ∩ real_initial_segment x)

noncomputable def upper_doubly_log_density (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => erdos_sum_up_to A x / Real.log (Real.log x))
    Filter.atTop

abbrev strictly_increasing_divisibility_chain (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∀ i : ℕ, n i ∣ n (i + 1)

abbrev chain_in_set (n : ℕ → ℕ) (A : Set ℕ) : Prop :=
  ∀ i : ℕ, n i ∈ A

noncomputable def chain_count_up_to (n : ℕ → ℕ) (x : ℝ) : ℕ :=
  Set.ncard {i : ℕ | (n i : ℝ) ≤ x}

noncomputable def upper_chain_density (n : ℕ → ℕ) : ENNReal :=
  Filter.limsup
    (fun x : ℝ => ENNReal.ofReal
      ((chain_count_up_to n x : ℝ) / Real.log (Real.log x)))
    Filter.atTop

abbrev upper_chain_density_at_least (n : ℕ → ℕ) (Delta : ℝ) : Prop :=
  ENNReal.ofReal Delta ≤ upper_chain_density n

/-- Erdős problem 1217: positive upper doubly logarithmic density yields an
infinite divisibility chain with at least that upper density. -/
theorem theorem_1217 :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_in_set n A ∧
        upper_chain_density_at_least n (upper_doubly_log_density A) := by
  sorry

def omega_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | ArithmeticFunction.cardFactors n = k}

def omega_ge_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | k ≤ ArithmeticFunction.cardFactors n}

def restrict_to_primes (A Q : Set ℕ) : Set ℕ :=
  {n : ℕ | n ∈ A ∧ ∀ p : ℕ, Nat.Prime p -> p ∣ n -> p ∈ Q}

abbrev IsSetOfOddPrimes (Q : Set ℕ) : Prop :=
  ∀ p : ℕ, p ∈ Q -> Nat.Prime p ∧ p ≠ 2

def oddBM_terminal (k : ℕ) (Q : Set ℕ) : Set ℕ :=
  restrict_to_primes (omega_layer k) Q

/-- Odd Banks--Martin: restricting a primitive set to odd primes is bounded by
the corresponding omega layer. -/
theorem theorem_odd_banks_martin {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hA : primitive_set A)
    (hAk : A ⊆ omega_ge_layer k) :
    erdos_sum (restrict_to_primes A Q) ≤ erdos_sum (oddBM_terminal k Q) := by
  sorry

noncomputable def reciprocal_dyadic_interval_sum (A : Set ℕ) (x y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (A ∩ {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}).indicator
      (fun n : ℕ => 1 / (n : ℝ)) n

/-- Ahlswede--Khachatrian--Sárközy: reciprocal mass in a dyadic interval has
the standard primitive-set upper bound. -/
theorem theorem_AKS :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        reciprocal_dyadic_interval_sum A x y ≤
          C * Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  sorry

abbrev IsSmallPrimePower (x : ℝ) (q : ℕ) : Prop :=
  ∃ p j : ℕ, Nat.Prime p ∧ 1 ≤ j ∧ (p : ℝ) ≤ x ∧ q = p ^ j

noncomputable def aksExponent (x : ℝ) : ℝ :=
  1 - 1 / (10 * Real.log x)

noncomputable def aksPartitionFunction (x s : ℝ) : ℝ :=
  by
    classical
    exact ∑' q : ℕ, if IsSmallPrimePower x q then 1 / Real.rpow (q : ℝ) s else 0

def aksInterval (x y : ℝ) : Set ℕ :=
  {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}

noncomputable def aksSmallPrimeSupport (x : ℝ) (n : ℕ) : Finset ℕ :=
  n.factorization.support.filter fun p => (p : ℝ) ≤ x

noncomputable def aksSmallPrimeFactorCount (x : ℝ) (n : ℕ) : ℕ :=
  (aksSmallPrimeSupport x n).card

noncomputable def aksPoissonMass (Z : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-Z) * Z ^ k / (Nat.factorial k : ℝ)

noncomputable def aksLYMWeight (x Z : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * aksPoissonMass Z (aksSmallPrimeFactorCount x n))

noncomputable def aksLYMSum (A : Set ℕ) (x y Z : ℝ) : ℝ :=
  ∑' n : ℕ, (A ∩ aksInterval x y).indicator (aksLYMWeight x Z) n

/-- LYM refinement: the AKS weighted sum is bounded by a constant times `log x`. -/
theorem aks_LYM_refinement :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        aksLYMSum A x y (aksPartitionFunction x (aksExponent x)) ≤
          C * Real.log x := by
  sorry

end Erdos1196
