import Mathlib

/-!
# Primitive sets and von Mangoldt chains

This file is a single-file Lean formalisation of `mangoldt_arxiv.tex`.  It
consolidates the development and keeps public names for all six headline
theorems and the AKS LYM refinement.
-/

namespace MangoldtArxiv

open scoped ComplexOrder

noncomputable def erdos_weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

noncomputable def erdos_sum (A : Set ℕ) : ℝ :=
  ∑' n : ℕ, A.indicator erdos_weight n

abbrev primitive_set (A : Set ℕ) : Prop :=
  IsAntichain (fun a b : ℕ => a ∣ b) A

/-- Primitivity is inherited by subsets. -/
lemma primitive_set_of_subset {A B : Set ℕ} (hA : primitive_set A) (hBA : B ⊆ A) :
    primitive_set B :=
  hA.subset hBA

abbrev supported_above (A : Set ℕ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ)

abbrev supported_in_interval (A : Set ℕ) (x X : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X

noncomputable def mangoldt_reciprocal_partial_sum (t : ℝ) : ℝ :=
  ∑' q : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0

noncomputable def mangoldt_dirichlet_series (u : ℝ) : ℝ :=
  ∑' q : ℕ, ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)

noncomputable def mangoldt_tail_term (m q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q /
    ((q : ℝ) * (Real.log (((m * q : ℕ) : ℝ))) ^ 2)

noncomputable def mangoldt_tail_sum (m : ℕ) (y : ℝ) : ℝ :=
  ∑' q : ℕ, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0

noncomputable def tail_majorant (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n ∧ (n : ℝ) < x then
      (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
    else 0

noncomputable def cut_capacity (x X : ℝ) : ℝ :=
  ∑' r : ℕ,
    if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
      (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
        (∑ q ∈ r.divisors,
          if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
    else 0

structure erdos1196_bound (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound :
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ 1 + C / Real.log x

structure erdos1196_finite_bound (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  bound :
    ∀ x X : ℝ, 2 ≤ x -> x ≤ X -> ∀ A : Set ℕ,
      primitive_set A -> supported_in_interval A x X ->
        erdos_sum A ≤ 1 + C / Real.log x

lemma von_mangoldt_divisor_sum (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q) = Real.log (n : ℝ) := by
  simpa using (ArithmeticFunction.vonMangoldt_sum (n := n))

lemma mertens_von_mangoldt_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ C := by
  classical
  let c0 : ℝ := Real.log (2 * Real.pi) / 2
  have htsum : ∀ t : ℝ, 0 ≤ t ->
      mangoldt_reciprocal_partial_sum t =
        ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
    intro t ht
    rw [mangoldt_reciprocal_partial_sum]
    calc
      (∑' q : ℕ,
          if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0)
          = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊,
              if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0 := by
            refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
              (s := Finset.Icc 1 ⌊t⌋₊)
              (f := fun q : ℕ =>
                if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0) ?_
            intro q hq
            by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ t
            · exfalso
              exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.le_floor hcond.2⟩)
            · simp [hcond]
      _ = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            rcases Finset.mem_Icc.mp hq with ⟨hq1, hqfloor⟩
            have hqt : (q : ℝ) ≤ t := by
              exact (Nat.cast_le.mpr hqfloor).trans (Nat.floor_le ht)
            simp [hq1, hqt]
  have hsumlog : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) = Real.log (n.factorial : ℝ) := by
    intro n
    rw [← Real.log_prod]
    · congr 1
      rw [← Finset.Ico_succ_succ_eq_Ioc (0 : ℕ) n]
      simpa [Order.succ_eq_add_one] using
        (show (∏ x ∈ Finset.Ico 1 (n + 1), (x : ℝ)) = (n.factorial : ℝ) by
          rw [← Nat.cast_prod]
          norm_num [Finset.prod_Ico_id_eq_factorial])
    · intro m hm
      have hmpos : 0 < m := (Finset.mem_Ioc.mp hm).1
      exact_mod_cast (ne_of_gt hmpos)
  have hB : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) =
        ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) := by
    intro n
    simpa [ArithmeticFunction.vonMangoldt_mul_zeta] using
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n)
  have hfloor_upper : ∀ n q : ℕ, ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / (q : ℝ) := by
    intro n q
    exact Nat.cast_div_le
  have hfloor_lower : ∀ n q : ℕ, (n : ℝ) / (q : ℝ) - 1 ≤ ((n / q : ℕ) : ℝ) := by
    intro n q
    by_cases hq : q = 0
    · subst q
      norm_num
    · have hlt : (n : ℝ) / (q : ℝ) < (⌊(n : ℝ) / (q : ℝ)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one ((n : ℝ) / (q : ℝ))
      rw [Nat.floor_div_natCast] at hlt
      rw [Nat.floor_natCast] at hlt
      linarith
  have hpsi_le : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q) ≤
        (Real.log 4 + 4) * (n : ℝ) := by
    intro n
    simpa [Chebyshev.psi, Nat.floor_natCast] using
      (Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity))
  have hlogfac_upper : ∀ n : ℕ,
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hfac : (n.factorial : ℝ) ≤ (n ^ n : ℕ) := by
        exact_mod_cast (Nat.factorial_le_pow n)
      have hpos : 0 < (n.factorial : ℝ) := by positivity
      have hlog := Real.log_le_log hpos hfac
      simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hlogfac_lower : ∀ n : ℕ, 1 ≤ n ->
      (n : ℝ) * Real.log (n : ℝ) - (1 + |c0|) * (n : ℝ) ≤
        Real.log (n.factorial : ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hs := Stirling.le_log_factorial_stirling (n := n) hn0
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hc : -|c0| * (n : ℝ) ≤ c0 := by
      by_cases hc0 : 0 ≤ c0
      · have hleft : -|c0| * (n : ℝ) ≤ 0 := by
          nlinarith [abs_nonneg c0, hnnonneg]
        exact hleft.trans hc0
      · have hc0lt : c0 < 0 := lt_of_not_ge hc0
        have habs : |c0| = -c0 := abs_of_neg hc0lt
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [habs]
        nlinarith
    have hc' : -|Real.log (2 * Real.pi) / 2| * (n : ℝ) ≤ Real.log (2 * Real.pi) / 2 := by
      simpa [c0] using hc
    nlinarith
  have hB_le_nA : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) ≤
        (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
          ≤ ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (hfloor_upper n q) hΛ
      _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
            field_simp [hqpos.ne']
  have hnA_le_B_psi : ∀ n : ℕ,
      (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) ≤
        (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) +
          ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q := by
    intro n
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    have hdiv_le : (n : ℝ) / (q : ℝ) ≤ ((n / q : ℕ) : ℝ) + 1 := by
      linarith [hfloor_lower n q]
    calc
      (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ))
          = ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            field_simp [hqpos.ne']
      _ ≤ ArithmeticFunction.vonMangoldt q * (((n / q : ℕ) : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left hdiv_le hΛ
      _ = ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) +
            ArithmeticFunction.vonMangoldt q := by
            ring
  let K1 : ℝ := 1 + |c0|
  let K2 : ℝ := Real.log 4 + 4
  let Cnat : ℝ := max K1 K2
  have hK1_nonneg : 0 ≤ K1 := by
    dsimp [K1]
    positivity
  have hK2_nonneg : 0 ≤ K2 := by
    dsimp [K2]
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hCnat_nonneg : 0 ≤ Cnat := by
    exact hK1_nonneg.trans (le_max_left K1 K2)
  have hK1_le_Cnat : K1 ≤ Cnat := le_max_left K1 K2
  have hK2_le_Cnat : K2 ≤ Cnat := le_max_right K1 K2
  have hnat_ioc : ∀ n : ℕ, 1 ≤ n ->
      |(∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
        Real.log (n : ℝ)| ≤ Cnat := by
    intro n hn
    set A : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)
    set B : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
    set P : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hB_eq : B = Real.log (n.factorial : ℝ) := by
      dsimp [B]
      exact (hB n).symm.trans (hsumlog n)
    have hB_le : B ≤ (n : ℝ) * A := by
      simpa [A, B] using hB_le_nA n
    have hnA_le : (n : ℝ) * A ≤ B + P := by
      simpa [A, B, P] using hnA_le_B_psi n
    have hP_le : P ≤ K2 * (n : ℝ) := by
      dsimp [P, K2]
      exact hpsi_le n
    have hA_upper : A - Real.log (n : ℝ) ≤ Cnat := by
      have hmul : (n : ℝ) * A ≤ (n : ℝ) * (Real.log (n : ℝ) + K2) := by
        have hfac := hlogfac_upper n
        rw [hB_eq] at hnA_le
        nlinarith
      have hA_le : A ≤ Real.log (n : ℝ) + K2 := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    have hA_lower : -Cnat ≤ A - Real.log (n : ℝ) := by
      have hmul : (n : ℝ) * (Real.log (n : ℝ) - K1) ≤ (n : ℝ) * A := by
        have hfac := hlogfac_lower n hn
        rw [hB_eq] at hB_le
        dsimp [K1]
        nlinarith
      have hlower : Real.log (n : ℝ) - K1 ≤ A := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    exact abs_le.mpr ⟨hA_lower, hA_upper⟩
  have hIoc_eq_Icc : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    ext q
    simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  refine ⟨Cnat + Real.log 2, ?_, ?_⟩
  · have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    let N : ℕ := ⌊t⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff t).mpr ht
    have hpartial := htsum t ht0
    have hnat := hnat_ioc N hN
    have hnat' :
        |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
          Real.log (N : ℝ)| ≤ Cnat := by
      simpa [hIoc_eq_Icc N] using hnat
    have hNpos_nat : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    have htpos : 0 < t := by linarith
    have hN_le_t : (N : ℝ) ≤ t := by
      dsimp [N]
      exact Nat.floor_le ht0
    have ht_lt_N_add_one : t < (N : ℝ) + 1 := by
      dsimp [N]
      simpa using (Nat.lt_floor_add_one t)
    have ht_le_twoN : t ≤ 2 * (N : ℝ) := by
      have hN_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogN_le_logt : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hNpos hN_le_t
    have hlogt_le_log2N : Real.log t ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log htpos ht_le_twoN
    have hlog2N : Real.log (2 * (N : ℝ)) = Real.log (2 : ℝ) + Real.log (N : ℝ) := by
      rw [Real.log_mul] <;> positivity
    have hlogdiff : |Real.log (N : ℝ) - Real.log t| ≤ Real.log (2 : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlogN_le_logt), neg_sub]
      rw [hlog2N] at hlogt_le_log2N
      linarith
    rw [hpartial]
    calc
      |(∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log t|
          = |((∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
                Real.log (N : ℝ)) + (Real.log (N : ℝ) - Real.log t)| := by
            dsimp [N]
            ring_nf
      _ ≤ |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log (N : ℝ)| +
            |Real.log (N : ℝ) - Real.log t| := abs_add_le _ _
      _ ≤ Cnat + Real.log (2 : ℝ) := add_le_add hnat' hlogdiff

noncomputable def dirichlet_eta_real (s : ℝ) : ℝ :=
  (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (s : ℂ))) * riemannZeta (s : ℂ)).re

lemma riemannZeta_pos_of_one_lt {s : ℝ} (hs : 1 < s) :
    0 < riemannZeta (s : ℂ) := by
  rw [← LSeries_one_eq_riemannZeta (s := (s : ℂ)) (by simpa using hs)]
  apply LSeries.positive
  · intro n
    norm_num
  · norm_num
  · rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs

lemma riemannZeta_re_pos_of_one_lt {s : ℝ} (hs : 1 < s) :
    0 < (riemannZeta (s : ℂ)).re :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hs)).1

lemma riemannZeta_im_eq_zero_of_one_lt {s : ℝ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).im = 0 :=
  (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hs)).2.symm

lemma dirichlet_eta_positive :
    ∀ s : ℝ, 1 < s -> 0 < dirichlet_eta_real s := by
  intro s hs
  unfold dirichlet_eta_real
  have hpow : (2 : ℂ) ^ ((1 : ℂ) - (s : ℂ)) = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
    symm
    simpa using (Complex.ofReal_cpow (x := (2 : ℝ)) (by norm_num) (1 - s))
  have hfactor_pos : 0 < (1 : ℝ) - (2 : ℝ) ^ (1 - s) := by
    have hlt : (2 : ℝ) ^ (1 - s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hzeta_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  rw [hpow]
  simpa [Complex.mul_re] using mul_pos hfactor_pos hzeta_pos

lemma dirichlet_eta_mellin_transform :
    ∀ s : ℝ, 1 < s ->
      dirichlet_eta_real s =
        (1 / Real.Gamma s) *
          ∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) := by
  intro s hs
  let S : ℂ := s
  have hgeom :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        HasSum (fun n : ℕ => ((-1 : ℂ) ^ n) * Real.exp (-(n + 1 : ℝ) * t))
          ((1 : ℂ) / (Real.exp t + 1)) := by
    intro t ht
    have htpos : 0 < t := ht
    have hnorm : ‖(-((Real.exp (-t) : ℝ) : ℂ))‖ < 1 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Real.exp_neg]
      bound
    convert
      ((hasSum_geometric_of_norm_lt_one (ξ := -((Real.exp (-t) : ℝ) : ℂ)) hnorm).mul_left
        ((Real.exp (-t) : ℝ) : ℂ)) using 1
    · rfl
    · ext n
      rw [show -((n : ℝ) + 1) * t = -t + (n : ℝ) * (-t) by ring]
      simp only [mul_neg, Complex.ofReal_exp, Complex.ofReal_add, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_natCast, Complex.exp_add]
      rw [show -(↑n * ↑t : ℂ) = ↑n * (-↑t) by ring, Complex.exp_nat_mul]
      ring
    · rw [Real.exp_neg]
      let E : ℂ := ↑(Real.exp t)
      have hE : E ≠ 0 := by
        dsimp [E]
        exact_mod_cast Real.exp_ne_zero t
      have hE1 : E + 1 ≠ 0 := by
        dsimp [E]
        norm_cast
        positivity
      have halg : 1 / (E + 1) = E⁻¹ * (1 - -E⁻¹)⁻¹ := by
        rw [sub_neg_eq_add]
        field_simp [hE, hE1]
      simpa [E] using halg
  have hsum :
      Summable (fun n : ℕ => ‖((-1 : ℂ) ^ n)‖ / ((n + 1 : ℝ)) ^ S.re) := by
    convert (Real.summable_one_div_nat_add_rpow 1 s).2 hs using 1
    ext n
    simp [S, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have hs0 : 0 < S.re := by
    dsimp [S]
    exact lt_trans zero_lt_one hs
  have hp : ∀ n : ℕ, ((-1 : ℂ) ^ n) = 0 ∨ 0 < (n + 1 : ℝ) := by
    intro n
    right
    positivity
  have hmellin :
      HasSum
        (fun n : ℕ => Complex.Gamma S * ((-1 : ℂ) ^ n) / ((n + 1 : ℝ) : ℂ) ^ S)
        (mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S) := by
    exact hasSum_mellin hp hs0 hgeom hsum
  have hmellin_real :
      mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S =
        ((∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) : ℝ) : ℂ) := by
    rw [mellin]
    simp only [smul_eq_mul]
    rw [← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hpow : (x : ℂ) ^ (S - 1) = ((x ^ (s - 1) : ℝ) : ℂ) := by
      dsimp [S]
      symm
      simpa using (Complex.ofReal_cpow (x := x) hxpos.le (s - 1))
    simp [hpow, div_eq_mul_inv]
  have hcomplex :
      mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S =
        Complex.Gamma S * (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S) := by
    have hs1 : 1 < S.re := by
      simpa [S] using hs
    have hf : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ S)) := by
      simpa using
        (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℂ) ^ S)) 1).2
          (Complex.summable_one_div_nat_cpow.mpr hs1)
    have hzeta_nat : riemannZeta S = ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) ^ S) := by
      simpa using zeta_eq_tsum_one_div_nat_add_one_cpow (s := S) hs1
    have hg : Summable (fun n : ℕ => ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) := by
      apply Summable.of_norm
      convert hsum using 1
      ext n
      have hbase : (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by
        norm_num
      rw [hbase, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (x := ((n + 1 : ℕ) : ℝ))
        (by positivity) S]
      simp [S, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    have hinj_even : Function.Injective (fun n : ℕ => 2 * n) := by
      exact mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
    have hinj_odd : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro a b h
      exact hinj_even (Nat.succ.inj h)
    have heven_scaled :
        (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) =
          (2 : ℂ) ^ (-S) * riemannZeta S := by
      rw [hzeta_nat]
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [show (2 * n + 2 : ℕ) = 2 * (n + 1) by ring]
      rw [show (((2 * (n + 1) : ℕ) : ℂ) ^ S) =
          (2 : ℂ) ^ S * (((n + 1 : ℕ) : ℂ) ^ S) by
        simpa using (Complex.natCast_mul_natCast_cpow 2 (n + 1) S)]
      rw [Complex.cpow_neg]
      field_simp [Complex.natCast_add_one_cpow_ne_zero 1 S,
        Complex.natCast_add_one_cpow_ne_zero n S]
    have hzeta_split :
        (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) +
          (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) = riemannZeta S := by
      rw [hzeta_nat]
      simpa [Nat.add_assoc] using
        (tsum_even_add_odd
          (f := fun k : ℕ => 1 / (((k + 1 : ℕ) : ℂ) ^ S))
          (hf.comp_injective hinj_even) (hf.comp_injective hinj_odd))
    have heta_split :
        (∑' n : ℕ, ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) =
          (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) -
            (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) := by
      rw [← tsum_even_add_odd
        (f := fun k : ℕ => ((-1 : ℂ) ^ k) / (((k + 1 : ℕ) : ℂ) ^ S))
        (hg.comp_injective hinj_even) (hg.comp_injective hinj_odd)]
      rw [sub_eq_add_neg, ← tsum_neg]
      congr 1
      · apply tsum_congr
        intro n
        simp [pow_mul]
      · apply tsum_congr
        intro n
        rw [show (2 * n + 1 + 1 : ℕ) = 2 * n + 2 by ring]
        simp [pow_succ, pow_mul, div_eq_mul_inv]
    have htwo : (2 : ℂ) ^ ((1 : ℂ) - S) = 2 * (2 : ℂ) ^ (-S) := by
      rw [show ((1 : ℂ) - S) = 1 + (-S) by ring]
      rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
    have heta_tsum :
        (∑' n : ℕ, ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) =
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S := by
      rw [heta_split]
      rw [show (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) -
          (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) =
          ((∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) +
            (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S))) -
            2 * (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) by ring]
      rw [hzeta_split, heven_scaled, htwo]
      ring
    rw [← hmellin.tsum_eq]
    rw [← heta_tsum]
    rw [← tsum_mul_left]
    congr 1
    ext n
    simp [div_eq_mul_inv]
    ring
  have hInt :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1)) =
        Real.Gamma s * dirichlet_eta_real s := by
    have hcomplex' :
        ((∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) : ℝ) : ℂ) =
          Complex.Gamma S * (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S) := by
      exact hmellin_real.symm.trans hcomplex
    have hre := congrArg Complex.re hcomplex'
    rw [dirichlet_eta_real]
    simp [S, Complex.Gamma_ofReal, Complex.mul_re] at hre ⊢
    linarith
  have hγ : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos (lt_trans zero_lt_one hs)).ne'
  rw [hInt]
  field_simp [hγ]

lemma gamma_logistic_expectation_eq_mellin_integral :
    ∀ s : ℝ, 1 < s ->
      (∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1)) =
        (1 / Real.Gamma s) *
          ∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) := by
  intro s hs
  rw [ProbabilityTheory.gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 < x
    · have hnonneg :
          0 ≤ 1 ^ s / Real.Gamma s * x ^ (s - 1) * Real.exp (-(1 * x)) := by
        simpa [ProbabilityTheory.gammaPDFReal, if_pos hx.le] using
          ProbabilityTheory.gammaPDFReal_nonneg (a := s) (r := 1) (by linarith) (by norm_num) x
      have hpdf :
          (ProbabilityTheory.gammaPDF s 1 x).toReal =
            1 ^ s / Real.Gamma s * x ^ (s - 1) * Real.exp (-(1 * x)) := by
        rw [ProbabilityTheory.gammaPDF_of_nonneg hx.le]
        exact ENNReal.toReal_ofReal hnonneg
      have hGamma_ne : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < s)).ne'
      rw [hpdf]
      simp [Set.mem_Ioi, hx, Real.exp_neg, div_eq_mul_inv]
      field_simp [hGamma_ne, Real.exp_ne_zero]
    · have hxle : x ≤ 0 := le_of_not_gt hx
      rcases lt_or_eq_of_le hxle with hxlt | hxeq
      · have hpdf : ProbabilityTheory.gammaPDF s 1 x = 0 := ProbabilityTheory.gammaPDF_of_neg hxlt
        simp [hpdf, Set.mem_Ioi, hx]
      · subst x
        have hsne : s - 1 ≠ 0 := by linarith
        have hnonneg :
            0 ≤ 1 ^ s / Real.Gamma s * (0 : ℝ) ^ (s - 1) * Real.exp (-(1 * 0)) := by
          simp [Real.zero_rpow hsne]
        have hpdf :
            (ProbabilityTheory.gammaPDF s 1 0).toReal =
              1 ^ s / Real.Gamma s * (0 : ℝ) ^ (s - 1) * Real.exp (-(1 * 0)) := by
          rw [ProbabilityTheory.gammaPDF_of_nonneg le_rfl]
          exact ENNReal.toReal_ofReal hnonneg
        simp [hpdf, Set.mem_Ioi, Real.zero_rpow hsne]
  · change Measurable (fun x : ℝ =>
      ENNReal.ofReal (ProbabilityTheory.gammaPDFReal s 1 x))
    exact ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal s 1)
  · filter_upwards with x
    simp [ProbabilityTheory.gammaPDF]

lemma dirichlet_eta_gamma_expectation :
    ∀ s : ℝ, 1 < s ->
      dirichlet_eta_real s =
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1) := by
  intro s hs
  exact (dirichlet_eta_mellin_transform s hs).trans
    (gamma_logistic_expectation_eq_mellin_integral s hs).symm

lemma gamma_logistic_expectation_mono_of_shape_le :
    ∀ ⦃a b : ℝ⦄, 0 < a -> a ≤ b ->
      (∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure a 1)) ≤
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure b 1) := by
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let c : ℝ := b - a
  let K : ℝ := Real.Gamma a / Real.Gamma b
  have hc : 0 ≤ c := by
    dsimp [c]
    linarith
  have hgamma_meas : AEMeasurable (ProbabilityTheory.gammaPDF a 1) MeasureTheory.volume :=
    (ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal a 1)).aemeasurable
  have hratio_meas :
      AEMeasurable (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c)) MeasureTheory.volume := by
    dsimp [K, c]
    fun_prop
  have htilt :
      ProbabilityTheory.gammaMeasure b 1 =
        (ProbabilityTheory.gammaMeasure a 1).withDensity
          (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c)) := by
    rw [ProbabilityTheory.gammaMeasure, ProbabilityTheory.gammaMeasure]
    rw [← MeasureTheory.withDensity_mul₀ hgamma_meas hratio_meas]
    apply MeasureTheory.withDensity_congr_ae
    have hne_zero : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne_zero] with x hx0
    by_cases hx : 0 < x
    · have hxle : 0 ≤ x := hx.le
      rw [ProbabilityTheory.gammaPDF_of_nonneg hxle]
      rw [Pi.mul_apply, ProbabilityTheory.gammaPDF_of_nonneg hxle]
      dsimp [K, c]
      rw [max_eq_left hxle]
      rw [← ENNReal.ofReal_mul]
      · congr 1
        have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
        have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
        rw [Real.one_rpow, Real.one_rpow]
        field_simp [hGa, hGb]
        rw [← Real.rpow_add hx]
        congr 1
        ring
      · positivity
    · have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      rw [ProbabilityTheory.gammaPDF_of_neg hxlt]
      rw [Pi.mul_apply, ProbabilityTheory.gammaPDF_of_neg hxlt]
      simp
  by_cases hba : b = a
  · subst b
    exact le_rfl
  have hcpos : 0 < c := by
    refine lt_of_le_of_ne' hc ?_
    intro hc0
    apply hba
    dsimp [c] at hc0
    linarith
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  let t : ℝ := (1 / K) ^ (c⁻¹)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_cross : K * (max t 0) ^ c = 1 := by
    have ht_eq : max t 0 = t := max_eq_left ht_nonneg
    rw [ht_eq]
    dsimp [t]
    rw [Real.rpow_inv_rpow (by positivity : 0 ≤ 1 / K) hcpos.ne']
    field_simp [hKpos.ne']
  have hpoint :
      ∀ x : ℝ,
        0 ≤ (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1) := by
    intro x
    by_cases hxt : x ≤ t
    · have hsig : Real.sigmoid x ≤ Real.sigmoid t := Real.sigmoid_monotone hxt
      have hmax : max x 0 ≤ max t 0 := max_le_max hxt le_rfl
      have hpow : (max x 0) ^ c ≤ (max t 0) ^ c := by
        exact Real.rpow_le_rpow (le_max_right x 0) hmax hc
      have hw : K * (max x 0) ^ c ≤ 1 := by
        calc
          K * (max x 0) ^ c ≤ K * (max t 0) ^ c := by gcongr
          _ = 1 := ht_cross
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hsig) (sub_nonpos.mpr hw)
    · have htx : t ≤ x := le_of_not_ge hxt
      have hsig : Real.sigmoid t ≤ Real.sigmoid x := Real.sigmoid_monotone htx
      have hmax : max t 0 ≤ max x 0 := max_le_max htx le_rfl
      have hpow : (max t 0) ^ c ≤ (max x 0) ^ c := by
        exact Real.rpow_le_rpow (le_max_right t 0) hmax hc
      have hw : 1 ≤ K * (max x 0) ^ c := by
        calc
          1 = K * (max t 0) ^ c := ht_cross.symm
          _ ≤ K * (max x 0) ^ c := by gcongr
      exact mul_nonneg (sub_nonneg.mpr hsig) (sub_nonneg.mpr hw)
  have hdens_real :
      ∀ x : ℝ, (ENNReal.ofReal (K * (max x 0) ^ c)).toReal = K * (max x 0) ^ c := by
    intro x
    rw [ENNReal.toReal_ofReal]
    positivity
  have hmass :
      ∫ x : ℝ, K * (max x 0) ^ c ∂(ProbabilityTheory.gammaMeasure a 1) = 1 := by
    calc
      ∫ x : ℝ, K * (max x 0) ^ c ∂(ProbabilityTheory.gammaMeasure a 1)
          = ∫ x : ℝ,
              (ENNReal.ofReal (K * (max x 0) ^ c)).toReal
                ∂(ProbabilityTheory.gammaMeasure a 1) := by
            simp_rw [hdens_real]
      _ = ∫ x : ℝ, (1 : ℝ) ∂((ProbabilityTheory.gammaMeasure a 1).withDensity
            (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c))) := by
            rw [integral_withDensity_eq_integral_toReal_smul₀ (f_meas := by fun_prop)
              (hf_lt_top := by simp) (fun _ : ℝ => (1 : ℝ))]
            simp
      _ = ∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gammaMeasure b 1) := by
            rw [← htilt]
      _ = 1 := by
            haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure b 1) :=
              ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb (by norm_num)
            simp
  haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure a 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha (by norm_num)
  have hmu_one : ∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gammaMeasure a 1) = 1 := by
    simp
  have hf_int : MeasureTheory.Integrable Real.sigmoid (ProbabilityTheory.gammaMeasure a 1) :=
    MeasureTheory.Integrable.of_mem_Icc 0 1 (by fun_prop)
      (Filter.Eventually.of_forall fun x => ⟨Real.sigmoid_nonneg x, Real.sigmoid_le_one x⟩)
  have hlintegral :
      (∫⁻ x, ENNReal.ofReal (K * (max x 0) ^ c) ∂(ProbabilityTheory.gammaMeasure a 1)) ≠
        (⊤ : ENNReal) := by
    haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure b 1) :=
      ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb (by norm_num)
    have hfinite : ((ProbabilityTheory.gammaMeasure b 1) Set.univ) < (⊤ : ENNReal) :=
      MeasureTheory.measure_lt_top (ProbabilityTheory.gammaMeasure b 1) Set.univ
    rw [htilt, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at hfinite
    simpa using (ne_of_lt hfinite)
  have hw_int :
      MeasureTheory.Integrable (fun x : ℝ => K * (max x 0) ^ c)
        (ProbabilityTheory.gammaMeasure a 1) := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hlintegral
    · fun_prop (disch := positivity)
    · exact Filter.Eventually.of_forall fun x => by positivity
  have hwf_int :
      MeasureTheory.Integrable (fun x : ℝ => K * (max x 0) ^ c * Real.sigmoid x)
        (ProbabilityTheory.gammaMeasure a 1) := by
    refine MeasureTheory.Integrable.mono' hw_int ?_ ?_
    · fun_prop (disch := positivity)
    · exact Filter.Eventually.of_forall fun x => by
        have hw0 : 0 ≤ K * (max x 0) ^ c := by positivity
        have hprod0 : 0 ≤ K * (max x 0) ^ c * Real.sigmoid x :=
          mul_nonneg hw0 (Real.sigmoid_nonneg x)
        rw [Real.norm_of_nonneg hprod0]
        exact mul_le_of_le_one_right hw0 (Real.sigmoid_le_one x)
  have hwt_int :
      MeasureTheory.Integrable (fun x : ℝ => Real.sigmoid t * (K * (max x 0) ^ c))
        (ProbabilityTheory.gammaMeasure a 1) :=
    hw_int.const_mul (Real.sigmoid t)
  have hconst_int :
      MeasureTheory.Integrable (fun _ : ℝ => Real.sigmoid t)
        (ProbabilityTheory.gammaMeasure a 1) := by
    fun_prop
  have hcov_nonneg :
      0 ≤ ∫ x : ℝ,
          (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
            ∂(ProbabilityTheory.gammaMeasure a 1) := by
    exact MeasureTheory.integral_nonneg
      (μ := ProbabilityTheory.gammaMeasure a 1)
      (f := fun x : ℝ => (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1))
      hpoint
  have hcov_eq :
      ∫ x : ℝ, (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
          ∂(ProbabilityTheory.gammaMeasure a 1)
        = ∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
            ∂(ProbabilityTheory.gammaMeasure a 1)
          - ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1) := by
    calc
      ∫ x : ℝ, (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
          ∂(ProbabilityTheory.gammaMeasure a 1)
          = ∫ x : ℝ,
              (K * (max x 0) ^ c * Real.sigmoid x - Real.sigmoid x) -
                (Real.sigmoid t * (K * (max x 0) ^ c) - Real.sigmoid t)
              ∂(ProbabilityTheory.gammaMeasure a 1) := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by ring
      _ = (∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
              ∂(ProbabilityTheory.gammaMeasure a 1) -
            ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1)) -
          (∫ x : ℝ, Real.sigmoid t * (K * (max x 0) ^ c)
              ∂(ProbabilityTheory.gammaMeasure a 1) -
            ∫ x : ℝ, Real.sigmoid t ∂(ProbabilityTheory.gammaMeasure a 1)) := by
            rw [MeasureTheory.integral_sub]
            · rw [MeasureTheory.integral_sub hwf_int hf_int]
              rw [MeasureTheory.integral_sub hwt_int hconst_int]
            · exact hwf_int.sub hf_int
            · exact hwt_int.sub hconst_int
      _ = ∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
            ∂(ProbabilityTheory.gammaMeasure a 1) -
          ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1) := by
            rw [MeasureTheory.integral_const_mul, hmass]
            simp
  simp only [one_div, ← Real.sigmoid_def]
  rw [htilt]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f_meas := by fun_prop)
    (hf_lt_top := by simp) Real.sigmoid]
  simp_rw [hdens_real, smul_eq_mul]
  have hdiff_nonneg := hcov_nonneg
  rw [hcov_eq] at hdiff_nonneg
  linarith

lemma gamma_logistic_expectation_monotone :
    MonotoneOn
      (fun s : ℝ =>
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1))
      (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  exact gamma_logistic_expectation_mono_of_shape_le ha hab

lemma dirichlet_eta_monotone :
    MonotoneOn dirichlet_eta_real (Set.Ioi (1 : ℝ)) := by
  intro s hs t ht hst
  rw [dirichlet_eta_gamma_expectation s hs, dirichlet_eta_gamma_expectation t ht]
  exact gamma_logistic_expectation_mono_of_shape_le (lt_trans zero_lt_one hs) hst

lemma dirichlet_eta_log_derivative_nonnegative :
    ∀ s : ℝ, 1 < s -> 0 ≤ deriv dirichlet_eta_real s / dirichlet_eta_real s := by
  intro s hs
  refine div_nonneg ?_ (le_of_lt (dirichlet_eta_positive s hs))
  simpa [derivWithin_of_isOpen isOpen_Ioi (show s ∈ Set.Ioi (1 : ℝ) from hs)] using
    (dirichlet_eta_monotone.derivWithin_nonneg (x := s))

lemma dirichlet_eta_zeta_log_derivative :
    ∀ u : ℝ, 0 < u ->
      deriv dirichlet_eta_real (1 + u) / dirichlet_eta_real (1 + u) =
        ((deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re +
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
  intro u hu
  have hfactor_deriv :
      deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          ((1 + u : ℝ) : ℂ) =
        (2 : ℂ) ^ (-(u : ℂ)) * Complex.log (2 : ℂ) := by
    have hinner :
        HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1 : ℂ) ((1 + u : ℝ) : ℂ) := by
      exact (hasDerivAt_id ((1 + u : ℝ) : ℂ)).const_sub (1 : ℂ)
    have hpow :
        HasDerivAt (fun z : ℂ => (2 : ℂ) ^ ((1 : ℂ) - z))
          ((2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))) *
            Complex.log (2 : ℂ) * (-1 : ℂ)) ((1 + u : ℝ) : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hinner.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    have hfactor :
        HasDerivAt (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          (-((2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))) *
            Complex.log (2 : ℂ) * (-1 : ℂ))) ((1 + u : ℝ) : ℂ) := by
      exact hpow.const_sub (1 : ℂ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfactor.deriv
  have hfactor_log :
      (logDeriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          ((1 + u : ℝ) : ℂ)).re =
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
    have hfactor_deriv_real :
        deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
            ((1 + u : ℝ) : ℂ) =
          ((Real.rpow (2 : ℝ) (-u) * Real.log (2 : ℝ) : ℝ) : ℂ) := by
      simpa [Complex.ofReal_cpow, mul_comm, mul_left_comm, mul_assoc] using hfactor_deriv
    have hpow_gt_one : 1 < Real.rpow (2 : ℝ) u := by
      exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
        (Or.inl ⟨by norm_num, hu⟩)
    have hden_ne : Real.rpow (2 : ℝ) u - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hpow_gt_one)
    have hfactor_val :
        ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) =
          ((1 - Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) := by
      simp [Complex.ofReal_cpow]
    rw [logDeriv]
    change (deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
        ((1 + u : ℝ) : ℂ) /
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))))).re =
      Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)
    rw [hfactor_deriv_real, hfactor_val]
    rw [← Complex.ofReal_div]
    norm_cast
    rw [show Real.rpow (2 : ℝ) (-u) = (Real.rpow (2 : ℝ) u)⁻¹ by
      exact Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) u]
    field_simp [hden_ne]
  have hpow_lt : Real.rpow (2 : ℝ) (-u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hfactor_ne :
      ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) ≠ 0 := by
    have hpow_ne : (2 : ℂ) ^ (-(u : ℂ)) ≠ 1 := by
      simpa [Complex.ofReal_cpow] using
        (show ((Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) ≠ 1 by
          exact_mod_cast hpow_lt.ne)
    simpa using sub_ne_zero.mpr (Ne.symm hpow_ne)
  have hz_ne : riemannZeta ((1 + u : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hf_diff :
      DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
        ((1 + u : ℝ) : ℂ) := by
    fun_prop
  have hz_diff : DifferentiableAt ℂ riemannZeta ((1 + u : ℝ) : ℂ) :=
    differentiableAt_riemannZeta (by norm_num [Complex.ext_iff]; linarith)
  have hprod_log :
      (logDeriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re =
        (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
            riemannZeta ((1 + u : ℝ) : ℂ)).re +
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
    have h := logDeriv_mul
      (f := fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
      (g := riemannZeta) ((1 + u : ℝ) : ℂ) hfactor_ne hz_ne hf_diff hz_diff
    calc
      (logDeriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re
          = (logDeriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
              ((1 + u : ℝ) : ℂ) + logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            rw [h]
      _ = Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) +
            (logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            rw [Complex.add_re]
            rw [hfactor_log]
      _ = Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) +
            (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
              riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            simp [logDeriv]
      _ = (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
            riemannZeta ((1 + u : ℝ) : ℂ)).re +
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
            ring
  have hE_diff :
      DifferentiableAt ℂ (fun z : ℂ =>
        ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
        ((1 + u : ℝ) : ℂ) :=
    hf_diff.mul hz_diff
  have hderiv_eta :
      deriv dirichlet_eta_real (1 + u) =
        (deriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re := by
    change deriv (fun x : ℝ =>
      ((((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (x : ℂ))) *
        riemannZeta (x : ℂ)).re)) (1 + u) = _
    exact hE_diff.hasDerivAt.real_of_complex.deriv
  have hfactor_val2 :
      ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) =
        ((1 - Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) := by
    simp [Complex.ofReal_cpow]
  have hz_im : (riemannZeta ((1 + u : ℝ) : ℂ)).im = 0 := by
    simpa using riemannZeta_im_eq_zero_of_one_lt (by linarith : 1 < 1 + u)
  have hE_im :
      (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) *
        riemannZeta ((1 + u : ℝ) : ℂ)).im = 0 := by
    rw [hfactor_val2]
    have hz_im' : (riemannZeta (1 + (u : ℂ))).im = 0 := by
      simpa [add_comm] using hz_im
    simp [hz_im']
  rw [← hprod_log]
  rw [logDeriv, hderiv_eta]
  unfold dirichlet_eta_real
  let A : ℂ := deriv (fun z : ℂ =>
    ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z) ((1 + u : ℝ) : ℂ)
  let B : ℂ :=
    ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) *
      riemannZeta ((1 + u : ℝ) : ℂ)
  have hB_im : B.im = 0 := by
    simpa [B] using hE_im
  have hB_ne : B ≠ 0 := by
    dsimp [B]
    exact mul_ne_zero hfactor_ne hz_ne
  have hB_re_ne : B.re ≠ 0 := by
    intro hB_re
    apply hB_ne
    exact Complex.ext hB_re hB_im
  change A.re / B.re = (A / B).re
  rw [Complex.div_re]
  simp [hB_im]
  field_simp [Complex.normSq, hB_im, hB_re_ne]
  rw [Complex.normSq_apply, hB_im]
  ring

lemma eta_log_derivative_nonnegative :
    ∀ u : ℝ, 0 < u ->
      0 ≤ ((deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re +
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
  intro u hu
  rw [← dirichlet_eta_zeta_log_derivative u hu]
  exact dirichlet_eta_log_derivative_nonnegative (1 + u) (by linarith)

lemma zeta_log_derivative_geometric_bound :
    ∀ u : ℝ, 0 < u ->
      ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) ≤
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
  intro u hu
  have h := eta_log_derivative_nonnegative u hu
  rw [neg_div, Complex.neg_re]
  linarith

lemma mangoldt_dirichlet_series_eq_zeta_log_derivative :
    ∀ u : ℝ, 0 < u ->
      (mangoldt_dirichlet_series u : ℂ) =
        - deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ) := by
  intro u hu
  have hs : 1 < (((1 + u : ℝ) : ℂ).re) := by
    simp
    linarith
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := ((1 + u : ℝ) : ℂ)) hs]
  change (mangoldt_dirichlet_series u : ℂ) =
    LSeries (fun q : ℕ => (ArithmeticFunction.vonMangoldt q : ℂ)) ((1 + u : ℝ) : ℂ)
  rw [mangoldt_dirichlet_series, LSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro q
  by_cases hq : q = 0
  · subst q
    simp [Real.zero_rpow (by linarith : (1 : ℝ) + u ≠ 0)]
  · rw [LSeries.term_of_ne_zero hq]
    rw [Complex.ofReal_div]
    congr 1
    exact Complex.ofReal_cpow (Nat.cast_nonneg q) (1 + u)

lemma zeta_geometric_bound_le_inv :
    ∀ u : ℝ, 0 < u ->
      Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤ 1 / u := by
  intro u hu
  have hpow_gt_one : 1 < Real.rpow (2 : ℝ) u := by
    exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
      (Or.inl ⟨by norm_num, hu⟩)
  have hden_pos : 0 < Real.rpow (2 : ℝ) u - 1 := by
    linarith
  have hmul : Real.log (2 : ℝ) * u ≤ Real.rpow (2 : ℝ) u - 1 := by
    have h := Real.add_one_le_exp (Real.log (2 : ℝ) * u)
    have h' : Real.log (2 : ℝ) * u + 1 ≤ Real.rpow (2 : ℝ) u := by
      simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) u] using h
    linarith
  rw [div_le_div_iff₀ hden_pos hu]
  simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma von_mangoldt_dirichlet_series_upper_bound :
    ∀ u : ℝ, 0 < u -> mangoldt_dirichlet_series u ≤ 1 / u := by
  intro u hu
  have hseries :
      mangoldt_dirichlet_series u =
        ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
    simpa using congrArg Complex.re
      (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu)
  calc
    mangoldt_dirichlet_series u
        = ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := hseries
    _ ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
      zeta_log_derivative_geometric_bound u hu
    _ ≤ 1 / u := zeta_geometric_bound_le_inv u hu

lemma mangoldt_tail_range_eq_ico (m N : ℕ) (y : ℝ) :
    (∑ q ∈ Finset.range N,
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) =
      ∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    simp [Nat.ceil_le, and_comm]
  · intro q hq
    rfl

lemma mangoldt_reciprocal_partial_sum_nat (n : ℕ) :
    mangoldt_reciprocal_partial_sum (n : ℝ) =
      ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum]
  calc
    (∑' q : ℕ,
        if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
          ArithmeticFunction.vonMangoldt q / (q : ℝ)
        else 0) =
        ∑ q ∈ Finset.Icc 1 n,
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.Icc 1 n)
        (f := fun q : ℕ =>
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0) ?_
      intro q hq
      by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)
      · exfalso
        exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.cast_le.mp hcond.2⟩)
      · exact if_neg hcond
    _ = ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hq1, hqn⟩
      have hqr : (q : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hqn
      simp [hq1, hqr]

lemma real_sub_div_square_le_inv_sub_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ^ 2 ≤ 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  field_simp [ha.ne', hb.ne']
  nlinarith

lemma mangoldt_log_increment_pointwise_le (m r : ℕ) (hm : 1 ≤ m) (hr : 2 ≤ r) :
    (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) /
        (Real.log (((m * (r + 1) : ℕ) : ℝ))) ^ 2 ≤
      1 / Real.log (((m * r : ℕ) : ℝ)) -
        1 / Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
  have hmr_two : 2 ≤ m * r := by
    exact Nat.mul_le_mul hm hr
  have hmr_pos_log : 0 < Real.log (((m * r : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmr_two)
  have hmr_le : (m * r : ℕ) ≤ m * (r + 1) := by
    exact Nat.mul_le_mul_left m (Nat.le_succ r)
  have hlog_le : Real.log (((m * r : ℕ) : ℝ)) ≤
      Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hmr_two)
    · exact_mod_cast hmr_le
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hr)
  have hr_succ_pos : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hlogdiff :
      Real.log (((m * (r + 1) : ℕ) : ℝ)) - Real.log (((m * r : ℕ) : ℝ)) =
        Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Real.log_mul hm_pos.ne' hr_succ_pos.ne', Real.log_mul hm_pos.ne' hr_pos.ne']
    ring
  have hcore := real_sub_div_square_le_inv_sub_inv hmr_pos_log hlog_le
  rw [hlogdiff] at hcore
  simpa [Nat.cast_mul] using hcore

lemma log_increment_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1),
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) = Real.log (r : ℝ) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl]
  rw [← Finset.sum_Ico_add
    (f := fun q : ℕ => Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
    (a := 1) (b := r) (c := 1)]
  have hsum := Finset.sum_Ico_sub (m := 1) (n := r)
    (f := fun i : ℕ => Real.log (i : ℝ)) hr
  simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel, Real.log_one] using hsum

lemma mangoldt_reciprocal_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1), ArithmeticFunction.vonMangoldt q / (q : ℝ)) =
      mangoldt_reciprocal_partial_sum (r : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum_nat]
  have hI : Finset.Ico 2 (r + 1) = Finset.Ioc 1 r := by
    simpa [Nat.succ_eq_add_one] using (Finset.Ico_succ_succ_eq_Ioc (1 : ℕ) r)
  rw [hI]
  rw [Finset.Icc_eq_cons_Ioc hr]
  simp

lemma mangoldt_mertens_error_partial_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (n k : ℕ) (hn : 2 ≤ n) :
    |∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))| ≤ 2 * D := by
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  have hendpoint : ∀ r : ℕ, 1 ≤ r -> |∑ q ∈ Finset.Ico 2 (r + 1), e q| ≤ D := by
    intro r hr
    have hrec := mangoldt_reciprocal_sum_ico_two r hr
    have hlog := log_increment_sum_ico_two r hr
    have hsum : (∑ q ∈ Finset.Ico 2 (r + 1), e q) =
        mangoldt_reciprocal_partial_sum (r : ℝ) - Real.log (r : ℝ) := by
      dsimp [e]
      rw [Finset.sum_sub_distrib]
      rw [hrec, hlog]
    rw [hsum]
    exact hD (r : ℝ) (by exact_mod_cast hr)
  by_cases hkn : k ≤ n
  · rw [Finset.Ico_eq_empty_of_le hkn]
    simp
    nlinarith
  · have hnk : n < k := not_le.mp hkn
    have hk_pred_one : 1 ≤ k - 1 := by omega
    have hn_pred_one : 1 ≤ n - 1 := by omega
    have hk_sum := hendpoint (k - 1) hk_pred_one
    have hn_sum := hendpoint (n - 1) hn_pred_one
    have hk_sum' : |∑ q ∈ Finset.Ico 2 k, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk_sum
    have hn_sum' : |∑ q ∈ Finset.Ico 2 n, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hn_sum
    have hconsec := Finset.sum_Ico_consecutive (f := e) (m := 2) (n := n) (k := k) hn hnk.le
    have hinterval : (∑ q ∈ Finset.Ico n k, e q) =
        (∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q) := by
      linarith
    rw [show (∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))) =
        ∑ q ∈ Finset.Ico n k, e q by rfl]
    rw [hinterval]
    calc
      |(∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q)| ≤
          |∑ q ∈ Finset.Ico 2 k, e q| + |∑ q ∈ Finset.Ico 2 n, e q| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (∑ q ∈ Finset.Ico 2 k, e q) (-(∑ q ∈ Finset.Ico 2 n, e q))
      _ ≤ D + D := by linarith
      _ = 2 * D := by ring

lemma mangoldt_mertens_error_weighted_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (m N : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  let w : ℕ → ℝ := fun q => 1 / (Real.log (((m * q : ℕ) : ℝ))) ^ 2
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  rw [show ⌈y⌉₊ = n by rfl]
  by_cases hN : n < N
  · let g : ℕ → ℝ := fun q => if n ≤ q then e q else 0
    have hG_eq : ∀ k : ℕ, (∑ q ∈ Finset.range k, g q) = ∑ q ∈ Finset.Ico n k, e q := by
      intro k
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        simp
    have hG_bound : ∀ k : ℕ, |∑ q ∈ Finset.range k, g q| ≤ 2 * D := by
      intro k
      rw [hG_eq k]
      exact mangoldt_mertens_error_partial_bound D hD_nonneg hD n k hn
    have htarget :
        (∑ q ∈ Finset.Ico n N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) =
          ∑ q ∈ Finset.range N, w q * g q := by
      symm
      dsimp [g]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        dsimp [w, e]
        ring
    rw [htarget]
    have hbp := Finset.sum_range_by_parts (f := w) (g := g) (n := N)
    have hbp' : ∑ i ∈ Finset.range N, w i * g i =
        w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) := by
      simpa only [smul_eq_mul] using hbp
    rw [hbp']
    have hLsq_pos : 0 < (Real.log ((m : ℝ) * y)) ^ 2 := sq_pos_of_pos hLpos
    have htwoD_nonneg : 0 ≤ 2 * D := by positivity
    have hfourD_nonneg : 0 ≤ 4 * D := by positivity
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hw_le_L : ∀ q : ℕ, n ≤ q -> w q ≤ 1 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      intro q hnq
      have hq_real : y ≤ (q : ℝ) := hyn.trans (by exact_mod_cast hnq)
      have harg : (m : ℝ) * y ≤ (((m * q : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hq_real (by positivity)
      have hlog : Real.log ((m : ℝ) * y) ≤ Real.log (((m * q : ℕ) : ℝ)) :=
        Real.log_le_log (by linarith) harg
      dsimp [w]
      gcongr
    have hw_nonneg : ∀ q : ℕ, n ≤ q -> 0 ≤ w q := by
      intro q hnq
      dsimp [w]
      positivity
    have hboundary : w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤
        2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hG_le : (∑ i ∈ Finset.range N, g i) ≤ 2 * D :=
        (le_abs_self _).trans (hG_bound N)
      have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
      have hwN_le := hw_le_L (N - 1) hN_pred_ge
      calc
        w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤ w (N - 1) * (2 * D) := by
          exact mul_le_mul_of_nonneg_left hG_le hwN_nonneg
        _ ≤ (1 / (Real.log ((m : ℝ) * y)) ^ 2) * (2 * D) := by
          exact mul_le_mul_of_nonneg_right hwN_le htwoD_nonneg
        _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    have hvar_point : ∀ i ∈ Finset.range (N - 1),
        -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) ≤
          2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
      intro i hi
      by_cases hni : n ≤ i
      · have hi_tail : n ≤ i + 1 := hni.trans (Nat.le_succ i)
        have hG_le : (∑ j ∈ Finset.range (i + 1), g j) ≤ 2 * D :=
          (le_abs_self _).trans (hG_bound (i + 1))
        have hw_mono : w (i + 1) ≤ w i := by
          have harg : (((m * i : ℕ) : ℝ)) ≤ (((m * (i + 1) : ℕ) : ℝ)) := by
            exact_mod_cast Nat.mul_le_mul_left m (Nat.le_succ i)
          have hi_two : 2 ≤ i := hn.trans hni
          have hlog_pos_i : 0 < Real.log (((m * i : ℕ) : ℝ)) := by
            have htwo : 2 ≤ m * i := Nat.mul_le_mul hm hi_two
            apply Real.log_pos
            exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
          have hlog_le : Real.log (((m * i : ℕ) : ℝ)) ≤
              Real.log (((m * (i + 1) : ℕ) : ℝ)) :=
            Real.log_le_log
              (by
                exact_mod_cast
                  (lt_of_lt_of_le Nat.zero_lt_two (Nat.mul_le_mul hm hi_two)))
              harg
          dsimp [w]
          gcongr
        have hdiff_nonneg : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr hw_mono
        calc
          -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) =
              (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), g j) := by ring
          _ ≤ (w i - w (i + 1)) * (2 * D) := by
            exact mul_le_mul_of_nonneg_left hG_le hdiff_nonneg
          _ = 2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by simp [hni, mul_comm, mul_assoc]
      · have hG_zero : (∑ j ∈ Finset.range (i + 1), g j) = 0 := by
          rw [hG_eq (i + 1)]
          rw [Finset.Ico_eq_empty_of_le]
          · simp
          · omega
        simp [hni, hG_zero]
    have hvariation :
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      calc
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) =
            ∑ i ∈ Finset.range (N - 1),
              -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) := by
          rw [Finset.sum_neg_distrib]
        _ ≤ ∑ i ∈ Finset.range (N - 1),
              2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
          exact Finset.sum_le_sum hvar_point
        _ = 2 * D * (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext i
            simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
          · intro i hi
            simp
        _ = 2 * D * (w n - w (N - 1)) := by
          have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := w) hN_pred_ge
          have hsum' : (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) = w n - w (N - 1) := by
            calc
              (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) =
                  - (∑ i ∈ Finset.Ico n (N - 1), (w (i + 1) - w i)) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = -(w (N - 1) - w n) := by rw [hsum]
              _ = w n - w (N - 1) := by ring
          rw [hsum']
        _ ≤ 2 * D * w n := by
          have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
          nlinarith [htwoD_nonneg]
        _ ≤ 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
          have hwn_le := hw_le_L n le_rfl
          calc
            2 * D * w n ≤ 2 * D * (1 / (Real.log ((m : ℝ) * y)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hwn_le htwoD_nonneg
            _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    calc
      w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 +
            2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
        linarith
      _ = 4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
  · rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp only [Nat.cast_mul, Finset.sum_empty, ge_iff_le]
    positivity

lemma mangoldt_log_increment_weighted_bound (m N : ℕ) (hm : 1 ≤ m) (y : ℝ)
    (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
        (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      1 / Real.log ((m : ℝ) * y) +
        Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  by_cases hN : n < N
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [← Finset.add_sum_Ioo_eq_sum_Ico
      (f := fun q : ℕ =>
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) hN]
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hnum : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log 2 := by
      have hnpos : 0 < n := by omega
      have hn1pos : 0 < n - 1 := by omega
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hnpos)
      have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hn1pos)
      rw [← Real.log_div hn_ne hn1_ne]
      apply Real.log_le_log
      · positivity
      · field_simp [hn1_ne]
        rw [Nat.cast_sub (by omega : 1 ≤ n)] at *
        norm_num at *
        nlinarith
    have hlog_mn : Real.log ((m : ℝ) * y) ≤ Real.log (((m * n : ℕ) : ℝ)) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      have harg : (m : ℝ) * y ≤ (((m * n : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hyn hm_nonneg
      exact Real.log_le_log (by linarith) harg
    have hlog_mn_pos : 0 < Real.log (((m * n : ℕ) : ℝ)) := hLpos.trans_le hlog_mn
    have hfirst :
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
            (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hstep₁ :
          (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
              (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 := by
        gcongr
      have hstep₂ :
          Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
        gcongr
      exact hstep₁.trans hstep₂
    let F : ℕ → ℝ := fun r => 1 / Real.log (((m * r : ℕ) : ℝ))
    have htel :
        (∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x)) = F n - F (N - 1) := by
      rw [← Finset.Ico_succ_left_eq_Ioo]
      rw [show Order.succ n = n + 1 by rfl]
      rw [show N = N - 1 + 1 by omega]
      rw [← Finset.sum_Ico_add
        (f := fun x : ℕ => F (x - 1) - F x) (a := n) (b := N - 1) (c := 1)]
      have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := F)
        (Nat.le_pred_of_lt hN)
      have hsum' :
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) = F n - F (N - 1) := by
        calc
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) =
              - (∑ i ∈ Finset.Ico n (N - 1), (F (i + 1) - F i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -(F (N - 1) - F n) := by rw [hsum]
          _ = F n - F (N - 1) := by ring
      simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel] using hsum'
    have htail_point : ∀ x ∈ Finset.Ioo n N,
        (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2 ≤ F (x - 1) - F x := by
      intro x hx
      have hx_left : n < x := (Finset.mem_Ioo.mp hx).1
      have hx_pred_ge : 2 ≤ x - 1 := by omega
      have hx_one_le : 1 ≤ x := by omega
      have h := mangoldt_log_increment_pointwise_le m (x - 1) hm hx_pred_ge
      dsimp [F]
      simpa [Nat.sub_add_cancel hx_one_le] using h
    have htail_le :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤ F n - F (N - 1) := by
      calc
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
            ∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x) := by
          exact Finset.sum_le_sum htail_point
        _ = F n - F (N - 1) := htel
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hlog_N_pred_pos : 0 < Real.log (((m * (N - 1) : ℕ) : ℝ)) := by
      have htwo : 2 ≤ m * (N - 1) := Nat.mul_le_mul hm hN_pred_two
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
    have hF_N_nonneg : 0 ≤ F (N - 1) := by
      dsimp [F]
      positivity
    have htail :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
          1 / Real.log ((m : ℝ) * y) := by
      have hFn : F n ≤ 1 / Real.log ((m : ℝ) * y) := by
        dsimp [F]
        gcongr
      linarith
    linarith
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp only [Nat.cast_mul, Finset.sum_empty, one_div, ge_iff_le]
    positivity

lemma mangoldt_tail_range_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
        1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨D, hD_nonneg, hD⟩ := mertens_von_mangoldt_reciprocal
  refine ⟨Real.log 2 + 4 * D, by positivity, ?_⟩
  intro m hm y hy N
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  rw [mangoldt_tail_range_eq_ico]
  let n : ℕ := ⌈y⌉₊
  have hn : 2 ≤ n := by
    have hyn : y ≤ (n : ℝ) := by
      simpa [n] using Nat.le_ceil y
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  have hsplit :
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q) =
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [mangoldt_tail_term]
    ring
  have hmain := mangoldt_log_increment_weighted_bound m N hm y hy
  have herror := mangoldt_mertens_error_weighted_bound D hD_nonneg hD m N hm y hy
  rw [hsplit]
  calc
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
        (1 / Real.log ((m : ℝ) * y) +
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2) +
          4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      exact add_le_add hmain herror
    _ = 1 / Real.log ((m : ℝ) * y) +
        (Real.log 2 + 4 * D) / (Real.log ((m : ℝ) * y)) ^ 2 := by
      ring

lemma mangoldt_tail_upper_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      Summable (fun q : ℕ => if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ∧
        mangoldt_tail_sum m y ≤
          1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := mangoldt_tail_range_sum_bound
  refine ⟨C, hC, ?_⟩
  intro m hm y hy
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    summable_of_sum_range_le hnonneg (hbound m hm y hy)
  refine ⟨hsumm, ?_⟩
  simpa [mangoldt_tail_sum] using
    hsumm.tsum_le_of_sum_range_le (hbound m hm y hy)

lemma mangoldt_tail_finite_sum_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y)
    (s : Finset ℕ) :
    (∑ q ∈ s, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
      mangoldt_tail_sum m y := by
  obtain ⟨_, _, hbound⟩ := mangoldt_tail_upper_bound
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    (hbound m hm y hy).1
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  simpa [mangoldt_tail_sum] using hsumm.sum_le_tsum s (fun q _ => hnonneg q)

lemma mangoldt_dirichlet_series_summable_local :
    ∀ u : ℝ, 0 < u ->
      Summable (fun q : ℕ =>
        ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)) := by
  intro u hu
  have hs : 1 < (((1 + u : ℝ) : ℂ).re) := by
    simp
    linarith
  have hcomplex := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((1 + u : ℝ) : ℂ)) hs
  rw [LSeriesSummable] at hcomplex
  have hcomplex' : Summable (fun q : ℕ =>
      ((ArithmeticFunction.vonMangoldt q /
        Real.rpow (q : ℝ) (1 + u) : ℝ) : ℂ)) := by
    refine hcomplex.congr ?_
    intro q
    by_cases hq : q = 0
    · subst q
      simp [LSeries.term_def, Real.zero_rpow (by linarith : (1 : ℝ) + u ≠ 0)]
    · rw [LSeries.term_of_ne_zero hq]
      rw [Complex.ofReal_div]
      congr 1
      exact (Complex.ofReal_cpow (Nat.cast_nonneg q) (1 + u)).symm
  exact Complex.summable_ofReal.mp hcomplex'

lemma mangoldt_dirichlet_series_finite_threshold_bound_local :
    ∀ u : ℝ, 0 < u -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤ 1 / u := by
  intro u hu N
  have hsumm := mangoldt_dirichlet_series_summable_local u hu
  have hnonneg : ∀ q : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
    intro q
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg q) (1 + u))
  calc
    (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤
        ∑ q ∈ Finset.range N,
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      split_ifs
      · rfl
      · exact hnonneg q
    _ ≤ mangoldt_dirichlet_series u := by
      simpa [mangoldt_dirichlet_series] using
        hsumm.sum_le_tsum (Finset.range N) (fun q _ => hnonneg q)
    _ ≤ 1 / u := von_mangoldt_dirichlet_series_upper_bound u hu

lemma log_square_integral_kernel_local (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t))) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := r) (by norm_num) hr
  calc
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      norm_num [Real.rpow_one]
    _ = (1 / r) ^ (2 : ℝ) * Real.Gamma 2 := h
    _ = 1 / r ^ 2 := by
      rw [Real.Gamma_two, Real.rpow_two]
      field_simp [hr.ne']

lemma log_square_integral_kernel_integrable_local (r : ℝ) (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-(r * t)))
      (Set.Ioi 0) := by
  have hhalf_ne : r / 2 ≠ 0 := by positivity
  have hrate_pos : -r + r / 2 < 0 := by linarith
  have hrate_neg : -r - r / 2 < 0 := by linarith
  have hint_pos : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp ((-r + r / 2) * t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_Ioi hrate_pos 0
  have hint_neg : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp ((-r - r / 2) * t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_Ioi hrate_neg 0
  have h := ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
    (X := fun t : ℝ => t) (v := -r) (t := r / 2)
    hhalf_ne hint_pos hint_neg 1
  change MeasureTheory.Integrable
    (fun t : ℝ => t * Real.exp (-(r * t)))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h

lemma mangoldt_tail_term_integral_local (m q : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) :
    mangoldt_tail_term m q =
      ∫ t : ℝ in Set.Ioi 0,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
  have hmq_two : 2 ≤ m * q := Nat.mul_le_mul hm hq
  have hmq_pos : 0 < (((m * q : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hmq_two)
  have hlog_pos : 0 < Real.log (((m * q : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmq_two)
  have hkernel :
      (∫ t : ℝ in Set.Ioi 0,
        t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) =
        1 / Real.log (((m * q : ℕ) : ℝ)) ^ 2 := by
    have hfun : (fun t : ℝ => t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) =
        fun t : ℝ => t * Real.exp (-(Real.log (((m * q : ℕ) : ℝ)) * t)) := by
      funext t
      change t * (((m * q : ℕ) : ℝ) ^ (-t)) =
        t * Real.exp (-(Real.log (((m * q : ℕ) : ℝ)) * t))
      rw [Real.rpow_def_of_pos hmq_pos]
      ring_nf
    rw [hfun]
    exact log_square_integral_kernel_local
      (Real.log (((m * q : ℕ) : ℝ))) hlog_pos
  calc
    mangoldt_tail_term m q =
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (1 / Real.log (((m * q : ℕ) : ℝ)) ^ 2) := by
      rw [mangoldt_tail_term]
      ring
    _ = (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
        (∫ t : ℝ in Set.Ioi 0,
          t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
      rw [hkernel]
    _ = ∫ t : ℝ in Set.Ioi 0,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
      rw [MeasureTheory.integral_const_mul]

lemma mangoldt_tail_integrand_factor_local (n N : ℕ) (t : ℝ) (hn : 2 ≤ n) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
      else 0) =
      t * Real.rpow (n : ℝ) (-t) *
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
          else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
  · have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
    have hq_nat : 2 ≤ q := by
      exact_mod_cast hqcond
    have hq_pos : 0 < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_nat)
    simp only [Nat.ofNat_le_cast, Nat.cast_mul, Real.rpow_eq_pow, mul_ite, mul_zero]
    rw [Real.mul_rpow hn_pos.le hq_pos.le]
    rw [Real.rpow_add hq_pos (1 : ℝ) t, Real.rpow_one]
    rw [Real.rpow_neg hq_pos.le t]
    field_simp [hq_pos.ne', (Real.rpow_pos_of_pos hq_pos t).ne']
  · simp [hqcond]

lemma mangoldt_tail_range_subinvariant_local (n N : ℕ) (hn : 2 ≤ n) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) ≤
      1 / Real.log (n : ℝ) := by
  have hm : 1 ≤ n := by omega
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  let F : ℝ → ℝ := fun t =>
    ∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
      else 0
  have hterm_int : ∀ q ∈ Finset.range N,
      MeasureTheory.Integrable
        (fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro q hq
    by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
    · have hq_nat : 2 ≤ q := by
        exact_mod_cast hqcond
      have hnq_two : 2 ≤ n * q := Nat.mul_le_mul hm hq_nat
      have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
      have hlog_nq_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
      have hbase_int : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          (Set.Ioi 0) := by
        have h := log_square_integral_kernel_integrable_local
          (Real.log (((n * q : ℕ) : ℝ))) hlog_nq_pos
        have hfun : (fun t : ℝ => t * Real.rpow (((n * q : ℕ) : ℝ)) (-t)) =
            fun t : ℝ => t * Real.exp (-(Real.log (((n * q : ℕ) : ℝ)) * t)) := by
          funext t
          change t * (((n * q : ℕ) : ℝ) ^ (-t)) =
            t * Real.exp (-(Real.log (((n * q : ℕ) : ℝ)) * t))
          rw [Real.rpow_def_of_pos hnq_pos]
          ring_nf
        rw [hfun]
        exact h
      simpa [hqcond] using
        hbase_int.const_mul (ArithmeticFunction.vonMangoldt q / (q : ℝ))
    · simp [hqcond]
  have hF_int : MeasureTheory.IntegrableOn F (Set.Ioi 0) := by
    have hF_int' : MeasureTheory.Integrable
        (∑ q ∈ Finset.range N, fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      MeasureTheory.integrable_finsetSum' (Finset.range N) hterm_int
    dsimp [F, MeasureTheory.IntegrableOn]
    convert hF_int' using 1
    funext t
    simp [Finset.sum_apply]
  have hG_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-(Real.log (n : ℝ) * t))) (Set.Ioi 0) := by
    have hrate : -Real.log (n : ℝ) < 0 := by linarith
    convert integrableOn_exp_mul_Ioi hrate 0 using 1
    funext t
    ring_nf
  have hsum_integral :
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := by
    calc
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
          ∑ q ∈ Finset.range N,
            ∫ t : ℝ in Set.Ioi 0,
              if (2 : ℝ) ≤ (q : ℝ) then
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
              else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
        · have hq_nat : 2 ≤ q := by
            exact_mod_cast hqcond
          simp [hqcond, mangoldt_tail_term_integral_local n q hm hq_nat]
        · simp [hqcond]
      _ = ∫ t : ℝ in Set.Ioi 0, F t := by
        symm
        dsimp [F]
        exact MeasureTheory.integral_finsetSum (Finset.range N) hterm_int
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      F t ≤ Real.exp (-(Real.log (n : ℝ) * t)) := by
    intro t ht
    have htpos : 0 < t := ht
    have hdir := mangoldt_dirichlet_series_finite_threshold_bound_local t htpos N
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (-t) :=
      Real.rpow_nonneg hn_pos.le (-t)
    have hcoef_nonneg : 0 ≤ t * Real.rpow (n : ℝ) (-t) := by positivity
    calc
      F t = t * Real.rpow (n : ℝ) (-t) *
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
            else 0) := by
        simpa [F] using mangoldt_tail_integrand_factor_local n N t hn
      _ ≤ t * Real.rpow (n : ℝ) (-t) * (1 / t) := by
        exact mul_le_mul_of_nonneg_left hdir hcoef_nonneg
      _ = Real.rpow (n : ℝ) (-t) := by
        field_simp [htpos.ne']
      _ = Real.exp (-(Real.log (n : ℝ) * t)) := by
        change ((n : ℝ) ^ (-t)) = Real.exp (-(Real.log (n : ℝ) * t))
        rw [Real.rpow_def_of_pos hn_pos]
        ring_nf
  have hintegral_le :
      (∫ t : ℝ in Set.Ioi 0, F t) ≤
        ∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t)) := by
    exact MeasureTheory.setIntegral_mono_on hF_int hG_int measurableSet_Ioi hpoint
  have hG_integral :
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t))) =
        1 / Real.log (n : ℝ) := by
    have hrate : -Real.log (n : ℝ) < 0 := by linarith
    have h := integral_exp_mul_Ioi (a := -Real.log (n : ℝ)) hrate 0
    simpa [hlog_pos.ne'] using h
  calc
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := hsum_integral
    _ ≤ ∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t)) := hintegral_le
    _ = 1 / Real.log (n : ℝ) := hG_integral

lemma mangoldt_subinvariant_bound :
    ∀ n : ℕ, 2 ≤ n -> Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤ 1 := by
  intro n hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hbound : ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) ≤
        1 / Real.log (n : ℝ) := by
    intro N
    exact mangoldt_tail_range_subinvariant_local n N hn
  have hsumm : Summable (fun q : ℕ =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) :=
    summable_of_sum_range_le hnonneg hbound
  have htail : mangoldt_tail_sum n 2 ≤ 1 / Real.log (n : ℝ) := by
    simpa [mangoldt_tail_sum] using hsumm.tsum_le_of_sum_range_le hbound
  calc
    Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤
        Real.log (n : ℝ) * (1 / Real.log (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail hlog_pos.le
    _ = 1 := by
      field_simp [hlog_pos.ne']

noncomputable def finite_chain_initial_mass (x X : ℝ) (n : ℕ) : ℝ :=
  if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then
    erdos_weight n -
      ∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0
  else 0

lemma finite_chain_erdos_le_initial_mass (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ ∑' n : ℕ, finite_chain_initial_mass x X n := by
  classical
  have hmass_nonneg : ∀ n : ℕ, 0 ≤ finite_chain_initial_mass x X n := by
    intro n
    rw [finite_chain_initial_mass]
    by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
    · rw [if_pos hnint]
      have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
      have hn_one : 1 ≤ n := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn_two)
      have hinner_le :
          (∑' q : ℕ,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0) ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
        apply tsum_le_of_sum_le'
        · apply mul_nonneg
          · positivity
          · rw [mangoldt_tail_sum]
            apply tsum_nonneg
            intro q
            split_ifs
            · rw [mangoldt_tail_term]
              exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
            · norm_num
        · intro s
          have hpoint : ∀ q : ℕ,
              (if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                (1 / (n : ℝ)) *
                  (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
            intro q
            by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
            · rw [if_pos hqcond]
              have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
              rw [if_pos hqreal]
              rw [erdos_weight, mangoldt_tail_term]
              rw [Nat.cast_mul]
              ring_nf
              exact le_rfl
            · rw [if_neg hqcond]
              apply mul_nonneg
              · positivity
              · split_ifs
                · rw [mangoldt_tail_term]
                  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
                · norm_num
          calc
            (∑ q ∈ s,
              if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                ∑ q ∈ s,
                  (1 / (n : ℝ)) *
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                apply Finset.sum_le_sum
                intro q _
                exact hpoint q
            _ = (1 / (n : ℝ)) *
                  ∑ q ∈ s,
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                rw [Finset.mul_sum]
            _ ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
                exact mul_le_mul_of_nonneg_left
                  (mangoldt_tail_finite_sum_le n hn_one 2 (by norm_num) s) (by positivity)
      have htail_le : mangoldt_tail_sum n 2 ≤ 1 / Real.log (n : ℝ) := by
        rw [le_div_iff₀ hlog_pos]
        simpa [mul_comm] using mangoldt_subinvariant_bound n hn_two
      have hscaled_le : (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤ erdos_weight n := by
        calc
          (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤
              (1 / (n : ℝ)) * (1 / Real.log (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left htail_le (by positivity)
          _ = erdos_weight n := by
              rw [erdos_weight]
              ring_nf
      linarith
    · rw [if_neg hnint]
  rw [erdos_sum]
  apply tsum_le_of_sum_le'
  · exact tsum_nonneg hmass_nonneg
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let R : Finset ℕ := (Finset.range M).filter (fun n => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    have hb_tsum_eq :
        (∑' n : ℕ, finite_chain_initial_mass x X n) =
          ∑ n ∈ R, finite_chain_initial_mass x X n := by
      exact tsum_eq_sum (s := R) (fun n hn => by
        have hnnot : ¬ (x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) := by
          intro hnx
          apply hn
          have hn_le_ceil : n ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
          have hn_lt_M : n < M := by
            dsimp [M]
            omega
          simp [R, hn_lt_M, hnx]
        rw [finite_chain_initial_mass, if_neg hnnot])
    have hleft_eq :
        (∑ i ∈ s, A.indicator erdos_weight i) =
          ∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0 := by
      have hs_eq :
          (∑ i ∈ s, A.indicator erdos_weight i) =
            ∑ i ∈ s.filter (fun i => i ∈ A), erdos_weight i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiA : i ∈ A
        · simp [hiA]
        · simp [hiA]
      have hR_eq :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) =
            ∑ n ∈ R.filter (fun n => n ∈ s ∧ n ∈ A), erdos_weight n := by
        exact (Finset.sum_filter (s := R)
          (p := fun n => n ∈ s ∧ n ∈ A) (f := erdos_weight)).symm
      rw [hs_eq, hR_eq]
      symm
      apply Finset.sum_bij (fun n hn => n)
      · intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.2.1, hn.2.2⟩
      · intro a ha b hb h
        exact h
      · intro b hb
        simp only [Finset.mem_filter] at hb
        have hB := hsupp b hb.2
        have hb_le_ceil : b ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hB.2 (Nat.le_ceil X))
        have hb_lt_M : b < M := by
          dsimp [M]
          omega
        refine ⟨b, ?_, rfl⟩
        simp [R, hb_lt_M, hB, hb]
      · intro n hn
        rfl
    have hmass_finite (n : ℕ) (hnR : n ∈ R) :
        finite_chain_initial_mass x X n = erdos_weight n -
          ∑ q ∈ Finset.range M,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0 := by
      have hnR' : n < M ∧ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
        simpa [R] using hnR
      have hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := hnR'.2
      rw [finite_chain_initial_mass, if_pos hnint]
      congr 1
      exact tsum_eq_sum (s := Finset.range M) (fun q hq => by
        have hqnot : ¬ (2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) := by
          intro hcond
          apply hq
          have hq_le_prod : q ≤ n * q := by
            have hn_one : 1 ≤ n := by
              have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
              omega
            exact Nat.le_mul_of_pos_left q hn_one
          have hq_le_X : (q : ℝ) ≤ X := by
            have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by
              exact_mod_cast hq_le_prod
            exact le_trans this hcond.2
          have hq_le_ceil : q ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
          have hq_lt_M : q < M := by
            dsimp [M]
            omega
          exact Finset.mem_range.mpr hq_lt_M
        rw [if_neg hqnot])
    have hfinite :
        (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) ≤
          ∑ n ∈ R, finite_chain_initial_mass x X n := by
      let shadow : ℕ → ℝ := fun n =>
        if ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ n then 1 else 0
      let pairs : Finset (ℕ × ℕ) := R.product (Finset.range M)
      let pairTerm : ℕ × ℕ → ℝ := fun p =>
        if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
          shadow p.1 * (erdos_weight (p.1 * p.2) *
            ArithmeticFunction.vonMangoldt p.2 / Real.log ((p.1 * p.2 : ℕ) : ℝ))
        else 0
      have hshadow_le_one : ∀ n, shadow n ≤ 1 := by
        intro n
        dsimp [shadow]
        split_ifs <;> norm_num
      have hfiber_bound : ∀ r ∈ R,
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤ erdos_weight r := by
        intro r hr
        have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
          simpa [R] using hr
        have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
        have hr_ne : r ≠ 0 := by omega
        have hlog_pos : 0 < Real.log (r : ℝ) := by
          apply Real.log_pos
          exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hr_two)
        let F : Finset (ℕ × ℕ) := pairs.filter (fun p => p.1 * p.2 = r)
        let boundTerm : ℕ → ℝ := fun q =>
          erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)
        have hbound_nonneg : ∀ q, 0 ≤ boundTerm q := by
          intro q
          dsimp [boundTerm]
          have hw : 0 ≤ erdos_weight r := by
            rw [erdos_weight]
            positivity
          exact div_nonneg (mul_nonneg hw ArithmeticFunction.vonMangoldt_nonneg) hlog_pos.le
        have hpoint : ∀ p ∈ F, pairTerm p ≤ boundTerm p.2 := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          dsimp [pairTerm, boundTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · rw [if_pos hcond, hprod]
            simpa using
              mul_le_mul_of_nonneg_right (hshadow_le_one p.1) (hbound_nonneg p.2)
          · rw [if_neg hcond]
            exact hbound_nonneg p.2
        have hsum_le : (∑ p ∈ F, pairTerm p) ≤ ∑ p ∈ F, boundTerm p.2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hpoint p hp
        have hsum_image : (∑ p ∈ F, boundTerm p.2) =
            ∑ q ∈ F.image Prod.snd, boundTerm q := by
          symm
          rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          have hpa : a.1 * a.2 = r := ha'.2
          have hpb : b.1 * b.2 = r := hb'.2
          have ha2_pos : 0 < a.2 := by
            by_contra hnot
            have ha2z : a.2 = 0 := Nat.eq_zero_of_not_pos hnot
            rw [ha2z] at hpa
            simp at hpa
            exact hr_ne hpa.symm
          have hfst : a.1 = b.1 := by
            apply Nat.mul_right_cancel ha2_pos
            rw [hpa, hab, hpb]
          exact Prod.ext hfst hab
        have himage_subset : F.image Prod.snd ⊆ r.divisors := by
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          have hqdiv : p.2 ∣ r := by
            refine ⟨p.1, ?_⟩
            rw [mul_comm, hprod]
          exact Nat.mem_divisors.mpr ⟨hqdiv, hr_ne⟩
        have himage_le : (∑ q ∈ F.image Prod.snd, boundTerm q) ≤
            ∑ q ∈ r.divisors, boundTerm q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro q hq hqnot
            exact hbound_nonneg q
        have hdiv_eq : (∑ q ∈ r.divisors, boundTerm q) = erdos_weight r := by
          dsimp [boundTerm]
          calc
            (∑ q ∈ r.divisors,
              erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)) =
                (erdos_weight r / Real.log (r : ℝ)) *
                  ∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
            _ = (erdos_weight r / Real.log (r : ℝ)) * Real.log (r : ℝ) := by
                rw [von_mangoldt_divisor_sum]
            _ = erdos_weight r := by
                field_simp [hlog_pos.ne']
        calc
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
              ∑ p ∈ F, pairTerm p := rfl
          _ ≤ ∑ p ∈ F, boundTerm p.2 := hsum_le
          _ = ∑ q ∈ F.image Prod.snd, boundTerm q := hsum_image
          _ ≤ ∑ q ∈ r.divisors, boundTerm q := himage_le
          _ = erdos_weight r := hdiv_eq
      have hfiber_zero_active : ∀ r ∈ R, r ∈ s ∧ r ∈ A ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hactive
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow]
            rw [if_neg]
            intro hex
            rcases hex with ⟨a, has, haA, hadiv⟩
            have hadivr : a ∣ r := by
              rcases hadiv with ⟨k, hk⟩
              refine ⟨k * p.2, ?_⟩
              rw [← hprod, hk, Nat.mul_assoc]
            have har : a = r := hprim.eq haA hactive.2 hadivr
            subst a
            have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
              simpa [R] using hr
            have hp2_gt_one : 1 < p.2 := by omega
            have hp1_pos : 0 < p.1 := by
              by_contra hp10
              have hp1z : p.1 = 0 := Nat.eq_zero_of_not_pos hp10
              rw [hp1z] at hprod
              simp at hprod
              have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
              omega
            have hp1_lt_r : p.1 < r := by
              rw [← hprod]
              exact lt_mul_of_one_lt_right hp1_pos hp2_gt_one
            exact not_le_of_gt hp1_lt_r (Nat.le_of_dvd hp1_pos hadiv)
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hshadow_factor_zero : ∀ r ∈ R, shadow r = 0 ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hsr
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow] at hsr ⊢
            by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ p.1
            · exfalso
              have hexr : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r := by
                rcases hex with ⟨a, has, haA, hadiv⟩
                refine ⟨a, has, haA, ?_⟩
                rcases hadiv with ⟨k, hk⟩
                refine ⟨k * p.2, ?_⟩
                rw [← hprod, hk, Nat.mul_assoc]
              rw [if_pos hexr] at hsr
              norm_num at hsr
            · rw [if_neg hex]
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hfiber : ∀ r ∈ R,
          (if r ∈ s ∧ r ∈ A then erdos_weight r else 0) +
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤
              shadow r * erdos_weight r := by
        intro r hr
        by_cases hactive : r ∈ s ∧ r ∈ A
        · have hsh : shadow r = 1 := by
            dsimp [shadow]
            rw [if_pos]
            exact ⟨r, hactive.1, hactive.2, dvd_rfl⟩
          rw [if_pos hactive, hfiber_zero_active r hr hactive, hsh]
          linarith
        · rw [if_neg hactive]
          by_cases hshadow : shadow r = 0
          · rw [hshadow_factor_zero r hr hshadow, hshadow]
            norm_num
          · have hsh : shadow r = 1 := by
              dsimp [shadow] at hshadow ⊢
              by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r
              · rw [if_pos hex]
              · rw [if_neg hex] at hshadow
                exfalso
                exact hshadow rfl
            rw [hsh]
            simpa using hfiber_bound r hr
      have hsum_fiber :
          (∑ r ∈ R, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        exact Finset.sum_fiberwise_eq_sum_filter pairs R
          (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
      have hupper :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p ≤
            ∑ n ∈ R, shadow n * erdos_weight n := by
        calc
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p =
                ∑ n ∈ R,
                  ((if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
                    ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = n), pairTerm p) := by
                rw [Finset.sum_add_distrib, hsum_fiber]
          _ ≤ ∑ n ∈ R, shadow n * erdos_weight n := by
                apply Finset.sum_le_sum
                intro n hn
                exact hfiber n hn
      have hpair_all_eq :
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p) =
            ∑ p ∈ pairs, pairTerm p := by
        apply Finset.sum_subset
        · intro p hp
          exact (Finset.mem_filter.mp hp).1
        · intro p hpairs hpnot
          have hprod_not : p.1 * p.2 ∉ R := by
            intro hpR
            apply hpnot
            simp [hpairs, hpR]
          have hp : p.1 ∈ R ∧ p.2 ∈ Finset.range M := by
            simpa [pairs] using hpairs
          dsimp [pairTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · exfalso
            apply hprod_not
            have hp1R : p.1 < M ∧ x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := by
              simpa [R] using hp.1
            have hp2one : 1 ≤ p.2 := by omega
            have hp1_le_prod : p.1 ≤ p.1 * p.2 :=
              Nat.le_mul_of_pos_right p.1 hp2one
            have hxprod : x ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
              have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
                exact_mod_cast hp1_le_prod
              exact le_trans hp1R.2.1 this
            have hprod_le_ceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
              exact_mod_cast (le_trans hcond.2 (Nat.le_ceil X))
            have hprod_lt_M : p.1 * p.2 < M := by
              dsimp [M]
              omega
            simp only [R, Finset.mem_filter, Finset.mem_range]
            exact ⟨hprod_lt_M, by simpa [Nat.cast_mul] using hxprod,
              by simpa [Nat.cast_mul] using hcond.2⟩
          · rw [if_neg hcond]
      have hpair_product :
          (∑ p ∈ pairs, pairTerm p) =
            ∑ n ∈ R, shadow n *
              ∑ q ∈ Finset.range M,
                if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                  erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                    Real.log ((n * q : ℕ) : ℝ)
                else 0 := by
        dsimp [pairs, pairTerm]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
        · simp
        · simp
      have hshadow_bound :
          (∑ n ∈ R, shadow n * erdos_weight n) ≤
            (∑ n ∈ R, finite_chain_initial_mass x X n) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        rw [hpair_all_eq, hpair_product]
        calc
          (∑ n ∈ R, shadow n * erdos_weight n) =
              ∑ n ∈ R, shadow n *
                (finite_chain_initial_mass x X n +
                  ∑ q ∈ Finset.range M,
                    if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                        Real.log ((n * q : ℕ) : ℝ)
                    else 0) := by
                apply Finset.sum_congr rfl
                intro n hn
                rw [hmass_finite n hn]
                ring
          _ = (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ ≤ (∑ n ∈ R, finite_chain_initial_mass x X n) +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                have hsum_le :
                    (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) ≤
                      ∑ n ∈ R, finite_chain_initial_mass x X n := by
                  apply Finset.sum_le_sum
                  intro n hn
                  simpa using
                    mul_le_mul_of_nonneg_right (hshadow_le_one n) (hmass_nonneg n)
                linarith
      linarith
    rw [hb_tsum_eq, hleft_eq]
    exact hfinite

lemma finite_chain_initial_mass_sum_eq_cut_capacity (x X : ℝ) (hx : 2 ≤ x) :
    (∑' n : ℕ, finite_chain_initial_mass x X n) = cut_capacity x X := by
  classical
  let s : Finset ℕ := Finset.range (⌈X⌉₊ + 1)
  let coeff : ℕ → ℝ := fun r => 1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2)
  let pairTerm : ℕ × ℕ → ℝ := fun p =>
    if x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X then
      if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
        coeff (p.1 * p.2) * ArithmeticFunction.vonMangoldt p.2
      else 0
    else 0
  have hincoming_point (n q : ℕ)
      (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
      (hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) :
      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
          Real.log ((n * q : ℕ) : ℝ) =
        coeff (n * q) * ArithmeticFunction.vonMangoldt q := by
    have hprod_gt_one : (1 : ℝ) < ((n * q : ℕ) : ℝ) := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      have hq_ge_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
      rw [Nat.cast_mul]
      nlinarith
    have hlog_ne : Real.log ((n * q : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos hprod_gt_one).ne'
    rw [erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hleft : (∑' n : ℕ, finite_chain_initial_mass x X n) =
      ∑ n ∈ s, finite_chain_initial_mass x X n := by
    exact tsum_eq_sum (s := s) (fun n hn => by
      rw [finite_chain_initial_mass]
      rw [if_neg]
      intro hnx
      apply hn
      simp only [s, Finset.mem_range]
      have hnleceil : n ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
      omega)
  have hinner (n : ℕ) (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) :
      (∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0) =
      ∑ q ∈ s,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0 := by
    refine tsum_eq_sum (s := s) ?_
    intro q hq
    rw [if_neg]
    intro hcond
    apply hq
    simp only [s, Finset.mem_range]
    have hn_ge_one : 1 ≤ n := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      exact_mod_cast (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    have hq_le_prod : q ≤ n * q := Nat.le_mul_of_pos_left q hn_ge_one
    have hq_le_X : (q : ℝ) ≤ X := by
      have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by exact_mod_cast hq_le_prod
      exact le_trans this hcond.2
    have hq_le_ceil : q ≤ ⌈X⌉₊ := by
      exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
    omega
  have hleft_expand :
      (∑' n : ℕ, finite_chain_initial_mass x X n) =
        (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
          ∑ p ∈ s.product s, pairTerm p := by
    rw [hleft]
    calc
      (∑ n ∈ s, finite_chain_initial_mass x X n)
          = ∑ n ∈ s,
              ((if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
                ∑ q ∈ s, pairTerm (n, q)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [finite_chain_initial_mass]
            by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
            · rw [if_pos hnint, hinner n hnint]
              simp only [if_pos hnint]
              congr 1
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
              · rw [if_pos hqcond, hincoming_point n q hnint hqcond]
                have hqcond' : 2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X := by
                  exact ⟨hqcond.1, by simpa [Nat.cast_mul] using hqcond.2⟩
                simp [pairTerm, hnint, hqcond, hqcond', Nat.cast_mul]
              · rw [if_neg hqcond]
                have hqcond' : ¬(2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X) := by
                  intro h
                  apply hqcond
                  exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
                simp [pairTerm, hnint, hqcond', Nat.cast_mul]
            · rw [if_neg hnint]
              simp [pairTerm, hnint]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ n ∈ s, ∑ q ∈ s, pairTerm (n, q) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ p ∈ s.product s, pairTerm p := by
          simpa using congrArg
            (fun z => (∑ n ∈ s,
              if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) - z)
            (Finset.sum_product (s := s) (t := s)
              (f := fun p : ℕ × ℕ => pairTerm p)).symm
  have hright : cut_capacity x X =
      ∑ r ∈ s,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          coeff r * (∑ q ∈ r.divisors,
            if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0 := by
    rw [cut_capacity]
    calc
      (∑' r : ℕ,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
            (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0)
          = ∑ r ∈ s,
              if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
                (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
                  (∑ q ∈ r.divisors,
                    if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
              else 0 := by
            exact tsum_eq_sum (s := s) (fun r hr => by
              rw [if_neg]
              intro hrx
              apply hr
              simp only [s, Finset.mem_range]
              have hrleceil : r ≤ ⌈X⌉₊ := by
                exact_mod_cast (le_trans hrx.2 (Nat.le_ceil X))
              omega)
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · simp [coeff, hrint]
            · simp [hrint]
  have hbase_point (r : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      erdos_weight r = coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) := by
    have hr_gt_one : (1 : ℝ) < (r : ℝ) := by linarith [le_trans hx hr.1]
    have hlog_ne : Real.log (r : ℝ) ≠ 0 := (Real.log_pos hr_gt_one).ne'
    rw [von_mangoldt_divisor_sum, erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hbase_sum :
      (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q)
          else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
    · rw [if_pos hrint, if_pos hrint, hbase_point r hrint]
    · simp [hrint]
  have hpair_fiber (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
      (p : ℕ × ℕ) (hp : p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)) :
      pairTerm p =
        if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then coeff r * ArithmeticFunction.vonMangoldt p.2 else 0 := by
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases hcond : 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)
    · have hp2_ge_one : 1 ≤ p.2 := by omega
      have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
      have hp1_le_X : (p.1 : ℝ) ≤ X := by
        have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
        rw [hprod] at this
        exact le_trans this hrint.2
      have hprod_le_X : (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := by simpa [hprod] using hrint.2
      have hprod_le_X' : (p.1 : ℝ) * (p.2 : ℝ) ≤ X := by
        simpa [Nat.cast_mul] using hprod_le_X
      have hcond' : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := ⟨hcond.1, hprod_le_X⟩
      have hcond'' : 2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X := ⟨hcond.1, hprod_le_X'⟩
      have houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := ⟨hcond.2, hp1_le_X⟩
      have hprod_coeff : coeff (p.1 * p.2) = coeff r := by rw [hprod]
      simp [pairTerm, houter, hcond', hcond'', hprod_coeff, Nat.cast_mul]
    · have hnot_outer_or_inner :
          ¬(x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X) ∨
            ¬(2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)) := by
        by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
        · right
          intro hinner
          apply hcond
          exact ⟨hinner.1, houter.1⟩
        · exact Or.inl houter
      rcases hnot_outer_or_inner with houter | hinner
      · simp [pairTerm, houter, hcond]
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, hinner', hcond, Nat.cast_mul]
  have hbij_sum (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
          (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt p.2) =
        ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt q := by
    refine Finset.sum_bij' (fun p hp => p.2) (fun q hq => (r / q, q)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hr_ne : r ≠ 0 := by
        have : (0 : ℝ) < (r : ℝ) := by linarith [hx, hrint.1]
        exact_mod_cast this.ne'
      have hp2pos : 0 < p.2 := by omega
      have hp2dvd : p.2 ∣ r := by
        refine ⟨p.1, ?_⟩
        rw [mul_comm, hprod]
      have hp1_eq : p.1 = r / p.2 := by
        rw [← hprod]
        simp [hp2pos]
      constructor
      · exact Nat.mem_divisors.mpr ⟨hp2dvd, hr_ne⟩
      · constructor
        · exact hpcond.1
        · simpa [← hp1_eq] using hpcond.2
    · intro q hq
      simp only [Finset.mem_filter] at hq ⊢
      rcases hq with ⟨hqdivmem, hqcond⟩
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp hqdivmem).1
      have hr_ne : r ≠ 0 := (Nat.mem_divisors.mp hqdivmem).2
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hqle : q ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr_ne) hqdiv
      have hdivle : r / q ≤ r := Nat.div_le_self r q
      have hr_lt : r < ⌈X⌉₊ + 1 := by simpa [s, Finset.mem_range] using hrmem
      have hqmems : q ∈ s := by simp only [s, Finset.mem_range]; omega
      have hdivmems : r / q ∈ s := by simp only [s, Finset.mem_range]; omega
      constructor
      · constructor
        · exact Finset.mem_product.mpr ⟨hdivmems, hqmems⟩
        · exact hprod
      · exact hqcond
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hp2pos : 0 < p.2 := by omega
      have hp1_eq : r / p.2 = p.1 := by rw [← hprod]; simp [hp2pos]
      ext
      · exact hp1_eq
      · rfl
    · intro q hq
      rfl
    · intro p hp
      rfl
  have hfiber_high (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) =
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
    calc
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p)
          = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then
                coeff r * ArithmeticFunction.vonMangoldt p.2
              else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hpair_fiber r hrint p hp
      _ = ∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
              (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt p.2 := by
            exact (Finset.sum_filter (s := (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r))
              (p := fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ))
              (f := fun p : ℕ × ℕ => coeff r * ArithmeticFunction.vonMangoldt p.2)).symm
      _ = ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt q := hbij_sum r hrmem hrint
      _ = coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
            rw [Finset.mul_sum]
            simpa [mul_ite] using
              (Finset.sum_filter (s := r.divisors)
                (p := fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ))
                (f := fun q : ℕ => coeff r * ArithmeticFunction.vonMangoldt q))
  have hfiber_zero (r : ℕ) (hrnot : ¬(x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · have hp2_ge_one : 1 ≤ p.2 := by omega
        have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
        have hxle_r : x ≤ (r : ℝ) := by
          have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
          rw [hprod] at this
          exact le_trans houter.1 this
        have hrleX : (r : ℝ) ≤ X := by simpa [hprod] using hinner.2
        exact False.elim (hrnot ⟨hxle_r, hrleX⟩)
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_zero_notmem (p : ℕ × ℕ) (hp : p ∈ s.product s)
      (hprodmem : ¬ p.1 * p.2 ∈ s) : pairTerm p = 0 := by
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · apply False.elim
        apply hprodmem
        simp only [s, Finset.mem_range]
        have hleceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hinner.2 (Nat.le_ceil X))
        omega
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_sum :
      (∑ p ∈ s.product s, pairTerm p) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
    calc
      (∑ p ∈ s.product s, pairTerm p)
          = ∑ p ∈ s.product s, if p.1 * p.2 ∈ s then pairTerm p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hprodmem : p.1 * p.2 ∈ s
            · simp [hprodmem]
            · rw [if_neg hprodmem, hpair_zero_notmem p hp hprodmem]
      _ = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 ∈ s), pairTerm p := by
            exact (Finset.sum_filter (s := s.product s)
              (p := fun p : ℕ × ℕ => p.1 * p.2 ∈ s) (f := pairTerm)).symm
      _ = ∑ r ∈ s, ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              pairTerm p := by
            exact (Finset.sum_fiberwise_eq_sum_filter (s.product s) s
              (fun p : ℕ × ℕ => p.1 * p.2) pairTerm).symm
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hrmem
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · rw [if_pos hrint, hfiber_high r hrmem hrint]
            · rw [if_neg hrint, hfiber_zero r hrint]
  have hfinal_point (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
        coeff r * (∑ q ∈ r.divisors,
          if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
    have hdiv_split :
        (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
          (∑ q ∈ r.divisors,
            if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors,
            if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hlt : ((r / q : ℕ) : ℝ) < x
      · have hnle : ¬ x ≤ ((r / q : ℕ) : ℝ) := not_le_of_gt hlt
        simp [hlt, hnle]
      · have hge : x ≤ ((r / q : ℕ) : ℝ) := le_of_not_gt hlt
        by_cases hq2 : 2 ≤ q
        · simp [hlt, hge, hq2]
        · have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
          have hqeq : q = 1 := by omega
          simp [hqeq]
    rw [← mul_sub, hdiv_split]
  rw [hleft_expand, hright, hbase_sum, hpair_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
  · rw [if_pos hrint, if_pos hrint, if_pos hrint]
    exact hfinal_point r hrint
  · rw [if_neg hrint, if_neg hrint, if_neg hrint]
    ring

lemma finite_chain_cut_bound (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ cut_capacity x X := by
  calc
    erdos_sum A ≤ ∑' n : ℕ, finite_chain_initial_mass x X n :=
      finite_chain_erdos_le_initial_mass A x X hx hprim hsupp
    _ = cut_capacity x X :=
      finite_chain_initial_mass_sum_eq_cut_capacity x X hx

lemma cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x := by
  rw [cut_capacity]
  apply tsum_le_of_sum_le'
  · rw [tail_majorant]
    apply tsum_nonneg
    intro n
    split_ifs with hn
    · apply mul_nonneg
      · positivity
      · rw [mangoldt_tail_sum]
        apply tsum_nonneg
        intro q
        split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    · norm_num
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let ns : Finset ℕ := (Finset.range ⌈x⌉₊).filter (fun n => 1 ≤ n ∧ (n : ℝ) < x)
    let qs : Finset ℕ := Finset.range M
    let pairs : Finset (ℕ × ℕ) := ns.product qs
    let pairTerm : ℕ × ℕ → ℝ := fun p =>
      (1 / (p.1 : ℝ)) *
        (if max (2 : ℝ) (x / (p.1 : ℝ)) ≤ (p.2 : ℝ) then
          mangoldt_tail_term p.1 p.2 else 0)
    have hpair_nonneg : ∀ p, 0 ≤ pairTerm p := by
      intro p
      simp only [pairTerm]
      apply mul_nonneg
      · positivity
      · split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    have hD_sum (r : ℕ) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            (∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q := by
      rw [Finset.mul_sum]
      simpa [mul_ite] using
        (Finset.sum_filter (s := r.divisors)
          (p := fun q : ℕ => ((r / q : ℕ) : ℝ) < x)
          (f := fun q : ℕ =>
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q)).symm
    have hterm (r q : ℕ) (hrx : x ≤ (r : ℝ))
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            ArithmeticFunction.vonMangoldt q = pairTerm (r / q, q) := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hcast : (((r / q) * q : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hprod
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hqtwo : (2 : ℝ) ≤ (q : ℝ) := by
        by_contra hnot
        have hq_lt_two : q < 2 := by exact_mod_cast lt_of_not_ge hnot
        have hq_le_one : q ≤ 1 := Nat.lt_succ_iff.mp hq_lt_two
        have hq_eq_one : q = 1 := Nat.le_antisymm hq_le_one hqpos
        have hr_eq : r / q = r := by simp [hq_eq_one]
        rw [hr_eq] at hnlt
        linarith
      have hxdiv : x / ((r / q : ℕ) : ℝ) ≤ (q : ℝ) := by
        have hnpos_real : 0 < ((r / q : ℕ) : ℝ) := by exact_mod_cast hnpos
        rw [div_le_iff₀ hnpos_real]
        calc
          x ≤ (r : ℝ) := hrx
          _ = (q : ℝ) * ((r / q : ℕ) : ℝ) := by
            rw [← hcast]
            simp [Nat.cast_mul, mul_comm]
      have hthresh : max (2 : ℝ) (x / ((r / q : ℕ) : ℝ)) ≤ (q : ℝ) :=
        max_le hqtwo hxdiv
      simp only [pairTerm]
      rw [if_pos hthresh, mangoldt_tail_term]
      rw [← hcast]
      simp only [Nat.cast_mul]
      ring_nf
    have hmem_pair (r q : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (r / q, q) ∈ pairs := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hnone : 1 ≤ r / q := Nat.succ_le_of_lt hnpos
      have hnltceil : r / q < ⌈x⌉₊ := by
        exact_mod_cast (lt_of_lt_of_le hnlt (Nat.le_ceil x))
      have hq_le_X : (q : ℝ) ≤ X := by
        have hqr : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqle
        linarith
      have hq_le_ceil : q ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
      have hq_lt_M : q < M := by
        dsimp [M]
        omega
      simp [pairs, ns, qs, hnltceil, hnone, hnlt, hq_lt_M]
    have hper (r : ℕ) :
        (if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
            ∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
        else 0) ≤
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
      by_cases hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
      · rw [if_pos hr]
        calc
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
              (∑ q ∈ r.divisors,
                if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0)
              = (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  (∑ q ∈ r.divisors,
                    if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
                ring_nf
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  ArithmeticFunction.vonMangoldt q := hD_sum r
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                pairTerm (r / q, q) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact hterm r q hr.1 hq
          _ = ∑ p ∈ (r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)).image
                (fun q => (r / q, q)), pairTerm p := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Prod.ext_iff.mp hab |>.2
          _ ≤ ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
                have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
                have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
                simp [hmem_pair r q hr hq, hprod]
              · intro p _ _
                exact hpair_nonneg p
      · rw [if_neg hr]
        exact Finset.sum_nonneg (fun p _ => hpair_nonneg p)
    have hsum_le :
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0) ≤ ∑ p ∈ pairs, pairTerm p := by
      calc
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0)
            ≤ ∑ i ∈ s, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = i), pairTerm p := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ s), pairTerm p := by
          exact Finset.sum_fiberwise_eq_sum_filter pairs s
            (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
        _ ≤ ∑ p ∈ pairs, pairTerm p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact (Finset.mem_filter.mp hp).1
          · intro p _ _
            exact hpair_nonneg p
    have htail_eq : tail_majorant x =
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0 := by
      rw [tail_majorant]
      exact tsum_eq_sum (s := ns) (fun n hn => by
        split_ifs with h
        · exfalso
          apply hn
          exact Finset.mem_filter.mpr
            ⟨by
              have hltceil : n < ⌈x⌉₊ := by
                exact_mod_cast (lt_of_lt_of_le h.2 (Nat.le_ceil x))
              simpa using hltceil, h⟩
        · rfl)
    have hfinite_tail_le : (∑ p ∈ pairs, pairTerm p) ≤ tail_majorant x := by
      rw [htail_eq]
      change (∑ p ∈ ns ×ˢ qs, pairTerm p) ≤
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0
      rw [Finset.sum_product]
      apply Finset.sum_le_sum
      intro n hn
      have hnmem : n < ⌈x⌉₊ ∧ 1 ≤ n ∧ (n : ℝ) < x := by simpa [ns] using hn
      have hnprop : 1 ≤ n ∧ (n : ℝ) < x := hnmem.2
      rw [if_pos hnprop]
      simp only [pairTerm]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mangoldt_tail_finite_sum_le n hnprop.1 (max (2 : ℝ) (x / (n : ℝ)))
          (le_max_left _ _) qs) (by positivity)
    exact hsum_le.trans hfinite_tail_le

lemma tail_majorant_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x -> tail_majorant x ≤ 1 + C / Real.log x := by
  classical
  obtain ⟨D, hD_nonneg, hD_bound⟩ := mangoldt_tail_upper_bound
  let K : ℝ := 1 + Real.log (2 : ℝ)
  let C : ℝ := K + D + K * D / Real.log (2 : ℝ)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx
  let N : ℕ := ⌈x⌉₊
  let L : ℝ := Real.log x
  let A : ℝ := 1 / L + D / L ^ 2
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hlog2_le_L : Real.log (2 : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hx
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfinite : tail_majorant x =
      ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := by
    unfold tail_majorant
    dsimp [N]
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (s := Finset.range ⌈x⌉₊)
      (f := fun n : ℕ =>
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0) ?_
    intro n hn
    have hn_not_lt_x : ¬ (n : ℝ) < x := by
      intro hnx
      have hn_lt_ceil : n < ⌈x⌉₊ := by
        by_contra hnot
        have hceil_le_n : ⌈x⌉₊ ≤ n := le_of_not_gt hnot
        have hx_le_n : x ≤ (n : ℝ) := by
          exact (Nat.le_ceil x).trans (Nat.cast_le.mpr hceil_le_n)
        exact (not_lt_of_ge hx_le_n) hnx
      exact hn (Finset.mem_range.mpr hn_lt_ceil)
    simp [hn_not_lt_x]
  have hterm_le : ∀ n : ℕ,
      (if 1 ≤ n ∧ (n : ℝ) < x then
        (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
      else 0) ≤
      (if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) := by
    intro n
    by_cases hn : 1 ≤ n ∧ (n : ℝ) < x
    · have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn.1
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      let y : ℝ := max (2 : ℝ) (x / (n : ℝ))
      have hy : 2 ≤ y := by
        dsimp [y]
        exact le_max_left _ _
      have hxy : x ≤ (n : ℝ) * y := by
        have hdiv_le : x / (n : ℝ) ≤ y := by
          dsimp [y]
          exact le_max_right _ _
        calc
          x = (n : ℝ) * (x / (n : ℝ)) := by
            field_simp [hn_pos.ne']
          _ ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hn_pos)
      have hlog_ge : L ≤ Real.log ((n : ℝ) * y) := by
        dsimp [L]
        exact Real.log_le_log hx_pos hxy
      have hlog_pos : 0 < Real.log ((n : ℝ) * y) := hL_pos.trans_le hlog_ge
      have htail := (hD_bound n hn.1 y hy).2
      have hone : 1 / Real.log ((n : ℝ) * y) ≤ 1 / L := by
        exact one_div_le_one_div_of_le hL_pos hlog_ge
      have hsquare : D / (Real.log ((n : ℝ) * y)) ^ 2 ≤ D / L ^ 2 := by
        have hsquares : L ^ 2 ≤ (Real.log ((n : ℝ) * y)) ^ 2 := by
          nlinarith [hlog_ge, le_of_lt hL_pos, le_of_lt hlog_pos]
        exact div_le_div_of_nonneg_left hD_nonneg (sq_pos_of_pos hL_pos) hsquares
      have htail_A : mangoldt_tail_sum n y ≤ A := by
        calc
          mangoldt_tail_sum n y ≤
              1 / Real.log ((n : ℝ) * y) + D / (Real.log ((n : ℝ) * y)) ^ 2 := htail
          _ ≤ 1 / L + D / L ^ 2 := add_le_add hone hsquare
          _ = A := by rfl
      have hmul := mul_le_mul_of_nonneg_left htail_A (by positivity : 0 ≤ 1 / (n : ℝ))
      simpa [hn, y, A] using hmul
    · simp [hn]
  have hsum_A :
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) ≤
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
    calc
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) =
          ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) < x),
            (1 / (n : ℝ)) * A := by
            rw [Finset.sum_filter]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          exact Finset.mem_Icc.mpr ⟨hn.2.1, Nat.le_of_lt hn.1⟩
        · intro n hnI hnnot
          positivity
  have hrecip_eq_harm :
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) = (harmonic N : ℝ) := by
    simp [one_div, harmonic_eq_sum_Icc]
  have htail_le_HA : tail_majorant x ≤ (harmonic N : ℝ) * A := by
    calc
      tail_majorant x = ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := hfinite
      _ ≤ ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0 := by
          exact Finset.sum_le_sum (by intro n hn; exact hterm_le n)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := hsum_A
      _ = (harmonic N : ℝ) * A := by
        rw [← Finset.sum_mul, hrecip_eq_harm]
  have hN_lt_add_one : (N : ℝ) < x + 1 := by
    dsimp [N]
    exact Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  have hN_le_two_x : (N : ℝ) ≤ 2 * x := by
    nlinarith [hN_lt_add_one, hx]
  have hN_pos : 0 < (N : ℝ) := by
    have hx_le_N : x ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil x
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log (2 : ℝ) + L := by
    have hlog_le := Real.log_le_log hN_pos hN_le_two_x
    have hlog_mul : Real.log (2 * x) = Real.log (2 : ℝ) + Real.log x := by
      rw [Real.log_mul] <;> positivity
    simpa [L, hlog_mul] using hlog_le
  have hH_le : (harmonic N : ℝ) ≤ L + K := by
    have hh := harmonic_le_one_add_log N
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := hh
      _ ≤ 1 + (Real.log (2 : ℝ) + L) := by linarith
      _ = L + K := by
        dsimp [K]
        ring
  have htail_le_main : tail_majorant x ≤ (L + K) * A :=
    le_trans htail_le_HA (mul_le_mul_of_nonneg_right hH_le hA_nonneg)
  have halg : (L + K) * A ≤ 1 + C / L := by
    have hKD_nonneg : 0 ≤ K * D := by positivity
    have hKD_div : K * D / L ≤ K * D / Real.log (2 : ℝ) := by
      exact div_le_div_of_nonneg_left hKD_nonneg hlog2_pos hlog2_le_L
    have hKD_sq : K * D / L ^ 2 ≤ (K * D / Real.log (2 : ℝ)) / L := by
      calc
        K * D / L ^ 2 = (K * D / L) / L := by
          field_simp [hL_pos.ne']
        _ ≤ (K * D / Real.log (2 : ℝ)) / L :=
          div_le_div_of_nonneg_right hKD_div (le_of_lt hL_pos)
    have hdecomp : (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := by
      dsimp [A]
      field_simp [hL_pos.ne']
      ring
    have htarget : 1 + (K + D) / L + K * D / L ^ 2 ≤
        1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := by
      linarith
    have hcombine : 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L =
        1 + C / L := by
      dsimp [C]
      field_simp [hL_pos.ne']
      ring
    calc
      (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := hdecomp
      _ ≤ 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := htarget
      _ = 1 + C / L := hcombine
  exact le_trans htail_le_main halg

lemma finite_large_primitive_bound :
    ∃ C : ℝ, erdos1196_finite_bound C := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ := tail_majorant_bound
  refine ⟨C, ⟨hC_nonneg, ?_⟩⟩
  intro x X hx _ A hprim hsupp
  calc
    erdos_sum A ≤ cut_capacity x X := finite_chain_cut_bound A x X hx hprim hsupp
    _ ≤ tail_majorant x := cut_capacity_le_tail_majorant x X hx
    _ ≤ 1 + C / Real.log x := hC_bound x hx

lemma finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C := by
  rintro ⟨C, hC⟩
  refine ⟨C, ⟨hC.nonneg, ?_⟩⟩
  intro x hx A hprim hsupp
  have hnonneg : ∀ n : ℕ, 0 ≤ A.indicator erdos_weight n := by
    intro n
    by_cases hnA : n ∈ A
    · rw [Set.indicator_of_mem hnA]
      rw [erdos_weight]
      have hn_two : (2 : ℝ) ≤ (n : ℝ) := le_trans hx (hsupp n hnA)
      have hn_one : (1 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hn_two
      exact div_nonneg zero_le_one
        (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn_one))
    · rw [Set.indicator_of_notMem hnA]
  have hpartial_bound : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, A.indicator erdos_weight i) ≤
        1 + C / Real.log x := by
    intro N
    let B : Set ℕ := A ∩ {n : ℕ | n < N}
    have hprimB : primitive_set B := by
      rw [primitive_set] at hprim ⊢
      exact hprim.subset (by intro n hn; exact hn.1)
    have hsuppB : supported_in_interval B x (max x (N : ℝ)) := by
      intro n hn
      refine ⟨hsupp n hn.1, ?_⟩
      exact le_trans (by exact_mod_cast Nat.le_of_lt hn.2) (le_max_right x (N : ℝ))
    have htsumB : erdos_sum B = ∑ i ∈ Finset.range N, B.indicator erdos_weight i := by
      rw [erdos_sum]
      exact tsum_eq_sum (s := Finset.range N) (fun n hn => by
        have hnB : n ∉ B := by
          intro h
          exact hn (Finset.mem_range.mpr h.2)
        simp [Set.indicator_of_notMem hnB])
    have hsum_eq :
        (∑ i ∈ Finset.range N, A.indicator erdos_weight i) = erdos_sum B := by
      rw [htsumB]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      by_cases hiA : i ∈ A
      · have hiB : i ∈ B := ⟨hiA, hi_lt⟩
        simp [Set.indicator_of_mem hiA, Set.indicator_of_mem hiB]
      · have hiB : i ∉ B := by
          intro h
          exact hiA h.1
        simp [Set.indicator_of_notMem hiA, Set.indicator_of_notMem hiB]
    calc
      (∑ i ∈ Finset.range N, A.indicator erdos_weight i) = erdos_sum B := hsum_eq
      _ ≤ 1 + C / Real.log x :=
          hC.bound x (max x (N : ℝ)) hx (le_max_left x (N : ℝ)) B hprimB hsuppB
  have hsumm : Summable (fun n : ℕ => A.indicator erdos_weight n) :=
    summable_of_sum_range_le hnonneg hpartial_bound
  refine ⟨hsumm, ?_⟩
  simpa [erdos_sum] using hsumm.tsum_le_of_sum_range_le hpartial_bound

theorem erdos_sarkozy_szemeredi_1196 :
    ∃ C : ℝ, erdos1196_bound C :=
  finite_truncation_principle finite_large_primitive_bound

def prime_layer : Set ℕ :=
  {n : ℕ | Nat.Prime n}

noncomputable def modified_prime_power_redirected_finite (p : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ k ∈ s, if 2 ≤ k then 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0

noncomputable def modified_prime_power_redirected_sum (p : ℕ) : ℝ :=
  ∑' k : ℕ, if 2 ≤ k then 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0

lemma mangoldt_dirichlet_series_finite_threshold_geometric_bound_local :
    ∀ u : ℝ, 0 < u -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
  intro u hu N
  have hsumm := mangoldt_dirichlet_series_summable_local u hu
  have hnonneg : ∀ q : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
    intro q
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg q) (1 + u))
  have hseries :
      mangoldt_dirichlet_series u =
        ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
    simpa using congrArg Complex.re
      (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu)
  calc
    (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤
        ∑ q ∈ Finset.range N,
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      split_ifs
      · rfl
      · exact hnonneg q
    _ ≤ mangoldt_dirichlet_series u := by
      simpa [mangoldt_dirichlet_series] using
        hsumm.sum_le_tsum (Finset.range N) (fun q _ => hnonneg q)
    _ = ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := hseries
    _ ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
      zeta_log_derivative_geometric_bound u hu

lemma two_power_kernel_midpoint_bound_local (t : ℝ) (ht : 0 < t) :
    t * Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) t - 1) ≤
      Real.rpow (2 : ℝ) (-(t / 2)) := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let s : ℝ := Real.log (2 : ℝ) * t
  have hs_pos : 0 < s := by
    exact mul_pos hlog2_pos ht
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hden_pos : 0 < Real.rpow (2 : ℝ) t - 1 := by
    have hpow_gt_one : 1 < Real.rpow (2 : ℝ) t := by
      exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
        (Or.inl ⟨by norm_num, ht⟩)
    linarith
  have hs_le_exp : s ≤ Real.exp (s / 2) - Real.exp (-(s / 2)) := by
    have hhalf_nonneg : 0 ≤ s / 2 := by positivity
    have hsinh : s / 2 ≤ Real.sinh (s / 2) :=
      (Real.self_le_sinh_iff).2 hhalf_nonneg
    have hmul : 2 * (s / 2) ≤ 2 * Real.sinh (s / 2) := by
      exact mul_le_mul_of_nonneg_left hsinh (by norm_num)
    rw [Real.sinh_eq] at hmul
    linarith
  have hprod :
      Real.rpow (2 : ℝ) (-(t / 2)) * (Real.rpow (2 : ℝ) t - 1) =
        Real.exp (s / 2) - Real.exp (-(s / 2)) := by
    have hpow_t : Real.rpow (2 : ℝ) t = Real.exp s := by
      dsimp [s]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) t]
    have hpow_half : Real.rpow (2 : ℝ) (-(t / 2)) = Real.exp (-(s / 2)) := by
      dsimp [s]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-(t / 2))]
      ring_nf
    rw [hpow_t, hpow_half]
    calc
      Real.exp (-(s / 2)) * (Real.exp s - 1) =
          Real.exp (-(s / 2)) * Real.exp s - Real.exp (-(s / 2)) := by ring
      _ = Real.exp (s / 2) - Real.exp (-(s / 2)) := by
        rw [← Real.exp_add]
        ring_nf
  rw [div_le_iff₀ hden_pos]
  calc
    t * Real.log (2 : ℝ) = s := by
      dsimp [s]
      ring
    _ ≤ Real.exp (s / 2) - Real.exp (-(s / 2)) := hs_le_exp
    _ = Real.rpow (2 : ℝ) (-(t / 2)) * (Real.rpow (2 : ℝ) t - 1) := hprod.symm

lemma mangoldt_tail_prime_range_slack_local (p N : ℕ) (hp : 2 ≤ p) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) ≤
      1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := by
  have hm : 1 ≤ p := by omega
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hp)
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden_pos : 0 < Real.log (p : ℝ) + Real.log (2 : ℝ) / 2 := by positivity
  let F : ℝ → ℝ := fun t =>
    ∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((p * q : ℕ) : ℝ)) (-t))
      else 0
  have hterm_int : ∀ q ∈ Finset.range N,
      MeasureTheory.Integrable
        (fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((p * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro q hq
    by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
    · have hq_nat : 2 ≤ q := by
        exact_mod_cast hqcond
      have hpq_two : 2 ≤ p * q := Nat.mul_le_mul hm hq_nat
      have hpq_pos : 0 < (((p * q : ℕ) : ℝ)) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hpq_two)
      have hlog_pq_pos : 0 < Real.log (((p * q : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hpq_two)
      have hbase_int : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.rpow (((p * q : ℕ) : ℝ)) (-t))
          (Set.Ioi 0) := by
        have h := log_square_integral_kernel_integrable_local
          (Real.log (((p * q : ℕ) : ℝ))) hlog_pq_pos
        have hfun : (fun t : ℝ => t * Real.rpow (((p * q : ℕ) : ℝ)) (-t)) =
            fun t : ℝ => t * Real.exp (-(Real.log (((p * q : ℕ) : ℝ)) * t)) := by
          funext t
          change t * (((p * q : ℕ) : ℝ) ^ (-t)) =
            t * Real.exp (-(Real.log (((p * q : ℕ) : ℝ)) * t))
          rw [Real.rpow_def_of_pos hpq_pos]
          ring_nf
        rw [hfun]
        exact h
      simpa [hqcond] using
        hbase_int.const_mul (ArithmeticFunction.vonMangoldt q / (q : ℝ))
    · simp [hqcond]
  have hF_int : MeasureTheory.IntegrableOn F (Set.Ioi 0) := by
    have hF_int' : MeasureTheory.Integrable
        (∑ q ∈ Finset.range N, fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((p * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      MeasureTheory.integrable_finsetSum' (Finset.range N) hterm_int
    dsimp [F, MeasureTheory.IntegrableOn]
    convert hF_int' using 1
    funext t
    simp [Finset.sum_apply]
  have hG_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t)))
      (Set.Ioi 0) := by
    have hrate : -(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) < 0 := by linarith
    convert integrableOn_exp_mul_Ioi hrate 0 using 1
    funext t
    ring_nf
  have hsum_integral :
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := by
    calc
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) =
          ∑ q ∈ Finset.range N,
            ∫ t : ℝ in Set.Ioi 0,
              if (2 : ℝ) ≤ (q : ℝ) then
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (t * Real.rpow (((p * q : ℕ) : ℝ)) (-t))
              else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
        · have hq_nat : 2 ≤ q := by
            exact_mod_cast hqcond
          simp [hqcond, mangoldt_tail_term_integral_local p q hm hq_nat]
        · simp [hqcond]
      _ = ∫ t : ℝ in Set.Ioi 0, F t := by
        symm
        dsimp [F]
        exact MeasureTheory.integral_finsetSum (Finset.range N) hterm_int
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      F t ≤ Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t)) := by
    intro t ht
    have htpos : 0 < t := ht
    have hdir := mangoldt_dirichlet_series_finite_threshold_geometric_bound_local t htpos N
    have hp_rpow_nonneg : 0 ≤ Real.rpow (p : ℝ) (-t) :=
      Real.rpow_nonneg hp_pos.le (-t)
    have hcoef_nonneg : 0 ≤ t * Real.rpow (p : ℝ) (-t) := by positivity
    calc
      F t = t * Real.rpow (p : ℝ) (-t) *
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
            else 0) := by
        simpa [F] using mangoldt_tail_integrand_factor_local p N t hp
      _ ≤ t * Real.rpow (p : ℝ) (-t) *
          (Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) t - 1)) := by
        exact mul_le_mul_of_nonneg_left hdir hcoef_nonneg
      _ = Real.rpow (p : ℝ) (-t) *
          (t * Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) t - 1)) := by ring
      _ ≤ Real.rpow (p : ℝ) (-t) * Real.rpow (2 : ℝ) (-(t / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (two_power_kernel_midpoint_bound_local t htpos) hp_rpow_nonneg
      _ = Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t)) := by
        have hpow_p : Real.rpow (p : ℝ) (-t) =
            Real.exp (-(Real.log (p : ℝ) * t)) := by
          change ((p : ℝ) ^ (-t)) = Real.exp (-(Real.log (p : ℝ) * t))
          rw [Real.rpow_def_of_pos hp_pos]
          ring_nf
        have hpow_2 : Real.rpow (2 : ℝ) (-(t / 2)) =
            Real.exp (-(Real.log (2 : ℝ) / 2 * t)) := by
          change ((2 : ℝ) ^ (-(t / 2))) = Real.exp (-(Real.log (2 : ℝ) / 2 * t))
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-(t / 2))]
          ring_nf
        rw [hpow_p, hpow_2]
        rw [← Real.exp_add]
        ring_nf
  have hintegral_le :
      (∫ t : ℝ in Set.Ioi 0, F t) ≤
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t)) := by
    exact MeasureTheory.setIntegral_mono_on hF_int hG_int measurableSet_Ioi hpoint
  have hG_integral :
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t))) =
        1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := by
    have hrate : -(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) < 0 := by linarith
    have h := integral_exp_mul_Ioi
      (a := -(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2)) hrate 0
    have hfun :
        (fun t : ℝ => Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t))) =
          fun t : ℝ => Real.exp ((-(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2)) * t) := by
      funext t
      ring_nf
    rw [hfun]
    calc
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp ((-(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2)) * t)) =
          -1 / (-(Real.log (p : ℝ) + Real.log (2 : ℝ) / 2)) := by
        simpa using h
      _ = 1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := by
        field_simp [hden_pos.ne']
  calc
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := hsum_integral
    _ ≤ ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-((Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) * t)) := hintegral_le
    _ = 1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := hG_integral

lemma mangoldt_tail_sharp_prime_slack :
    ∀ p : ℕ, p ∈ prime_layer ->
      Real.log (p : ℝ) * mangoldt_tail_sum p 2 ≤
        (Real.log (p : ℝ) / Real.log 2) /
          (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ)) := by
  intro p hp
  have hp_prime : Nat.Prime p := by
    simpa [prime_layer] using hp
  have hp_two : 2 ≤ p := hp_prime.two_le
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp_two)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden_pos : 0 < Real.log (p : ℝ) + Real.log (2 : ℝ) / 2 := by positivity
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hbound : ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) ≤
        1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := by
    intro N
    exact mangoldt_tail_prime_range_slack_local p N hp_two
  have hsumm : Summable (fun q : ℕ =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) :=
    summable_of_sum_range_le hnonneg hbound
  have htail : mangoldt_tail_sum p 2 ≤
      1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2) := by
    simpa [mangoldt_tail_sum] using hsumm.tsum_le_of_sum_range_le hbound
  calc
    Real.log (p : ℝ) * mangoldt_tail_sum p 2 ≤
        Real.log (p : ℝ) *
          (1 / (Real.log (p : ℝ) + Real.log (2 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left htail hlogp_pos.le
    _ = (Real.log (p : ℝ) / Real.log 2) /
          (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ)) := by
      field_simp [hlog2_pos.ne', hden_pos.ne']

lemma modified_prime_power_redirected_bound :
    ∀ p : ℕ, p ∈ prime_layer ->
      modified_prime_power_redirected_sum p ≤
          1 - (Real.log (p : ℝ) / Real.log 2) /
            (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ)) ∧
      ∀ s : Finset ℕ,
        modified_prime_power_redirected_finite p s ≤
          1 - (Real.log (p : ℝ) / Real.log 2) /
            (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ)) := by
  intro p hp
  have hpprime : Nat.Prime p := by simpa [prime_layer] using hp
  let x : ℝ := Real.log (p : ℝ) / Real.log 2
  let a : ℝ := 1 / (2 * (p : ℝ))
  have hp_two_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hp_pos_real : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
  have hpoint : ∀ k : ℕ,
      (if 2 ≤ k then 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0) ≤
        if 2 ≤ k then a / 2 / (2 : ℝ) ^ (k - 2) else 0 := by
    intro k
    by_cases hk : 2 ≤ k
    · rw [if_pos hk, if_pos hk]
      have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk_sq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have hpow_le : (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ (k - 2) := by
        exact pow_le_pow_left₀ (by norm_num) hp_two_real (k - 2)
      have hppow : (p : ℝ) * (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ (k - 1) := by
        calc
          (p : ℝ) * (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) * (p : ℝ) ^ (k - 2) := by
            exact mul_le_mul_of_nonneg_left hpow_le hp_pos_real.le
          _ = (p : ℝ) ^ (k - 1) := by
            have hkpred : k - 1 = (k - 2) + 1 := by omega
            rw [hkpred, pow_succ]
            ring
      have hden0 : (4 : ℝ) * ((p : ℝ) * (2 : ℝ) ^ (k - 2)) ≤
          ((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)) := by
        exact mul_le_mul hk_sq hppow
          (mul_nonneg hp_pos_real.le (pow_nonneg (by norm_num) _))
          (sq_nonneg (k : ℝ))
      have hden_le : ((4 : ℝ) * (p : ℝ)) * (2 : ℝ) ^ (k - 2) ≤
          ((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)) := by
        nlinarith [hden0]
      calc
        1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) ≤
            1 / (((4 : ℝ) * (p : ℝ)) * (2 : ℝ) ^ (k - 2)) :=
          one_div_le_one_div_of_le (by positivity) hden_le
        _ = a / 2 / (2 : ℝ) ^ (k - 2) := by
          dsimp [a]
          ring_nf
    · rw [if_neg hk, if_neg hk]
  have hsumm : Summable (fun n : ℕ => a / 2 / (2 : ℝ) ^ n) :=
    summable_geometric_two' a
  have htsum : (∑' n : ℕ, a / 2 / (2 : ℝ) ^ n) = a :=
    tsum_geometric_two' a
  have hfinite_binary : ∀ s : Finset ℕ, modified_prime_power_redirected_finite p s ≤ a := by
    intro s
    have himage :
        (∑ j ∈ (s.filter (fun k => 2 ≤ k)).image (fun k => k - 2),
          a / 2 / (2 : ℝ) ^ j) =
            ∑ k ∈ s.filter (fun k => 2 ≤ k), a / 2 / (2 : ℝ) ^ (k - 2) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      simp at hx hy
      change x - 2 = y - 2 at hxy
      omega
    calc
      modified_prime_power_redirected_finite p s =
          ∑ k ∈ s, if 2 ≤ k then
            1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0 := by
        rfl
      _ ≤ ∑ k ∈ s, if 2 ≤ k then a / 2 / (2 : ℝ) ^ (k - 2) else 0 := by
        apply Finset.sum_le_sum
        intro k _
        exact hpoint k
      _ = ∑ k ∈ s.filter (fun k => 2 ≤ k), a / 2 / (2 : ℝ) ^ (k - 2) := by
        rw [← Finset.sum_filter]
      _ = ∑ j ∈ (s.filter (fun k => 2 ≤ k)).image (fun k => k - 2),
            a / 2 / (2 : ℝ) ^ j := himage.symm
      _ ≤ ∑' j : ℕ, a / 2 / (2 : ℝ) ^ j := by
        exact hsumm.sum_le_tsum _ (fun _ _ => by dsimp [a]; positivity)
      _ = a := htsum
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpprime.one_le)) hlog2_pos.le
  have hpred_lt : p - 1 < 2 ^ (p - 1) := Nat.lt_two_pow_self
  have hpow_nat : p ≤ 2 ^ (p - 1) := by
    have hp_pos_nat : 0 < p := hpprime.pos
    omega
  have hpow_real : (p : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by exact_mod_cast hpow_nat
  have hlog_le_pow : Real.log (p : ℝ) ≤ Real.log ((2 : ℝ) ^ (p - 1)) :=
    Real.log_le_log hp_pos_real hpow_real
  have hlog_le : Real.log (p : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * Real.log 2 := by
    simpa [Real.log_pow] using hlog_le_pow
  have hx_le_pred : x ≤ ((p - 1 : ℕ) : ℝ) := by
    dsimp [x]
    rw [div_le_iff₀ hlog2_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlog_le
  have hpred_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by exact hpprime.one_le : 1 ≤ p)]
  have hden_pos : 0 < x + 1 / 2 := by nlinarith
  have hden_le_p : x + 1 / 2 ≤ (p : ℝ) := by
    have hx_le_pminus : x ≤ (p : ℝ) - 1 := by simpa [hpred_cast] using hx_le_pred
    nlinarith
  have ha_le_slack : a ≤ 1 - x / (x + 1 / 2) := by
    have hrecip : 1 / (p : ℝ) ≤ 1 / (x + 1 / 2) :=
      one_div_le_one_div_of_le hden_pos hden_le_p
    calc
      a = (1 / 2 : ℝ) * (1 / (p : ℝ)) := by
        dsimp [a]
        ring
      _ ≤ (1 / 2 : ℝ) * (1 / (x + 1 / 2)) := by
        exact mul_le_mul_of_nonneg_left hrecip (by norm_num)
      _ = 1 - x / (x + 1 / 2) := by
        field_simp [hden_pos.ne']
        ring
  have hslack_nonneg : 0 ≤ 1 - x / (x + 1 / 2) := by
    exact (show 0 ≤ a by dsimp [a]; positivity).trans ha_le_slack
  have hfinite_slack : ∀ s : Finset ℕ,
      modified_prime_power_redirected_finite p s ≤ 1 - x / (x + 1 / 2) := by
    intro s
    exact (hfinite_binary s).trans ha_le_slack
  constructor
  · rw [modified_prime_power_redirected_sum]
    apply tsum_le_of_sum_le'
    · change 0 ≤ 1 - x / (x + 1 / 2)
      exact hslack_nonneg
    · intro s
      change (∑ k ∈ s, if 2 ≤ k then
          1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0) ≤ 1 - x / (x + 1 / 2)
      simpa [modified_prime_power_redirected_finite] using (hfinite_slack s)
  · intro s
    change modified_prime_power_redirected_finite p s ≤ 1 - x / (x + 1 / 2)
    exact hfinite_slack s

lemma modified_prime_power_incoming_bound :
    ∀ p : ℕ, p ∈ prime_layer ->
      Real.log (p : ℝ) * mangoldt_tail_sum p 2 +
          modified_prime_power_redirected_sum p ≤ 1 ∧
      ∀ s t : Finset ℕ,
        Real.log (p : ℝ) *
            (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
          modified_prime_power_redirected_finite p t ≤ 1 := by
  intro p hp
  have hp_prime : Nat.Prime p := by
    simpa [prime_layer] using hp
  have hp_two : 2 ≤ p := hp_prime.two_le
  have hp_one : 1 ≤ p := by
    exact le_trans (by norm_num : (1 : ℕ) ≤ 2) hp_two
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp_two)
  have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := le_of_lt hlogp_pos
  have htail := mangoldt_tail_sharp_prime_slack p hp
  rcases modified_prime_power_redirected_bound p hp with
    ⟨hredirected, hredirected_finite⟩
  constructor
  · linarith
  · intro s t
    have hfinite_tail :
        (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) ≤
          mangoldt_tail_sum p 2 := by
      exact mangoldt_tail_finite_sum_le p hp_one 2 (by norm_num) s
    have hfinite_tail_scaled :
        Real.log (p : ℝ) *
            (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) ≤
          Real.log (p : ℝ) * mangoldt_tail_sum p 2 := by
      exact mul_le_mul_of_nonneg_left hfinite_tail hlogp_nonneg
    have hredirected_t := hredirected_finite t
    linarith

lemma eps_modified_chain_prime_power_incoming_reindex (P : ℕ → ℕ → ℝ) :
    (∀ n q : ℕ, 2 ≤ n -> n ∉ prime_layer ->
      (∀ r k : ℕ, r ∈ prime_layer -> 2 ≤ k -> n ≠ r ^ k) ->
      1 < q -> q ∣ n ->
        P n (n / q) = ArithmeticFunction.vonMangoldt q / Real.log (n : ℝ)) ->
    (∀ r k : ℕ, r ∈ prime_layer -> 2 ≤ k ->
      P (r ^ k) r =
        ArithmeticFunction.vonMangoldt (r ^ (k - 1)) /
          Real.log ((r ^ k : ℕ) : ℝ) + 1 / (k : ℝ)) ->
    (∀ r k m : ℕ, r ∈ prime_layer -> 2 ≤ k -> P (r ^ k) m ≠ 0 ->
      m = r ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = r ^ (k - j)) ->
    ∀ p : ℕ, p ∈ prime_layer ->
      (∑' q : ℕ, if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
          erdos_weight p *
            (Real.log (p : ℝ) * mangoldt_tail_sum p 2 +
              modified_prime_power_redirected_sum p) ∧
        ∀ s : Finset ℕ,
          ∃ t : Finset ℕ,
            (∑ q ∈ s,
              if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
                erdos_weight p *
                  (Real.log (p : ℝ) *
                      (∑ q ∈ s,
                        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
                    modified_prime_power_redirected_finite p t) := by
  intro hordinary hbase hsupport p hp
  classical
  have hfinite : ∀ s : Finset ℕ,
      ∃ t : Finset ℕ,
        (∑ q ∈ s,
          if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
            erdos_weight p *
              (Real.log (p : ℝ) *
                  (∑ q ∈ s,
                    if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
                modified_prime_power_redirected_finite p t) := by
    intro s
    let t : Finset ℕ := Finset.range ((∑ q ∈ s, q) + 1)
    refine ⟨t, ?_⟩
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hp_two : 2 ≤ p := hp_prime.two_le
    have hp_one : 1 ≤ p := by omega
    have hlogp_pos : 0 < Real.log (p : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp_two)
    have hweight_nonneg : 0 ≤ erdos_weight p := by
      rw [erdos_weight]
      positivity
    have hp_real_ne : (p : ℝ) ≠ 0 := by positivity
    have hweight_mul : (p : ℝ) * Real.log (p : ℝ) * erdos_weight p = 1 := by
      rw [erdos_weight]
      field_simp [hlogp_pos.ne', hp_real_ne]
    let ordinaryTerm : ℕ → ℝ := fun q =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0
    let redirectedTerm : ℕ → ℝ := fun q =>
      ∑ k ∈ t,
        if q = p ^ (k - 1) ∧ 2 ≤ k then
          1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)))
        else 0
    have hpoint : ∀ q ∈ s,
        (if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
          erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q + redirectedTerm q) := by
      intro q hqmem
      have hordinary_nonneg : 0 ≤ ordinaryTerm q := by
        dsimp [ordinaryTerm]
        split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
      have hredirected_nonneg : 0 ≤ redirectedTerm q := by
        dsimp [redirectedTerm]
        apply Finset.sum_nonneg
        intro k hk
        split_ifs
        · positivity
        · norm_num
      by_cases hqone : 1 < q
      · rw [if_pos hqone]
        by_cases hqpow : ∃ k : ℕ, 2 ≤ k ∧ q = p ^ (k - 1)
        · rcases hqpow with ⟨k, hk, hqpow⟩
          have hk_le_q : k ≤ q := by
            have htwo_pow_le : 2 ^ (k - 1) ≤ p ^ (k - 1) := by
              exact Nat.pow_le_pow_left hp_two (k - 1)
            have hkpred_lt : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
            have hkpred_lt_q : k - 1 < q := by
              exact lt_of_lt_of_le hkpred_lt (by simpa [hqpow] using htwo_pow_le)
            omega
          have hq_le_sum : q ≤ ∑ x ∈ s, x := by
            exact Finset.single_le_sum (fun x _ => Nat.zero_le x) hqmem
          have hk_mem_t : k ∈ t := by
            dsimp [t]
            simp [le_trans hk_le_q hq_le_sum]
          have hredirected_ge :
              1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) ≤ redirectedTerm q := by
            dsimp [redirectedTerm]
            have hnonneg : ∀ k' ∈ t,
                0 ≤ if q = p ^ (k' - 1) ∧ 2 ≤ k' then
                  1 / (((k' : ℝ) ^ 2) * ((p : ℝ) ^ (k' - 1)))
                else 0 := by
              intro k' hk'
              split_ifs
              · positivity
              · norm_num
            have hsingle := Finset.single_le_sum hnonneg hk_mem_t
            simpa [hqpow, hk] using hsingle
          have hterm_eq :
              erdos_weight (p * q) * P (p * q) p =
                erdos_weight p *
                  (Real.log (p : ℝ) * ordinaryTerm q +
                    1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)))) := by
            have hq_two : 2 ≤ q := by omega
            have hq_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_two
            have hk_succ : k = (k - 1) + 1 := by omega
            have hstate : p * q = p ^ k := by
              have hpow : p ^ k = p ^ (k - 1) * p := by
                have hidx : k - 1 + 1 - 1 = k - 1 := by omega
                rw [hk_succ, pow_succ, hidx]
              calc
                p * q = p * p ^ (k - 1) := by rw [hqpow]
                _ = p ^ (k - 1) * p := by rw [mul_comm]
                _ = p ^ k := hpow.symm
            have hPp :
                P (p * q) p =
                  ArithmeticFunction.vonMangoldt q /
                      Real.log ((p * q : ℕ) : ℝ) + 1 / (k : ℝ) := by
              rw [hstate, hqpow]
              exact hbase p k hp hk
            have hlog_pq :
                Real.log ((p * q : ℕ) : ℝ) = (k : ℝ) * Real.log (p : ℝ) := by
              rw [hstate, Nat.cast_pow]
              exact Real.log_pow (p : ℝ) k
            rw [hPp]
            dsimp [ordinaryTerm]
            rw [if_pos hq_two_real]
            rw [erdos_weight, mangoldt_tail_term, hlog_pq, hqpow]
            have hp_real_ne : (p : ℝ) ≠ 0 := by positivity
            have hk_real_ne : (k : ℝ) ≠ 0 := by positivity
            rw [Nat.cast_mul, Nat.cast_pow]
            field_simp [erdos_weight, hlogp_pos.ne', hp_real_ne, hk_real_ne]
            calc
              ArithmeticFunction.vonMangoldt (p ^ (k - 1)) + Real.log (p : ℝ) =
                  (ArithmeticFunction.vonMangoldt (p ^ (k - 1)) + Real.log (p : ℝ)) *
                    ((p : ℝ) * Real.log (p : ℝ) * erdos_weight p) := by
                rw [hweight_mul]
                ring
              _ = (p : ℝ) * Real.log (p : ℝ) *
                    (ArithmeticFunction.vonMangoldt (p ^ (k - 1)) + Real.log (p : ℝ)) *
                    erdos_weight p := by
                ring
          calc
            erdos_weight (p * q) * P (p * q) p =
                erdos_weight p *
                  (Real.log (p : ℝ) * ordinaryTerm q +
                    1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)))) := hterm_eq
            _ ≤ erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q + redirectedTerm q) := by
              apply mul_le_mul_of_nonneg_left
              · nlinarith [hredirected_ge]
              · exact hweight_nonneg
        · have hterm_eq :
              erdos_weight (p * q) * P (p * q) p =
                erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q) := by
            have hq_two : 2 ≤ q := by omega
            have hq_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_two
            have hpq_two : 2 ≤ p * q := Nat.mul_le_mul hp_one hq_two
            have hpq_not_prime : p * q ∉ prime_layer := by
              intro hpq
              exact Nat.not_prime_mul hp_prime.ne_one (ne_of_gt hqone)
                (by simpa [prime_layer] using hpq)
            have hpq_not_pow :
                ∀ r k : ℕ, r ∈ prime_layer -> 2 ≤ k -> p * q ≠ r ^ k := by
              intro r k hr hk hEq
              have hr_prime : Nat.Prime r := by simpa [prime_layer] using hr
              have hp_dvd : p ∣ r ^ k := by
                rw [← hEq]
                exact dvd_mul_right p q
              have hpr : p = r := Nat.prime_eq_prime_of_dvd_pow hp_prime hr_prime hp_dvd
              subst r
              have hk_succ : k = (k - 1) + 1 := by omega
              have hpow_eq : p ^ k = p * p ^ (k - 1) := by
                have hpow : p ^ k = p ^ (k - 1) * p := by
                  have hidx : k - 1 + 1 - 1 = k - 1 := by omega
                  rw [hk_succ, pow_succ, hidx]
                rw [hpow, mul_comm]
              have hq_eq : q = p ^ (k - 1) := by
                have hmul : p * q = p * p ^ (k - 1) := by
                  simpa [hpow_eq] using hEq
                exact Nat.mul_left_cancel hp_prime.pos hmul
              exact hqpow ⟨k, hk, hq_eq⟩
            have hq_dvd : q ∣ p * q := by
              exact ⟨p, by rw [mul_comm]⟩
            have hdiv_eq : (p * q) / q = p := by
              rw [mul_comm]
              exact Nat.mul_div_right p (by omega)
            have hP := hordinary (p * q) q hpq_two hpq_not_prime hpq_not_pow hqone hq_dvd
            have hPp :
                P (p * q) p =
                  ArithmeticFunction.vonMangoldt q / Real.log ((p * q : ℕ) : ℝ) := by
              simpa [hdiv_eq] using hP
            rw [hPp]
            dsimp [ordinaryTerm]
            rw [if_pos hq_two_real]
            rw [erdos_weight, mangoldt_tail_term]
            have hp_real_ne : (p : ℝ) ≠ 0 := by positivity
            have hlogpq_ne : Real.log ((p * q : ℕ) : ℝ) ≠ 0 := by
              have hlogpq_pos : 0 < Real.log ((p * q : ℕ) : ℝ) := by
                apply Real.log_pos
                have hpq_gt_one : 1 < p * q := lt_of_lt_of_le Nat.one_lt_two hpq_two
                exact_mod_cast hpq_gt_one
              exact hlogpq_pos.ne'
            rw [Nat.cast_mul]
            field_simp [erdos_weight, hlogp_pos.ne', hp_real_ne, hlogpq_ne]
            calc
              ArithmeticFunction.vonMangoldt q / Real.log ((p : ℝ) * (q : ℝ)) ^ 2 =
                  (ArithmeticFunction.vonMangoldt q / Real.log ((p : ℝ) * (q : ℝ)) ^ 2) *
                    ((p : ℝ) * Real.log (p : ℝ) * erdos_weight p) := by
                rw [hweight_mul]
                ring
              _ = (p : ℝ) * ArithmeticFunction.vonMangoldt q * erdos_weight p *
                    Real.log (p : ℝ) / Real.log ((p : ℝ) * (q : ℝ)) ^ 2 := by
                ring
          calc
            erdos_weight (p * q) * P (p * q) p =
                erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q) := hterm_eq
            _ ≤ erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q + redirectedTerm q) := by
              exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hredirected_nonneg)
                hweight_nonneg
      · rw [if_neg hqone]
        exact mul_nonneg hweight_nonneg
          (add_nonneg (mul_nonneg hlogp_pos.le hordinary_nonneg) hredirected_nonneg)
    have hredirected_sum :
        (∑ q ∈ s, redirectedTerm q) ≤ modified_prime_power_redirected_finite p t := by
      dsimp [redirectedTerm, modified_prime_power_redirected_finite]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk2 : 2 ≤ k
      · have hterm_nonneg :
            0 ≤ 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) := by
          positivity
        calc
          (∑ q ∈ s,
            if q = p ^ (k - 1) ∧ 2 ≤ k then
              1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)))
            else 0) =
              ∑ q ∈ s,
                if q = p ^ (k - 1) then
                  1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1)))
                else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            simp [hk2]
          _ ≤ 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) := by
            by_cases hmem : p ^ (k - 1) ∈ s
            · simp [Finset.sum_ite_eq', hmem]
            · simpa [Finset.sum_ite_eq', hmem] using hterm_nonneg
          _ = (if 2 ≤ k then
              1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0) := by
            simp [hk2]
      · simp [hk2]
    calc
      (∑ q ∈ s,
        if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
          ∑ q ∈ s,
            erdos_weight p * (Real.log (p : ℝ) * ordinaryTerm q + redirectedTerm q) := by
        exact Finset.sum_le_sum hpoint
      _ = erdos_weight p *
          (Real.log (p : ℝ) *
              (∑ q ∈ s,
                if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
            ∑ q ∈ s, redirectedTerm q) := by
        dsimp [ordinaryTerm]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ erdos_weight p *
          (Real.log (p : ℝ) *
              (∑ q ∈ s,
                if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
            modified_prime_power_redirected_finite p t) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [hredirected_sum]
        · exact hweight_nonneg
  constructor
  · have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hp_two : 2 ≤ p := hp_prime.two_le
    have hp_one : 1 ≤ p := by omega
    have hlogp_pos : 0 < Real.log (p : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp_two)
    have hweight_nonneg : 0 ≤ erdos_weight p := by
      rw [erdos_weight]
      positivity
    have htail_nonneg : 0 ≤ mangoldt_tail_sum p 2 := by
      rw [mangoldt_tail_sum]
      apply tsum_nonneg
      intro q
      split_ifs
      · rw [mangoldt_tail_term]
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      · norm_num
    have hredirected_nonneg : 0 ≤ modified_prime_power_redirected_sum p := by
      rw [modified_prime_power_redirected_sum]
      apply tsum_nonneg
      intro k
      split_ifs
      · positivity
      · norm_num
    have hredirected_finite_le_sum : ∀ t : Finset ℕ,
        modified_prime_power_redirected_finite p t ≤ modified_prime_power_redirected_sum p := by
      intro t
      let red : ℕ → ℝ := fun k =>
        if 2 ≤ k then 1 / (((k : ℝ) ^ 2) * ((p : ℝ) ^ (k - 1))) else 0
      have hred_nonneg : ∀ k : ℕ, 0 ≤ red k := by
        intro k
        dsimp [red]
        split_ifs
        · positivity
        · norm_num
      rcases modified_prime_power_redirected_bound p hp with ⟨_, hfinite_bound⟩
      let slack : ℝ :=
        1 - (Real.log (p : ℝ) / Real.log 2) /
          (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ))
      have hbound : ∀ N : ℕ, (∑ k ∈ Finset.range N, red k) ≤ slack := by
        intro N
        dsimp [red, slack]
        simpa [modified_prime_power_redirected_finite] using
          hfinite_bound (Finset.range N)
      have hsumm : Summable red := summable_of_sum_range_le hred_nonneg hbound
      simpa [red, modified_prime_power_redirected_finite, modified_prime_power_redirected_sum]
        using hsumm.sum_le_tsum t (fun k _ => hred_nonneg k)
    apply tsum_le_of_sum_le'
    · exact mul_nonneg hweight_nonneg
        (add_nonneg (mul_nonneg hlogp_pos.le htail_nonneg) hredirected_nonneg)
    · intro s
      rcases hfinite s with ⟨t, hst⟩
      have htail_le :
          (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) ≤
            mangoldt_tail_sum p 2 := by
        exact mangoldt_tail_finite_sum_le p hp_one 2 (by norm_num) s
      have hinside_le :
          Real.log (p : ℝ) *
                (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
              modified_prime_power_redirected_finite p t ≤
            Real.log (p : ℝ) * mangoldt_tail_sum p 2 +
              modified_prime_power_redirected_sum p := by
        exact add_le_add (mul_le_mul_of_nonneg_left htail_le hlogp_pos.le)
          (hredirected_finite_le_sum t)
      calc
        (∑ q ∈ s,
          if 1 < q then erdos_weight (p * q) * P (p * q) p else 0) ≤
            erdos_weight p *
              (Real.log (p : ℝ) *
                  (∑ q ∈ s,
                    if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term p q else 0) +
                modified_prime_power_redirected_finite p t) := hst
        _ ≤ erdos_weight p *
            (Real.log (p : ℝ) * mangoldt_tail_sum p 2 +
              modified_prime_power_redirected_sum p) := by
          exact mul_le_mul_of_nonneg_left hinside_le hweight_nonneg
  · exact hfinite

structure eps_modified_chain_kernel_subinvariant (P : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ n m : ℕ, 0 ≤ P n m
  row : ∀ n : ℕ, 1 ≤ n -> (∑' m : ℕ, P n m) = 1
  one_one : P 1 1 = 1
  one_zero : ∀ m : ℕ, m ≠ 1 -> P 1 m = 0
  prime_absorb : ∀ p : ℕ, p ∈ prime_layer -> P p p = 1
  prime_zero : ∀ p m : ℕ, p ∈ prime_layer -> m ≠ p -> P p m = 0
  support : ∀ n m : ℕ, 2 ≤ n -> P n m ≠ 0 ->
    m ∣ n ∧ ((m = n ∧ n ∈ prime_layer) ∨ m < n)
  ordinary_rule : ∀ n q : ℕ, 2 ≤ n -> n ∉ prime_layer ->
    (∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k -> n ≠ p ^ k) ->
    1 < q -> q ∣ n ->
      P n (n / q) = ArithmeticFunction.vonMangoldt q / Real.log (n : ℝ)
  prime_power_redirect : ∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k ->
    P (p ^ k) p =
      ArithmeticFunction.vonMangoldt (p ^ (k - 1)) /
        Real.log ((p ^ k : ℕ) : ℝ) + 1 / (k : ℝ)
  prime_power_rule : ∀ p k j : ℕ, p ∈ prime_layer -> 2 ≤ k -> 1 ≤ j -> j ≤ k - 2 ->
    P (p ^ k) (p ^ (k - j)) =
      ArithmeticFunction.vonMangoldt (p ^ j) / Real.log ((p ^ k : ℕ) : ℝ)
  prime_power_support : ∀ p k m : ℕ, p ∈ prime_layer -> 2 ≤ k -> P (p ^ k) m ≠ 0 ->
    m = p ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j)
  subinvariant : ∀ m : ℕ, 2 ≤ m ->
    (∑' q : ℕ, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) ≤
      erdos_weight m
  finite_subinvariant : ∀ m : ℕ, 2 ≤ m -> ∀ s : Finset ℕ,
    (∑ q ∈ s, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) ≤
      erdos_weight m

lemma eps_modified_chain_subinvariant :
    ∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P := by
  classical
  let ppBase : (n : ℕ) → IsPrimePow n → ℕ := fun n hn =>
    Classical.choose ((isPrimePow_nat_iff n).mp hn)
  let ppExp : (n : ℕ) → (hn : IsPrimePow n) → ℕ := fun n hn =>
    Classical.choose (Classical.choose_spec ((isPrimePow_nat_iff n).mp hn))
  have pp_spec : ∀ n (hn : IsPrimePow n),
      Nat.Prime (ppBase n hn) ∧ 0 < ppExp n hn ∧
        (ppBase n hn) ^ (ppExp n hn) = n := by
    intro n hn
    dsimp [ppBase, ppExp]
    exact Classical.choose_spec (Classical.choose_spec ((isPrimePow_nat_iff n).mp hn))
  let P : ℕ → ℕ → ℝ := fun n m =>
    if n = 1 then
      if m = 1 then 1 else 0
    else if n ∈ prime_layer then
      if m = n then 1 else 0
    else if hnpp : IsPrimePow n then
      let p := ppBase n hnpp
      let k := ppExp n hnpp
      if m = p then
        ArithmeticFunction.vonMangoldt (p ^ (k - 1)) / Real.log (n : ℝ) + 1 / (k : ℝ)
      else if hm : ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j) then
        ArithmeticFunction.vonMangoldt (p ^ (Classical.choose hm)) / Real.log (n : ℝ)
      else 0
    else if m ∣ n ∧ m < n then
      ArithmeticFunction.vonMangoldt (n / m) / Real.log (n : ℝ)
    else 0
  have pp_unique : ∀ {n p k : ℕ} (hnpp : IsPrimePow n),
      Nat.Prime p -> 0 < k -> p ^ k = n ->
        ppBase n hnpp = p ∧ ppExp n hnpp = k := by
    intro n p k hnpp hp hk hpow
    have hspec := pp_spec n hnpp
    have hEq : ppBase n hnpp ^ ppExp n hnpp = p ^ k := by
      calc
        ppBase n hnpp ^ ppExp n hnpp = n := hspec.2.2
        _ = p ^ k := hpow.symm
    have hpowSucc :
        ppBase n hnpp ^ ((ppExp n hnpp - 1) + 1) =
          p ^ ((k - 1) + 1) := by
      have hExp : ppExp n hnpp = (ppExp n hnpp - 1) + 1 := by omega
      have hK : k = (k - 1) + 1 := by omega
      simpa [← hExp, ← hK] using hEq
    have huniq := Nat.Prime.pow_inj hspec.1 hp hpowSucc
    exact ⟨huniq.1, by omega⟩
  have prime_power_ne_one : ∀ {p k : ℕ}, p ∈ prime_layer -> 1 ≤ k -> p ^ k ≠ 1 := by
    intro p k hp hk
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    exact ne_of_gt (Nat.one_lt_pow (by omega) hp_prime.one_lt)
  have prime_power_not_prime : ∀ {p k : ℕ}, p ∈ prime_layer -> 2 ≤ k -> p ^ k ∉ prime_layer := by
    intro p k hp hk hprime_layer
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have htail_ne_one : p ^ (k - 1) ≠ 1 := by
      exact ne_of_gt (Nat.one_lt_pow (by omega) hp_prime.one_lt)
    have hpow_mul : p ^ k = p * p ^ (k - 1) := by
      have hk_succ : k = (k - 1) + 1 := by omega
      have hidx : k - 1 + 1 - 1 = k - 1 := by omega
      rw [hk_succ, pow_succ, hidx, mul_comm]
    have hprime_nat : Nat.Prime (p ^ k) := by
      simpa [prime_layer] using hprime_layer
    rw [hpow_mul] at hprime_nat
    exact (Nat.not_prime_mul hp_prime.ne_one htail_ne_one) hprime_nat
  have pp_exp_two_of_not_prime : ∀ {n : ℕ} (hnpp : IsPrimePow n),
      n ∉ prime_layer -> 2 ≤ ppExp n hnpp := by
    intro n hnpp hnprime
    have hspec := pp_spec n hnpp
    by_contra hknot
    have hk_one : ppExp n hnpp = 1 := by omega
    have hn_prime_nat : Nat.Prime n := by
      rw [← hspec.2.2, hk_one, pow_one]
      exact hspec.1
    exact hnprime (by simpa [prime_layer] using hn_prime_nat)
  have hordinaryP : ∀ n q : ℕ, 2 ≤ n -> n ∉ prime_layer ->
      (∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k -> n ≠ p ^ k) ->
      1 < q -> q ∣ n ->
        P n (n / q) = ArithmeticFunction.vonMangoldt q / Real.log (n : ℝ) := by
    intro n q hn hnprime hnotpp hq hqdiv
    have hn_ne_one : n ≠ 1 := by omega
    have hnpp_false : ¬ IsPrimePow n := by
      intro hnpp
      rcases (isPrimePow_nat_iff n).mp hnpp with ⟨p, k, hp, hkpos, hpow⟩
      by_cases hk_one : k = 1
      · have hn_prime_nat : Nat.Prime n := by
          rw [← hpow, hk_one, pow_one]
          exact hp
        exact hnprime (by simpa [prime_layer] using hn_prime_nat)
      · have hk_two : 2 ≤ k := by omega
        exact hnotpp p k (by simpa [prime_layer] using hp) hk_two (by rw [← hpow])
    have hdiv : n / q ∣ n ∧ n / q < n := by
      constructor
      · exact Nat.div_dvd_of_dvd hqdiv
      · have hqpos : 0 < q := by omega
        rw [Nat.div_lt_iff_lt_mul hqpos]
        have hnpos : 0 < n := by omega
        simpa using Nat.mul_lt_mul_of_pos_left hq hnpos
    have hq_eq : n / (n / q) = q := by
      exact Nat.div_div_self hqdiv (by omega)
    simp [P, hn_ne_one, hnprime, hnpp_false, hdiv, hq_eq]
  have hbaseP : ∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k ->
      P (p ^ k) p =
        ArithmeticFunction.vonMangoldt (p ^ (k - 1)) /
          Real.log ((p ^ k : ℕ) : ℝ) + 1 / (k : ℝ) := by
    intro p k hp hk
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2]
  have hstepP : ∀ p k j : ℕ, p ∈ prime_layer -> 2 ≤ k -> 1 ≤ j -> j ≤ k - 2 ->
      P (p ^ k) (p ^ (k - j)) =
        ArithmeticFunction.vonMangoldt (p ^ j) / Real.log ((p ^ k : ℕ) : ℝ) := by
    intro p k j hp hk hj hjle
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    have hnot_base : p ^ (k - j) ≠ p := by
      intro hpow
      have hexp : k - j = 1 := by
        exact Nat.pow_right_injective hp_prime.two_le (by simpa [pow_one] using hpow)
      omega
    let hstep : ∃ j' : ℕ, 1 ≤ j' ∧ j' ≤ k - 2 ∧ p ^ (k - j) = p ^ (k - j') :=
      ⟨j, hj, hjle, rfl⟩
    have hchoose_eq : Classical.choose hstep = j := by
      have hspec := Classical.choose_spec hstep
      have hexp : k - j = k - Classical.choose hstep := by
        exact Nat.pow_right_injective hp_prime.two_le hspec.2.2
      omega
    simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2,
      hnot_base, hstep, hchoose_eq]
  have hsupportPrimePowerP : ∀ p k m : ℕ, p ∈ prime_layer -> 2 ≤ k -> P (p ^ k) m ≠ 0 ->
      m = p ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j) := by
    intro p k m hp hk hP
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    by_cases hm_base : m = p
    · exact Or.inl hm_base
    · by_cases hmstep : ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j)
      · exact Or.inr hmstep
      · exfalso
        have hzero : P (p ^ k) m = 0 := by
          simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2,
            hm_base, hmstep]
        exact hP hzero
  have hcompositeTransition : ∀ m q : ℕ, 2 ≤ m -> m ∉ prime_layer -> 1 < q ->
      P (m * q) m = ArithmeticFunction.vonMangoldt q / Real.log ((m * q : ℕ) : ℝ) := by
    intro m q hm hmprime hq
    have hm_ne_one : m ≠ 1 := by omega
    have hq_ne_one : q ≠ 1 := by omega
    have hmq_two : 2 ≤ m * q := by
      exact Nat.mul_le_mul hm (by omega : 1 ≤ q)
    have hmq_not_prime : m * q ∉ prime_layer := by
      intro hprime_layer
      have hprime_nat : Nat.Prime (m * q) := by
        simpa [prime_layer] using hprime_layer
      exact (Nat.not_prime_mul hm_ne_one hq_ne_one) hprime_nat
    by_cases hmqpp : IsPrimePow (m * q)
    · rcases (isPrimePow_nat_iff (m * q)).mp hmqpp with ⟨p, k, hp, hkpos, hpk⟩
      have hp_layer : p ∈ prime_layer := by
        simpa [prime_layer] using hp
      have hmpp : IsPrimePow m := by
        exact IsPrimePow.dvd hmqpp (dvd_mul_right m q) hm_ne_one
      rcases (isPrimePow_nat_iff m).mp hmpp with ⟨r, a, hr, hapos, hra⟩
      have hr_dvd_pk : r ∣ p ^ k := by
        rw [hpk]
        have hr_dvd_m : r ∣ m := by
          rw [← hra]
          simpa [pow_one] using Nat.pow_dvd_pow r (by omega : 1 ≤ a)
        exact dvd_mul_of_dvd_left hr_dvd_m q
      have hr_eq_hp : r = p := Nat.prime_eq_prime_of_dvd_pow hr hp hr_dvd_pk
      subst r
      have ha_two : 2 ≤ a := by
        by_contra ha_not
        have ha_one : a = 1 := by omega
        have hm_prime_nat : Nat.Prime m := by
          rw [← hra, ha_one, pow_one]
          exact hp
        exact hmprime (by simpa [prime_layer] using hm_prime_nat)
      have hpa_dvd_pk : p ^ a ∣ p ^ k := by
        rw [hpk, hra]
        exact dvd_mul_right m q
      have ha_le_k : a ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpa_dvd_pk
      have hq_eq : q = p ^ (k - a) := by
        have hpow_split : p ^ k = p ^ a * p ^ (k - a) := by
          rw [← pow_add]
          congr 1
          omega
        have hmul : p ^ a * q = p ^ a * p ^ (k - a) := by
          calc
            p ^ a * q = m * q := by rw [hra]
            _ = p ^ k := hpk.symm
            _ = p ^ a * p ^ (k - a) := hpow_split
        exact Nat.mul_left_cancel (Nat.pow_pos (a := p) (n := a) hp.pos) hmul
      have hj : 1 ≤ k - a := by
        by_contra hj_not
        have hka_zero : k - a = 0 := by omega
        have hq_one : q = 1 := by
          rw [hq_eq, hka_zero, pow_zero]
        exact hq_ne_one hq_one
      have hjle : k - a ≤ k - 2 := by omega
      have hk_two : 2 ≤ k := by omega
      have hm_eq : m = p ^ (k - (k - a)) := by
        rw [← hra]
        congr 1
        omega
      have hstep := hstepP p k (k - a) hp_layer hk_two hj hjle
      simpa [hpk, hra, hq_eq, hm_eq] using hstep
    · have hnotpp_clause : ∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k -> m * q ≠ p ^ k := by
        intro p k hp hk hEq
        apply hmqpp
        rw [isPrimePow_nat_iff]
        exact ⟨p, k, by simpa [prime_layer] using hp, by omega, hEq.symm⟩
      have hq_dvd : q ∣ m * q := by
        exact ⟨m, by rw [mul_comm]⟩
      have hdiv_eq : (m * q) / q = m := by
        rw [mul_comm]
        exact Nat.mul_div_right m (by omega)
      simpa [hdiv_eq] using hordinaryP (m * q) q hmq_two hmq_not_prime hnotpp_clause hq hq_dvd
  have hsubinvFinite : ∀ m : ℕ, 2 ≤ m -> ∀ s : Finset ℕ,
      (∑ q ∈ s, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) ≤
        erdos_weight m := by
    intro m hm s
    have hm_one : 1 ≤ m := by omega
    have hlogm_pos : 0 < Real.log (m : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hm)
    have hweight_nonneg : 0 ≤ erdos_weight m := by
      rw [erdos_weight]
      positivity
    by_cases hmprime : m ∈ prime_layer
    · rcases (eps_modified_chain_prime_power_incoming_reindex P hordinaryP hbaseP
        hsupportPrimePowerP m hmprime).2 s with ⟨t, hst⟩
      have hbound := (modified_prime_power_incoming_bound m hmprime).2 s t
      calc
        (∑ q ∈ s, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) ≤
            erdos_weight m *
              (Real.log (m : ℝ) *
                  (∑ q ∈ s, if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term m q else 0) +
                modified_prime_power_redirected_finite m t) := hst
        _ ≤ erdos_weight m * 1 := by
          exact mul_le_mul_of_nonneg_left hbound hweight_nonneg
        _ = erdos_weight m := by ring
    · let T : ℕ → ℝ := fun q =>
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term m q else 0
      have hpoint : ∀ q ∈ s,
          (if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) =
            erdos_weight m * (Real.log (m : ℝ) * T q) := by
        intro q hqmem
        by_cases hq : 1 < q
        · have hq_two : 2 ≤ q := by omega
          have hq_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_two
          have hmq_two : 2 ≤ m * q := Nat.mul_le_mul hm (by omega : 1 ≤ q)
          have hlogmq_pos : 0 < Real.log ((m * q : ℕ) : ℝ) := by
            apply Real.log_pos
            have hmq_gt_one : 1 < m * q := lt_of_lt_of_le Nat.one_lt_two hmq_two
            exact_mod_cast hmq_gt_one
          have hm_real_ne : (m : ℝ) ≠ 0 := by positivity
          have hq_real_ne : (q : ℝ) ≠ 0 := by positivity
          rw [if_pos hq]
          dsimp [T]
          rw [if_pos hq_two_real, hcompositeTransition m q hm hmprime hq]
          rw [erdos_weight, mangoldt_tail_term, Nat.cast_mul]
          field_simp [hm_real_ne, hq_real_ne, hlogm_pos.ne', hlogmq_pos.ne']
          have hmul : (m : ℝ) * erdos_weight m * Real.log (m : ℝ) = 1 := by
            rw [erdos_weight]
            field_simp [hm_real_ne, hlogm_pos.ne']
          calc
            ArithmeticFunction.vonMangoldt q / Real.log ((m : ℝ) * (q : ℝ)) ^ 2 =
                ArithmeticFunction.vonMangoldt q / Real.log ((m : ℝ) * (q : ℝ)) ^ 2 * 1 := by ring
            _ = ArithmeticFunction.vonMangoldt q / Real.log ((m : ℝ) * (q : ℝ)) ^ 2 *
                ((m : ℝ) * erdos_weight m * Real.log (m : ℝ)) := by rw [hmul]
            _ = (m : ℝ) * ArithmeticFunction.vonMangoldt q * erdos_weight m *
                Real.log (m : ℝ) / Real.log ((m : ℝ) * (q : ℝ)) ^ 2 := by ring
        · have hq_lt_two : q < 2 := by omega
          have hq_not_two : ¬2 ≤ q := by omega
          have hq_not_two_real : ¬(2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_not_two
          have hT_zero : T q = 0 := by
            dsimp [T]
            simp [hq_not_two_real]
          simp [hq, hT_zero]
      calc
        (∑ q ∈ s, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) =
            ∑ q ∈ s, erdos_weight m * (Real.log (m : ℝ) * T q) := by
          apply Finset.sum_congr rfl
          intro q hqmem
          exact hpoint q hqmem
        _ = erdos_weight m * (Real.log (m : ℝ) * ∑ q ∈ s, T q) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ erdos_weight m * 1 := by
          have htail_le : (∑ q ∈ s, T q) ≤ mangoldt_tail_sum m 2 := by
            dsimp [T]
            exact mangoldt_tail_finite_sum_le m hm_one 2 (by norm_num) s
          have hinside_le : Real.log (m : ℝ) * (∑ q ∈ s, T q) ≤ 1 := by
            exact (mul_le_mul_of_nonneg_left htail_le hlogm_pos.le).trans
              (mangoldt_subinvariant_bound m hm)
          exact mul_le_mul_of_nonneg_left hinside_le hweight_nonneg
        _ = erdos_weight m := by ring
  have hsubinvInfinite : ∀ m : ℕ, 2 ≤ m ->
      (∑' q : ℕ, if 1 < q then erdos_weight (m * q) * P (m * q) m else 0) ≤
        erdos_weight m := by
    intro m hm
    apply tsum_le_of_sum_le'
    · rw [erdos_weight]
      positivity
    · intro s
      exact hsubinvFinite m hm s
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m
    dsimp [P]
    split_ifs with hn_one hm_one hn_prime hm_self hnpp hm_base hm_step hm_div
    · positivity
    · positivity
    · positivity
    · positivity
    · have hspec := pp_spec n hnpp
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        have hn_gt_one : 1 < n := by
          rw [← hspec.2.2]
          exact Nat.one_lt_pow (ne_of_gt hspec.2.1) hspec.1.one_lt
        exact_mod_cast hn_gt_one
      exact add_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog_pos.le)
        (by positivity)
    · have hspec := pp_spec n hnpp
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        have hn_gt_one : 1 < n := by
          rw [← hspec.2.2]
          exact Nat.one_lt_pow (ne_of_gt hspec.2.1) hspec.1.one_lt
        exact_mod_cast hn_gt_one
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog_pos.le
    · positivity
    · have hn_gt_one : 1 < n := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        exact_mod_cast hn_gt_one
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog_pos.le
    · positivity
  · intro n hnpos
    by_cases hn_one : n = 1
    · subst n
      calc
        (∑' m : ℕ, P 1 m) = ∑ m ∈ ({1} : Finset ℕ), P 1 m := by
          refine tsum_eq_sum (s := ({1} : Finset ℕ)) ?_
          intro m hm
          have hm_ne : m ≠ 1 := by simpa using hm
          simp [P, hm_ne]
        _ = 1 := by simp [P]
    · by_cases hn_prime : n ∈ prime_layer
      · calc
          (∑' m : ℕ, P n m) = ∑ m ∈ ({n} : Finset ℕ), P n m := by
            refine tsum_eq_sum (s := ({n} : Finset ℕ)) ?_
            intro m hm
            have hm_ne : m ≠ n := by simpa using hm
            simp [P, hn_one, hn_prime, hm_ne]
          _ = 1 := by simp [P, hn_one, hn_prime]
      · by_cases hnpp : IsPrimePow n
        · let p := ppBase n hnpp
          let k := ppExp n hnpp
          have hspec := pp_spec n hnpp
          have hp : Nat.Prime p := by
            dsimp [p]
            exact hspec.1
          have hk_two : 2 ≤ k := by
            dsimp [k]
            exact pp_exp_two_of_not_prime hnpp hn_prime
          have hk_ne_zero : k ≠ 0 := by omega
          have hn_eq : n = p ^ k := by
            dsimp [p, k]
            exact hspec.2.2.symm
          have hlogp_pos : 0 < Real.log (p : ℝ) := by
            apply Real.log_pos
            exact_mod_cast hp.one_lt
          have hlogn : Real.log (n : ℝ) = (k : ℝ) * Real.log (p : ℝ) := by
            rw [hn_eq, Nat.cast_pow]
            exact Real.log_pow (p : ℝ) k
          let S : Finset ℕ := ({p} : Finset ℕ) ∪
            (Finset.Icc 1 (k - 2)).image (fun j : ℕ => p ^ (k - j))
          have htsum : (∑' m : ℕ, P n m) = ∑ m ∈ S, P n m := by
            refine tsum_eq_sum (s := S) ?_
            intro m hmS
            have hm_ne_p : m ≠ p := by
              intro hm
              apply hmS
              dsimp [S]
              simp [hm]
            have hm_step_false : ¬∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j) := by
              intro hmstep
              rcases hmstep with ⟨j, hj, hjle, hm_eq⟩
              apply hmS
              dsimp [S]
              exact Finset.mem_insert.mpr
                (Or.inr (Finset.mem_image.mpr
                  ⟨j, Finset.mem_Icc.mpr ⟨hj, hjle⟩, hm_eq.symm⟩))
            simp [P, p, k, hn_one, hn_prime, hnpp, hm_ne_p, hm_step_false]
          have hdisj : Disjoint ({p} : Finset ℕ)
              ((Finset.Icc 1 (k - 2)).image (fun j : ℕ => p ^ (k - j))) := by
            rw [Finset.disjoint_left]
            intro x hx hpows
            simp only [Finset.mem_singleton] at hx
            subst x
            rcases Finset.mem_image.mp hpows with ⟨j, hjmem, hjpow⟩
            have hj := (Finset.mem_Icc.mp hjmem).1
            have hjle := (Finset.mem_Icc.mp hjmem).2
            have hexp : k - j = 1 := by
              exact Nat.pow_right_injective hp.two_le (by simpa [pow_one] using hjpow)
            omega
          have hinj : ∀ a ∈ Finset.Icc 1 (k - 2), ∀ b ∈ Finset.Icc 1 (k - 2),
              p ^ (k - a) = p ^ (k - b) -> a = b := by
            intro a ha b hb hab
            have ha_bounds := Finset.mem_Icc.mp ha
            have hb_bounds := Finset.mem_Icc.mp hb
            have ha_le : a ≤ k := by omega
            have hb_le : b ≤ k := by omega
            have hexp : k - a = k - b := Nat.pow_right_injective hp.two_le hab
            omega
          have hbase_value : P n p =
              ArithmeticFunction.vonMangoldt (p ^ (k - 1)) / Real.log (n : ℝ) + 1 / (k : ℝ) := by
            simp [P, p, k, hn_one, hn_prime, hnpp]
          have hstep_value : ∀ j ∈ Finset.Icc 1 (k - 2),
              P n (p ^ (k - j)) =
                ArithmeticFunction.vonMangoldt (p ^ j) / Real.log (n : ℝ) := by
            intro j hjmem
            have hj : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
            have hjle : j ≤ k - 2 := (Finset.mem_Icc.mp hjmem).2
            have hnot_base : p ^ (k - j) ≠ p := by
              intro hpow
              have hexp : k - j = 1 := by
                exact Nat.pow_right_injective hp.two_le (by simpa [pow_one] using hpow)
              omega
            let hstep : ∃ j' : ℕ, 1 ≤ j' ∧ j' ≤ k - 2 ∧ p ^ (k - j) = p ^ (k - j') :=
              ⟨j, hj, hjle, rfl⟩
            have hchoose_eq : Classical.choose hstep = j := by
              have hspec_step := Classical.choose_spec hstep
              have hexp : k - j = k - Classical.choose hstep := by
                exact Nat.pow_right_injective hp.two_le hspec_step.2.2
              omega
            simp [P, p, k, hn_one, hn_prime, hnpp, hnot_base, hstep, hchoose_eq]
          have hsum_steps :
              (∑ j ∈ Finset.Icc 1 (k - 2),
                ArithmeticFunction.vonMangoldt (p ^ j) / Real.log (n : ℝ)) =
                ((k - 2 : ℕ) : ℝ) * (Real.log (p : ℝ) / Real.log (n : ℝ)) := by
            calc
              (∑ j ∈ Finset.Icc 1 (k - 2),
                ArithmeticFunction.vonMangoldt (p ^ j) / Real.log (n : ℝ)) =
                  ∑ j ∈ Finset.Icc 1 (k - 2),
                    Real.log (p : ℝ) / Real.log (n : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro j hjmem
                    have hj_ne : j ≠ 0 := by
                      have hj : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
                      omega
                    rw [ArithmeticFunction.vonMangoldt_apply_pow hj_ne,
                      ArithmeticFunction.vonMangoldt_apply_prime hp]
              _ = ((Finset.Icc 1 (k - 2)).card : ℝ) *
                    (Real.log (p : ℝ) / Real.log (n : ℝ)) := by
                    simp
              _ = ((k - 2 : ℕ) : ℝ) *
                    (Real.log (p : ℝ) / Real.log (n : ℝ)) := by
                    congr 1
                    simp
          have hbase_von : ArithmeticFunction.vonMangoldt (p ^ (k - 1)) = Real.log (p : ℝ) := by
            have hkpred_ne : k - 1 ≠ 0 := by omega
            rw [ArithmeticFunction.vonMangoldt_apply_pow hkpred_ne,
              ArithmeticFunction.vonMangoldt_apply_prime hp]
          rw [htsum]
          calc
            (∑ m ∈ S, P n m) =
                P n p + ∑ m ∈ (Finset.Icc 1 (k - 2)).image (fun j : ℕ => p ^ (k - j)), P n m := by
              dsimp [S]
              have hp_not_mem : p ∉ (Finset.Icc 1 (k - 2)).image (fun j : ℕ => p ^ (k - j)) := by
                intro hpows
                exact (Finset.disjoint_left.mp hdisj) (by simp) hpows
              rw [Finset.sum_insert hp_not_mem]
            _ = P n p + ∑ j ∈ Finset.Icc 1 (k - 2), P n (p ^ (k - j)) := by
              rw [Finset.sum_image]
              intro a ha b hb hab
              exact hinj a (by simpa using ha) b (by simpa using hb) hab
            _ = (ArithmeticFunction.vonMangoldt (p ^ (k - 1)) / Real.log (n : ℝ) + 1 / (k : ℝ)) +
                ∑ j ∈ Finset.Icc 1 (k - 2),
                  ArithmeticFunction.vonMangoldt (p ^ j) / Real.log (n : ℝ) := by
              rw [hbase_value]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              exact hstep_value j hj
            _ = (Real.log (p : ℝ) / Real.log (n : ℝ) + 1 / (k : ℝ)) +
                ((k - 2 : ℕ) : ℝ) * (Real.log (p : ℝ) / Real.log (n : ℝ)) := by
              rw [hbase_von, hsum_steps]
            _ = 1 := by
              rw [hlogn]
              have hk_cast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
                norm_num [Nat.cast_sub hk_two]
              rw [hk_cast]
              field_simp [hlogp_pos.ne', hk_ne_zero]
              ring
        · have hn_ne_zero : n ≠ 0 := by omega
          have hlog_pos : 0 < Real.log (n : ℝ) := by
            apply Real.log_pos
            have hn_gt_one : 1 < n := by omega
            exact_mod_cast hn_gt_one
          have hdiv_compl :
              (∑ m ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / m)) =
                ∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q := by
            refine Finset.sum_bij' (fun m _ => n / m) (fun q _ => n / q) ?_ ?_ ?_ ?_ ?_
            · intro m hm
              have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
              exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hmdvd, hn_ne_zero⟩
            · intro q hq
              have hqdvd : q ∣ n := (Nat.mem_divisors.mp hq).1
              exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hqdvd, hn_ne_zero⟩
            · intro m hm
              have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
              exact Nat.div_div_self hmdvd hn_ne_zero
            · intro q hq
              have hqdvd : q ∣ n := (Nat.mem_divisors.mp hq).1
              exact Nat.div_div_self hqdvd hn_ne_zero
            · intro m hm
              rfl
          calc
            (∑' m : ℕ, P n m) = ∑ m ∈ n.divisors, P n m := by
              refine tsum_eq_sum (s := n.divisors) ?_
              intro m hm
              have hmcond_false : ¬(m ∣ n ∧ m < n) := by
                intro hcond
                exact hm (Nat.mem_divisors.mpr ⟨hcond.1, hn_ne_zero⟩)
              simp [P, hn_one, hn_prime, hnpp, hmcond_false]
            _ = ∑ m ∈ n.divisors,
                ArithmeticFunction.vonMangoldt (n / m) / Real.log (n : ℝ) := by
              apply Finset.sum_congr rfl
              intro m hm
              have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
              have hm_le : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn_ne_zero) hmdvd
              by_cases hlt : m < n
              · have hmcond : m ∣ n ∧ m < n := ⟨hmdvd, hlt⟩
                simp [P, hn_one, hn_prime, hnpp, hmcond]
              · have hm_eq : m = n := by omega
                subst m
                have hmcond_false : ¬(n ∣ n ∧ n < n) := by omega
                simp [P, hn_one, hn_prime, hnpp, Nat.div_self (Nat.pos_of_ne_zero hn_ne_zero)]
            _ = (1 / Real.log (n : ℝ)) *
                (∑ m ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / m)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m hm
              ring
            _ = (1 / Real.log (n : ℝ)) * Real.log (n : ℝ) := by
              rw [hdiv_compl, von_mangoldt_divisor_sum]
            _ = 1 := by
              field_simp [hlog_pos.ne']
  · simp [P]
  · intro m hm
    simp [P, hm]
  · intro p hp
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    simp [P, hp, hp_prime.ne_one]
  · intro p m hp hm
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    simp [P, hp, hp_prime.ne_one, hm]
  · intro n m hn hPne
    dsimp [P] at hPne
    split_ifs at hPne with hn_one hm_one hn_prime hm_self hnpp hm_base hmstep hmdiv
    · omega
    · exact (hPne rfl).elim
    · subst m
      exact ⟨dvd_rfl, Or.inl ⟨rfl, hn_prime⟩⟩
    · exact (hPne rfl).elim
    · have hspec := pp_spec n hnpp
      have hk_two : 2 ≤ ppExp n hnpp := pp_exp_two_of_not_prime hnpp hn_prime
      have hdiv : ppBase n hnpp ∣ n := by
        have hdiv_pow : ppBase n hnpp ∣ ppBase n hnpp ^ ppExp n hnpp := by
          simpa [pow_one] using Nat.pow_dvd_pow (ppBase n hnpp) (by omega : 1 ≤ ppExp n hnpp)
        simpa [hspec.2.2] using hdiv_pow
      have hlt : ppBase n hnpp < n := by
        have hlt_pow : ppBase n hnpp < ppBase n hnpp ^ ppExp n hnpp := by
          simpa [pow_one] using Nat.pow_lt_pow_right hspec.1.one_lt (by omega : 1 < ppExp n hnpp)
        simpa [hspec.2.2] using hlt_pow
      rw [hm_base]
      exact ⟨hdiv, Or.inr hlt⟩
    · have hspec := pp_spec n hnpp
      rcases hmstep with ⟨j, hj, hjle, hm_eq⟩
      have hdiv : m ∣ n := by
        have hdiv_pow : ppBase n hnpp ^ (ppExp n hnpp - j) ∣
            ppBase n hnpp ^ ppExp n hnpp := by
          exact Nat.pow_dvd_pow (ppBase n hnpp) (by omega : ppExp n hnpp - j ≤ ppExp n hnpp)
        simpa [hm_eq, hspec.2.2] using hdiv_pow
      have hlt : m < n := by
        have hlt_pow : ppBase n hnpp ^ (ppExp n hnpp - j) <
            ppBase n hnpp ^ ppExp n hnpp := by
          exact Nat.pow_lt_pow_right hspec.1.one_lt (by omega : ppExp n hnpp - j < ppExp n hnpp)
        simpa [hm_eq, hspec.2.2] using hlt_pow
      exact ⟨hdiv, Or.inr hlt⟩
    · exact (hPne rfl).elim
    · exact ⟨hmdiv.1, Or.inr hmdiv.2⟩
    · exact (hPne rfl).elim
  · intro n q hn hnprime hnotpp hq hqdiv
    have hn_ne_one : n ≠ 1 := by omega
    have hnpp_false : ¬ IsPrimePow n := by
      intro hnpp
      rcases (isPrimePow_nat_iff n).mp hnpp with ⟨p, k, hp, hkpos, hpow⟩
      by_cases hk_one : k = 1
      · have hn_prime_nat : Nat.Prime n := by
          rw [← hpow, hk_one, pow_one]
          exact hp
        exact hnprime (by simpa [prime_layer] using hn_prime_nat)
      · have hk_two : 2 ≤ k := by omega
        exact hnotpp p k (by simpa [prime_layer] using hp) hk_two (by rw [← hpow])
    have hdiv : n / q ∣ n ∧ n / q < n := by
      constructor
      · exact Nat.div_dvd_of_dvd hqdiv
      · have hqpos : 0 < q := by omega
        rw [Nat.div_lt_iff_lt_mul hqpos]
        have hnpos : 0 < n := by omega
        simpa using Nat.mul_lt_mul_of_pos_left hq hnpos
    have hq_eq : n / (n / q) = q := by
      exact Nat.div_div_self hqdiv (by omega)
    simp [P, hn_ne_one, hnprime, hnpp_false, hdiv, hq_eq]
  · intro p k hp hk
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hne_one : p ^ k ≠ 1 := prime_power_ne_one hp (by omega)
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2]
  · intro p k j hp hk hj hjle
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    have hnot_base : p ^ (k - j) ≠ p := by
      intro hpow
      have hexp : k - j = 1 := by
        exact Nat.pow_right_injective hp_prime.two_le (by simpa [pow_one] using hpow)
      omega
    let hstep : ∃ j' : ℕ, 1 ≤ j' ∧ j' ≤ k - 2 ∧ p ^ (k - j) = p ^ (k - j') :=
      ⟨j, hj, hjle, rfl⟩
    have hchoose_eq : Classical.choose hstep = j := by
      have hspec := Classical.choose_spec hstep
      have hexp : k - j = k - Classical.choose hstep := by
        exact Nat.pow_right_injective hp_prime.two_le hspec.2.2
      omega
    simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2,
      hnot_base, hstep, hchoose_eq]
  · intro p k m hp hk hP
    have hp_prime : Nat.Prime p := by
      simpa [prime_layer] using hp
    have hnot_prime : p ^ k ∉ prime_layer := prime_power_not_prime hp hk
    have hnpp : IsPrimePow (p ^ k) := by
      rw [isPrimePow_nat_iff]
      exact ⟨p, k, hp_prime, by omega, rfl⟩
    have huniq := pp_unique hnpp hp_prime (by omega) rfl
    have hk_ne_zero : k ≠ 0 := by omega
    by_cases hm_base : m = p
    · exact Or.inl hm_base
    · by_cases hmstep : ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ m = p ^ (k - j)
      · exact Or.inr hmstep
      · exfalso
        have hzero : P (p ^ k) m = 0 := by
          simp [P, hp_prime.ne_one, hk_ne_zero, hnot_prime, hnpp, huniq.1, huniq.2,
            hm_base, hmstep]
        exact hP hzero
  · exact hsubinvInfinite
  · exact hsubinvFinite

structure eps_adjoint_kernel_package (P : ℕ → ℕ → ℝ)
    (U : Option ℕ → Option ℕ → ℝ) : Prop where
  nonneg : ∀ a b : Option ℕ, 0 ≤ U a b
  row_tsum : ∀ n : ℕ, 2 ≤ n ->
    (∑' m : ℕ, if 2 ≤ m then U (some n) (some m) else 0) +
        U (some n) none = 1
  finite_row : ∀ n : ℕ, 2 ≤ n -> ∀ s : Finset ℕ,
    (∑ m ∈ s, if 2 ≤ m then U (some n) (some m) else 0) ≤ 1
  none_none : U (none : Option ℕ) (none : Option ℕ) = 1
  none_some : ∀ m : ℕ, U (none : Option ℕ) (some m) = 0
  diag_zero : ∀ n : ℕ, 2 ≤ n -> U (some n) (some n) = 0
  adjoint_formula : ∀ n m : ℕ, 2 ≤ n -> 2 ≤ m -> m ≠ n ->
    U (some n) (some m) = erdos_weight m / erdos_weight n * P m n
  support : ∀ n m : ℕ, U (some n) (some m) ≠ 0 ->
    2 ≤ n ∧ 2 ≤ m ∧ ∃ q : ℕ, 1 < q ∧ m = n * q
  slack : ∀ n : ℕ, 2 ≤ n ->
    U (some n) none =
      1 - (∑' m : ℕ,
        if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0)

structure eps_adjoint_hitting_mass_facts (U : Option ℕ → Option ℕ → ℝ)
    (h : ℕ → ℝ) : Prop where
  nonneg : ∀ n : ℕ, 0 ≤ h n
  recurrence : ∀ n : ℕ, 2 ≤ n ->
    h n =
      prime_layer.indicator erdos_weight n +
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0)
  equals_erdos : ∀ n : ℕ, h n = erdos_weight n
  prime_summable : Summable (fun n : ℕ => prime_layer.indicator h n)

abbrev eps_adjoint_primitive_chain_antichain_facts (h : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ, primitive_set A ->
    (∀ s : Finset ℕ,
      (∑ n ∈ s, A.indicator h n) ≤
        ∑' n : ℕ, prime_layer.indicator h n) ∧
    Summable (fun n : ℕ => A.indicator h n) ∧
      (∑' n : ℕ, A.indicator h n) ≤
        ∑' n : ℕ, prime_layer.indicator h n

lemma eps_adjoint_kernel_package_from_subinvariant {P : ℕ → ℕ → ℝ} :
    eps_modified_chain_kernel_subinvariant P ->
      ∃ U : Option ℕ → Option ℕ → ℝ, eps_adjoint_kernel_package P U := by
  classical
  intro hP
  let U : Option ℕ → Option ℕ → ℝ := fun a b =>
    match a, b with
    | none, none => 1
    | none, some _ => 0
    | some n, none =>
        if 2 ≤ n then
          1 - (∑' m : ℕ,
            if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0)
        else 0
    | some n, some m =>
        if 2 ≤ n ∧ 2 ≤ m ∧ m ≠ n then
          erdos_weight m / erdos_weight n * P m n
        else 0
  refine ⟨U, ?_⟩
  rcases hP with
    ⟨hP_nonneg, hP_row, hP_one, hP_one_zero, hP_prime_absorb,
      hP_prime_zero, hP_support, hP_rule, hP_pp_redirect,
      hP_pp_rule, hP_pp_support, hP_subinf, hP_subfin⟩
  have hweight_pos : ∀ n : ℕ, 2 ≤ n -> 0 < erdos_weight n := by
    intro n hn
    rw [erdos_weight]
    apply div_pos zero_lt_one
    apply mul_pos
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
    · apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hweight_nonneg : ∀ n : ℕ, 2 ≤ n -> 0 ≤ erdos_weight n := by
    intro n hn
    exact (hweight_pos n hn).le
  have hrow_term_nonneg : ∀ n m : ℕ, 2 ≤ n ->
      0 ≤ (if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0) := by
    intro n m hn
    by_cases hm : 2 ≤ m ∧ m ≠ n
    · rw [if_pos hm]
      exact mul_nonneg (div_nonneg (hweight_nonneg m hm.1) (hweight_nonneg n hn))
        (hP_nonneg m n)
    · rw [if_neg hm]
  have hrow_finite_bound : ∀ n : ℕ, 2 ≤ n -> ∀ s : Finset ℕ,
      (∑ m ∈ s,
        if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0) ≤ 1 := by
    intro n hn s
    let r : Finset ℕ := s.filter (fun m => 2 ≤ m ∧ m ≠ n ∧ P m n ≠ 0)
    have hmul_div : ∀ m ∈ r, m = n * (m / n) ∧ 1 < m / n := by
      intro m hm
      have hm' : 2 ≤ m ∧ m ≠ n ∧ P m n ≠ 0 := by
        have hm'' : m ∈ s ∧ (2 ≤ m ∧ m ≠ n ∧ P m n ≠ 0) := by
          simpa [r] using hm
        exact hm''.2
      have hsupp := hP_support m n hm'.1 hm'.2.2
      have hlt : n < m := by
        rcases hsupp.2 with hdiag | hlt
        · exact False.elim (hm'.2.1 hdiag.1.symm)
        · exact hlt
      have hmul : m = n * (m / n) := (Nat.mul_div_cancel' hsupp.1).symm
      have hqpos : 0 < m / n := by
        by_contra hqnot
        have hqzero : m / n = 0 := Nat.eq_zero_of_not_pos hqnot
        rw [hmul, hqzero, Nat.mul_zero] at hlt
        omega
      have hqne : m / n ≠ 1 := by
        intro hqone
        rw [hmul, hqone, Nat.mul_one] at hm'
        exact hm'.2.1 rfl
      have hqgt : 1 < m / n := by omega
      exact ⟨hmul, hqgt⟩
    have hsum_restrict :
        (∑ m ∈ s,
          if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0) =
            ∑ m ∈ r, erdos_weight m / erdos_weight n * P m n := by
      dsimp [r]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmcond : 2 ≤ m ∧ m ≠ n
      · by_cases hpmn : P m n = 0
        · rw [if_pos hmcond, hpmn, mul_zero]
          simp
        · rw [if_pos hmcond]
          have hpred : 2 ≤ m ∧ m ≠ n ∧ P m n ≠ 0 := ⟨hmcond.1, hmcond.2, hpmn⟩
          rw [if_pos hpred]
      · rw [if_neg hmcond]
        have hpred : ¬(2 ≤ m ∧ m ≠ n ∧ P m n ≠ 0) := by
          intro h
          exact hmcond ⟨h.1, h.2.1⟩
        rw [if_neg hpred]
    have hsum_image_raw :
        (∑ q ∈ r.image (fun m => m / n),
          if 1 < q then erdos_weight (n * q) / erdos_weight n * P (n * q) n else 0) =
            ∑ m ∈ r,
              if 1 < m / n then
                erdos_weight (n * (m / n)) / erdos_weight n * P (n * (m / n)) n
              else 0 := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      have ha_eq := (hmul_div a ha).1
      have hb_eq := (hmul_div b hb).1
      change a / n = b / n at hab
      rw [ha_eq, hb_eq, hab]
    have hsum_image_congr :
        (∑ m ∈ r,
          if 1 < m / n then
            erdos_weight (n * (m / n)) / erdos_weight n * P (n * (m / n)) n
          else 0) =
            ∑ m ∈ r, erdos_weight m / erdos_weight n * P m n := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmd := hmul_div m hm
      rw [if_pos hmd.2, ← hmd.1]
    have hsum_image :
        (∑ m ∈ r, erdos_weight m / erdos_weight n * P m n) =
          ∑ q ∈ r.image (fun m => m / n),
            if 1 < q then erdos_weight (n * q) / erdos_weight n * P (n * q) n else 0 := by
      exact (hsum_image_raw.trans hsum_image_congr).symm
    have hscale_eq :
        (∑ q ∈ r.image (fun m => m / n),
          if 1 < q then erdos_weight (n * q) / erdos_weight n * P (n * q) n else 0) =
            (1 / erdos_weight n) *
              ∑ q ∈ r.image (fun m => m / n),
                if 1 < q then erdos_weight (n * q) * P (n * q) n else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqone : 1 < q
      · rw [if_pos hqone, if_pos hqone]
        ring
      · rw [if_neg hqone, if_neg hqone]
        ring
    have hscaled_le :
        (1 / erdos_weight n) *
          (∑ q ∈ r.image (fun m => m / n),
            if 1 < q then erdos_weight (n * q) * P (n * q) n else 0) ≤ 1 := by
      have hsub := hP_subfin n hn (r.image (fun m => m / n))
      have hmul := mul_le_mul_of_nonneg_left hsub
        (div_nonneg zero_le_one (hweight_nonneg n hn))
      calc
        (1 / erdos_weight n) *
            (∑ q ∈ r.image (fun m => m / n),
              if 1 < q then erdos_weight (n * q) * P (n * q) n else 0) ≤
            (1 / erdos_weight n) * erdos_weight n := hmul
        _ = 1 := by
            field_simp [(hweight_pos n hn).ne']
    calc
      (∑ m ∈ s,
        if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0) =
          ∑ m ∈ r, erdos_weight m / erdos_weight n * P m n := hsum_restrict
      _ = ∑ q ∈ r.image (fun m => m / n),
            if 1 < q then erdos_weight (n * q) / erdos_weight n * P (n * q) n else 0 := hsum_image
      _ = (1 / erdos_weight n) *
            ∑ q ∈ r.image (fun m => m / n),
              if 1 < q then erdos_weight (n * q) * P (n * q) n else 0 := hscale_eq
      _ ≤ 1 := hscaled_le
  have hrow_tsum_bound : ∀ n : ℕ, 2 ≤ n ->
      (∑' m : ℕ,
        if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0) ≤ 1 := by
    intro n hn
    apply tsum_le_of_sum_le'
    · norm_num
    · intro s
      exact hrow_finite_bound n hn s
  have hrow_tsum_eq : ∀ n : ℕ, 2 ≤ n ->
      (∑' m : ℕ, if 2 ≤ m then U (some n) (some m) else 0) =
        ∑' m : ℕ,
          if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0 := by
    intro n hn
    apply tsum_congr
    intro m
    by_cases hm : 2 ≤ m
    · by_cases hmn : m ≠ n
      · simp [U, hn, hm, hmn]
      · simp [U, hn, hm, hmn]
    · have hnot : ¬(2 ≤ m ∧ m ≠ n) := by
        intro h
        exact hm h.1
      simp [U, hm]
  have hrow_finset_eq : ∀ n : ℕ, 2 ≤ n -> ∀ s : Finset ℕ,
      (∑ m ∈ s, if 2 ≤ m then U (some n) (some m) else 0) =
        ∑ m ∈ s,
          if 2 ≤ m ∧ m ≠ n then erdos_weight m / erdos_weight n * P m n else 0 := by
    intro n hn s
    apply Finset.sum_congr rfl
    intro m hm_mem
    by_cases hm : 2 ≤ m
    · by_cases hmn : m ≠ n
      · simp [U, hn, hm, hmn]
      · simp [U, hn, hm, hmn]
    · have hnot : ¬(2 ≤ m ∧ m ≠ n) := by
        intro h
        exact hm h.1
      simp [U, hm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    cases a with
    | none =>
      cases b <;> simp [U]
    | some n =>
      cases b with
      | none =>
        by_cases hn : 2 ≤ n
        · simp [U, hn, sub_nonneg.mpr (hrow_tsum_bound n hn)]
        · simp [U, hn]
      | some m =>
        by_cases hcond : 2 ≤ n ∧ 2 ≤ m ∧ m ≠ n
        · dsimp [U]
          rw [if_pos hcond]
          exact mul_nonneg
            (div_nonneg (hweight_nonneg m hcond.2.1) (hweight_nonneg n hcond.1))
            (hP_nonneg m n)
        · dsimp [U]
          rw [if_neg hcond]
  · intro n hn
    rw [hrow_tsum_eq n hn]
    simp [U, hn]
  · intro n hn s
    rw [hrow_finset_eq n hn s]
    exact hrow_finite_bound n hn s
  · simp [U]
  · intro m
    simp [U]
  · intro n hn
    simp [U, hn]
  · intro n m hn hm hne
    simp [U, hn, hm, hne]
  · intro n m hne
    by_cases hcond : 2 ≤ n ∧ 2 ≤ m ∧ m ≠ n
    · have hpmn : P m n ≠ 0 := by
        intro hp
        apply hne
        simp [U, hcond, hp]
      have hsupp := hP_support m n hcond.2.1 hpmn
      have hlt : n < m := by
        rcases hsupp.2 with hdiag | hlt
        · exact False.elim (hcond.2.2 hdiag.1.symm)
        · exact hlt
      rcases hsupp.1 with ⟨q, hqeq⟩
      have hqgt : 1 < q := by
        have hqpos : 0 < q := by
          by_contra hqnot
          have hqzero : q = 0 := Nat.eq_zero_of_not_pos hqnot
          rw [hqzero, Nat.mul_zero] at hqeq
          omega
        have hqne : q ≠ 1 := by
          intro hqone
          rw [hqone, Nat.mul_one] at hqeq
          omega
        omega
      exact ⟨hcond.1, hcond.2.1, ⟨q, hqgt, hqeq⟩⟩
    · exfalso
      apply hne
      simp [U, hcond]
  · intro n hn
    simp [U, hn]

lemma eps_adjoint_hitting_mass_facts_from_adjoint_kernel {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ} :
    eps_modified_chain_kernel_subinvariant P -> eps_adjoint_kernel_package P U ->
      eps_adjoint_hitting_mass_facts U erdos_weight := by
  classical
  intro hP hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [erdos_weight]
    positivity
  · intro n hn
    rcases hP with
      ⟨hP_nonneg, hP_row, hP_one_one, hP_one_zero, hP_prime_one, hP_prime_zero,
        hP_support, hP_ordinary, hP_prime_power_base, hP_prime_power_step,
        hP_prime_power_support, hP_subinv, hP_subinv_finite⟩
    rcases hU with
      ⟨hU_nonneg, hU_row, hU_finite_row, hU_none_none, hU_none_some,
        hU_diag_zero, hU_formula, hU_support, hU_slack⟩
    by_cases hnprime : n ∈ prime_layer
    · have hnprime_nat : Nat.Prime n := by
        simpa [prime_layer] using hnprime
      have hsum_zero :
          (∑' (q : ℕ),
            if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
              erdos_weight (n / q) * U (some (n / q)) (some n)
            else 0) = 0 := by
        have hfun_zero :
            (fun q : ℕ =>
              if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
                erdos_weight (n / q) * U (some (n / q)) (some n)
              else 0) = fun _ : ℕ => 0 := by
          funext q
          by_cases hq : 1 < q ∧ q ∣ n ∧ 2 ≤ n / q
          · have hq_ne_one : q ≠ 1 := by omega
            have hn_eq_q : n = q := (Nat.Prime.dvd_iff_eq hnprime_nat hq_ne_one).mp hq.2.1
            have hquot : n / q = 1 := by
              rw [← hn_eq_q]
              exact Nat.div_self hnprime_nat.pos
            omega
          · simp [hq]
        rw [hfun_zero]
        simp
      simp [Set.indicator_of_mem hnprime, hsum_zero]
    · have hn_pos : 0 < n := by omega
      have hn_ne_zero : n ≠ 0 := by omega
      have hP_n_one : P n 1 = 0 := by
        by_contra hP_n_one_ne
        by_cases hnpp : IsPrimePow n
        · rcases (isPrimePow_nat_iff n).mp hnpp with ⟨p, k, hp, hkpos, hpk⟩
          have hp_layer : p ∈ prime_layer := by
            simpa [prime_layer] using hp
          have hk_two : 2 ≤ k := by
            by_contra hk_not_two
            have hk_one : k = 1 := by omega
            subst k
            rw [pow_one] at hpk
            have hn_prime_nat : Nat.Prime n := hpk ▸ hp
            exact hnprime (by simpa [prime_layer] using hn_prime_nat)
          have hsupport_one :
              1 = p ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ k - 2 ∧ 1 = p ^ (k - j) := by
            exact hP_prime_power_support p k 1 hp_layer hk_two (by simpa [hpk] using hP_n_one_ne)
          rcases hsupport_one with h_eq_p | ⟨j, hj_one, hj_le, h_eq_pow⟩
          · exact hp.ne_one h_eq_p.symm
          · have hexp_ne_zero : k - j ≠ 0 := by omega
            have hpow_gt : 1 < p ^ (k - j) := Nat.one_lt_pow hexp_ne_zero hp.one_lt
            exact (ne_of_gt hpow_gt) h_eq_pow.symm
        · have hn_not_prime_power_clause :
              ∀ p k : ℕ, p ∈ prime_layer -> 2 ≤ k -> n ≠ p ^ k := by
            intro p k hp hk hnk
            apply hnpp
            rw [isPrimePow_nat_iff]
            exact ⟨p, k, by simpa [prime_layer] using hp, by omega, hnk.symm⟩
          have hordinary := hP_ordinary n n hn hnprime hn_not_prime_power_clause (by omega) dvd_rfl
          have hLambda_zero : ArithmeticFunction.vonMangoldt n = 0 :=
            (ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr hnpp
          have hP_n_one_zero : P n 1 = 0 := by
            simpa [Nat.div_self hn_pos, hLambda_zero] using hordinary
          exact hP_n_one_ne hP_n_one_zero
      have hP_n_self : P n n = 0 := by
        by_contra hP_n_self_ne
        have hsupport_self := hP_support n n hn hP_n_self_ne
        rcases hsupport_self.2 with hprime_case | hlt
        · exact hnprime hprime_case.2
        · exact (Nat.lt_irrefl n) hlt
      let G : ℕ → ℝ := fun m => if 2 ≤ m ∧ m ≠ n then P n m else 0
      have hG_eq_P : G = fun m : ℕ => P n m := by
        funext m
        dsimp [G]
        by_cases hm : 2 ≤ m ∧ m ≠ n
        · simp [hm]
        · have hP_zero : P n m = 0 := by
            by_cases hm_one : m = 1
            · subst m
              exact hP_n_one
            · by_cases hm_self : m = n
              · subst m
                exact hP_n_self
              · have hm_not_two : ¬2 ≤ m := by
                  intro hm_two
                  exact hm ⟨hm_two, hm_self⟩
                have hm_zero : m = 0 := by omega
                subst m
                by_contra hP_n_zero_ne
                have hsupport_zero := hP_support n 0 hn hP_n_zero_ne
                rcases hsupport_zero.1 with ⟨c, hc⟩
                omega
          simp [hm, hP_zero]
      have hG_tsum : (∑' m : ℕ, G m) = 1 := by
        rw [hG_eq_P]
        exact hP_row n (by omega)
      have hP_qsum :
          (∑' (q : ℕ), if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) = 1 := by
        have hq_fin :
            (∑' (q : ℕ), if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) =
              ∑ q ∈ n.divisors, if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0 := by
          refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := n.divisors)
            (f := fun q : ℕ => if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) ?_
          intro q hq_not_mem
          have hq_not_dvd : ¬q ∣ n := by
            intro hq_dvd
            exact hq_not_mem (Nat.mem_divisors.mpr ⟨hq_dvd, hn_ne_zero⟩)
          simp [hq_not_dvd]
        have hG_fin :
            (∑' m : ℕ, G m) = ∑ m ∈ n.divisors, G m := by
          refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := n.divisors) (f := G) ?_
          intro m hm_not_mem
          dsimp [G]
          by_cases hm : 2 ≤ m ∧ m ≠ n
          · by_cases hP_nm : P n m = 0
            · simp [hm, hP_nm]
            · have hsupport_m := hP_support n m hn hP_nm
              exact False.elim (hm_not_mem (Nat.mem_divisors.mpr ⟨hsupport_m.1, hn_ne_zero⟩))
          · simp [hm]
        have hfin_reindex :
            (∑ q ∈ n.divisors, if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) =
              ∑ m ∈ n.divisors, G m := by
          calc
            (∑ q ∈ n.divisors, if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0)
                = ∑ q ∈ n.divisors, G (n / q) := by
                  refine Finset.sum_congr rfl ?_
                  intro q hq_mem
                  have hq_dvd : q ∣ n := (Nat.mem_divisors.mp hq_mem).1
                  have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hq_dvd hn_pos
                  by_cases hq_one : q = 1
                  · subst q
                    simp [G]
                  · have hq_gt_one : 1 < q := by omega
                    have hquot_ne : n / q ≠ n := by
                      have hquot_lt : n / q < n := Nat.div_lt_self hn_pos hq_gt_one
                      omega
                    simp [G, hq_gt_one, hq_dvd, hquot_ne]
            _ = ∑ m ∈ n.divisors, G m := Nat.sum_div_divisors n G
        rw [hq_fin, hfin_reindex]
        rw [← hG_fin]
        exact hG_tsum
      have hweighted_sum :
          (∑' (q : ℕ),
            if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
              erdos_weight (n / q) * U (some (n / q)) (some n)
            else 0) = erdos_weight n := by
        have hterm_eq : ∀ q : ℕ,
            (if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
              erdos_weight (n / q) * U (some (n / q)) (some n)
            else 0) =
              erdos_weight n *
                (if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) := by
          intro q
          by_cases hq : 1 < q ∧ q ∣ n ∧ 2 ≤ n / q
          · have hquot_ne_n : n ≠ n / q := by
              have hquot_lt : n / q < n := Nat.div_lt_self hn_pos hq.1
              omega
            have hweight_quot_ne : erdos_weight (n / q) ≠ 0 := by
              have hquot_pos : 0 < ((n / q : ℕ) : ℝ) := by
                exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq.2.2)
              have hlog_pos : 0 < Real.log ((n / q : ℕ) : ℝ) := by
                apply Real.log_pos
                exact_mod_cast (Nat.lt_of_lt_of_le Nat.one_lt_two hq.2.2)
              rw [erdos_weight]
              exact ne_of_gt (one_div_pos.mpr (mul_pos hquot_pos hlog_pos))
            rw [if_pos hq, if_pos hq]
            rw [hU_formula (n / q) n hq.2.2 hn hquot_ne_n]
            field_simp [hweight_quot_ne]
          · simp [hq]
        calc
          (∑' (q : ℕ),
            if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
              erdos_weight (n / q) * U (some (n / q)) (some n)
            else 0)
              = ∑' q : ℕ,
                  erdos_weight n *
                    (if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) := by
                exact tsum_congr hterm_eq
          _ = erdos_weight n *
                (∑' q : ℕ, if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then P n (n / q) else 0) := by
                rw [tsum_mul_left]
          _ = erdos_weight n := by
                rw [hP_qsum, mul_one]
      simp [Set.indicator_of_notMem hnprime, hweighted_sum]
  · intro n
    rfl
  · rcases erdos_sarkozy_szemeredi_1196 with ⟨C, hC⟩
    have hprim : primitive_set prime_layer := by
      rw [primitive_set]
      intro a ha b hb hne hdiv
      have hpa : Nat.Prime a := by
        simpa [prime_layer] using ha
      have hpb : Nat.Prime b := by
        simpa [prime_layer] using hb
      have hb_eq_a : b = a := (Nat.Prime.dvd_iff_eq hpb hpa.ne_one).mp hdiv
      exact hne hb_eq_a.symm
    have hsupp : supported_above prime_layer 2 := by
      intro n hn
      have hnprime : Nat.Prime n := by
        simpa [prime_layer] using hn
      exact_mod_cast hnprime.two_le
    exact (hC.bound 2 (by norm_num) prime_layer hprim hsupp).1

lemma eps_adjoint_pathwise_primitive_chain_antichain_bound {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ} {h : ℕ → ℝ} :
    eps_adjoint_kernel_package P U -> eps_adjoint_hitting_mass_facts U h ->
      eps_adjoint_primitive_chain_antichain_facts h := by
  classical
  intro hU hh
  have hfinite : ∀ A : Set ℕ, primitive_set A -> ∀ s : Finset ℕ,
      (∑ n ∈ s, A.indicator h n) ≤
        ∑' n : ℕ, prime_layer.indicator h n := by
    intro A hA s
    rcases hU with
      ⟨hU_nonneg, hU_row_tsum, hU_row_fin, hU_none_none, hU_none_some,
        hU_diag, hU_adjoint, hU_support, hU_slack⟩
    rcases hh with ⟨hh_nonneg, hh_rec, hh_eq, hh_prime_summ⟩
    let T : Finset ℕ := s.filter (fun n => n ∈ A ∧ 2 ≤ n)
    let D : Finset ℕ := T.biUnion (fun a => a.divisors.filter (fun d => 2 ≤ d))
    let N : Finset ℕ := D.filter (fun n => n ∉ T)
    have hD_two : ∀ n : ℕ, n ∈ D -> 2 ≤ n := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      exact (Finset.mem_filter.mp hn).2
    have hT_subset_D : T ⊆ D := by
      intro n hnT
      have hnT' : n ∈ s ∧ n ∈ A ∧ 2 ≤ n := by
        simpa [T] using hnT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨n, hnT, ?_⟩
      have hn_ne : n ≠ 0 := by omega
      simp [hnT'.2.2, hn_ne]
    have hD_dvd_active : ∀ n : ℕ, n ∈ D -> ∃ a : ℕ, a ∈ T ∧ n ∣ a := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      have hn' := Finset.mem_filter.mp hn
      exact ⟨a, haT, (Nat.mem_divisors.mp hn'.1).1⟩
    have hD_pred : ∀ {n p : ℕ}, n ∈ D -> p ∣ n -> 2 ≤ p -> p ∈ D := by
      intro n p hnD hpn hp2
      rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
      have hpa : p ∣ a := dvd_trans hpn hna
      have haT' : a ∈ s ∧ a ∈ A ∧ 2 ≤ a := by
        simpa [T] using haT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨a, haT, ?_⟩
      have ha_ne : a ≠ 0 := by omega
      simp [hp2, Nat.mem_divisors.mpr ⟨hpa, ha_ne⟩]
    have hsmall : ∀ n : ℕ, ¬ 2 ≤ n -> h n = 0 := by
      intro n hn
      have hcases : n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl
      · rw [hh_eq 0, erdos_weight]
        norm_num
      · rw [hh_eq 1, erdos_weight]
        norm_num
    have hleft_eq : (∑ n ∈ s, A.indicator h n) = ∑ n ∈ T, h n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnA : n ∈ A
      · by_cases hn2 : 2 ≤ n
        · simp [hnA, hn2]
        · simp [hnA, hn2, hsmall n hn2]
      · simp [hnA]
    have hsum_D_split : (∑ n ∈ D, h n) = (∑ n ∈ T, h n) + ∑ n ∈ N, h n := by
      have hfilter_T : D.filter (fun n => n ∈ T) = T := by
        ext n
        by_cases hnT : n ∈ T
        · simp [hnT, hT_subset_D hnT]
        · simp [hnT]
      have hpartition := Finset.sum_filter_add_sum_filter_not
        (s := D) (p := fun n => n ∈ T) (f := fun n => h n)
      rw [hfilter_T] at hpartition
      simpa [N, add_comm] using hpartition.symm
    have hincoming_le_N : ∀ n : ℕ, n ∈ D ->
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
      intro n hnD
      let f : ℕ → ℝ := fun q =>
        if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
          h (n / q) * U (some (n / q)) (some n)
        else 0
      let Q : Finset ℕ := n.divisors.filter (fun q => 1 < q ∧ q ∣ n ∧ 2 ≤ n / q)
      have hn_ne : n ≠ 0 := by
        have hn2 := hD_two n hnD
        omega
      have htsum_eq : (∑' q : ℕ, f q) = ∑ q ∈ n.divisors, f q := by
        exact tsum_eq_sum (s := n.divisors) (fun q hq => by
          dsimp [f]
          by_cases hcond : 1 < q ∧ q ∣ n ∧ 2 ≤ n / q
          · exfalso
            exact hq (Nat.mem_divisors.mpr ⟨hcond.2.1, hn_ne⟩)
          · simp [hcond])
      have hsum_filter : (∑ q ∈ n.divisors, f q) =
          ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
        dsimp [Q, f]
        exact (Finset.sum_filter (s := n.divisors)
          (p := fun q => 1 < q ∧ q ∣ n ∧ 2 ≤ n / q)
          (f := fun q => h (n / q) * U (some (n / q)) (some n))).symm
      have hinj : ∀ q ∈ Q, ∀ r ∈ Q, n / q = n / r -> q = r := by
        intro q hq r hr hqr
        have hq' : 1 < q ∧ q ∣ n ∧ 2 ≤ n / q := (Finset.mem_filter.mp hq).2
        have hr' : 1 < r ∧ r ∣ n ∧ 2 ≤ n / r := (Finset.mem_filter.mp hr).2
        have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
        have hrmul : n / r * r = n := Nat.div_mul_cancel hr'.2.1
        have hqpos : 0 < n / q := by omega
        apply Nat.mul_left_cancel hqpos
        calc
          n / q * q = n := hqmul
          _ = n / r * r := hrmul.symm
          _ = n / q * r := by rw [hqr]
      have hsum_image : (∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n)) =
          ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := by
        symm
        rw [Finset.sum_image]
        intro q hq r hr hqr
        exact hinj q hq r hr hqr
      have himage_subset : Q.image (fun q => n / q) ⊆ N := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨q, hqQ, rfl⟩
        have hq' : 1 < q ∧ q ∣ n ∧ 2 ≤ n / q := (Finset.mem_filter.mp hqQ).2
        have hpred_dvd : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hq'.2.1).symm⟩
        have hpredD : n / q ∈ D := hD_pred hnD hpred_dvd hq'.2.2
        have hpred_not_T : n / q ∉ T := by
          intro hpT
          rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
          have hpT' : n / q ∈ s ∧ n / q ∈ A ∧ 2 ≤ n / q := by
            simpa [T] using hpT
          have haT' : a ∈ s ∧ a ∈ A ∧ 2 ≤ a := by
            simpa [T] using haT
          have hp_dvd_a : n / q ∣ a := dvd_trans hpred_dvd hna
          have hpa_eq : n / q = a := hA.eq hpT'.2.1 haT'.2.1 hp_dvd_a
          subst a
          have hn_le_pred : n ≤ n / q := Nat.le_of_dvd (by omega) hna
          have hpred_lt_n : n / q < n := by
            have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
            calc
              n / q < n / q * q :=
                (Nat.lt_mul_iff_one_lt_right (a := n / q) (b := q) (by omega)).mpr hq'.1
              _ = n := hqmul
          omega
        simp [N, hpredD, hpred_not_T]
      calc
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) = ∑' q : ℕ, f q := rfl
        _ = ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
          rw [htsum_eq, hsum_filter]
        _ = ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := hsum_image
        _ ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro p hpN hpnot
            exact mul_nonneg (hh_nonneg p) (hU_nonneg (some p) (some n))
    have hbalance : (∑ n ∈ D, h n) ≤
        (∑ n ∈ D, prime_layer.indicator h n) +
          ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
      calc
        (∑ n ∈ D, h n) =
            ∑ n ∈ D,
              (prime_layer.indicator h n +
                ∑' q : ℕ,
                  if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
                    h (n / q) * U (some (n / q)) (some n)
                  else 0) := by
              apply Finset.sum_congr rfl
              intro n hnD
              calc
                h n = prime_layer.indicator erdos_weight n +
                    ∑' q : ℕ,
                      if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
                        h (n / q) * U (some (n / q)) (some n)
                      else 0 := hh_rec n (hD_two n hnD)
                _ = prime_layer.indicator h n +
                    ∑' q : ℕ,
                      if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
                        h (n / q) * U (some (n / q)) (some n)
                      else 0 := by
                      congr 1
                      by_cases hnprime : n ∈ prime_layer
                      · simp [Set.indicator_of_mem hnprime, hh_eq n]
                      · simp [Set.indicator_of_notMem hnprime]
        _ ≤ ∑ n ∈ D,
              (prime_layer.indicator h n +
                ∑ p ∈ N, h p * U (some p) (some n)) := by
              apply Finset.sum_le_sum
              intro n hnD
              exact add_le_add le_rfl (hincoming_le_N n hnD)
        _ = (∑ n ∈ D, prime_layer.indicator h n) +
              ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.sum_comm]
    have hout_le : (∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n)) ≤
        ∑ p ∈ N, h p := by
      apply Finset.sum_le_sum
      intro p hpN
      have hpD : p ∈ D := (Finset.mem_filter.mp hpN).1
      have hp2 : 2 ≤ p := hD_two p hpD
      have hrow : (∑ n ∈ D, U (some p) (some n)) ≤ 1 := by
        have hrow' := hU_row_fin p hp2 D
        convert hrow' using 1
        apply Finset.sum_congr rfl
        intro n hnD
        simp [hD_two n hnD]
      calc
        (∑ n ∈ D, h p * U (some p) (some n)) =
            h p * ∑ n ∈ D, U (some p) (some n) := by
              rw [Finset.mul_sum]
        _ ≤ h p * 1 := mul_le_mul_of_nonneg_left hrow (hh_nonneg p)
        _ = h p := by ring
    have hinit_le : (∑ n ∈ D, prime_layer.indicator h n) ≤
        ∑' n : ℕ, prime_layer.indicator h n := by
      exact hh_prime_summ.sum_le_tsum D (fun n hn => by
        by_cases hnprime : n ∈ prime_layer
        · rw [Set.indicator_of_mem hnprime]
          exact hh_nonneg n
        · rw [Set.indicator_of_notMem hnprime])
    have hactive_le_init : (∑ n ∈ T, h n) ≤
        ∑ n ∈ D, prime_layer.indicator h n := by
      have hsplit := hsum_D_split
      have hb := hbalance
      have ho := hout_le
      linarith
    rw [hleft_eq]
    exact le_trans hactive_le_init hinit_le
  intro A hA
  have hnonneg : ∀ n : ℕ, 0 ≤ A.indicator h n := by
    intro n
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn]
      exact hh.nonneg n
    · rw [Set.indicator_of_notMem hn]
  have hsumm : Summable (fun n : ℕ => A.indicator h n) :=
    summable_of_sum_range_le hnonneg (fun N => hfinite A hA (Finset.range N))
  exact ⟨hfinite A hA, hsumm, hsumm.tsum_le_of_sum_range_le
    (fun N => hfinite A hA (Finset.range N))⟩

/-- The adjoint chain only moves along proper upward divisibility steps. -/
lemma eps_adjoint_kernel_some_some_eq_zero_of_not_forward {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ}
    (hU : eps_adjoint_kernel_package P U) {n m : ℕ}
    (hnot : ¬ (2 ≤ n ∧ 2 ≤ m ∧ ∃ q : ℕ, 1 < q ∧ m = n * q)) :
    U (some n) (some m) = 0 := by
  by_contra hne
  exact hnot (hU.support n m hne)

/-- Paper equation `\eqref{nu-recurse}` for the constructed EPS adjoint chain. -/
lemma eps_adjoint_erdos_weight_recurrence
    {U : Option ℕ → Option ℕ → ℝ} {h : ℕ → ℝ}
    (hh : eps_adjoint_hitting_mass_facts U h) {n : ℕ} (hn : 2 ≤ n) :
    erdos_weight n =
      prime_layer.indicator erdos_weight n +
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ 2 ≤ n / q then
            erdos_weight (n / q) * U (some (n / q)) (some n)
          else 0) := by
  simpa [hh.equals_erdos] using hh.recurrence n hn

/-- Paper inequality `\eqref{psum-weight-upper}` for the EPS hitting mass. -/
lemma eps_adjoint_primitive_hitting_mass_bound {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ} {h : ℕ → ℝ}
    (hU : eps_adjoint_kernel_package P U)
    (hh : eps_adjoint_hitting_mass_facts U h)
    {A : Set ℕ} (hA : primitive_set A) :
    Summable (fun n : ℕ => A.indicator h n) ∧
      (∑' n : ℕ, A.indicator h n) ≤
        ∑' n : ℕ, prime_layer.indicator h n := by
  rcases eps_adjoint_pathwise_primitive_chain_antichain_bound hU hh A hA with
    ⟨_, hAsumm, hAle⟩
  exact ⟨hAsumm, hAle⟩

lemma eps_adjoint_hitting_mass_package_from_subinvariant :
    (∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P) ->
      ∃ P : ℕ → ℕ → ℝ,
        ∃ U : Option ℕ → Option ℕ → ℝ,
          ∃ h : ℕ → ℝ,
            eps_modified_chain_kernel_subinvariant P ∧
              eps_adjoint_kernel_package P U ∧
                eps_adjoint_hitting_mass_facts U h ∧
                  eps_adjoint_primitive_chain_antichain_facts h := by
  rintro ⟨P, hP⟩
  rcases eps_adjoint_kernel_package_from_subinvariant hP with ⟨U, hU⟩
  have hh : eps_adjoint_hitting_mass_facts U erdos_weight :=
    eps_adjoint_hitting_mass_facts_from_adjoint_kernel hP hU
  have hprim : eps_adjoint_primitive_chain_antichain_facts erdos_weight :=
    eps_adjoint_pathwise_primitive_chain_antichain_bound hU hh
  exact ⟨P, U, erdos_weight, hP, hU, hh, hprim⟩

lemma eps_modified_chain_hitting_mass_identity :
    (∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P) ->
      Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
        ∀ A : Set ℕ, primitive_set A ->
          Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
            erdos_sum A ≤ erdos_sum prime_layer := by
  intro hsub
  rcases eps_adjoint_hitting_mass_package_from_subinvariant hsub with
    ⟨_, _, h, _, _, hh, hprim⟩
  rcases hh with ⟨_, _, h_eq, hprime⟩
  constructor
  · simpa [Set.indicator, h_eq] using hprime
  · intro A hA
    rcases hprim A hA with ⟨_, hAsumm, hAle⟩
    constructor
    · simpa [Set.indicator, h_eq] using hAsumm
    · simpa [erdos_sum, Set.indicator, h_eq] using hAle

lemma eps_chain_antichain_bound :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer :=
  eps_modified_chain_hitting_mass_identity eps_modified_chain_subinvariant

theorem erdos_primitive_set_conjecture_164 :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer :=
  eps_chain_antichain_bound

def real_initial_segment (x : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x}

noncomputable def erdos_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  erdos_sum (A ∩ real_initial_segment x)

noncomputable def upper_doubly_log_density (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => erdos_sum_up_to A x / Real.log (Real.log x))
    Filter.atTop

noncomputable def mangoldt_weight (n : ℕ) : ℝ :=
  if n = 1 then 1 else
    ∫ s : ℝ in Set.Ioi (1 : ℝ),
      Real.log (n : ℝ) /
        (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s)

noncomputable def mangoldt_weight_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (A ∩ real_initial_segment x).indicator mangoldt_weight n

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

noncomputable def chain_hits_count_up_to (n : ℕ → ℕ) (A : Set ℕ) (x : ℝ) : ℕ :=
  Set.ncard {i : ℕ | n i ∈ A ∧ (n i : ℝ) ≤ x}

noncomputable def upper_chain_hit_density (n : ℕ → ℕ) (A : Set ℕ) : ENNReal :=
  Filter.limsup
    (fun x : ℝ => ENNReal.ofReal
      ((chain_hits_count_up_to n A x : ℝ) / Real.log (Real.log x)))
    Filter.atTop

abbrev chain_hits_density_at_least (n : ℕ → ℕ) (A : Set ℕ) (Delta : ℝ) : Prop :=
  ENNReal.ofReal Delta ≤ upper_chain_hit_density n A

lemma log_square_tail_summable :
    Summable (fun n : ℕ =>
      if 2 ≤ n then 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) else 0) := by
  refine
    (summable_condensed_iff_of_eventually_nonneg
      (f := fun n : ℕ =>
        if 2 ≤ n then 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) else 0) ?_ ?_).mp ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    simp only [hn, if_true, Pi.zero_apply, one_div, mul_inv_rev]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
    have hn_one : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_one
    have hden_pos : 0 < (n : ℝ) * Real.log (n : ℝ) ^ 2 :=
      mul_pos hn_pos (pow_pos hlog_pos 2)
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
      le_of_lt (one_div_pos.mpr hden_pos)
  · filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hk_succ : 2 ≤ k + 1 := le_trans hk (Nat.le_succ k)
    simp only [hk, hk_succ, if_true, Nat.cast_add, Nat.cast_one, one_div, mul_inv_rev,
      ge_iff_le]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk)
    have hk_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk)
    have hk_le_succ : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have hlog_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (le_of_lt hk_one)
    have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_one
    have hlog_le : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk_pos hk_le_succ
    have hlog_sq_le : Real.log (k : ℝ) ^ 2 ≤ Real.log ((k + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [mul_self_le_mul_self hlog_nonneg hlog_le]
    have hden_le :
        (k : ℝ) * Real.log (k : ℝ) ^ 2 ≤
          ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) ^ 2 := by
      exact mul_le_mul hk_le_succ hlog_sq_le (sq_nonneg _) (by exact_mod_cast Nat.zero_le (k + 1))
    have hden_pos : 0 < (k : ℝ) * Real.log (k : ℝ) ^ 2 :=
      mul_pos hk_pos (pow_pos hlog_pos 2)
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
      one_div_le_one_div_of_le hden_pos hden_le
  · refine
      ((Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2)).mul_left
        (1 / (Real.log 2) ^ 2)).congr_atTop ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk_ne : k ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hk)
    have hpow_ge : 2 ≤ 2 ^ k := by
      exact Nat.succ_le_of_lt (Nat.one_lt_two_pow hk_ne)
    simp [hpow_ge, Nat.cast_pow, Real.log_pow, one_div, mul_comm, mul_left_comm, mul_pow]

lemma reciprocal_zeta_second_order_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ u : ℝ, 0 < u -> u ≤ δ ->
        |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤ C * u ^ 2 := by
  have hshift :
      Filter.Tendsto (fun u : ℝ => 1 + u) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : ContinuousAt (fun u : ℝ => 1 + u) 0 :=
        continuousAt_const.add continuousAt_id
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      rw [Set.mem_Ioi] at hu ⊢
      linarith
  have h0 :
      Filter.Tendsto
        (fun u : ℝ =>
          (((fun s : ℝ => riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)) (1 + u))).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Real.eulerMascheroniConstant) := by
    exact (Complex.continuous_re.tendsto (Real.eulerMascheroniConstant : ℂ)).comp
      (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp hshift)
  have hzeta :
      Filter.Tendsto (fun u : ℝ => (riemannZeta ((1 + u : ℝ) : ℂ)).re - u⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Real.eulerMascheroniConstant) := by
    refine Filter.Tendsto.congr' ?_ h0
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Set.mem_Ioi] at hu
    simp [sub_eq_add_neg]
  let B : ℝ := |Real.eulerMascheroniConstant| + 1
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg Real.eulerMascheroniConstant]
  have hB_event :
      ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖(riemannZeta ((1 + u : ℝ) : ℂ)).re - u⁻¹‖ ≤ B := by
    have hlt :
        ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ‖(riemannZeta ((1 + u : ℝ) : ℂ)).re - u⁻¹‖ < B := by
      dsimp [B]
      simpa [Real.norm_eq_abs] using
        (hzeta.norm.eventually_lt_const (by
          rw [Real.norm_eq_abs]
          linarith [abs_nonneg Real.eulerMascheroniConstant]))
    exact hlt.mono (fun u hu => le_of_lt hu)
  have hB_nhds := eventually_nhdsWithin_iff.mp hB_event
  rcases Metric.eventually_nhds_iff.mp hB_nhds with ⟨ε, hεpos, hε⟩
  refine ⟨min (ε / 2) (1 / (2 * B)), 2 * B, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (one_div_pos.mpr (mul_pos (by norm_num) hBpos))
  · positivity
  · intro u hu hule
    let z : ℝ := (riemannZeta ((1 + u : ℝ) : ℂ)).re
    have hzpos : 0 < z := by
      dsimp [z]
      exact riemannZeta_re_pos_of_one_lt (by linarith)
    have hdist : dist u (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu]
      have hle_eps : u ≤ ε / 2 := le_trans hule (min_le_left _ _)
      linarith
    have hb_norm : ‖z - u⁻¹‖ ≤ B := by
      dsimp [z]
      exact hε hdist (by simpa [Set.mem_Ioi] using hu)
    have hb_abs : |z - u⁻¹| ≤ B := by
      simpa [Real.norm_eq_abs] using hb_norm
    have hb_abs' : |u⁻¹ - z| ≤ B := by
      simpa [abs_sub_comm] using hb_abs
    have hsmall : B * u ≤ 1 / 2 := by
      have huleB : u ≤ 1 / (2 * B) := le_trans hule (min_le_right _ _)
      have hmul := mul_le_mul_of_nonneg_left huleB (le_of_lt hBpos)
      have hcalc : B * (1 / (2 * B)) = 1 / 2 := by
        field_simp [hBpos.ne']
      nlinarith
    have hB_le_inv : B ≤ 1 / (2 * u) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hu)]
      nlinarith [hsmall]
    have hlower1 : u⁻¹ - B ≤ z := by
      have hneg : u⁻¹ - z ≤ |z - u⁻¹| := by
        simpa [abs_sub_comm] using neg_le_abs (z - u⁻¹)
      linarith [hneg, hb_abs]
    have hhalf_le : 1 / (2 * u) ≤ u⁻¹ - B := by
      have hsplit : u⁻¹ - 1 / (2 * u) = 1 / (2 * u) := by
        field_simp [hu.ne']
        ring
      linarith
    have hz_ge : 1 / (2 * u) ≤ z := le_trans hhalf_le hlower1
    have hzinv_le : 1 / z ≤ 2 * u := by
      have hhalf_pos : 0 < 1 / (2 * u) := one_div_pos.mpr (mul_pos (by norm_num) hu)
      simpa [one_div, inv_inv] using one_div_le_one_div_of_le hhalf_pos hz_ge
    have herr_eq : 1 / z - u = (u * (u⁻¹ - z)) / z := by
      field_simp [hu.ne', hzpos.ne']
    calc
      |1 / z - u| = |(u * (u⁻¹ - z)) / z| := by rw [herr_eq]
      _ = u * |u⁻¹ - z| / z := by
        rw [abs_div, abs_mul, abs_of_pos hu, abs_of_pos hzpos]
      _ ≤ u * B / z := by gcongr
      _ = (u * B) * (1 / z) := by ring
      _ ≤ (u * B) * (2 * u) := by gcongr
      _ = 2 * B * u ^ 2 := by ring

lemma mangoldt_weight_integral_change_of_variables_ioi_translate_one (F : ℝ → ℝ) :
    (∫ s : ℝ in Set.Ioi (1 : ℝ), F s) =
      ∫ u : ℝ in Set.Ioi (0 : ℝ), F (u + 1) := by
  rw [← MeasureTheory.integral_indicator
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))]
  rw [← MeasureTheory.integral_add_right_eq_self
    (f := (Set.Ioi (1 : ℝ)).indicator F) (g := (1 : ℝ))]
  rw [← MeasureTheory.integral_indicator
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases hu : 0 < u
  · have hmem1 : u + 1 ∈ Set.Ioi (1 : ℝ) := by
      simpa [Set.mem_Ioi] using add_lt_add_right hu (1 : ℝ)
    have hmem0 : u ∈ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_Ioi] using hu
    simp [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem0]
  · have hnot1 : u + 1 ∉ Set.Ioi (1 : ℝ) := by
      simp [Set.mem_Ioi] at hu ⊢
      linarith
    have hnot0 : u ∉ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_Ioi] using hu
    simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot0]

lemma mangoldt_weight_integral_change_of_variables_erdos_laplace
    (n : ℕ) (hn : 2 ≤ n) :
    erdos_weight n =
      (1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u) := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hkernel :
      (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u) =
        1 / Real.log (n : ℝ) := by
    have hfun :
        (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u) =
          fun u : ℝ => Real.log (n : ℝ) *
            (u * Real.exp (-(Real.log (n : ℝ) * u))) := by
      funext u
      change Real.log (n : ℝ) * ((n : ℝ) ^ (-u)) * u =
        Real.log (n : ℝ) * (u * Real.exp (-(Real.log (n : ℝ) * u)))
      rw [Real.rpow_def_of_pos hn_pos]
      ring_nf
    calc
      (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u)
          = ∫ u : ℝ in Set.Ioi (0 : ℝ),
              Real.log (n : ℝ) * (u * Real.exp (-(Real.log (n : ℝ) * u))) := by
              rw [hfun]
      _ = Real.log (n : ℝ) *
            (∫ u : ℝ in Set.Ioi (0 : ℝ),
              u * Real.exp (-(Real.log (n : ℝ) * u))) := by
              rw [MeasureTheory.integral_const_mul]
      _ = Real.log (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) := by
              rw [log_square_integral_kernel_local (Real.log (n : ℝ)) hlog_pos]
      _ = 1 / Real.log (n : ℝ) := by
              field_simp [hlog_pos.ne']
  rw [erdos_weight, hkernel]
  field_simp [hlog_pos.ne', hn_pos.ne']

lemma mangoldt_weight_integral_change_of_variables_mangoldt_laplace
    (n : ℕ) (hn : 2 ≤ n) :
    mangoldt_weight n =
      (1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))) := by
  have hn_ne_one : n ≠ 1 := by omega
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  rw [mangoldt_weight, if_neg hn_ne_one]
  rw [mangoldt_weight_integral_change_of_variables_ioi_translate_one]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem
    (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
  have hu_pos : 0 < u := by
    simpa [Set.mem_Ioi] using hu
  have hz_pos : 0 < (riemannZeta ((u + 1 : ℝ) : ℂ)).re := by
    exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < u + 1)
  have hz_pos' : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
    exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
  have hrpow_pos : 0 < Real.rpow (n : ℝ) u := Real.rpow_pos_of_pos hn_pos u
  have hrpow_add_pos : 0 < Real.rpow (n : ℝ) (u + 1) :=
    Real.rpow_pos_of_pos hn_pos (u + 1)
  rw [show (↑(u + 1 : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by norm_num [add_comm]]
  change Real.log (n : ℝ) /
      ((riemannZeta ((1 + u : ℝ) : ℂ)).re * ((n : ℝ) ^ (u + 1))) =
    1 / (n : ℝ) *
      (Real.log (n : ℝ) * ((n : ℝ) ^ (-u)) *
        (1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re))
  rw [Real.rpow_add hn_pos u 1, Real.rpow_one]
  rw [Real.rpow_neg hn_pos.le u]
  field_simp [hz_pos'.ne', hn_pos.ne', hrpow_pos.ne']

lemma mangoldt_weight_integral_change_of_variables_one_le_zeta_re
    {x : ℝ} (hx : 1 < x) :
    1 ≤ (riemannZeta (x : ℂ)).re := by
  let f : ℕ → ℝ := fun n => (1 / (((n + 1 : ℕ) : ℂ) ^ (x : ℂ))).re
  have hxC : 1 < ((x : ℂ).re) := by
    simpa using hx
  have hfC : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ (x : ℂ))) := by
    simpa using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℂ) ^ (x : ℂ))) 1).2
        (Complex.summable_one_div_nat_cpow.mpr hxC)
  have hf : Summable f := by
    simpa [f] using Complex.reCLM.summable hfC
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have hterm : f n = 1 / (((n + 1 : ℕ) : ℝ) ^ x) := by
      have hbase_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      calc
        f n = (1 / (((((n + 1 : ℕ) : ℝ) : ℂ) ^ (x : ℂ)))).re := by
          simp [f]
        _ = (1 / ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ)).re := by
          rw [← Complex.ofReal_cpow hbase_nonneg x]
        _ = 1 / (((n + 1 : ℕ) : ℝ) ^ x) := by
          simp
    rw [hterm]
    positivity
  have hle_tsum : f 0 ≤ ∑' n : ℕ, f n := by
    have htail_nonneg : 0 ≤ ∑' n : ℕ, f (n + 1) := by
      exact tsum_nonneg fun n => hf_nonneg (n + 1)
    have hsum_split : (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := by
      exact hf.tsum_eq_zero_add
    rw [hsum_split]
    exact le_add_of_nonneg_right htail_nonneg
  have hf_zero : f 0 = 1 := by
    simp [f]
  have hzeta : (riemannZeta (x : ℂ)).re = ∑' n : ℕ, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC]
    simpa [f, Nat.cast_add, Nat.cast_one] using Complex.re_tsum hfC
  linarith

lemma mangoldt_weight_integral_change_of_variables_erdos_kernel_integrable
    (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u)
      (Set.Ioi 0) := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hfun :
      (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u) =
        fun u : ℝ => Real.log (n : ℝ) *
          (u * Real.exp (-(Real.log (n : ℝ) * u))) := by
    funext u
    change Real.log (n : ℝ) * ((n : ℝ) ^ (-u)) * u =
      Real.log (n : ℝ) * (u * Real.exp (-(Real.log (n : ℝ) * u)))
    rw [Real.rpow_def_of_pos hn_pos]
    ring_nf
  rw [hfun]
  exact (log_square_integral_kernel_integrable_local
    (Real.log (n : ℝ)) hlog_pos).const_mul (Real.log (n : ℝ))

lemma mangoldt_weight_integral_change_of_variables_zeta_kernel_integrable
    (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
        (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)))
      (Set.Ioi 0) := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hbase_int : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u))
      (Set.Ioi 0) := by
    have hexp : MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp ((-Real.log (n : ℝ)) * u))
        (Set.Ioi 0) := by
      exact integrableOn_exp_mul_Ioi (by linarith : -Real.log (n : ℝ) < 0) 0
    have hfun :
        (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u)) =
          fun u : ℝ => Real.log (n : ℝ) *
            Real.exp ((-Real.log (n : ℝ)) * u) := by
      funext u
      change Real.log (n : ℝ) * ((n : ℝ) ^ (-u)) =
        Real.log (n : ℝ) * Real.exp ((-Real.log (n : ℝ)) * u)
      rw [Real.rpow_def_of_pos hn_pos]
      ring_nf
    rw [hfun]
    exact hexp.const_mul (Real.log (n : ℝ))
  refine MeasureTheory.Integrable.mono' hbase_int ?_ ?_
  · have hfun_meas :
        (fun u : ℝ => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))) =
          fun u : ℝ => Real.log (n : ℝ) *
            Real.exp ((-Real.log (n : ℝ)) * u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) := by
      funext u
      change Real.log (n : ℝ) * ((n : ℝ) ^ (-u)) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) =
        Real.log (n : ℝ) * Real.exp ((-Real.log (n : ℝ)) * u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))
      rw [Real.rpow_def_of_pos hn_pos]
      ring_nf
    rw [hfun_meas]
    have hzeta_cont : ContinuousOn
        (fun u : ℝ => riemannZeta ((1 + u : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) := by
      intro u hu
      have hu_pos : 0 < u := by
        simpa [Set.mem_Ioi] using hu
      have hne : ((1 + u : ℝ) : ℂ) ≠ 1 := by
        norm_num [Complex.ext_iff]
        linarith
      have hzeta_ofReal_cont : ContinuousAt
          (fun y : ℝ => riemannZeta (y : ℂ)) (1 + u) := by
        simpa [Function.comp_def] using
          (differentiableAt_riemannZeta hne).continuousAt.comp
            Complex.continuous_ofReal.continuousAt
      have hlin : ContinuousAt (fun u : ℝ => 1 + u) u := by
        fun_prop
      simpa [Function.comp_def] using
        (hzeta_ofReal_cont.comp hlin).continuousWithinAt
    have hden_cont : ContinuousOn
        (fun u : ℝ => (riemannZeta ((1 + u : ℝ) : ℂ)).re) (Set.Ioi (0 : ℝ)) := by
      simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn hzeta_cont
    have hrec_cont : ContinuousOn
        (fun u : ℝ => 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re) (Set.Ioi (0 : ℝ)) := by
      have hinv := hden_cont.inv₀ (fun u hu => by
        exact (riemannZeta_re_pos_of_one_lt (by
          have hu_pos : 0 < u := by simpa [Set.mem_Ioi] using hu
          linarith : 1 < 1 + u)).ne')
      simpa [one_div] using hinv
    have hnum_cont : ContinuousOn
        (fun u : ℝ => Real.log (n : ℝ) * Real.exp ((-Real.log (n : ℝ)) * u))
        (Set.Ioi (0 : ℝ)) := by
      fun_prop
    exact (hnum_cont.mul hrec_cont).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
    have hu_pos : 0 < u := by
      simpa [Set.mem_Ioi] using hu
    have hz_pos : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
      exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
    have hz_one_le : 1 ≤ (riemannZeta ((1 + u : ℝ) : ℂ)).re :=
      mangoldt_weight_integral_change_of_variables_one_le_zeta_re
        (by linarith : 1 < 1 + u)
    have hrec_nonneg : 0 ≤ 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
      exact one_div_nonneg.mpr hz_pos.le
    have hrec_le_one : 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 := by
      exact (div_le_one₀ hz_pos).2 hz_one_le
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (-u) :=
      Real.rpow_nonneg hn_pos.le (-u)
    have hbase_nonneg : 0 ≤ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) :=
      mul_nonneg hlog_pos.le hrpow_nonneg
    have hprod_nonneg :
        0 ≤ Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
          (1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re) :=
      mul_nonneg hbase_nonneg hrec_nonneg
    rw [Real.norm_of_nonneg hprod_nonneg]
    exact mul_le_of_le_one_right hbase_nonneg hrec_le_one

lemma mangoldt_weight_integral_change_of_variables :
    ∀ n : ℕ, 2 ≤ n ->
      mangoldt_weight n - erdos_weight n =
        (1 / (n : ℝ)) *
          (∫ u : ℝ in Set.Ioi 0,
            Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
              (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)) := by
  intro n hn
  let f : ℝ → ℝ := fun u => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
    (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))
  let g : ℝ → ℝ := fun u => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) * u
  have hz_int : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    simpa [f] using mangoldt_weight_integral_change_of_variables_zeta_kernel_integrable n hn
  have he_int : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    simpa [g] using mangoldt_weight_integral_change_of_variables_erdos_kernel_integrable n hn
  have hsub := MeasureTheory.integral_sub
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) hz_int he_int
  rw [mangoldt_weight_integral_change_of_variables_mangoldt_laplace n hn,
    mangoldt_weight_integral_change_of_variables_erdos_laplace n hn]
  change (1 / (n : ℝ)) * (∫ u : ℝ in Set.Ioi 0, f u) -
      (1 / (n : ℝ)) * (∫ u : ℝ in Set.Ioi 0, g u) =
    (1 / (n : ℝ)) *
      (∫ u : ℝ in Set.Ioi 0,
        Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u))
  calc
    (1 / (n : ℝ)) * (∫ u : ℝ in Set.Ioi 0, f u) -
        (1 / (n : ℝ)) * (∫ u : ℝ in Set.Ioi 0, g u)
        = (1 / (n : ℝ)) *
          ((∫ u : ℝ in Set.Ioi 0, f u) - (∫ u : ℝ in Set.Ioi 0, g u)) := by
          ring
    _ = (1 / (n : ℝ)) *
          (∫ u : ℝ in Set.Ioi 0, f u - g u) := by
          rw [← hsub]
    _ = (1 / (n : ℝ)) *
          (∫ u : ℝ in Set.Ioi 0,
            Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
              (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          dsimp [f, g]
          ring

lemma mangoldt_weight_laplace_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n ->
      |(1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0,
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u))| ≤
        C * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) := by
  rcases reciprocal_zeta_second_order_bound with ⟨δ, C₀, hδ_pos, hC₀_nonneg, hlocal⟩
  let K : ℝ := max C₀ (δ⁻¹ ^ 2 + δ⁻¹)
  have hK_nonneg : 0 ≤ K := le_trans hC₀_nonneg (le_max_left _ _)
  have hglobal : ∀ u : ℝ, 0 < u ->
      |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤ K * u ^ 2 := by
    intro u hu_pos
    by_cases hu_le_delta : u ≤ δ
    · exact le_trans (hlocal u hu_pos hu_le_delta) (by gcongr; exact le_max_left _ _)
    · have hdelta_lt_u : δ < u := lt_of_not_ge hu_le_delta
      have hdelta_le_u : δ ≤ u := le_of_lt hdelta_lt_u
      have hz_pos : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
        exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
      have hz_one_le : 1 ≤ (riemannZeta ((1 + u : ℝ) : ℂ)).re :=
        mangoldt_weight_integral_change_of_variables_one_le_zeta_re
          (by linarith : 1 < 1 + u)
      have hrec_nonneg : 0 ≤ 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
        exact one_div_nonneg.mpr hz_pos.le
      have hrec_le_one : 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 := by
        exact (div_le_one₀ hz_pos).2 hz_one_le
      have herr_linear : |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤ 1 + u := by
        calc
          |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤
              |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)| + |u| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) (-u)
          _ = 1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) + u := by
              rw [abs_of_nonneg hrec_nonneg, abs_of_pos hu_pos]
          _ ≤ 1 + u := by linarith
      have hinv_mul : 1 ≤ δ⁻¹ * u := by
        have hmul := mul_le_mul_of_nonneg_left hdelta_le_u (le_of_lt (inv_pos.mpr hδ_pos))
        rwa [inv_mul_cancel₀ hδ_pos.ne'] at hmul
      have h_one_quad : 1 ≤ δ⁻¹ ^ 2 * u ^ 2 := by
        nlinarith [sq_nonneg (δ⁻¹ * u), hinv_mul]
      have h_u_quad : u ≤ δ⁻¹ * u ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hinv_mul hu_pos.le
        nlinarith
      have htail_quad : 1 + u ≤ (δ⁻¹ ^ 2 + δ⁻¹) * u ^ 2 := by
        nlinarith
      exact le_trans herr_linear (le_trans htail_quad (by gcongr; exact le_max_right _ _))
  refine ⟨2 * K, by nlinarith [hK_nonneg], ?_⟩
  intro n hn
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  let L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by simpa [L] using hlog_pos
  have hquad_base_int : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ 2 * Real.exp (-(L * u))) (Set.Ioi 0) := by
    have hhalf_ne : L / 2 ≠ 0 := by positivity
    have hrate_pos : -L + L / 2 < 0 := by linarith
    have hrate_neg : -L - L / 2 < 0 := by linarith
    have hint_pos : MeasureTheory.Integrable
        (fun u : ℝ => Real.exp ((-L + L / 2) * u))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_Ioi hrate_pos 0
    have hint_neg : MeasureTheory.Integrable
        (fun u : ℝ => Real.exp ((-L - L / 2) * u))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_Ioi hrate_neg 0
    have h := ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (X := fun u : ℝ => u) (v := -L) (t := L / 2)
      hhalf_ne hint_pos hint_neg 2
    change MeasureTheory.Integrable
      (fun u : ℝ => u ^ 2 * Real.exp (-(L * u)))
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    convert h using 1
    ext u
    rw [show -(L * u) = -L * u by ring]
  have hquad_int : MeasureTheory.Integrable
      (fun u : ℝ => L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hscaled := hquad_base_int.const_mul (K * L)
    convert hscaled using 1
    ext u
    change L * ((n : ℝ) ^ (-u)) * (K * u ^ 2) = K * L * (u ^ 2 * Real.exp (-(L * u)))
    rw [Real.rpow_def_of_pos hn_pos]
    simp [L, mul_comm, mul_left_comm, mul_assoc]
  have hquad_base_eval :
      (∫ u : ℝ in Set.Ioi 0, u ^ 2 * Real.exp (-(L * u))) = 2 / L ^ 3 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (3 : ℝ)) (r := L) (by norm_num) hL_pos
    calc
      (∫ u : ℝ in Set.Ioi 0, u ^ 2 * Real.exp (-(L * u))) =
          ∫ u : ℝ in Set.Ioi 0, u ^ ((3 : ℝ) - 1) * Real.exp (-(L * u)) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            have hu_nonneg : 0 ≤ u := le_of_lt (by simpa [Set.mem_Ioi] using hu)
            norm_num [Real.rpow_natCast, hu_nonneg]
      _ = (1 / L) ^ (3 : ℝ) * Real.Gamma 3 := h
      _ = 2 / L ^ 3 := by
            norm_num [Real.Gamma_ofNat_eq_factorial]
            field_simp [hL_pos.ne']
  have hquad_eval :
      (∫ u : ℝ in Set.Ioi 0, L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2)) =
        K * (2 / L ^ 2) := by
    have hfun : (fun u : ℝ => L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2)) =
        fun u : ℝ => (K * L) * (u ^ 2 * Real.exp (-(L * u))) := by
      funext u
      change L * ((n : ℝ) ^ (-u)) * (K * u ^ 2) = K * L * (u ^ 2 * Real.exp (-(L * u)))
      rw [Real.rpow_def_of_pos hn_pos]
      simp [L, mul_comm, mul_left_comm, mul_assoc]
    calc
      (∫ u : ℝ in Set.Ioi 0, L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2)) =
          ∫ u : ℝ in Set.Ioi 0, (K * L) * (u ^ 2 * Real.exp (-(L * u))) := by
            rw [hfun]
      _ = (K * L) * (∫ u : ℝ in Set.Ioi 0, u ^ 2 * Real.exp (-(L * u))) := by
            rw [MeasureTheory.integral_const_mul]
      _ = (K * L) * (2 / L ^ 3) := by rw [hquad_base_eval]
      _ = K * (2 / L ^ 2) := by
            field_simp [hL_pos.ne']
  have hintegral_bound :
      |∫ u : ℝ in Set.Ioi 0,
        L * Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)| ≤ K * (2 / L ^ 2) := by
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (f := fun u : ℝ => L * Real.rpow (n : ℝ) (-u) *
        (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u))
      (g := fun u : ℝ => L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2))
      hquad_int ?_
    · change ‖∫ u : ℝ in Set.Ioi 0,
        L * Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)‖ ≤
          (∫ u : ℝ in Set.Ioi 0, L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2)) at hnorm
      rw [hquad_eval] at hnorm
      simpa [Real.norm_eq_abs] using hnorm
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
      have hu_pos : 0 < u := by simpa [Set.mem_Ioi] using hu
      have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (-u) := Real.rpow_nonneg hn_pos.le (-u)
      have hbase_nonneg : 0 ≤ L * Real.rpow (n : ℝ) (-u) := mul_nonneg hL_pos.le hrpow_nonneg
      have herr := hglobal u hu_pos
      calc
        ‖L * Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)‖ =
            |L * Real.rpow (n : ℝ) (-u) *
              (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)| := by
              rw [Real.norm_eq_abs]
        _ = L * Real.rpow (n : ℝ) (-u) *
              |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| := by
              rw [abs_mul, abs_of_nonneg hbase_nonneg]
        _ ≤ L * Real.rpow (n : ℝ) (-u) * (K * u ^ 2) := by
              exact mul_le_mul_of_nonneg_left herr hbase_nonneg
  have hscale_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  calc
    |(1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0,
          Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u))| =
        (1 / (n : ℝ)) *
          |∫ u : ℝ in Set.Ioi 0,
            L * Real.rpow (n : ℝ) (-u) *
              (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u)| := by
          rw [abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ (1 / (n : ℝ)) * (K * (2 / L ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hintegral_bound hscale_nonneg
    _ = (2 * K) * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) := by
          field_simp [hn_pos.ne', hL_pos.ne']
          simp [L]

lemma mangoldt_weight_erdos_pointwise_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n ->
      |mangoldt_weight n - erdos_weight n| ≤
        C * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) := by
  rcases mangoldt_weight_laplace_error_bound with ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro n hn
  rw [mangoldt_weight_integral_change_of_variables n hn]
  exact hC_bound n hn

lemma mangoldt_weight_erdos_summable_error :
    Summable (fun n : ℕ => |mangoldt_weight n - erdos_weight n|) := by
  rcases mangoldt_weight_erdos_pointwise_error_bound with ⟨C, hC_nonneg, hC_bound⟩
  have hmajorant : Summable (fun n : ℕ =>
      C * (if 2 ≤ n then 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) else 0)) := by
    exact log_square_tail_summable.mul_left C
  refine Summable.of_norm_bounded_eventually_nat hmajorant ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simpa [hn, Real.norm_eq_abs] using hC_bound n hn

lemma summable_error_limsup_transfer_vanishing_perturbation {f g : ℝ → ℝ}
    (hfg : Filter.Tendsto (fun x : ℝ => |f x - g x|) Filter.atTop (nhds (0 : ℝ))) :
    Filter.limsup f Filter.atTop = Filter.limsup g Filter.atTop := by
  have hbounded_left {p q : ℝ → ℝ}
      (hpq : Filter.Tendsto (fun x : ℝ => |p x - q x|) Filter.atTop (nhds (0 : ℝ)))
      (hq : Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) q) :
      Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) p := by
    have hpq_one : ∀ᶠ x in Filter.atTop, |p x - q x| < (1 : ℝ) := by
      exact hpq.eventually (eventually_lt_nhds zero_lt_one)
    obtain ⟨B, hB⟩ := hq.eventually_le
    refine Filter.isBoundedUnder_of_eventually_le (f := Filter.atTop) (u := p) (a := B + 1) ?_
    filter_upwards [hB, hpq_one] with x hqx hx
    have hpx : p x - q x < 1 := (abs_lt.mp hx).2
    linarith
  have hcobounded_left {p q : ℝ → ℝ}
      (hpq : Filter.Tendsto (fun x : ℝ => |p x - q x|) Filter.atTop (nhds (0 : ℝ)))
      (hq : Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) q) :
      Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) p := by
    have hpq_one : ∀ᶠ x in Filter.atTop, |p x - q x| < (1 : ℝ) := by
      exact hpq.eventually (eventually_lt_nhds zero_lt_one)
    obtain ⟨B, hB⟩ := hq.frequently_ge
    refine Filter.IsCoboundedUnder.of_frequently_ge (f := Filter.atTop) (u := p) (a := B - 1) ?_
    refine (hB.and_eventually hpq_one).mono ?_
    intro x hx
    rcases hx with ⟨hqx, hxabs⟩
    have hpx : -(1 : ℝ) < p x - q x := (abs_lt.mp hxabs).1
    linarith
  have hle_of {p q : ℝ → ℝ}
      (hpq : Filter.Tendsto (fun x : ℝ => |p x - q x|) Filter.atTop (nhds (0 : ℝ)))
      (hpb : Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) p)
      (hpc : Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) p)
      (hqb : Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) q) :
      Filter.limsup p Filter.atTop ≤ Filter.limsup q Filter.atTop := by
    rw [Filter.limsup_le_iff' hpc hpb]
    intro y hy
    obtain ⟨z, hzq, hzy⟩ := exists_between hy
    have hε : 0 < y - z := sub_pos.mpr hzy
    have hpq_eps : ∀ᶠ x in Filter.atTop, |p x - q x| < y - z := by
      exact hpq.eventually (eventually_lt_nhds hε)
    have hqz : ∀ᶠ x in Filter.atTop, q x < z := by
      exact Filter.eventually_lt_of_limsup_lt hzq hqb
    filter_upwards [hpq_eps, hqz] with x hx hqx
    have hpq_lt : p x - q x < y - z := (abs_lt.mp hx).2
    linarith
  by_cases hfb : Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) f
  · by_cases hfc : Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) f
    · have hgf : Filter.Tendsto (fun x : ℝ => |g x - f x|) Filter.atTop (nhds (0 : ℝ)) := by
        simpa [abs_sub_comm] using hfg
      have hgb : Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) g :=
        hbounded_left (p := g) (q := f) hgf hfb
      have hgc : Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) g :=
        hcobounded_left (p := g) (q := f) hgf hfc
      exact le_antisymm (hle_of (p := f) (q := g) hfg hfb hfc hgb)
        (hle_of (p := g) (q := f) hgf hgb hgc hfb)
    · have hgnotc : ¬ Filter.atTop.IsCoboundedUnder (fun a b : ℝ => a ≤ b) g := by
        intro hgc
        exact hfc (hcobounded_left (p := f) (q := g) hfg hgc)
      rw [Real.limsup_of_not_isCoboundedUnder hfc, Real.limsup_of_not_isCoboundedUnder hgnotc]
  · have hgnotb : ¬ Filter.atTop.IsBoundedUnder (fun a b : ℝ => a ≤ b) g := by
      intro hgb
      exact hfb (hbounded_left (p := f) (q := g) hfg hgb)
    rw [Real.limsup_of_not_isBoundedUnder hfb, Real.limsup_of_not_isBoundedUnder hgnotb]

lemma summable_error_limsup_transfer_truncated_error_bound {w v : ℕ → ℝ}
    (h : Summable (fun n : ℕ => |w n - v n|)) (A : Set ℕ) (x : ℝ) :
    |(∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) -
      (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n)| ≤
      ∑' n : ℕ, |w n - v n| := by
  let S : Set ℕ := A ∩ real_initial_segment x
  change |(∑' n : ℕ, S.indicator w n) - (∑' n : ℕ, S.indicator v n)| ≤
    ∑' n : ℕ, |w n - v n|
  have hfin : S.Finite := by
    exact (((Set.finite_le_nat ⌊x⌋₊).subset (by
      intro n hn
      exact Nat.le_floor hn.2)).inter_of_right A)
  have hsumm (F : ℕ → ℝ) : Summable (fun n : ℕ => S.indicator F n) :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (by
      intro n hn
      exact Set.indicator_of_notMem (fun hmem => hn (hfin.mem_toFinset.mpr hmem)) F)
  have hdiff : (∑' n : ℕ, S.indicator w n) - (∑' n : ℕ, S.indicator v n) =
      ∑' n : ℕ, S.indicator (fun n => w n - v n) n := by
    rw [← (hsumm w).tsum_sub (hsumm v)]
    congr 1
    ext n
    by_cases hn : n ∈ S <;> simp [hn]
  have hnorm_summ : Summable (fun n : ℕ => ‖S.indicator (fun n => w n - v n) n‖) :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (by
      intro n hn
      have hnot : n ∉ S := fun hmem => hn (hfin.mem_toFinset.mpr hmem)
      simp [Set.indicator_of_notMem hnot])
  have hnorm_eq : (∑' n : ℕ, ‖S.indicator (fun n => w n - v n) n‖) =
      ∑' n : ℕ, S.indicator (fun n => |w n - v n|) n := by
    apply tsum_congr
    intro n
    by_cases hn : n ∈ S <;> simp [hn, Real.norm_eq_abs]
  have hind_le : (∑' n : ℕ, S.indicator (fun n => |w n - v n|) n) ≤
      ∑' n : ℕ, |w n - v n| := by
    exact Summable.tsum_le_tsum
      (by
        intro n
        by_cases hn : n ∈ S <;> simp [hn, abs_nonneg])
      (hsumm (fun n => |w n - v n|)) h
  rw [hdiff]
  calc
    |∑' n : ℕ, S.indicator (fun n => w n - v n) n| ≤
        ∑' n : ℕ, ‖S.indicator (fun n => w n - v n) n‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm_summ
    _ = ∑' n : ℕ, S.indicator (fun n => |w n - v n|) n := hnorm_eq
    _ ≤ ∑' n : ℕ, |w n - v n| := hind_le

lemma summable_error_limsup_transfer {w v : ℕ → ℝ}
    (h : Summable (fun n : ℕ => |w n - v n|)) :
    ∀ A : Set ℕ,
      Filter.limsup
        (fun x : ℝ =>
          (∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) /
            Real.log (Real.log x))
        Filter.atTop =
      Filter.limsup
        (fun x : ℝ =>
          (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n) /
            Real.log (Real.log x))
        Filter.atTop := by
  intro A
  let F : ℝ → ℝ := fun x : ℝ =>
    (∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) / Real.log (Real.log x)
  let G : ℝ → ℝ := fun x : ℝ =>
    (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n) / Real.log (Real.log x)
  let C : ℝ := ∑' n : ℕ, |w n - v n|
  change Filter.limsup F Filter.atTop = Filter.limsup G Filter.atTop
  apply summable_error_limsup_transfer_vanishing_perturbation
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hCdiv :
      Filter.Tendsto (fun x : ℝ => C / Real.log (Real.log x)) Filter.atTop
        (nhds (0 : ℝ)) :=
    hloglog.const_div_atTop C
  have hden_pos : ∀ᶠ x in Filter.atTop, 0 < Real.log (Real.log x) :=
    hloglog.eventually_gt_atTop (0 : ℝ)
  have hscaled_bound : ∀ᶠ x in Filter.atTop, |F x - G x| ≤ C / Real.log (Real.log x) := by
    filter_upwards [hden_pos] with x hx
    have hden_nonneg : 0 ≤ Real.log (Real.log x) := le_of_lt hx
    have htrunc := summable_error_limsup_transfer_truncated_error_bound h A x
    dsimp [F, G, C]
    calc
      |(∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) / Real.log (Real.log x) -
          (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n) / Real.log (Real.log x)| =
          |(∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) -
            (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n)| / Real.log (Real.log x) := by
        rw [show (∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) / Real.log (Real.log x) -
            (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n) / Real.log (Real.log x) =
            ((∑' n : ℕ, (A ∩ real_initial_segment x).indicator w n) -
              (∑' n : ℕ, (A ∩ real_initial_segment x).indicator v n)) /
              Real.log (Real.log x) by ring]
        rw [abs_div, abs_of_pos hx]
      _ ≤ (∑' n : ℕ, |w n - v n|) / Real.log (Real.log x) :=
        div_le_div_of_nonneg_right htrunc hden_nonneg
  have hnonneg : ∀ᶠ x in Filter.atTop, 0 ≤ |F x - G x| := by
    filter_upwards with x
    exact abs_nonneg (F x - G x)
  exact squeeze_zero' hnonneg hscaled_bound hCdiv

lemma mangoldt_weight_aggregate_comparison :
    ∀ A : Set ℕ,
      Filter.limsup
        (fun x : ℝ => mangoldt_weight_sum_up_to A x / Real.log (Real.log x))
        Filter.atTop = upper_doubly_log_density A := by
  intro A
  simpa [mangoldt_weight_sum_up_to, upper_doubly_log_density, erdos_sum_up_to, erdos_sum]
    using (summable_error_limsup_transfer (w := mangoldt_weight) (v := erdos_weight)
      mangoldt_weight_erdos_summable_error A)

noncomputable def mangoldt_weight_upper_density (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => mangoldt_weight_sum_up_to A x / Real.log (Real.log x))
    Filter.atTop

abbrev mangoldt_adjoint_visit_identity {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ n : ℕ, (∑' k : ℕ, μ {ω : Ω | path ω k = n}) = ENNReal.ofReal (mangoldt_weight n)

noncomputable def mangoldt_adjoint_hit_second_moment {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) (A : Set ℕ) (x : ℝ) : ENNReal :=
  ∑' i : ℕ, ∑' j : ℕ,
    μ {ω : Ω |
      path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
        path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}

abbrev mangoldt_adjoint_second_moment_bound {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in Filter.atTop,
    0 < Real.log (Real.log x) ∧
      mangoldt_adjoint_hit_second_moment μ path A x ≤
        ENNReal.ofReal (C * (Real.log (Real.log x)) ^ 2)

abbrev mangoldt_adjoint_reverse_fatou_extraction_principle {Ω : Type}
    [MeasurableSpace Ω] (_μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
    ∃ ω : Ω, chain_hits_density_at_least (path ω) A (mangoldt_weight_upper_density A)

structure mangoldt_von_mangoldt_downward_kernel_invariant
    (P : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ n m : ℕ, 0 ≤ P n m
  row : ∀ n : ℕ, 1 ≤ n -> (∑' m : ℕ, P n m) = 1
  one_one : P 1 1 = 1
  one_zero : ∀ m : ℕ, m ≠ 1 -> P 1 m = 0
  support : ∀ n m : ℕ, 2 ≤ n -> P n m ≠ 0 -> m ∣ n ∧ m < n
  rule : ∀ n q : ℕ, 2 ≤ n -> 1 < q -> q ∣ n ->
    P n (n / q) = ArithmeticFunction.vonMangoldt q / Real.log (n : ℝ)
  incoming : ∀ n : ℕ, 1 ≤ n ->
    (∑' q : ℕ, if 1 < q then mangoldt_weight (n * q) * P (n * q) n else 0) =
      mangoldt_weight n

lemma mangoldt_weight_incoming_integral_bridge_deriv_identity
    (s : ℝ) (hs : 1 < s) :
    deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s =
      (1 / ((riemannZeta (s : ℂ)).re)) * mangoldt_dirichlet_series (s - 1) := by
  have hu : 0 < s - 1 := by linarith
  have hz_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  have hz_diff : DifferentiableAt ℂ riemannZeta (s : ℂ) :=
    differentiableAt_riemannZeta (by
      norm_num [Complex.ext_iff]
      linarith)
  have hbase_has : HasDerivAt
      (fun t : ℝ => (riemannZeta (t : ℂ)).re)
      (deriv riemannZeta (s : ℂ)).re s := by
    exact hz_diff.hasDerivAt.real_of_complex
  have hrecip_deriv :
      deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s =
        - (deriv riemannZeta (s : ℂ)).re / ((riemannZeta (s : ℂ)).re) ^ 2 := by
    have hfun :
        (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) =
          fun t : ℝ => ((riemannZeta (t : ℂ)).re)⁻¹ := by
      funext t
      rw [one_div]
    rw [hfun]
    exact (hbase_has.inv hz_pos.ne').deriv
  have hdir_real :
      mangoldt_dirichlet_series (s - 1) =
        (- deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re := by
    have h := congrArg Complex.re
      (mangoldt_dirichlet_series_eq_zeta_log_derivative (s - 1) hu)
    simpa using h
  have hz_im : (riemannZeta (s : ℂ)).im = 0 :=
    riemannZeta_im_eq_zero_of_one_lt hs
  have hdiv_re :
      (- deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re =
        - (deriv riemannZeta (s : ℂ)).re / (riemannZeta (s : ℂ)).re := by
    rw [Complex.div_re]
    simp [hz_im]
    field_simp [Complex.normSq, hz_im, hz_pos.ne']
    rw [Complex.normSq_apply, hz_im]
    ring
  rw [hrecip_deriv, hdir_real, hdiv_re]
  field_simp [hz_pos.ne']

lemma mangoldt_weight_incoming_integral_bridge_rhs_laplace
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ s : ℝ in Set.Ioi (1 : ℝ),
        deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s /
          Real.rpow (n : ℝ) s) =
      (1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            mangoldt_dirichlet_series u) := by
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  rw [mangoldt_weight_integral_change_of_variables_ioi_translate_one]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem
    (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
  have hu_pos : 0 < u := by simpa [Set.mem_Ioi] using hu
  have hs : 1 < u + 1 := by linarith
  have hpow_pos : 0 < Real.rpow (n : ℝ) u := Real.rpow_pos_of_pos hn_pos u
  rw [mangoldt_weight_incoming_integral_bridge_deriv_identity (u + 1) hs]
  rw [show ((u + 1 : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by norm_num [add_comm]]
  simp [show u + 1 - 1 = u by ring, Real.rpow_add hn_pos u 1, Real.rpow_one,
    Real.rpow_neg hn_pos.le u]
  field_simp [hn_pos.ne', hpow_pos.ne']

lemma mangoldt_weight_incoming_integral_bridge_term_laplace
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 < q) :
    mangoldt_weight (n * q) *
        (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ)) =
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / (n : ℝ)) *
          (Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            (ArithmeticFunction.vonMangoldt q /
              Real.rpow (q : ℝ) (1 + u))) := by
  have hq_two : 2 ≤ q := by omega
  have hnq_two : 2 ≤ n * q := by
    exact Nat.mul_le_mul hn hq_two
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hq_pos : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_two)
  have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
  have hlog_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
  have hlog_mul_ne : Real.log ((n : ℝ) * (q : ℝ)) ≠ 0 := by
    simpa [Nat.cast_mul] using hlog_pos.ne'
  have hweight := mangoldt_weight_integral_change_of_variables_mangoldt_laplace
    (n * q) hnq_two
  calc
    mangoldt_weight (n * q) *
        (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ)) =
        ((ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ)) *
          (1 / ((n * q : ℕ) : ℝ))) *
          (∫ u : ℝ in Set.Ioi (0 : ℝ),
            Real.log (((n * q : ℕ) : ℝ)) *
              Real.rpow ((n * q : ℕ) : ℝ) (-u) *
              (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))) := by
      rw [hweight]
      ring
    _ = ∫ u : ℝ in Set.Ioi (0 : ℝ),
        ((ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ)) *
          (1 / ((n * q : ℕ) : ℝ))) *
          (Real.log (((n * q : ℕ) : ℝ)) *
            Real.rpow ((n * q : ℕ) : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))) := by
      rw [← MeasureTheory.integral_const_mul]
    _ = ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / (n : ℝ)) *
          (Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            (ArithmeticFunction.vonMangoldt q /
              Real.rpow (q : ℝ) (1 + u))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
      have hn_rpow_pos : 0 < Real.rpow (n : ℝ) u := Real.rpow_pos_of_pos hn_pos u
      have hq_rpow_pos : 0 < Real.rpow (q : ℝ) u := Real.rpow_pos_of_pos hq_pos u
      rw [Nat.cast_mul]
      simp [Real.mul_rpow hn_pos.le hq_pos.le, Real.rpow_neg hn_pos.le u,
        Real.rpow_neg hq_pos.le u]
      field_simp [hn_pos.ne', hq_pos.ne', hn_rpow_pos.ne', hq_rpow_pos.ne', hlog_mul_ne]
      rw [Real.rpow_add hq_pos 1 u, Real.rpow_one]
      field_simp [hlog_mul_ne]

lemma mangoldt_weight_incoming_integral_bridge_weighted_summable
    (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ =>
      ‖if 1 < q then
        mangoldt_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0‖) := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  obtain ⟨_, _, htail_bound⟩ := mangoldt_tail_upper_bound
  have htail_summ : Summable (fun q : ℕ =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) :=
    (htail_bound n hn 2 (by norm_num)).1
  have herdos_summ : Summable (fun q : ℕ =>
      if 1 < q then
        erdos_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0) := by
    have hscaled := htail_summ.mul_left (1 / (n : ℝ))
    refine hscaled.congr ?_
    intro q
    by_cases hq : 1 < q
    · have hq_two : 2 ≤ q := by omega
      have hq_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_two
      have hnq_two : 2 ≤ n * q := Nat.mul_le_mul hn hq_two
      have hq_pos : 0 < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_two)
      have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
      have hlog_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
      simp [hq, hq_real, erdos_weight, mangoldt_tail_term, Nat.cast_mul]
      field_simp [hn_pos.ne', hq_pos.ne', hlog_pos.ne']
    · have hq_not_two : ¬ 2 ≤ q := by omega
      have hq_not_real : ¬ (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_not_two
      simp [hq, hq_not_real]
  have hinj : Function.Injective (fun q : ℕ => n * q) := by
    intro a b h
    exact Nat.mul_left_cancel hn_pos_nat h
  have herror_subseq : Summable (fun q : ℕ =>
      |mangoldt_weight (n * q) - erdos_weight (n * q)|) := by
    simpa [Function.comp_def] using
      (mangoldt_weight_erdos_summable_error.comp_injective hinj)
  have herror_if_summ : Summable (fun q : ℕ =>
      if 1 < q then |mangoldt_weight (n * q) - erdos_weight (n * q)| else 0) := by
    refine Summable.of_norm_bounded herror_subseq ?_
    intro q
    by_cases hq : 1 < q <;> simp [hq, abs_nonneg]
  refine Summable.of_norm_bounded (herdos_summ.add herror_if_summ) ?_
  intro q
  by_cases hq : 1 < q
  · have hq_two : 2 ≤ q := by omega
    have hnq_two : 2 ≤ n * q := Nat.mul_le_mul hn hq_two
    have hq_pos : 0 < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_two)
    have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
    have hlog_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
    have hq_le_nq_nat : q ≤ n * q := by
      simpa using (Nat.mul_le_mul_right q hn)
    have hq_le_nq : (q : ℝ) ≤ ((n * q : ℕ) : ℝ) := by exact_mod_cast hq_le_nq_nat
    have hLambda_le_logq : ArithmeticFunction.vonMangoldt q ≤ Real.log (q : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hlogq_le_lognq : Real.log (q : ℝ) ≤ Real.log (((n * q : ℕ) : ℝ)) :=
      Real.log_le_log hq_pos hq_le_nq
    have hlog_mul_pos : 0 < Real.log ((n : ℝ) * (q : ℝ)) := by
      simpa [Nat.cast_mul] using hlog_pos
    have hfactor_nonneg :
        0 ≤ ArithmeticFunction.vonMangoldt q / Real.log (((n * q : ℕ) : ℝ)) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog_pos.le
    have hfactor_nonneg_mul :
        0 ≤ ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ)) := by
      simpa [Nat.cast_mul] using hfactor_nonneg
    have hfactor_le_one :
        ArithmeticFunction.vonMangoldt q / Real.log (((n * q : ℕ) : ℝ)) ≤ 1 := by
      exact (div_le_one₀ hlog_pos).2 (le_trans hLambda_le_logq hlogq_le_lognq)
    have hfactor_le_one_mul :
        ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ)) ≤ 1 := by
      simpa [Nat.cast_mul] using hfactor_le_one
    have herd_nonneg : 0 ≤ erdos_weight (n * q) := by
      rw [erdos_weight]
      positivity
    have hfactor_abs :
        |ArithmeticFunction.vonMangoldt q| / |Real.log ((n : ℝ) * (q : ℝ))| =
          ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ)) := by
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_pos hlog_mul_pos]
    have hweight_abs :
        |mangoldt_weight (n * q)| ≤
          erdos_weight (n * q) + |mangoldt_weight (n * q) - erdos_weight (n * q)| := by
      have hsplit : mangoldt_weight (n * q) =
          erdos_weight (n * q) + (mangoldt_weight (n * q) - erdos_weight (n * q)) := by
        ring
      have hcalc := abs_add_le (erdos_weight (n * q))
        (mangoldt_weight (n * q) - erdos_weight (n * q))
      rw [← hsplit] at hcalc
      simpa [abs_of_nonneg herd_nonneg] using hcalc
    simp only [hq, if_true, Nat.cast_mul, Real.norm_eq_abs, abs_mul, abs_div, abs_abs,
      ge_iff_le]
    rw [hfactor_abs]
    calc
      |mangoldt_weight (n * q)| *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ))) ≤
          (erdos_weight (n * q) + |mangoldt_weight (n * q) - erdos_weight (n * q)|) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hweight_abs hfactor_nonneg_mul
      _ = erdos_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ))) +
            |mangoldt_weight (n * q) - erdos_weight (n * q)| *
              (ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ))) := by
        ring
      _ ≤ erdos_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n : ℝ) * (q : ℝ))) +
            |mangoldt_weight (n * q) - erdos_weight (n * q)| := by
        have hmul := mul_le_of_le_one_right
          (abs_nonneg (mangoldt_weight (n * q) - erdos_weight (n * q))) hfactor_le_one_mul
        linarith
  · simp [hq]

lemma mangoldt_weight_incoming_integral_bridge_inner_tsum
    (n : ℕ) (_hn : 1 ≤ n) (u : ℝ) (_hu : 0 < u) :
    (∑' q : ℕ,
      if 1 < q then
        (1 / (n : ℝ)) *
          (Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            (ArithmeticFunction.vonMangoldt q /
              Real.rpow (q : ℝ) (1 + u)))
      else 0) =
      (1 / (n : ℝ)) *
        (Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
          mangoldt_dirichlet_series u) := by
  let c : ℝ := (1 / (n : ℝ)) *
    (Real.rpow (n : ℝ) (-u) *
      (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)))
  calc
    (∑' q : ℕ,
      if 1 < q then
        (1 / (n : ℝ)) *
          (Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            (ArithmeticFunction.vonMangoldt q /
              Real.rpow (q : ℝ) (1 + u)))
      else 0) =
        ∑' q : ℕ,
          if 1 < q then
            c * (ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u))
          else 0 := by
      apply tsum_congr
      intro q
      by_cases hq : 1 < q <;> simp [hq, c, mul_assoc]
    _ = c * mangoldt_dirichlet_series u := by
      rw [mangoldt_dirichlet_series]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      by_cases hq : 1 < q
      · simp [hq, c, mul_assoc]
      · have hq_cases : q = 0 ∨ q = 1 := by omega
        rcases hq_cases with rfl | rfl <;> simp [hq, c]
    _ = (1 / (n : ℝ)) *
        (Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
          mangoldt_dirichlet_series u) := by
      simp [c, mul_assoc]

lemma mangoldt_weight_incoming_integral_bridge_lhs_laplace
    (n : ℕ) (hn : 1 ≤ n) :
    (∑' q : ℕ,
      if 1 < q then
        mangoldt_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0) =
      (1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            mangoldt_dirichlet_series u) := by
  let F : ℕ → ℝ → ℝ := fun q u =>
    if 1 < q then
      (1 / (n : ℝ)) *
        (Real.rpow (n : ℝ) (-u) *
          (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
          (ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)))
    else 0
  have hterm : ∀ q : ℕ,
      (if 1 < q then
        mangoldt_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0) = ∫ u : ℝ in Set.Ioi (0 : ℝ), F q u := by
    intro q
    by_cases hq : 1 < q
    · simpa [F, hq, Nat.cast_mul] using
        mangoldt_weight_incoming_integral_bridge_term_laplace n q hn hq
    · simp [F, hq]
  have hF_int : ∀ q : ℕ, MeasureTheory.Integrable (F q)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro q
    by_cases hq : 1 < q
    · have hq_two : 2 ≤ q := by omega
      have hnq_two : 2 ≤ n * q := Nat.mul_le_mul hn hq_two
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hq_pos : 0 < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_two)
      have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
      have hlog_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
      have hlog_mul_ne : Real.log ((n : ℝ) * (q : ℝ)) ≠ 0 := by
        simpa [Nat.cast_mul] using hlog_pos.ne'
      have hbase := mangoldt_weight_integral_change_of_variables_zeta_kernel_integrable
        (n * q) hnq_two
      have hscaled := hbase.const_mul
        ((ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ)) *
          (1 / ((n * q : ℕ) : ℝ)))
      convert hscaled using 1
      ext u
      have hn_rpow_pos : 0 < Real.rpow (n : ℝ) u := Real.rpow_pos_of_pos hn_pos u
      have hq_rpow_pos : 0 < Real.rpow (q : ℝ) u := Real.rpow_pos_of_pos hq_pos u
      simp [F, hq, Nat.cast_mul]
      simp [Real.mul_rpow hn_pos.le hq_pos.le, Real.rpow_neg hn_pos.le u,
        Real.rpow_neg hq_pos.le u]
      field_simp [hn_pos.ne', hq_pos.ne', hn_rpow_pos.ne', hq_rpow_pos.ne', hlog_mul_ne]
      rw [Real.rpow_add hq_pos 1 u, Real.rpow_one]
      field_simp [hlog_mul_ne]
    · simp [F, hq]
  have hF_sum : Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Ioi (0 : ℝ), ‖F q u‖) := by
    have hweighted := mangoldt_weight_incoming_integral_bridge_weighted_summable n hn
    refine hweighted.congr ?_
    intro q
    have hF_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] fun u : ℝ => F q u := by
      by_cases hq : 1 < q
      · have hq_two : 2 ≤ q := by omega
        have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hq_pos : 0 < (q : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_two)
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := MeasureTheory.volume)
            (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
        have hu_pos : 0 < u := by simpa [Set.mem_Ioi] using hu
        have hz_pos : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re :=
          riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
        have hn_rpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (-u) :=
          Real.rpow_nonneg hn_pos.le (-u)
        have hq_rpow_pos : 0 < Real.rpow (q : ℝ) (1 + u) :=
          Real.rpow_pos_of_pos hq_pos (1 + u)
        simp only [F, hq, if_true, Pi.zero_apply, ge_iff_le]
        have hinv_n_nonneg : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one hn_pos.le
        have hrec_nonneg :
            0 ≤ 1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) :=
          div_nonneg zero_le_one hz_pos.le
        have hLambda_div_nonneg :
            0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg hq_rpow_pos.le
        exact mul_nonneg hinv_n_nonneg
          (mul_nonneg (mul_nonneg hn_rpow_nonneg hrec_nonneg) hLambda_div_nonneg)
      · filter_upwards with u
        simp [F, hq]
    have hnorm_integral :
        (∫ u : ℝ in Set.Ioi (0 : ℝ), ‖F q u‖) =
          ∫ u : ℝ in Set.Ioi (0 : ℝ), F q u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hF_nonneg] with u hu
      rw [Real.norm_of_nonneg hu]
    have hterm_nonneg : 0 ≤
        (if 1 < q then
          mangoldt_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
        else 0) := by
      rw [hterm q]
      exact MeasureTheory.integral_nonneg_of_ae hF_nonneg
    calc
      ‖if 1 < q then
          mangoldt_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
        else 0‖ =
          (if 1 < q then
            mangoldt_weight (n * q) *
              (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
          else 0) := by
        rw [Real.norm_of_nonneg hterm_nonneg]
      _ = ∫ u : ℝ in Set.Ioi (0 : ℝ), F q u := hterm q
      _ = ∫ u : ℝ in Set.Ioi (0 : ℝ), ‖F q u‖ := hnorm_integral.symm
  calc
    (∑' q : ℕ,
      if 1 < q then
        mangoldt_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0) = ∑' q : ℕ, ∫ u : ℝ in Set.Ioi (0 : ℝ), F q u := by
      apply tsum_congr
      intro q
      exact hterm q
    _ = ∫ u : ℝ in Set.Ioi (0 : ℝ), ∑' q : ℕ, F q u := by
      exact MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
    _ = ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / (n : ℝ)) *
          (Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            mangoldt_dirichlet_series u) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
      have hu_pos : 0 < u := by simpa [Set.mem_Ioi] using hu
      simpa [F] using mangoldt_weight_incoming_integral_bridge_inner_tsum n hn u hu_pos
    _ = (1 / (n : ℝ)) *
        (∫ u : ℝ in Set.Ioi (0 : ℝ),
          Real.rpow (n : ℝ) (-u) *
            (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) *
            mangoldt_dirichlet_series u) := by
      rw [MeasureTheory.integral_const_mul]

lemma mangoldt_weight_incoming_integral_bridge :
    ∀ n : ℕ, 1 ≤ n ->
      (∑' q : ℕ,
        if 1 < q then
          mangoldt_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
        else 0) =
        ∫ s : ℝ in Set.Ioi (1 : ℝ),
          deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s /
            Real.rpow (n : ℝ) s := by
  intro n hn
  rw [mangoldt_weight_incoming_integral_bridge_lhs_laplace n hn,
    ← mangoldt_weight_incoming_integral_bridge_rhs_laplace n hn]

lemma reciprocal_zeta_tendsto_one_right :
    Filter.Tendsto
      (fun s : ℝ => 1 / ((riemannZeta (s : ℂ)).re))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (0 : ℝ)) := by
  rcases reciprocal_zeta_second_order_bound with ⟨δ, C, hδ_pos, hC_nonneg, hbound⟩
  have hδ_event :
      ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), u ≤ δ := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ_pos] with u hu _
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hu
    exact le_of_lt (lt_of_le_of_lt (le_abs_self u) hu)
  have hshifted :
      Filter.Tendsto
        (fun u : ℝ => 1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    have hupper :
        ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)| ≤ u + C * u ^ 2 := by
      filter_upwards [self_mem_nhdsWithin, hδ_event] with u hu hule
      rw [Set.mem_Ioi] at hu
      have hlocal := hbound u hu hule
      calc
        |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)|
            = |(1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u) + u| := by
              ring_nf
        _ ≤ |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| + |u| :=
              abs_add_le _ _
        _ ≤ C * u ^ 2 + u := by
              exact add_le_add hlocal (le_of_eq (abs_of_pos hu))
        _ = u + C * u ^ 2 := by ring
    have hnonneg :
        ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          0 ≤ |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)| := by
      filter_upwards with u
      exact abs_nonneg _
    have hu_tend :
        Filter.Tendsto (fun u : ℝ => u) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (0 : ℝ)) := by
      exact continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hquad_tend :
        Filter.Tendsto (fun u : ℝ => C * u ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
      simpa using (hu_tend.pow 2).const_mul C
    have hrhs_tend :
        Filter.Tendsto (fun u : ℝ => u + C * u ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
      simpa using hu_tend.add hquad_tend
    have habs_tend :
        Filter.Tendsto
          (fun u : ℝ => |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      squeeze_zero' hnonneg hupper hrhs_tend
    exact (tendsto_zero_iff_abs_tendsto_zero
      (fun u : ℝ => 1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))).mpr habs_tend
  have hsub :
      Filter.Tendsto (fun s : ℝ => s - 1)
        (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : ContinuousAt (fun s : ℝ => s - 1) 1 :=
        continuousAt_id.sub continuousAt_const
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Set.mem_Ioi] at hs ⊢
      linarith
  have hcomp := hshifted.comp hsub
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp

lemma reciprocal_zeta_tendsto_at_top :
    Filter.Tendsto
      (fun s : ℝ => 1 / ((riemannZeta (s : ℂ)).re))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hsum : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹) ^ (2 : ℝ)) := by
    simpa [one_div, Nat.cast_add, Nat.cast_one] using
      (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num : (1 : ℝ) < 2)
  have hterm : ∀ n : ℕ,
      Filter.Tendsto (fun s : ℝ => (((n + 1 : ℕ) : ℝ)⁻¹) ^ s)
        Filter.atTop (nhds (if n = 0 then (1 : ℝ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hbase_pos : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
        positivity
      have hbase_gt : -1 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
        linarith
      have hbase_lt : (((n + 1 : ℕ) : ℝ)⁻¹) < 1 := by
        have hn1 : (1 : ℕ) < n + 1 := Nat.succ_lt_succ (Nat.pos_of_ne_zero hn)
        have hnreal : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast hn1
        exact inv_lt_one_of_one_lt₀ hnreal
      simpa [hn] using
        tendsto_rpow_atTop_of_base_lt_one (((n + 1 : ℕ) : ℝ)⁻¹) hbase_gt hbase_lt
  have hbound :
      ∀ᶠ s : ℝ in Filter.atTop,
        ∀ n : ℕ, ‖(((n + 1 : ℕ) : ℝ)⁻¹) ^ s‖ ≤
          (((n + 1 : ℕ) : ℝ)⁻¹) ^ (2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with s hs n
    have hbase_pos : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
      positivity
    have hbase_le : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
      have hn_ge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact inv_le_one_of_one_le₀ hn_ge
    have hpow : (((n + 1 : ℕ) : ℝ)⁻¹) ^ s ≤
        (((n + 1 : ℕ) : ℝ)⁻¹) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hbase_pos hbase_le hs
    have hnonneg : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) ^ s := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hpow
  have htsum :
      Filter.Tendsto
        (fun s : ℝ => ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)⁻¹) ^ s)
        Filter.atTop (nhds (∑' n : ℕ, if n = 0 then (1 : ℝ) else 0)) :=
    tendsto_tsum_of_dominated_convergence hsum hterm hbound
  have htsum_one :
      Filter.Tendsto
        (fun s : ℝ => ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)⁻¹) ^ s)
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa using htsum
  have hzeta_eventually :
      (fun s : ℝ => ∑' n : ℕ, (((n + 1 : ℕ) : ℝ)⁻¹) ^ s)
        =ᶠ[Filter.atTop] fun s : ℝ => (riemannZeta (s : ℂ)).re := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with s hs
    have hsC : 1 < ((s : ℂ).re) := by
      simpa using hs
    have hfC : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ (s : ℂ))) := by
      simpa using
        (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℂ) ^ (s : ℂ))) 1).2
          (Complex.summable_one_div_nat_cpow.mpr hsC)
    have hterm_eq :
        (fun n : ℕ => (1 / (((n + 1 : ℕ) : ℂ) ^ (s : ℂ))).re) =
          fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹) ^ s := by
      funext n
      have hbase_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by
        positivity
      calc
        (1 / (((n + 1 : ℕ) : ℂ) ^ (s : ℂ))).re =
            (1 / (((((n + 1 : ℕ) : ℝ) : ℂ) ^ (s : ℂ)))).re := by
          simp
        _ = (1 / ((((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ)).re := by
          rw [← Complex.ofReal_cpow hbase_nonneg s]
        _ = 1 / (((n + 1 : ℕ) : ℝ) ^ s) := by
          simp
        _ = (1 / ((n + 1 : ℕ) : ℝ)) ^ s := by
          rw [Real.div_rpow zero_le_one hbase_nonneg s]
          simp
        _ = (((n + 1 : ℕ) : ℝ)⁻¹) ^ s := by
          simp [one_div]
    have hzeta_real :
        (riemannZeta (s : ℂ)).re =
          ∑' n : ℕ, (1 / (((n + 1 : ℕ) : ℂ) ^ (s : ℂ))).re := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (s : ℂ)) hsC]
      simpa using Complex.re_tsum hfC
    rw [hzeta_real, hterm_eq]
  have hzeta_re :
      Filter.Tendsto (fun s : ℝ => (riemannZeta (s : ℂ)).re)
        Filter.atTop (nhds (1 : ℝ)) :=
    Filter.Tendsto.congr' hzeta_eventually htsum_one
  simpa [one_div] using hzeta_re.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

lemma reciprocal_zeta_ibp_regularity :
    (∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) ->
      HasDerivAt
        (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re))
        (deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s) s) ∧
    MeasureTheory.IntegrableOn
      (fun s : ℝ => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s)
      (Set.Ioi (1 : ℝ)) ∧
    (∀ n : ℕ, 2 ≤ n ->
      (∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) ->
        HasDerivAt
          (fun t : ℝ => 1 / Real.rpow (n : ℝ) t)
          (-(Real.log (n : ℝ) / Real.rpow (n : ℝ) s)) s) ∧
      MeasureTheory.IntegrableOn
        (fun s : ℝ =>
          (1 / ((riemannZeta (s : ℂ)).re)) *
            (-(Real.log (n : ℝ) / Real.rpow (n : ℝ) s)))
        (Set.Ioi (1 : ℝ)) ∧
      MeasureTheory.IntegrableOn
        (fun s : ℝ =>
          deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s *
            (1 / Real.rpow (n : ℝ) s))
        (Set.Ioi (1 : ℝ)) ∧
      Filter.Tendsto
        (fun s : ℝ =>
          (1 / ((riemannZeta (s : ℂ)).re)) * (1 / Real.rpow (n : ℝ) s))
        (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (fun s : ℝ =>
          (1 / ((riemannZeta (s : ℂ)).re)) * (1 / Real.rpow (n : ℝ) s))
        Filter.atTop (nhds (0 : ℝ))) := by
  have hrec_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s)
      (Set.Ioi (1 : ℝ)) := by
    rcases reciprocal_zeta_second_order_bound with ⟨δ, C₀, hδ_pos, hC₀_nonneg, hlocal⟩
    let K : ℝ := max C₀ (δ⁻¹ ^ 2 + δ⁻¹)
    have hK_nonneg : 0 ≤ K := le_trans hC₀_nonneg (le_max_left _ _)
    have hglobal : ∀ u : ℝ, 0 < u ->
        |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤ K * u ^ 2 := by
      intro u hu_pos
      by_cases hu_le_delta : u ≤ δ
      · exact le_trans (hlocal u hu_pos hu_le_delta) (by gcongr; exact le_max_left _ _)
      · have hdelta_lt_u : δ < u := lt_of_not_ge hu_le_delta
        have hdelta_le_u : δ ≤ u := le_of_lt hdelta_lt_u
        have hz_pos : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
          exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
        have hz_one_le : 1 ≤ (riemannZeta ((1 + u : ℝ) : ℂ)).re :=
          mangoldt_weight_integral_change_of_variables_one_le_zeta_re
            (by linarith : 1 < 1 + u)
        have hrec_nonneg : 0 ≤ 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
          exact one_div_nonneg.mpr hz_pos.le
        have hrec_le_one : 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re ≤ 1 := by
          exact (div_le_one₀ hz_pos).2 hz_one_le
        have herr_linear : |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤ 1 + u := by
          calc
            |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u| ≤
                |1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)| + |u| := by
                simpa [sub_eq_add_neg, abs_neg] using
                  abs_add_le (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re)) (-u)
            _ = 1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) + u := by
                rw [abs_of_nonneg hrec_nonneg, abs_of_pos hu_pos]
            _ ≤ 1 + u := by linarith
        have hinv_mul : 1 ≤ δ⁻¹ * u := by
          have hmul := mul_le_mul_of_nonneg_left hdelta_le_u (le_of_lt (inv_pos.mpr hδ_pos))
          rwa [inv_mul_cancel₀ hδ_pos.ne'] at hmul
        have h_one_quad : 1 ≤ δ⁻¹ ^ 2 * u ^ 2 := by
          nlinarith [sq_nonneg (δ⁻¹ * u), hinv_mul]
        have h_u_quad : u ≤ δ⁻¹ * u ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_right hinv_mul hu_pos.le
          nlinarith
        have htail_quad : 1 + u ≤ (δ⁻¹ ^ 2 + δ⁻¹) * u ^ 2 := by
          nlinarith
        exact le_trans herr_linear (le_trans htail_quad (by gcongr; exact le_max_right _ _))
    have hmds_nonneg : ∀ u : ℝ, 0 < u -> 0 ≤ mangoldt_dirichlet_series u := by
      intro u hu
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg q) (1 + u))
    have hnear : MeasureTheory.IntegrableOn
        (fun s : ℝ => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s)
        (Set.Ioc (1 : ℝ) 2) := by
      refine MeasureTheory.IntegrableOn.of_bound (by simp)
        (aestronglyMeasurable_deriv
          (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re))
          (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) 2))) (1 + K) ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (μ := MeasureTheory.volume)
          (measurableSet_Ioc : MeasurableSet (Set.Ioc (1 : ℝ) 2))] with s hs
      have hs1 : 1 < s := hs.1
      have hs2 : s ≤ 2 := hs.2
      let u : ℝ := s - 1
      have hu_pos : 0 < u := by dsimp [u]; linarith
      have hu_le_one : u ≤ 1 := by dsimp [u]; linarith
      have hone : (1 + u : ℝ) = s := by dsimp [u]; ring
      have hderiv_eq := mangoldt_weight_incoming_integral_bridge_deriv_identity s hs1
      have hmds_ge : 0 ≤ mangoldt_dirichlet_series (s - 1) :=
        hmds_nonneg (s - 1) (by linarith)
      have hmds_le : mangoldt_dirichlet_series (s - 1) ≤ 1 / (s - 1) :=
        von_mangoldt_dirichlet_series_upper_bound (s - 1) (by linarith)
      have hz_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs1
      have hrec_nonneg : 0 ≤ 1 / (riemannZeta (s : ℂ)).re := one_div_nonneg.mpr hz_pos.le
      have hrec_le : 1 / (riemannZeta (s : ℂ)).re ≤ u + K * u ^ 2 := by
        have hloc := hglobal u hu_pos
        have hle :
            1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re) - u ≤ K * u ^ 2 :=
          le_trans (le_abs_self _) hloc
        rw [hone] at hle
        linarith
      have hrhs_nonneg : 0 ≤ u + K * u ^ 2 := by positivity
      have hprod_nonneg : 0 ≤
          (1 / (riemannZeta (s : ℂ)).re) * mangoldt_dirichlet_series (s - 1) :=
        mul_nonneg hrec_nonneg hmds_ge
      rw [hderiv_eq, Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
      calc
        (1 / (riemannZeta (s : ℂ)).re) * mangoldt_dirichlet_series (s - 1) ≤
            (u + K * u ^ 2) * (1 / u) := by
          simpa [u] using mul_le_mul hrec_le hmds_le hmds_ge hrhs_nonneg
        _ = 1 + K * u := by
          field_simp [hu_pos.ne']
        _ ≤ 1 + K := by
          nlinarith [mul_le_mul_of_nonneg_left hu_le_one hK_nonneg]
    have htail : MeasureTheory.IntegrableOn
        (fun s : ℝ => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s)
        (Set.Ioi (2 : ℝ)) := by
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hrate : -(Real.log (2 : ℝ) / 2) < 0 := by linarith
      have hexp : MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp ((-(Real.log (2 : ℝ) / 2)) * s))
          (Set.Ioi (2 : ℝ)) := integrableOn_exp_mul_Ioi hrate 2
      have hbound_int : MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.exp (Real.log (2 : ℝ) / 2) *
            Real.exp ((-(Real.log (2 : ℝ) / 2)) * s))
          (Set.Ioi (2 : ℝ)) := hexp.const_mul (Real.exp (Real.log (2 : ℝ) / 2))
      refine hbound_int.mono'
        (aestronglyMeasurable_deriv
          (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re))
          (MeasureTheory.volume.restrict (Set.Ioi (2 : ℝ)))) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (2 : ℝ)))] with s hs
      have hs2 : 2 < s := by simpa [Set.mem_Ioi] using hs
      have hs1 : 1 < s := by linarith
      let u : ℝ := s - 1
      have hu_pos : 0 < u := by dsimp [u]; linarith
      have hu_ge_one : 1 ≤ u := by dsimp [u]; linarith
      have hderiv_eq := mangoldt_weight_incoming_integral_bridge_deriv_identity s hs1
      have hz_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs1
      have hz_one_le : 1 ≤ (riemannZeta (s : ℂ)).re :=
        mangoldt_weight_integral_change_of_variables_one_le_zeta_re hs1
      have hrec_nonneg : 0 ≤ 1 / (riemannZeta (s : ℂ)).re := one_div_nonneg.mpr hz_pos.le
      have hrec_le_one : 1 / (riemannZeta (s : ℂ)).re ≤ 1 :=
        (div_le_one₀ hz_pos).2 hz_one_le
      have hmds_ge : 0 ≤ mangoldt_dirichlet_series (s - 1) :=
        hmds_nonneg (s - 1) (by linarith)
      have hmds_le_geom : mangoldt_dirichlet_series u ≤
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
        have hseries :
            mangoldt_dirichlet_series u =
              ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
                riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
          simpa using congrArg Complex.re
            (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu_pos)
        calc
          mangoldt_dirichlet_series u =
              ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
                riemannZeta ((1 + u : ℝ) : ℂ)).re) := hseries
          _ ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
              zeta_log_derivative_geometric_bound u hu_pos
      have hpow_gt_one : 1 < Real.rpow (2 : ℝ) u := by
        exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
          (Or.inl ⟨by norm_num, hu_pos⟩)
      have hden_pos : 0 < Real.rpow (2 : ℝ) u - 1 := by linarith
      have hgeom_nonneg : 0 ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
        div_nonneg hlog2_pos.le hden_pos.le
      have hgeom_le_mul :
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤
            u * (Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_right hu_ge_one hgeom_nonneg]
      have hgeom_le_exp :
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤
            Real.exp (Real.log (2 : ℝ) / 2) *
              Real.exp ((-(Real.log (2 : ℝ) / 2)) * s) := by
        calc
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤
              u * (Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := hgeom_le_mul
          _ ≤ Real.rpow (2 : ℝ) (-(u / 2)) := by
            simpa [mul_div_assoc] using two_power_kernel_midpoint_bound_local u hu_pos
          _ = Real.exp (Real.log (2 : ℝ) / 2) *
              Real.exp ((-(Real.log (2 : ℝ) / 2)) * s) := by
            dsimp [u]
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
            rw [← Real.exp_add]
            congr 1
            ring
      have hprod_nonneg : 0 ≤
          (1 / (riemannZeta (s : ℂ)).re) * mangoldt_dirichlet_series (s - 1) :=
        mul_nonneg hrec_nonneg hmds_ge
      rw [hderiv_eq, Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
      calc
        (1 / (riemannZeta (s : ℂ)).re) * mangoldt_dirichlet_series (s - 1) ≤
            Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
          calc
            (1 / (riemannZeta (s : ℂ)).re) * mangoldt_dirichlet_series (s - 1) ≤
                1 * (Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
              exact mul_le_mul hrec_le_one (by simpa [u] using hmds_le_geom) hmds_ge zero_le_one
            _ = Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by ring
        _ ≤ Real.exp (Real.log (2 : ℝ) / 2) *
            Real.exp ((-(Real.log (2 : ℝ) / 2)) * s) := hgeom_le_exp
    have hcover : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) 2 ∪ Set.Ioi (2 : ℝ) := by
      ext s
      constructor
      · intro hs
        by_cases hs2 : s ≤ 2
        · exact Or.inl ⟨hs, hs2⟩
        · exact Or.inr (lt_of_not_ge hs2)
      · rintro (⟨hs, _⟩ | hs)
        · exact hs
        · have hs' : 2 < s := by simpa [Set.mem_Ioi] using hs
          exact (by simpa [Set.mem_Ioi] using (by linarith : (1 : ℝ) < s))
    rw [hcover]
    exact hnear.union htail
  refine ⟨?hrec_deriv, hrec_int, ?hkernels⟩
  · intro s hs
    have hs' : 1 < s := by simpa [Set.mem_Ioi] using hs
    have hz_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs'
    have hz_diff : DifferentiableAt ℂ riemannZeta (s : ℂ) :=
      differentiableAt_riemannZeta (by
        norm_num [Complex.ext_iff]
        linarith)
    have hbase_has : HasDerivAt
        (fun t : ℝ => (riemannZeta (t : ℂ)).re)
        (deriv riemannZeta (s : ℂ)).re s := by
      exact hz_diff.hasDerivAt.real_of_complex
    have hhas : HasDerivAt
        (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re))
        (-(deriv riemannZeta (s : ℂ)).re / ((riemannZeta (s : ℂ)).re) ^ 2) s := by
      have hfun :
          (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) =
            fun t : ℝ => ((riemannZeta (t : ℂ)).re)⁻¹ := by
        funext t
        rw [one_div]
      rw [hfun]
      exact hbase_has.inv hz_pos.ne'
    exact hhas.differentiableAt.hasDerivAt
  · intro n hn
    have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
    refine ⟨?hker_deriv, ?huv_int, ?hduv_int, ?hlim_one, ?hlim_top⟩
    · intro s hs
      have hbase_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
      have hder : HasDerivAt
          (fun t : ℝ => ((n : ℝ)⁻¹) ^ t)
          (Real.log ((n : ℝ)⁻¹) * 1 * ((n : ℝ)⁻¹) ^ s) s := by
        simpa using (hasDerivAt_id s).const_rpow hbase_pos
      have hfun : (fun t : ℝ => 1 / Real.rpow (n : ℝ) t) =
          (fun t : ℝ => ((n : ℝ)⁻¹) ^ t) := by
        funext t
        simpa [one_div] using (Real.inv_rpow hn_pos.le t).symm
      rw [hfun]
      convert hder using 1
      rw [Real.log_inv]
      rw [Real.inv_rpow hn_pos.le]
      simp [div_eq_mul_inv]
    · have hbase_int : MeasureTheory.IntegrableOn
          (fun s : ℝ => Real.log (n : ℝ) / Real.rpow (n : ℝ) s)
          (Set.Ioi (1 : ℝ)) := by
        have hrate : -Real.log (n : ℝ) < 0 := by linarith
        have hexp : MeasureTheory.IntegrableOn
            (fun s : ℝ => Real.exp ((-Real.log (n : ℝ)) * s))
            (Set.Ioi (1 : ℝ)) := integrableOn_exp_mul_Ioi hrate 1
        have hscaled := hexp.const_mul (Real.log (n : ℝ))
        have hfun : (fun s : ℝ => Real.log (n : ℝ) / Real.rpow (n : ℝ) s) =
            fun s : ℝ => Real.log (n : ℝ) * Real.exp ((-Real.log (n : ℝ)) * s) := by
          funext s
          change Real.log (n : ℝ) / ((n : ℝ) ^ s) =
            Real.log (n : ℝ) * Real.exp ((-Real.log (n : ℝ)) * s)
          rw [Real.rpow_def_of_pos hn_pos]
          field_simp [(Real.exp_pos (Real.log (n : ℝ) * s)).ne']
          rw [← Real.exp_add]
          ring_nf
          simp
        rw [hfun]
        exact hscaled
      have hz_cont : ContinuousOn
          (fun s : ℝ => (riemannZeta (s : ℂ)).re) (Set.Ioi (1 : ℝ)) := by
        intro s hs
        have hs' : 1 < s := by simpa [Set.mem_Ioi] using hs
        have hz_diff : DifferentiableAt ℂ riemannZeta (s : ℂ) :=
          differentiableAt_riemannZeta (by
            norm_num [Complex.ext_iff]
            linarith)
        exact (Complex.continuous_re.continuousAt.comp
          (hz_diff.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
      have hrec_cont : ContinuousOn
          (fun s : ℝ => 1 / ((riemannZeta (s : ℂ)).re)) (Set.Ioi (1 : ℝ)) := by
        simpa [one_div] using hz_cont.inv₀ (by
          intro s hs
          exact (riemannZeta_re_pos_of_one_lt (by simpa [Set.mem_Ioi] using hs)).ne')
      have hpow_cont : Continuous (fun s : ℝ => Real.rpow (n : ℝ) s) :=
        Real.continuous_const_rpow hn_pos.ne'
      have hfactor_cont : Continuous (fun s : ℝ => -(Real.log (n : ℝ) / Real.rpow (n : ℝ) s)) := by
        exact (continuous_const.div hpow_cont (fun s => (Real.rpow_pos_of_pos hn_pos s).ne')).neg
      have htarget_meas : MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ =>
            (1 / ((riemannZeta (s : ℂ)).re)) *
              (-(Real.log (n : ℝ) / Real.rpow (n : ℝ) s)))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        exact (hrec_cont.mul hfactor_cont.continuousOn).aestronglyMeasurable measurableSet_Ioi
      refine hbase_int.mono' htarget_meas ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with s hs
      have hs' : 1 < s := by simpa [Set.mem_Ioi] using hs
      have hz_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs'
      have hz_one_le : 1 ≤ (riemannZeta (s : ℂ)).re :=
        mangoldt_weight_integral_change_of_variables_one_le_zeta_re hs'
      have hrec_nonneg : 0 ≤ 1 / (riemannZeta (s : ℂ)).re := one_div_nonneg.mpr hz_pos.le
      have hrec_le_one : 1 / (riemannZeta (s : ℂ)).re ≤ 1 :=
        (div_le_one₀ hz_pos).2 hz_one_le
      have hpow_pos : 0 < Real.rpow (n : ℝ) s := Real.rpow_pos_of_pos hn_pos s
      have hbase_nonneg : 0 ≤ Real.log (n : ℝ) / Real.rpow (n : ℝ) s :=
        div_nonneg hlog_pos.le hpow_pos.le
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hrec_nonneg,
        abs_of_nonneg hbase_nonneg]
      exact mul_le_of_le_one_left hbase_nonneg hrec_le_one
    · have hderiv_int : MeasureTheory.Integrable
          (fun s : ℝ => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s)
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := hrec_int
      have hkernel_meas : MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => 1 / Real.rpow (n : ℝ) s)
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        have hcont_pow : Continuous (fun s : ℝ => Real.rpow (n : ℝ) s) :=
          Real.continuous_const_rpow hn_pos.ne'
        have hcont : Continuous (fun s : ℝ => 1 / Real.rpow (n : ℝ) s) := by
          exact continuous_const.div hcont_pow (fun s => (Real.rpow_pos_of_pos hn_pos s).ne')
        exact hcont.aestronglyMeasurable
      have hkernel_bound : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)),
          ‖1 / Real.rpow (n : ℝ) s‖ ≤ (1 : ℝ) := by
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := MeasureTheory.volume)
            (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with s hs
        have hs' : 1 < s := by simpa [Set.mem_Ioi] using hs
        have hpow_ge_one : 1 ≤ Real.rpow (n : ℝ) s := by
          have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have hn_gt_one : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
          exact ((Real.one_lt_rpow_iff hn_pos.le).2 (Or.inl ⟨hn_gt_one, by linarith⟩)).le
        have hpow_pos : 0 < Real.rpow (n : ℝ) s := Real.rpow_pos_of_pos hn_pos s
        rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr hpow_pos.le)]
        exact (div_le_one₀ hpow_pos).2 hpow_ge_one
      exact hderiv_int.mul_bdd hkernel_meas hkernel_bound
    · have hf := reciprocal_zeta_tendsto_one_right
      have hkernel : Filter.Tendsto
          (fun s : ℝ => 1 / Real.rpow (n : ℝ) s)
          (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)))
          (nhds (1 / Real.rpow (n : ℝ) (1 : ℝ))) := by
        have hcont : ContinuousAt (fun s : ℝ => 1 / Real.rpow (n : ℝ) s) 1 := by
          have hcont_pow : ContinuousAt (fun s : ℝ => Real.rpow (n : ℝ) s) 1 :=
            Real.continuousAt_const_rpow hn_pos.ne'
          exact continuousAt_const.div hcont_pow (Real.rpow_pos_of_pos hn_pos (1 : ℝ)).ne'
        exact hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hmul := hf.mul hkernel
      have hzero : (0 : ℝ) * (1 / Real.rpow (n : ℝ) (1 : ℝ)) = 0 := by ring
      simpa [hzero] using hmul
    · have hf := reciprocal_zeta_tendsto_at_top
      have hbase_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
      have hbase_gt : -1 < (n : ℝ)⁻¹ := by linarith [hbase_pos]
      have hbase_lt : (n : ℝ)⁻¹ < 1 := by
        have hn_gt_one : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
        exact inv_lt_one_of_one_lt₀ hn_gt_one
      have hkernel' : Filter.Tendsto (fun s : ℝ => ((n : ℝ)⁻¹) ^ s)
          Filter.atTop (nhds (0 : ℝ)) :=
        tendsto_rpow_atTop_of_base_lt_one ((n : ℝ)⁻¹) hbase_gt hbase_lt
      have hkernel : Filter.Tendsto
          (fun s : ℝ => 1 / Real.rpow (n : ℝ) s)
          Filter.atTop (nhds (0 : ℝ)) := by
        simpa [one_div, Real.inv_rpow hn_pos.le] using hkernel'
      have hmul := hf.mul hkernel
      simpa using hmul

lemma reciprocal_zeta_derivative_integral_one :
    (∫ s : ℝ in Set.Ioi (1 : ℝ),
      deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s) = 1 := by
  let f : ℝ → ℝ := fun s : ℝ => 1 / ((riemannZeta (s : ℂ)).re)
  let f' : ℝ → ℝ := fun s : ℝ => deriv f s
  rcases reciprocal_zeta_ibp_regularity with ⟨hderiv, hint, _⟩
  have hf_deriv : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) -> HasDerivAt f (f' s) s := by
    intro s hs
    simpa [f, f'] using hderiv s hs
  have hconst_deriv : ∀ s : ℝ, s ∈ Set.Ioi (1 : ℝ) ->
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := by
    intro s _
    exact hasDerivAt_const s (1 : ℝ)
  have hint_prod : MeasureTheory.IntegrableOn
      (f' * (fun _ : ℝ => (1 : ℝ)) + f * (fun _ : ℝ => (0 : ℝ)))
      (Set.Ioi (1 : ℝ)) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro s hs
    simp [Pi.mul_apply, Pi.add_apply, f, f']
  have hzero_f : Filter.Tendsto f
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (0 : ℝ)) := by
    simpa [f] using reciprocal_zeta_tendsto_one_right
  have hzero : Filter.Tendsto (f * (fun _ : ℝ => (1 : ℝ)))
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (0 : ℝ)) := by
    have hzero_lam : Filter.Tendsto (fun s : ℝ => f s * (1 : ℝ))
        (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (0 : ℝ)) := by
      simpa using
        hzero_f.mul
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
            (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (1 : ℝ)))
    exact Filter.Tendsto.congr' (by filter_upwards with s; simp [Pi.mul_apply]) hzero_lam
  have hinfty_f : Filter.Tendsto f Filter.atTop (nhds (1 : ℝ)) := by
    simpa [f] using reciprocal_zeta_tendsto_at_top
  have hinfty : Filter.Tendsto (f * (fun _ : ℝ => (1 : ℝ)))
      Filter.atTop (nhds (1 : ℝ)) := by
    have hinfty_lam : Filter.Tendsto (fun s : ℝ => f s * (1 : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
      simpa using
        hinfty_f.mul
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
            Filter.atTop (nhds (1 : ℝ)))
    exact Filter.Tendsto.congr' (by filter_upwards with s; simp [Pi.mul_apply]) hinfty_lam
  have hftc := MeasureTheory.integral_Ioi_deriv_mul_eq_sub
    (a := (1 : ℝ)) (u := f) (u' := f') (v := fun _ : ℝ => (1 : ℝ))
    (v' := fun _ : ℝ => (0 : ℝ)) (a' := (0 : ℝ)) (b' := (1 : ℝ))
    hf_deriv hconst_deriv hint_prod hzero hinfty
  simpa [f, f'] using hftc

lemma mangoldt_weight_reciprocal_zeta_integration_by_parts
    (n : ℕ) (hn : 2 ≤ n) :
    (∫ s : ℝ in Set.Ioi (1 : ℝ),
        deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s /
          Real.rpow (n : ℝ) s) =
      ∫ s : ℝ in Set.Ioi (1 : ℝ),
        Real.log (n : ℝ) /
          (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s) := by
  rcases reciprocal_zeta_ibp_regularity with ⟨hu_deriv, _, hreg⟩
  rcases hreg n hn with ⟨hv_deriv, huvDeriv_int, huDerivv_int, hzero_one, hzero_top⟩
  let u : ℝ → ℝ := fun s => 1 / ((riemannZeta (s : ℂ)).re)
  let v : ℝ → ℝ := fun s => 1 / Real.rpow (n : ℝ) s
  let uDeriv : ℝ → ℝ := fun s => deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s
  let vDeriv : ℝ → ℝ := fun s => -(Real.log (n : ℝ) / Real.rpow (n : ℝ) s)
  have huDerivv_int' : MeasureTheory.IntegrableOn (fun s : ℝ => uDeriv s * v s)
      (Set.Ioi (1 : ℝ)) := by
    simpa [uDeriv, v] using huDerivv_int
  have huvDeriv_int' : MeasureTheory.IntegrableOn (fun s : ℝ => u s * vDeriv s)
      (Set.Ioi (1 : ℝ)) := by
    simpa [u, vDeriv] using huvDeriv_int
  have hsum_int : MeasureTheory.IntegrableOn (uDeriv * v + u * vDeriv)
      (Set.Ioi (1 : ℝ)) := by
    change MeasureTheory.IntegrableOn
      ((fun s : ℝ => uDeriv s * v s) + fun s : ℝ => u s * vDeriv s)
      (Set.Ioi (1 : ℝ))
    exact huDerivv_int'.add huvDeriv_int'
  have hibp :
      (∫ s : ℝ in Set.Ioi (1 : ℝ), uDeriv s * v s + u s * vDeriv s) = 0 := by
    have h := MeasureTheory.integral_Ioi_deriv_mul_eq_sub
      (a := (1 : ℝ)) (u := u) (u' := uDeriv) (v := v) (v' := vDeriv)
      (a' := (0 : ℝ)) (b' := (0 : ℝ))
      (hu := by
        intro s hs
        simpa [u, uDeriv] using hu_deriv s hs)
      (hv := by
        intro s hs
        simpa [v, vDeriv] using hv_deriv s hs)
      hsum_int
      (by
        change Filter.Tendsto (fun s : ℝ =>
          (1 / ((riemannZeta (s : ℂ)).re)) * (1 / Real.rpow (n : ℝ) s))
          (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds 0)
        simpa using hzero_one)
      (by
        change Filter.Tendsto (fun s : ℝ =>
          (1 / ((riemannZeta (s : ℂ)).re)) * (1 / Real.rpow (n : ℝ) s))
          Filter.atTop (nhds 0)
        simpa using hzero_top)
    simpa using h
  have hsum :
      (∫ s : ℝ in Set.Ioi (1 : ℝ), uDeriv s * v s) +
        (∫ s : ℝ in Set.Ioi (1 : ℝ), u s * vDeriv s) = 0 := by
    have hadd := MeasureTheory.integral_add
      (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
      huDerivv_int' huvDeriv_int'
    rw [← hadd]
    exact hibp
  have hright :
      (∫ s : ℝ in Set.Ioi (1 : ℝ),
        Real.log (n : ℝ) /
          (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s)) =
        - (∫ s : ℝ in Set.Ioi (1 : ℝ), u s * vDeriv s) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    dsimp [u, vDeriv]
    ring_nf
  have hmain :
      (∫ s : ℝ in Set.Ioi (1 : ℝ), uDeriv s * v s) =
        ∫ s : ℝ in Set.Ioi (1 : ℝ),
          Real.log (n : ℝ) /
            (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s) := by
    linarith
  calc
    (∫ s : ℝ in Set.Ioi (1 : ℝ),
        deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s /
          Real.rpow (n : ℝ) s)
        = ∫ s : ℝ in Set.Ioi (1 : ℝ), uDeriv s * v s := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro s _hs
          simp [uDeriv, v, div_eq_mul_inv]
    _ = ∫ s : ℝ in Set.Ioi (1 : ℝ),
          Real.log (n : ℝ) /
            (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s) := hmain

lemma mangoldt_weight_reciprocal_zeta_endpoint_evaluation :
    ∀ n : ℕ, 1 ≤ n ->
      (∫ s : ℝ in Set.Ioi (1 : ℝ),
        deriv (fun t : ℝ => 1 / ((riemannZeta (t : ℂ)).re)) s /
          Real.rpow (n : ℝ) s) = mangoldt_weight n := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    simpa [mangoldt_weight] using reciprocal_zeta_derivative_integral_one
  · have hn2 : 2 ≤ n := by omega
    simpa [mangoldt_weight, h1] using
      mangoldt_weight_reciprocal_zeta_integration_by_parts n hn2

lemma mangoldt_weight_von_mangoldt_invariant_recurrence :
    ∀ n : ℕ, 1 ≤ n ->
      (∑' q : ℕ,
        if 1 < q then
          mangoldt_weight (n * q) *
            (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
        else 0) = mangoldt_weight n := by
  intro n hn
  rw [mangoldt_weight_incoming_integral_bridge n hn,
    mangoldt_weight_reciprocal_zeta_endpoint_evaluation n hn]

structure mangoldt_adjoint_kernel_package (P U : ℕ → ℕ → ℝ) : Prop where
  invariant : mangoldt_von_mangoldt_downward_kernel_invariant P
  nonneg : ∀ n m : ℕ, 0 ≤ U n m
  row : ∀ n : ℕ, 1 ≤ n -> (∑' m : ℕ, U n m) = 1
  diag_zero : ∀ n : ℕ, U n n = 0
  formula : ∀ n m : ℕ, 1 ≤ n -> 1 ≤ m -> m ≠ n ->
    U n m = mangoldt_weight m / mangoldt_weight n * P m n
  support : ∀ n m : ℕ, U n m ≠ 0 -> n < m ∧ n ∣ m

lemma mangoldt_weight_positive :
    ∀ n : ℕ, 1 ≤ n -> 0 < mangoldt_weight n := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num [mangoldt_weight]
  · have hn2 : 2 ≤ n := by omega
    let f : ℝ → ℝ := fun u => Real.log (n : ℝ) * Real.rpow (n : ℝ) (-u) *
      (1 / ((riemannZeta ((1 + u : ℝ) : ℂ)).re))
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn2)
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn2) : (1 : ℝ) < n)
    have hf_int : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
      simpa [f] using mangoldt_weight_integral_change_of_variables_zeta_kernel_integrable n hn2
    have hf_pos : ∀ u : ℝ, 0 < u -> 0 < f u := by
      intro u hu
      have hz_pos : 0 < (riemannZeta ((1 + u : ℝ) : ℂ)).re := by
        exact riemannZeta_re_pos_of_one_lt (by linarith : 1 < 1 + u)
      exact mul_pos (mul_pos hlog_pos (Real.rpow_pos_of_pos hn_pos (-u)))
        (one_div_pos.mpr hz_pos)
    have hf_nonneg_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] f := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (μ := MeasureTheory.volume) (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))] with u hu
      exact (hf_pos u (by simpa [Set.mem_Ioi] using hu)).le
    have hmeasure : 0 < MeasureTheory.volume (Function.support f ∩ Set.Ioi (0 : ℝ)) := by
      have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Function.support f ∩ Set.Ioi (0 : ℝ) := by
        intro u hu
        constructor
        · exact (hf_pos u hu.1).ne'
        · exact hu.1
      exact lt_of_lt_of_le
        ((MeasureTheory.Measure.measure_Ioo_pos (μ := MeasureTheory.volume)).2
          (by norm_num : (0 : ℝ) < 1))
        (MeasureTheory.measure_mono hsub)
    have hint_pos : 0 < ∫ u : ℝ in Set.Ioi (0 : ℝ), f u := by
      exact (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hf_nonneg_ae hf_int).2 hmeasure
    rw [mangoldt_weight_integral_change_of_variables_mangoldt_laplace n hn2]
    exact mul_pos (one_div_pos.mpr hn_pos) hint_pos

lemma mangoldt_von_mangoldt_downward_kernel_invariant_exists :
    ∃ P : ℕ → ℕ → ℝ, mangoldt_von_mangoldt_downward_kernel_invariant P := by
  classical
  let P : ℕ → ℕ → ℝ := fun n m =>
    if n = 1 then
      if m = 1 then 1 else 0
    else if m ∣ n ∧ m < n then
      ArithmeticFunction.vonMangoldt (n / m) / Real.log (n : ℝ)
    else 0
  have htransition : ∀ n q : ℕ, 2 ≤ n -> 1 < q -> q ∣ n ->
      P n (n / q) = ArithmeticFunction.vonMangoldt q / Real.log (n : ℝ) := by
    intro n q hn hq hqdiv
    have hn_ne_one : n ≠ 1 := by omega
    have hdiv : n / q ∣ n ∧ n / q < n := by
      constructor
      · exact Nat.div_dvd_of_dvd hqdiv
      · have hqpos : 0 < q := by omega
        rw [Nat.div_lt_iff_lt_mul hqpos]
        have hnpos : 0 < n := by omega
        simpa using Nat.mul_lt_mul_of_pos_left hq hnpos
    have hq_eq : n / (n / q) = q := by
      exact Nat.div_div_self hqdiv (by omega)
    simp [P, hn_ne_one, hdiv, hq_eq]
  have hincoming : ∀ n : ℕ, 1 ≤ n ->
      (∑' q : ℕ, if 1 < q then mangoldt_weight (n * q) * P (n * q) n else 0) =
        mangoldt_weight n := by
    intro n hn
    trans (∑' q : ℕ,
      if 1 < q then
        mangoldt_weight (n * q) *
          (ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ))
      else 0)
    · apply tsum_congr
      intro q
      by_cases hq : 1 < q
      · rw [if_pos hq, if_pos hq]
        have hnq_two : 2 ≤ n * q := by
          have hq_two : 2 ≤ q := by omega
          simpa using Nat.mul_le_mul hn hq_two
        have hq_dvd : q ∣ n * q := ⟨n, by rw [mul_comm]⟩
        have hdiv_eq : (n * q) / q = n := by
          rw [mul_comm]
          exact Nat.mul_div_right n (by omega : 0 < q)
        have hp : P (n * q) n =
            ArithmeticFunction.vonMangoldt q / Real.log ((n * q : ℕ) : ℝ) := by
          simpa [hdiv_eq] using htransition (n * q) q hnq_two hq hq_dvd
        rw [hp]
      · rw [if_neg hq, if_neg hq]
    · exact mangoldt_weight_von_mangoldt_invariant_recurrence n hn
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, htransition, hincoming⟩
  · intro n m
    dsimp [P]
    split_ifs with hn hm hmdiv
    · positivity
    · positivity
    · have hn_gt_one : 1 < n := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        exact Real.log_pos (by exact_mod_cast hn_gt_one : (1 : ℝ) < n)
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog_pos.le
    · positivity
  · intro n hnpos
    by_cases hn_one : n = 1
    · subst n
      calc
        (∑' m : ℕ, P 1 m) = ∑ m ∈ ({1} : Finset ℕ), P 1 m := by
          refine tsum_eq_sum (s := ({1} : Finset ℕ)) ?_
          intro m hm
          have hm_ne : m ≠ 1 := by simpa using hm
          simp [P, hm_ne]
        _ = 1 := by simp [P]
    · have hn_ne_zero : n ≠ 0 := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        have hn_gt_one : 1 < n := by omega
        exact Real.log_pos (by exact_mod_cast hn_gt_one : (1 : ℝ) < n)
      have hdiv_compl :
          (∑ m ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / m)) =
            ∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q := by
        refine Finset.sum_bij' (fun m _ => n / m) (fun q _ => n / q) ?_ ?_ ?_ ?_ ?_
        · intro m hm
          have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
          exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hmdvd, hn_ne_zero⟩
        · intro q hq
          have hqdvd : q ∣ n := (Nat.mem_divisors.mp hq).1
          exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hqdvd, hn_ne_zero⟩
        · intro m hm
          have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
          exact Nat.div_div_self hmdvd hn_ne_zero
        · intro q hq
          have hqdvd : q ∣ n := (Nat.mem_divisors.mp hq).1
          exact Nat.div_div_self hqdvd hn_ne_zero
        · intro m hm
          rfl
      calc
        (∑' m : ℕ, P n m) = ∑ m ∈ n.divisors, P n m := by
          refine tsum_eq_sum (s := n.divisors) ?_
          intro m hm
          have hmcond_false : ¬(m ∣ n ∧ m < n) := by
            intro hcond
            exact hm (Nat.mem_divisors.mpr ⟨hcond.1, hn_ne_zero⟩)
          simp [P, hn_one, hmcond_false]
        _ = ∑ m ∈ n.divisors,
            ArithmeticFunction.vonMangoldt (n / m) / Real.log (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
          have hm_le : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn_ne_zero) hmdvd
          by_cases hlt : m < n
          · have hmcond : m ∣ n ∧ m < n := ⟨hmdvd, hlt⟩
            simp [P, hn_one, hmcond]
          · have hm_eq : m = n := by omega
            subst m
            have hmcond_false : ¬(n ∣ n ∧ n < n) := by omega
            simp [P, hn_one, Nat.div_self (Nat.pos_of_ne_zero hn_ne_zero)]
        _ = (1 / Real.log (n : ℝ)) *
            (∑ m ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / m)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
        _ = (1 / Real.log (n : ℝ)) * Real.log (n : ℝ) := by
          rw [hdiv_compl, von_mangoldt_divisor_sum n]
        _ = 1 := by
          field_simp [hlog_pos.ne']
  · simp [P]
  · intro m hm
    simp [P, hm]
  · intro n m hn hP
    have hn_ne_one : n ≠ 1 := by omega
    by_cases hmcond : m ∣ n ∧ m < n
    · exact hmcond
    · exfalso
      have hzero : P n m = 0 := by simp [P, hn_ne_one, hmcond]
      exact hP hzero

lemma mangoldt_adjoint_kernel_package_exists :
    ∃ (P : ℕ → ℕ → ℝ) (U : ℕ → ℕ → ℝ),
      mangoldt_adjoint_kernel_package P U := by
  classical
  rcases mangoldt_von_mangoldt_downward_kernel_invariant_exists with ⟨P, hPpkg⟩
  let U : ℕ → ℕ → ℝ := fun n m =>
    if 1 ≤ n ∧ 1 ≤ m ∧ m ≠ n then
      mangoldt_weight m / mangoldt_weight n * P m n
    else 0
  refine ⟨P, U, ?_⟩
  rcases hPpkg with
    ⟨hP_nonneg, hP_row, hP_one, hP_one_zero, hP_support, hP_rule, hP_incoming⟩
  have hPpkg' : mangoldt_von_mangoldt_downward_kernel_invariant P := by
    exact ⟨hP_nonneg, hP_row, hP_one, hP_one_zero, hP_support, hP_rule, hP_incoming⟩
  have hrow : ∀ n : ℕ, 1 ≤ n -> (∑' m : ℕ, U n m) = 1 := by
    intro n hn
    let F : ℕ → ℝ := fun m =>
      if 1 ≤ m ∧ m ≠ n then mangoldt_weight m / mangoldt_weight n * P m n else 0
    have hUF : ∀ m : ℕ, U n m = F m := by
      intro m
      by_cases hm : 1 ≤ m ∧ m ≠ n
      · have hcond : 1 ≤ n ∧ 1 ≤ m ∧ m ≠ n := ⟨hn, hm.1, hm.2⟩
        simp [U, F, hcond]
      · have hcond : ¬(1 ≤ n ∧ 1 ≤ m ∧ m ≠ n) := by
          intro h
          exact hm ⟨h.2.1, h.2.2⟩
        simp [U, F, hm]
    have hsupport : Function.support F ⊆ Set.range (fun q : ℕ => n * q) := by
      intro m hmF
      by_cases hmcond : 1 ≤ m ∧ m ≠ n
      · have hPmn : P m n ≠ 0 := by
          intro hp
          apply hmF
          simp [F, hmcond, hp]
        have hm_two : 2 ≤ m := by
          by_cases hm1 : m = 1
          · subst m
            have hpzero : P 1 n = 0 := hP_one_zero n (by
              intro hn1
              exact hmcond.2 hn1.symm)
            exact False.elim (hPmn hpzero)
          · omega
        have hsupp := hP_support m n hm_two hPmn
        exact ⟨m / n, Nat.mul_div_cancel' hsupp.1⟩
      · exfalso
        apply hmF
        simp [F, hmcond]
    have hinj : Function.Injective (fun q : ℕ => n * q) := by
      intro a b hab
      exact Nat.mul_left_cancel (by omega : 0 < n) hab
    have hreindex : (∑' q : ℕ, F (n * q)) = ∑' m : ℕ, F m := by
      exact Function.Injective.tsum_eq hinj hsupport
    calc
      (∑' m : ℕ, U n m) = ∑' m : ℕ, F m := by
        apply tsum_congr
        intro m
        exact hUF m
      _ = ∑' q : ℕ, F (n * q) := hreindex.symm
      _ = ∑' q : ℕ, (1 / mangoldt_weight n) *
          (if 1 < q then mangoldt_weight (n * q) * P (n * q) n else 0) := by
        apply tsum_congr
        intro q
        by_cases hq : 1 < q
        · rw [if_pos hq]
          have hnq_pos : 1 ≤ n * q := by
            have hn_pos : 0 < n := by omega
            have hq_pos : 0 < q := by omega
            exact Nat.succ_le_iff.mpr (Nat.mul_pos hn_pos hq_pos)
          have hnq_ne : n * q ≠ n := by
            intro hmul
            have hq_one : q = 1 := by
              exact Nat.mul_left_cancel (by omega : 0 < n) (by simpa using hmul)
            omega
          have hcond : 1 ≤ n * q ∧ n * q ≠ n := ⟨hnq_pos, hnq_ne⟩
          simp [F, hcond]
          ring
        · rw [if_neg hq]
          have hq_cases : q = 0 ∨ q = 1 := by omega
          rcases hq_cases with hq0 | hq1
          · subst q
            simp [F]
          · subst q
            simp [F]
      _ = (1 / mangoldt_weight n) *
          (∑' q : ℕ, if 1 < q then mangoldt_weight (n * q) * P (n * q) n else 0) := by
        rw [tsum_mul_left]
      _ = (1 / mangoldt_weight n) * mangoldt_weight n := by
        rw [hP_incoming n hn]
      _ = 1 := by
        field_simp [(mangoldt_weight_positive n hn).ne']
  refine ⟨hPpkg', ?_, hrow, ?_, ?_, ?_⟩
  · intro n m
    by_cases hcond : 1 ≤ n ∧ 1 ≤ m ∧ m ≠ n
    · dsimp [U]
      rw [if_pos hcond]
      exact mul_nonneg
        (div_nonneg (mangoldt_weight_positive m hcond.2.1).le
          (mangoldt_weight_positive n hcond.1).le)
        (hP_nonneg m n)
    · dsimp [U]
      rw [if_neg hcond]
  · intro n
    simp [U]
  · intro n m hn hm hne
    simp [U, hn, hm, hne]
  · intro n m hU
    by_cases hcond : 1 ≤ n ∧ 1 ≤ m ∧ m ≠ n
    · have hPmn : P m n ≠ 0 := by
        intro hp
        apply hU
        simp [U, hcond, hp]
      have hm_two : 2 ≤ m := by
        by_cases hm1 : m = 1
        · subst m
          have hpzero : P 1 n = 0 := hP_one_zero n (by
            intro hn1
            exact hcond.2.2 hn1.symm)
          exact False.elim (hPmn hpzero)
        · omega
      have hsupp := hP_support m n hm_two hPmn
      exact ⟨hsupp.2, hsupp.1⟩
    · exfalso
      apply hU
      simp [U, hcond]

abbrev mangoldt_adjoint_kernel_markov_law {Ω : Type} [MeasurableSpace Ω]
    (U : ℕ → ℕ → ℝ) (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ k n m : ℕ,
    μ {ω : Ω | path ω k = n ∧ path ω (k + 1) = m} =
      ENNReal.ofReal (U n m) * μ {ω : Ω | path ω k = n}

abbrev mangoldt_adjoint_supported_path (U : ℕ → ℕ → ℝ) (path : ℕ → ℕ) : Prop :=
  path 0 = 1 ∧
    strictly_increasing_divisibility_chain path ∧
      ∀ k : ℕ, U (path k) (path (k + 1)) ≠ 0

def mangoldt_adjoint_supported_path_space (U : ℕ → ℕ → ℝ) : Type :=
  {path : ℕ → ℕ // mangoldt_adjoint_supported_path U path}

structure mangoldt_adjoint_kernel_path_data {Ω : Type} [MeasurableSpace Ω]
    (U : ℕ → ℕ → ℝ) (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop where
  mass : μ Set.univ = 1
  start : ∀ ω : Ω, path ω 0 = 1
  chain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω)
  measurable : ∀ k : ℕ, Measurable fun ω : Ω => path ω k
  support : ∀ ω : Ω, ∀ k : ℕ, U (path ω k) (path ω (k + 1)) ≠ 0
  markov : mangoldt_adjoint_kernel_markov_law U μ path

lemma mangoldt_adjoint_kernel_path_data_exists :
    ∃ (P : ℕ → ℕ → ℝ) (U : ℕ → ℕ → ℝ) (Ω : Type) (mΩ : MeasurableSpace Ω)
      (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ),
        mangoldt_adjoint_kernel_package P U ∧
          @mangoldt_adjoint_kernel_path_data Ω mΩ U μ path := by
  classical
  rcases mangoldt_adjoint_kernel_package_exists with ⟨P, U, hpack⟩
  rcases hpack with ⟨hPpkg, hU_nonneg, hU_row, hU_diag, hU_formula, hU_support⟩
  let rowPMF : ℕ → PMF ℕ := fun n =>
    if hn : 1 ≤ n then
      ⟨fun m => ENNReal.ofReal (U n m), by
        have hsumm : Summable fun m : ℕ => U n m := by
          by_contra hns
          have hzero : (∑' m : ℕ, U n m) = 0 := tsum_eq_zero_of_not_summable hns
          have hone : (∑' m : ℕ, U n m) = 1 := hU_row n hn
          linarith
        have htsum : (∑' m : ℕ, ENNReal.ofReal (U n m)) = 1 := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => hU_nonneg n m) hsumm,
            hU_row n hn]
          norm_num
        exact (ENNReal.summable.hasSum_iff).2 htsum⟩
    else
      PMF.pure 1
  let K : ProbabilityTheory.Kernel ℕ ℕ :=
    ProbabilityTheory.Kernel.ofFunOfCountable fun n => (rowPMF n).toMeasure
  have hK_markov : ProbabilityTheory.IsMarkovKernel K := by
    refine ⟨?_⟩
    intro n
    change MeasureTheory.IsProbabilityMeasure ((rowPMF n).toMeasure)
    infer_instance
  have hK_singleton : ∀ n m : ℕ, 1 ≤ n -> K n ({m} : Set ℕ) = ENNReal.ofReal (U n m) := by
    intro n m hn
    change (rowPMF n).toMeasure ({m} : Set ℕ) = ENNReal.ofReal (U n m)
    simp [rowPMF, hn, PMF.toMeasure_apply_singleton]
    rfl
  have hpack : mangoldt_adjoint_kernel_package P U :=
    ⟨hPpkg, hU_nonneg, hU_row, hU_diag, hU_formula, hU_support⟩
  haveI : ProbabilityTheory.IsMarkovKernel K := hK_markov
  let X : ℕ → Type := fun _ => ℕ
  let step : (n : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic n) → X i) (X (n + 1)) := fun n =>
    ProbabilityTheory.Kernel.comap K (fun x => x ⟨n, by simp⟩) (by fun_prop)
  have hstep_markov : ∀ n : ℕ, ProbabilityTheory.IsMarkovKernel (step n) := by
    intro n
    dsimp [step]
    infer_instance
  haveI : ∀ n : ℕ, ProbabilityTheory.IsMarkovKernel (step n) := hstep_markov
  let μFull : MeasureTheory.Measure ((n : ℕ) → X n) :=
    ProbabilityTheory.Kernel.trajMeasure (MeasureTheory.Measure.dirac 1) step
  let pathFull : ((n : ℕ) → X n) → ℕ → ℕ := fun ω k => ω k
  have hfull_markov_pos : ∀ k n m : ℕ, 1 ≤ n ->
      μFull {ω : (n : ℕ) → X n | pathFull ω k = n ∧ pathFull ω (k + 1) = m} =
        ENNReal.ofReal (U n m) * μFull {ω : (n : ℕ) → X n | pathFull ω k = n} := by
    intro k n m hn
    let s : Set ((i : Finset.Iic k) → X i) := {x | x ⟨k, by simp⟩ = n}
    let t : Set (X (k + 1)) := {m}
    have hs : MeasurableSet s := by
      dsimp [s]
      measurability
    have ht : MeasurableSet t := by
      dsimp [t]
      measurability
    have hcomp :
        MeasureTheory.Measure.compProd (μFull.map (Preorder.frestrictLe (π := X) k)) (step k) =
          μFull.map (fun x : (n : ℕ) → X n =>
            (Preorder.frestrictLe (π := X) k x, x (k + 1))) := by
      simpa [μFull] using
        (ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
          (μ₀ := MeasureTheory.Measure.dirac 1) (κ := step) (a := k))
    have hpair := congrArg
      (fun μ : MeasureTheory.Measure (((i : Finset.Iic k) → X i) × X (k + 1)) =>
        μ (s ×ˢ t)) hcomp
    have hright :
        μFull.map (fun x : (n : ℕ) → X n =>
          (Preorder.frestrictLe (π := X) k x, x (k + 1))) (s ×ˢ t) =
          μFull {ω : (n : ℕ) → X n | pathFull ω k = n ∧ pathFull ω (k + 1) = m} := by
      rw [MeasureTheory.Measure.map_apply]
      · congr 1
      · fun_prop
      · exact hs.prod ht
    have hleft :
        MeasureTheory.Measure.compProd
          (μFull.map (Preorder.frestrictLe (π := X) k)) (step k) (s ×ˢ t) =
          ∫⁻ x in s, step k x t ∂(μFull.map (Preorder.frestrictLe (π := X) k)) := by
      rw [MeasureTheory.Measure.compProd_apply_prod hs ht]
    have hbase :
        μFull.map (Preorder.frestrictLe (π := X) k) s =
          μFull {ω : (n : ℕ) → X n | pathFull ω k = n} := by
      rw [MeasureTheory.Measure.map_apply]
      · simp [s, pathFull]
      · fun_prop
      · exact hs
    have hintegral :
        ∫⁻ x in s, step k x t ∂(μFull.map (Preorder.frestrictLe (π := X) k)) =
          ENNReal.ofReal (U n m) * μFull.map (Preorder.frestrictLe (π := X) k) s := by
      rw [MeasureTheory.setLIntegral_congr_fun hs]
      · rw [MeasureTheory.setLIntegral_const]
      · intro x hx
        have hx' : x ⟨k, by simp⟩ = n := by simpa [s] using hx
        calc
          step k x t = K (x ⟨k, by simp⟩) t := rfl
          _ = K n ({m} : Set ℕ) := by simp [t, hx']
          _ = ENNReal.ofReal (U n m) := hK_singleton n m hn
    calc
      μFull {ω : (n : ℕ) → X n | pathFull ω k = n ∧ pathFull ω (k + 1) = m}
          = μFull.map (fun x : (n : ℕ) → X n =>
              (Preorder.frestrictLe (π := X) k x, x (k + 1))) (s ×ˢ t) :=
            hright.symm
      _ = MeasureTheory.Measure.compProd
            (μFull.map (Preorder.frestrictLe (π := X) k)) (step k) (s ×ˢ t) :=
          hpair.symm
      _ = ∫⁻ x in s, step k x t ∂(μFull.map (Preorder.frestrictLe (π := X) k)) := hleft
      _ = ENNReal.ofReal (U n m) * μFull.map (Preorder.frestrictLe (π := X) k) s := hintegral
      _ = ENNReal.ofReal (U n m) * μFull {ω : (n : ℕ) → X n | pathFull ω k = n} := by rw [hbase]
  have hstart_full : μFull {ω : (n : ℕ) → X n | pathFull ω 0 = 1} = 1 := by
    dsimp [μFull, ProbabilityTheory.Kernel.trajMeasure, pathFull]
    rw [MeasureTheory.Measure.map_dirac]
    rw [MeasureTheory.Measure.dirac_bind]
    · let x0 : (i : Finset.Iic 0) → X i :=
        (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm 1
      change (ProbabilityTheory.Kernel.traj step 0 x0) {ω : (n : ℕ) → X n | ω 0 = 1} = 1
      have hmap := ProbabilityTheory.Kernel.traj_map_updateFinset (κ := step) (n := 0) (x := x0)
      rw [← hmap]
      rw [MeasureTheory.Measure.map_apply]
      · simp [Function.updateFinset, x0]
      · fun_prop
      · measurability
    · exact (ProbabilityTheory.Kernel.traj step 0).measurable
  let good : Set ((n : ℕ) → X n) :=
    {ω | pathFull ω 0 = 1 ∧ ∀ k : ℕ, U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0}
  have hstart_ae : ∀ᵐ ω ∂μFull, pathFull ω 0 = 1 := by
    exact (MeasureTheory.ae_iff_prob_eq_one (by measurability)).2 hstart_full
  have htrans_cond_ae : ∀ k : ℕ,
      ∀ᵐ ω ∂μFull,
        1 ≤ pathFull ω k -> U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0 := by
    intro k
    let pair : ((n : ℕ) → X n) → ℕ × ℕ := fun ω => (pathFull ω k, pathFull ω (k + 1))
    let bad : Set (ℕ × ℕ) := {p | 1 ≤ p.1 ∧ U p.1 p.2 = 0}
    have hbad_count : bad.Countable := by
      exact bad.to_countable
    have hbad_zero : μFull (pair ⁻¹' bad) = 0 := by
      rw [MeasureTheory.measure_preimage_eq_zero_iff_of_countable hbad_count]
      intro p hp
      rcases p with ⟨n, m⟩
      have hn : 1 ≤ n := hp.1
      have hzero : U n m = 0 := hp.2
      have h := hfull_markov_pos k n m hn
      change μFull {ω : (i : ℕ) → X i | (pathFull ω k, pathFull ω (k + 1)) = (n, m)} = 0
      simpa [Prod.ext_iff, hzero] using h
    rw [MeasureTheory.ae_iff]
    change μFull {ω : (n : ℕ) → X n |
      ¬(1 ≤ pathFull ω k -> U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0)} = 0
    simpa [pair, bad, Classical.not_imp, not_not, and_comm] using hbad_zero
  have hpos_ae : ∀ k : ℕ, ∀ᵐ ω ∂μFull, 1 ≤ pathFull ω k := by
    intro k
    induction k with
    | zero =>
        filter_upwards [hstart_ae] with ω hω
        simp [pathFull, hω]
    | succ k ih =>
        filter_upwards [ih, htrans_cond_ae k] with ω hpos htrans
        have hne : U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0 := htrans hpos
        exact le_trans hpos (le_of_lt (hU_support (pathFull ω k) (pathFull ω (k + 1)) hne).1)
  have hsupport_ae : ∀ᵐ ω ∂μFull,
      ∀ k : ℕ, U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards [hpos_ae k, htrans_cond_ae k] with ω hpos htrans
    exact htrans hpos
  have hgood_ae : ∀ᵐ ω ∂μFull, ω ∈ good := by
    filter_upwards [hstart_ae, hsupport_ae] with ω hstart hsupp
    exact ⟨hstart, hsupp⟩
  have hgood_meas : MeasurableSet good := by
    have hcoord : ∀ k : ℕ, Measurable fun ω : (n : ℕ) → X n => pathFull ω k := by
      intro k
      simpa [pathFull] using (measurable_pi_apply k : Measurable fun ω : (n : ℕ) → X n => ω k)
    have hUfun : Measurable fun p : ℕ × ℕ => U p.1 p.2 := measurable_of_countable _
    have htrans_meas : ∀ k : ℕ,
        MeasurableSet {ω : (n : ℕ) → X n | U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0} := by
      intro k
      have hp : Measurable fun ω : (n : ℕ) → X n => (pathFull ω k, pathFull ω (k + 1)) :=
        (hcoord k).prodMk (hcoord (k + 1))
      exact (measurableSet_singleton (0 : ℝ)).compl.preimage (hUfun.comp hp)
    have hstart_meas : MeasurableSet {ω : (n : ℕ) → X n | pathFull ω 0 = 1} :=
      (measurableSet_singleton (1 : ℕ)).preimage (hcoord 0)
    rw [show good = ({ω : (n : ℕ) → X n | pathFull ω 0 = 1} ∩
      ⋂ k : ℕ, {ω : (n : ℕ) → X n | U (pathFull ω k) (pathFull ω (k + 1)) ≠ 0}) by
      ext ω
      simp [good]]
    exact hstart_meas.inter (MeasurableSet.iInter htrans_meas)
  let Ω : Type := good
  let μ : MeasureTheory.Measure Ω := μFull.comap (Subtype.val : Ω -> ((n : ℕ) → X n))
  let path : Ω → ℕ → ℕ := fun ω k => pathFull ω.1 k
  have hmeasEmb : MeasurableEmbedding (Subtype.val : Ω -> ((n : ℕ) → X n)) := by
    simpa [Ω] using MeasurableEmbedding.subtype_coe hgood_meas
  have hmp : MeasureTheory.MeasurePreserving (Subtype.val : Ω -> ((n : ℕ) → X n)) μ μFull := by
    have hmp0 := MeasureTheory.measurePreserving_subtype_coe (μa := μFull) hgood_meas
    have hres : μFull.restrict good = μFull :=
      MeasureTheory.Measure.restrict_eq_self_of_ae_mem hgood_ae
    simpa [Ω, μ, hres] using hmp0
  refine ⟨P, U, Ω, inferInstance, μ, path, hpack, ?_⟩
  have hpath_pos : ∀ (ω : Ω) (k : ℕ), 1 ≤ path ω k := by
    intro ω k
    induction k with
    | zero =>
        have hstart : path ω 0 = 1 := ω.property.1
        simp [path, hstart]
    | succ k ih =>
        have hne : U (path ω k) (path ω (k + 1)) ≠ 0 := ω.property.2 k
        exact le_trans ih (le_of_lt (hU_support (path ω k) (path ω (k + 1)) hne).1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      μ Set.univ = μFull Set.univ := by
        simpa using hmp.measure_preimage_emb hmeasEmb Set.univ
      _ = 1 := by simp
  · intro ω
    exact ω.property.1
  · intro ω
    refine ⟨?_, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro k
      exact (hU_support (path ω k) (path ω (k + 1)) (ω.property.2 k)).1
    · intro k
      exact (hU_support (path ω k) (path ω (k + 1)) (ω.property.2 k)).2
  · intro k
    change Measurable
      (((fun ω : (n : ℕ) → X n => ω k) ∘
        (Subtype.val : Ω -> ((n : ℕ) → X n))))
    exact (measurable_pi_apply k : Measurable fun ω : (n : ℕ) → X n => ω k).comp
      measurable_subtype_coe
  · intro ω k
    exact ω.property.2 k
  · intro k n m
    by_cases hn : 1 ≤ n
    · calc
        μ {ω : Ω | path ω k = n ∧ path ω (k + 1) = m}
            = μFull {ω : (i : ℕ) → X i | pathFull ω k = n ∧ pathFull ω (k + 1) = m} := by
              simpa [path, pathFull] using
                hmp.measure_preimage_emb hmeasEmb
                  {ω : (i : ℕ) → X i | pathFull ω k = n ∧ pathFull ω (k + 1) = m}
        _ = ENNReal.ofReal (U n m) * μFull {ω : (i : ℕ) → X i | pathFull ω k = n} :=
              hfull_markov_pos k n m hn
        _ = ENNReal.ofReal (U n m) * μ {ω : Ω | path ω k = n} := by
              congr 1
              simpa [path, pathFull] using
                (hmp.measure_preimage_emb hmeasEmb {ω : (i : ℕ) → X i | pathFull ω k = n}).symm
    · have hn0 : n = 0 := by omega
      have hbase_empty : {ω : Ω | path ω k = n} = ∅ := by
        ext ω
        constructor
        · intro hω
          have hpos := hpath_pos ω k
          have hzero : path ω k = 0 := by simpa [hn0] using hω
          omega
        · intro hω
          cases hω
      have hpair_empty : {ω : Ω | path ω k = n ∧ path ω (k + 1) = m} = ∅ := by
        ext ω
        constructor
        · intro hω
          have hpos := hpath_pos ω k
          have hzero : path ω k = 0 := by simpa [hn0] using hω.1
          omega
        · intro hω
          cases hω
      simp [hbase_empty, hpair_empty]

structure mangoldt_adjoint_random_model {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop where
  mass : μ Set.univ = 1
  chain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω)
  measurable : ∀ k : ℕ, Measurable fun ω : Ω => path ω k
  visit : mangoldt_adjoint_visit_identity μ path
  second_moment : mangoldt_adjoint_second_moment_bound μ path
  reverse_fatou : mangoldt_adjoint_reverse_fatou_extraction_principle μ path

structure mangoldt_adjoint_constructed_path_data {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop where
  mass : μ Set.univ = 1
  chain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω)
  measurable : ∀ k : ℕ, Measurable fun ω : Ω => path ω k
  visit : mangoldt_adjoint_visit_identity μ path

lemma mangoldt_adjoint_visit_identity_from_kernel_path_data {Ω : Type}
    [MeasurableSpace Ω] {P U : ℕ → ℕ → ℝ} {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_kernel_package P U ->
      mangoldt_adjoint_kernel_path_data U μ path ->
        mangoldt_adjoint_visit_identity μ path := by
  classical
  intro hpack hdata
  rcases hpack with
    ⟨hPpkg, hU_nonneg, hU_row, hU_diag, hU_formula, hU_support⟩
  rcases hPpkg with
    ⟨hP_nonneg, hP_row, hP_one, hP_one_zero, hP_support, hP_rule, hP_incoming⟩
  rcases hdata with ⟨hμ, hstart, hchain, hmeas, hsupp_path, hmarkov⟩
  have hpath_ge : ∀ ω k, k + 1 ≤ path ω k := by
    intro ω k
    have h := StrictMono.add_le_nat (hchain ω).1 k 0
    simpa [hstart ω] using h
  unfold mangoldt_adjoint_visit_identity
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  have hno_zero : ∀ k : ℕ, {ω : Ω | path ω k = 0} = ∅ := by
    intro k
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hk := hpath_ge ω k
    omega
  cases n with
  | zero =>
      simp [hno_zero, mangoldt_weight]
  | succ n =>
      cases n with
      | zero =>
          have htail_zero : ∀ k ∉ ({0} : Finset ℕ), μ {ω : Ω | path ω k = 1} = 0 := by
            intro k hk
            have hkpos : 1 ≤ k := by
              simp at hk
              omega
            have hset : {ω : Ω | path ω k = 1} = ∅ := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro h
              have hge := hpath_ge ω k
              omega
            simp [hset]
          have hzero_event : {ω : Ω | path ω 0 = 1} = Set.univ := by
            ext ω
            simp [hstart ω]
          calc
            (∑' k : ℕ, μ {ω : Ω | path ω k = 1}) =
                ∑ k ∈ ({0} : Finset ℕ), μ {ω : Ω | path ω k = 1} := by
              exact tsum_eq_sum htail_zero
            _ = μ {ω : Ω | path ω 0 = 1} := by simp
            _ = ENNReal.ofReal (mangoldt_weight 1) := by
              simp [hzero_event, hμ, mangoldt_weight]
      | succ n =>
          have hstep_cover : ∀ k : ℕ,
              {ω : Ω | path ω (k + 1) = n + 1 + 1} =
                ⋃ p ∈ Finset.range (n + 1 + 1),
                  {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1} := by
            intro k
            ext ω
            constructor
            · intro hω
              refine Set.mem_iUnion.mpr ⟨path ω k, ?_⟩
              refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
              · simp only [Finset.mem_range, Order.lt_add_one_iff]
                have hmono : path ω k < path ω (k + 1) := by
                  simpa [Nat.succ_eq_add_one] using (hchain ω).1 (Nat.lt_succ_self k)
                have hlt : path ω k ≤ n + 1 := by
                  rw [hω] at hmono
                  omega
                exact hlt
              · exact ⟨rfl, hω⟩
            · intro hω
              rcases Set.mem_iUnion.mp hω with ⟨p, hp⟩
              rcases Set.mem_iUnion.mp hp with ⟨hp_range, hp_event⟩
              exact hp_event.2
          have hstep_measure : ∀ k : ℕ,
              μ {ω : Ω | path ω (k + 1) = n + 1 + 1} =
                ∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (U p (n + 1 + 1)) * μ {ω : Ω | path ω k = p} := by
            intro k
            have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1 + 1)))
                (fun p : ℕ => {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1}) := by
              intro p hp q hq hpq
              change Disjoint
                {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1}
                {ω : Ω | path ω k = q ∧ path ω (k + 1) = n + 1 + 1}
              exact Set.disjoint_left.mpr (by
                intro ω hpω hqω
                exact hpq (by rw [← hpω.1, hqω.1]))
            have hmeas_step : ∀ p ∈ Finset.range (n + 1 + 1),
                MeasurableSet {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1} := by
              intro p hp
              exact (measurableSet_eq_fun (hmeas k) measurable_const).inter
                (measurableSet_eq_fun (hmeas (k + 1)) measurable_const)
            calc
              μ {ω : Ω | path ω (k + 1) = n + 1 + 1} =
                  μ (⋃ p ∈ Finset.range (n + 1 + 1),
                    {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1}) := by
                rw [hstep_cover k]
              _ = ∑ p ∈ Finset.range (n + 1 + 1),
                    μ {ω : Ω | path ω k = p ∧ path ω (k + 1) = n + 1 + 1} := by
                exact MeasureTheory.measure_biUnion_finset hdisj hmeas_step
              _ = ∑ p ∈ Finset.range (n + 1 + 1),
                    ENNReal.ofReal (U p (n + 1 + 1)) * μ {ω : Ω | path ω k = p} := by
                apply Finset.sum_congr rfl
                intro p hp
                exact hmarkov k p (n + 1 + 1)
          have htail_zero : ∀ k ∉ Finset.range (n + 1 + 1),
              μ {ω : Ω | path ω k = n + 1 + 1} = 0 := by
            intro k hk
            have hkge : n + 1 + 1 ≤ k := by
              simpa using hk
            have hset : {ω : Ω | path ω k = n + 1 + 1} = ∅ := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro hω
              have hge := hpath_ge ω k
              rw [hω] at hge
              omega
            rw [hset]
            simp
          have hzero_time : μ {ω : Ω | path ω 0 = n + 1 + 1} = 0 := by
            have hset : {ω : Ω | path ω 0 = n + 1 + 1} = ∅ := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro hω
              have h0 := hstart ω
              omega
            rw [hset]
            simp
          have hshift :
              (∑ k ∈ Finset.range (n + 1 + 1), μ {ω : Ω | path ω k = n + 1 + 1}) =
                ∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω (k + 1) = n + 1 + 1} := by
            calc
              (∑ k ∈ Finset.range (n + 1 + 1), μ {ω : Ω | path ω k = n + 1 + 1}) =
                  (∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω (k + 1) = n + 1 + 1}) +
                    μ {ω : Ω | path ω 0 = n + 1 + 1} := by
                rw [Finset.sum_range_succ']
              _ = ∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω (k + 1) = n + 1 + 1} := by
                rw [hzero_time, add_zero]
          have hprev_full : ∀ p ∈ Finset.range (n + 1 + 1),
              (∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω k = p}) =
                ∑' k : ℕ, μ {ω : Ω | path ω k = p} := by
            intro p hp
            symm
            refine tsum_eq_sum ?_
            intro k hk
            have hkge : n + 1 ≤ k := by
              simpa using hk
            have hp_le : p ≤ n + 1 := by
              simpa using hp
            have hset : {ω : Ω | path ω k = p} = ∅ := by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro hω
              have hge := hpath_ge ω k
              rw [hω] at hge
              omega
            rw [hset]
            simp
          have hrec :
              (∑' k : ℕ, μ {ω : Ω | path ω k = n + 1 + 1}) =
                ∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (U p (n + 1 + 1)) * ENNReal.ofReal (mangoldt_weight p) := by
            calc
              (∑' k : ℕ, μ {ω : Ω | path ω k = n + 1 + 1}) =
                  ∑ k ∈ Finset.range (n + 1 + 1), μ {ω : Ω | path ω k = n + 1 + 1} := by
                exact tsum_eq_sum htail_zero
              _ = ∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω (k + 1) = n + 1 + 1} := hshift
              _ = ∑ k ∈ Finset.range (n + 1),
                    ∑ p ∈ Finset.range (n + 1 + 1),
                      ENNReal.ofReal (U p (n + 1 + 1)) * μ {ω : Ω | path ω k = p} := by
                apply Finset.sum_congr rfl
                intro k hk
                exact hstep_measure k
              _ = ∑ p ∈ Finset.range (n + 1 + 1),
                    ∑ k ∈ Finset.range (n + 1),
                      ENNReal.ofReal (U p (n + 1 + 1)) * μ {ω : Ω | path ω k = p} := by
                rw [Finset.sum_comm]
              _ = ∑ p ∈ Finset.range (n + 1 + 1),
                    ENNReal.ofReal (U p (n + 1 + 1)) *
                      (∑ k ∈ Finset.range (n + 1), μ {ω : Ω | path ω k = p}) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [Finset.mul_sum]
              _ = ∑ p ∈ Finset.range (n + 1 + 1),
                    ENNReal.ofReal (U p (n + 1 + 1)) * ENNReal.ofReal (mangoldt_weight p) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [hprev_full p hp]
                exact congrArg (fun x => ENNReal.ofReal (U p (n + 1 + 1)) * x)
                  (ih p (by simpa using hp))
          have hN_pos : 1 ≤ n + 1 + 1 := by omega
          have hN_two : 2 ≤ n + 1 + 1 := by omega
          have hweightN_nonneg : 0 ≤ mangoldt_weight (n + 1 + 1) :=
            (mangoldt_weight_positive (n + 1 + 1) hN_pos).le
          have hterm_real : ∀ p ∈ Finset.range (n + 1 + 1),
              U p (n + 1 + 1) * mangoldt_weight p =
                mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p := by
            intro p hp
            by_cases hp0 : p = 0
            · subst p
              have hU0 : U 0 (n + 1 + 1) = 0 := by
                by_contra hne
                have hs := hU_support 0 (n + 1 + 1) hne
                rcases hs.2 with ⟨c, hc⟩
                omega
              have hP0 : P (n + 1 + 1) 0 = 0 := by
                by_contra hne
                have hs := hP_support (n + 1 + 1) 0 hN_two hne
                rcases hs.1 with ⟨c, hc⟩
                omega
              simp [hU0, hP0]
            · have hp_pos : 1 ≤ p := by omega
              have hp_ne : n + 1 + 1 ≠ p := by
                have hp_lt : p < n + 1 + 1 := by simpa using hp
                omega
              have hUf := hU_formula p (n + 1 + 1) hp_pos hN_pos hp_ne
              calc
                U p (n + 1 + 1) * mangoldt_weight p =
                    (mangoldt_weight (n + 1 + 1) / mangoldt_weight p * P (n + 1 + 1) p) *
                      mangoldt_weight p := by
                  rw [hUf]
                _ = mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p := by
                  field_simp [(mangoldt_weight_positive p hp_pos).ne']
          have hsum_terms :
              (∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (U p (n + 1 + 1)) * ENNReal.ofReal (mangoldt_weight p)) =
                ∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [← ENNReal.ofReal_mul (hU_nonneg p (n + 1 + 1)), hterm_real p hp]
          have hP_tail_zero : ∀ m ∉ Finset.range (n + 1 + 1), P (n + 1 + 1) m = 0 := by
            intro m hm
            by_contra hne
            have hmge : n + 1 + 1 ≤ m := by
              simpa using hm
            have hs := hP_support (n + 1 + 1) m hN_two hne
            omega
          have hP_sum_range : (∑ m ∈ Finset.range (n + 1 + 1), P (n + 1 + 1) m) = 1 := by
            have htsum : (∑' m : ℕ, P (n + 1 + 1) m) =
                ∑ m ∈ Finset.range (n + 1 + 1), P (n + 1 + 1) m := by
              exact tsum_eq_sum hP_tail_zero
            have hrow := hP_row (n + 1 + 1) hN_pos
            rw [htsum] at hrow
            exact hrow
          have hsum_weightP :
              (∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p)) =
                ENNReal.ofReal (mangoldt_weight (n + 1 + 1)) := by
            calc
              (∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p)) =
                  ENNReal.ofReal
                    (∑ p ∈ Finset.range (n + 1 + 1),
                      mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p) := by
                rw [ENNReal.ofReal_sum_of_nonneg]
                intro p hp
                exact mul_nonneg hweightN_nonneg (hP_nonneg (n + 1 + 1) p)
              _ = ENNReal.ofReal
                    (mangoldt_weight (n + 1 + 1) *
                      ∑ p ∈ Finset.range (n + 1 + 1), P (n + 1 + 1) p) := by
                rw [Finset.mul_sum]
              _ = ENNReal.ofReal (mangoldt_weight (n + 1 + 1)) := by
                rw [hP_sum_range, mul_one]
          calc
            (∑' k : ℕ, μ {ω : Ω | path ω k = n + 1 + 1}) =
                ∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (U p (n + 1 + 1)) * ENNReal.ofReal (mangoldt_weight p) := hrec
            _ = ∑ p ∈ Finset.range (n + 1 + 1),
                  ENNReal.ofReal (mangoldt_weight (n + 1 + 1) * P (n + 1 + 1) p) := hsum_terms
            _ = ENNReal.ofReal (mangoldt_weight (n + 1 + 1)) := hsum_weightP

abbrev mangoldt_adjoint_two_point_divisor_bound {Ω : Type}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in Filter.atTop,
    0 < Real.log (Real.log x) ∧
      mangoldt_adjoint_hit_second_moment μ path A x ≤
        ENNReal.ofReal
          (C * (∑' n : ℕ,
            (A ∩ real_initial_segment x).indicator
              (fun n : ℕ =>
                ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                  max (mangoldt_weight n) 0)) n))

lemma mangoldt_adjoint_card_factors_strict_of_dvd_lt {a b : ℕ}
    (ha : a ≠ 0) (hdvd : a ∣ b) (hlt : a < b) :
    ArithmeticFunction.cardFactors a < ArithmeticFunction.cardFactors b := by
  rcases hdvd with ⟨c, rfl⟩
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  have hc_gt_one : 1 < c := by
    have hmul : a * 1 < a * c := by
      simpa [Nat.mul_one] using hlt
    exact (Nat.mul_lt_mul_left hapos).mp hmul
  have hc_ne : c ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hc_gt_one)
  have homega_c_pos : 0 < ArithmeticFunction.cardFactors c := by
    exact ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hc_gt_one
  rw [ArithmeticFunction.cardFactors_mul ha hc_ne]
  exact Nat.lt_add_of_pos_right homega_c_pos

lemma mangoldt_adjoint_index_le_card_factors_of_strict_chain {n : ℕ → ℕ}
    (hchain : strictly_increasing_divisibility_chain n) :
    ∀ k : ℕ, k ≤ ArithmeticFunction.cardFactors (n k) := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hstep_lt : n k < n (k + 1) := hchain.1 (Nat.lt_succ_self k)
      have hstep_dvd : n k ∣ n (k + 1) := hchain.2 k
      have hne : n k ≠ 0 := by
        intro hzero
        have hnext_zero : n (k + 1) = 0 := by
          exact Nat.eq_zero_of_zero_dvd (by simpa [hzero] using hstep_dvd)
        omega
      have homega_lt :
          ArithmeticFunction.cardFactors (n k) <
            ArithmeticFunction.cardFactors (n (k + 1)) :=
        mangoldt_adjoint_card_factors_strict_of_dvd_lt hne hstep_dvd hstep_lt
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih homega_lt)

lemma mangoldt_adjoint_positive_of_strict_chain {n : ℕ → ℕ}
    (hchain : strictly_increasing_divisibility_chain n) :
    ∀ k : ℕ, 0 < n k := by
  intro k
  cases k with
  | zero =>
      by_contra hzero
      have hn0_zero : n 0 = 0 := by omega
      have hnext_zero : n 1 = 0 := by
        have hzero_dvd : 0 ∣ n 1 := by
          rw [← hn0_zero]
          exact hchain.2 0
        exact Nat.eq_zero_of_zero_dvd hzero_dvd
      have hlt : n 0 < n 1 := hchain.1 (Nat.zero_lt_one)
      omega
  | succ k =>
      have hlt : n 0 < n (k + 1) := hchain.1 (Nat.succ_pos k)
      omega

lemma mangoldt_adjoint_ennreal_tsum_ite_le (k : ℕ) (a : ENNReal) :
    (∑' i : ℕ, if i ≤ k then a else 0) = (k + 1 : ℕ) * a := by
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · have hsum :
        (∑ b ∈ Finset.range (k + 1), if b ≤ k then a else 0) =
          ∑ b ∈ Finset.range (k + 1), a := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      have hb_le : b ≤ k := Nat.lt_succ_iff.mp (by simpa using hb)
      simp [hb_le]
    rw [hsum]
    simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul]
  · intro i hi
    have hi_not_le : ¬ i ≤ k := by
      rw [Finset.mem_range] at hi
      omega
    simp [hi_not_le]

lemma mangoldt_adjoint_pair_measure_tsum_le_index {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (E : ℕ → Set Ω) :
    (∑' i : ℕ, ∑' j : ℕ, μ (E i ∩ E j)) ≤
      2 * (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k)) := by
  let lower : ℕ → ℕ → ENNReal := fun i j => if i ≤ j then μ (E j) else 0
  let upper : ℕ → ℕ → ENNReal := fun i j => if j ≤ i then μ (E i) else 0
  have hterm : ∀ i j : ℕ, μ (E i ∩ E j) ≤ lower i j + upper i j := by
    intro i j
    by_cases hij : i ≤ j
    · have hle : μ (E i ∩ E j) ≤ μ (E j) :=
        MeasureTheory.measure_mono Set.inter_subset_right
      exact hle.trans (by simp [lower, upper, hij])
    · have hji : j ≤ i := le_of_lt (Nat.lt_of_not_ge hij)
      have hle : μ (E i ∩ E j) ≤ μ (E i) :=
        MeasureTheory.measure_mono Set.inter_subset_left
      exact hle.trans (by simp [lower, upper, hij, hji])
  have hlower :
      (∑' i : ℕ, ∑' j : ℕ, lower i j) =
        ∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k) := by
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro j
    exact mangoldt_adjoint_ennreal_tsum_ite_le j (μ (E j))
  have hupper :
      (∑' i : ℕ, ∑' j : ℕ, upper i j) =
        ∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k) := by
    apply tsum_congr
    intro i
    exact mangoldt_adjoint_ennreal_tsum_ite_le i (μ (E i))
  calc
    (∑' i : ℕ, ∑' j : ℕ, μ (E i ∩ E j)) ≤
        ∑' i : ℕ, ∑' j : ℕ, (lower i j + upper i j) := by
      exact ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum (hterm i)
    _ = (∑' i : ℕ, ∑' j : ℕ, lower i j) +
        (∑' i : ℕ, ∑' j : ℕ, upper i j) := by
      simp_rw [ENNReal.tsum_add]
    _ = (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k)) +
        (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k)) := by
      rw [hlower, hupper]
    _ = 2 * (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (E k)) := by
      rw [two_mul]

lemma mangoldt_adjoint_weighted_hit_tsum_le_divisor_sum {Ω : Type}
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω))
    (hmeas : ∀ k : ℕ, Measurable fun ω : Ω => path ω k)
    (hvisit : mangoldt_adjoint_visit_identity μ path) (A : Set ℕ) (x : ℝ) :
    (∑' k : ℕ,
        ((k + 1 : ℕ) : ENNReal) *
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) ≤
      ENNReal.ofReal
        (∑' n : ℕ,
          (A ∩ real_initial_segment x).indicator
            (fun n : ℕ =>
              ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                max (mangoldt_weight n) 0)) n) := by
  classical
  let S : Set ℕ := A ∩ real_initial_segment x
  let rterm : ℕ → ℝ := fun n =>
    ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
      max (mangoldt_weight n) 0)
  have hSfinite : S.Finite := by
    rcases exists_nat_ge x with ⟨N, hN⟩
    refine (Set.finite_le_nat N).subset ?_
    intro n hn
    have hnle : (n : ℝ) ≤ N := by
      exact le_trans hn.2.2 hN
    exact_mod_cast hnle
  have hhit_eq : ∀ k : ℕ,
      {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
        (fun ω : Ω => path ω k) ⁻¹' S := by
    intro k
    ext ω
    constructor
    · intro hω
      exact ⟨hω.1,
        ⟨mangoldt_adjoint_positive_of_strict_chain (hchain ω) k, hω.2⟩⟩
    · intro hω
      exact ⟨hω.1, hω.2.2⟩
  have hper : ∀ k : ℕ,
      ((k + 1 : ℕ) : ENNReal) *
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} ≤
        ∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            μ {ω : Ω | path ω k = (n : ℕ)}) := by
    intro k
    have hfiber_meas :
        ∀ n : ℕ, n ∈ S -> MeasurableSet ((fun ω : Ω => path ω k) ⁻¹' ({n} : Set ℕ)) := by
      intro n hn
      exact hmeas k (measurableSet_singleton n)
    have hpartition :
        (∑' n : S, μ ((fun ω : Ω => path ω k) ⁻¹' ({(n : ℕ)} : Set ℕ))) =
          μ ((fun ω : Ω => path ω k) ⁻¹' S) :=
      MeasureTheory.tsum_measure_preimage_singleton hSfinite.countable hfiber_meas
    calc
      ((k + 1 : ℕ) : ENNReal) *
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
          ((k + 1 : ℕ) : ENNReal) *
            (∑' n : S, μ ((fun ω : Ω => path ω k) ⁻¹' ({(n : ℕ)} : Set ℕ))) := by
        rw [hpartition]
        simp [hhit_eq k]
      _ = ∑' n : S,
          ((k + 1 : ℕ) : ENNReal) *
            μ ((fun ω : Ω => path ω k) ⁻¹' ({(n : ℕ)} : Set ℕ)) := by
        rw [← ENNReal.tsum_mul_left]
      _ ≤ ∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            μ ((fun ω : Ω => path ω k) ⁻¹' ({(n : ℕ)} : Set ℕ))) := by
        refine ENNReal.tsum_le_tsum ?_
        intro n
        by_cases hk : k ≤ ArithmeticFunction.cardFactors (n : ℕ)
        · have hcoeff : ((k + 1 : ℕ) : ENNReal) ≤
              ((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) := by
            exact_mod_cast Nat.succ_le_succ hk
          exact mul_le_mul_of_nonneg_right hcoeff zero_le
        · have hempty : ((fun ω : Ω => path ω k) ⁻¹' ({(n : ℕ)} : Set ℕ)) = ∅ := by
            ext ω
            constructor
            · intro hω
              have hidx := mangoldt_adjoint_index_le_card_factors_of_strict_chain
                (hchain ω) k
              have hpath : path ω k = (n : ℕ) := by simpa using hω
              rw [hpath] at hidx
              exact False.elim (hk hidx)
            · intro hω
              cases hω
          simp [hempty]
      _ = ∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            μ {ω : Ω | path ω k = (n : ℕ)}) := by
        apply tsum_congr
        intro n
        rfl
  have hsum_le :
      (∑' k : ℕ,
          ((k + 1 : ℕ) : ENNReal) *
            μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) ≤
        ∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (mangoldt_weight (n : ℕ))) := by
    calc
      (∑' k : ℕ,
          ((k + 1 : ℕ) : ENNReal) *
            μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) ≤
          ∑' k : ℕ, ∑' n : S,
            (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
              μ {ω : Ω | path ω k = (n : ℕ)}) := by
        exact ENNReal.tsum_le_tsum hper
      _ = ∑' n : S, ∑' k : ℕ,
            (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
              μ {ω : Ω | path ω k = (n : ℕ)}) := by
        rw [ENNReal.tsum_comm]
      _ = ∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (mangoldt_weight (n : ℕ))) := by
        apply tsum_congr
        intro n
        rw [ENNReal.tsum_mul_left]
        exact congrArg
          (fun y => (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) * y))
          (hvisit (n : ℕ))
  have hterm_eq : ∀ n : S,
      (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
          ENNReal.ofReal (mangoldt_weight (n : ℕ))) =
        ENNReal.ofReal (rterm (n : ℕ)) := by
    intro n
    have hcoeff_nonneg :
        0 ≤ ((((ArithmeticFunction.cardFactors (n : ℕ) : ℕ) + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.zero_le (ArithmeticFunction.cardFactors (n : ℕ) + 1)
    have hcoeff_eq :
        (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal)) =
          ENNReal.ofReal ((((ArithmeticFunction.cardFactors (n : ℕ) : ℕ) + 1 : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_natCast]
    dsimp [rterm]
    rw [hcoeff_eq, ENNReal.ofReal_mul hcoeff_nonneg]
    simp
  have hreal_tsum :
      (∑' n : ℕ, S.indicator rterm n) = ∑ n ∈ hSfinite.toFinset, rterm n := by
    rw [tsum_eq_sum (s := hSfinite.toFinset)]
    · refine Finset.sum_congr rfl ?_
      intro n hn
      have hnS : n ∈ S := by
        simpa [Set.Finite.mem_toFinset] using hn
      simp [Set.indicator_of_mem hnS]
    · intro n hn
      have hnS : n ∉ S := by
        simpa [Set.Finite.mem_toFinset] using hn
      simp [Set.indicator_of_notMem hnS]
  have hsub_eq :
      (∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (mangoldt_weight (n : ℕ)))) =
        ENNReal.ofReal (∑' n : ℕ, S.indicator rterm n) := by
    letI : Fintype S := hSfinite.fintype
    calc
      (∑' n : S,
          (((ArithmeticFunction.cardFactors (n : ℕ) + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (mangoldt_weight (n : ℕ)))) =
          ∑' n : S, ENNReal.ofReal (rterm (n : ℕ)) := by
        exact tsum_congr hterm_eq
      _ = ∑ n : S, ENNReal.ofReal (rterm (n : ℕ)) := by
        simp
      _ = ∑ n ∈ hSfinite.toFinset, ENNReal.ofReal (rterm n) := by
        simpa using
          (Finset.sum_set_coe (s := S)
            (f := fun n : ℕ => ENNReal.ofReal (rterm n)))
      _ = ENNReal.ofReal (∑ n ∈ hSfinite.toFinset, rterm n) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n hn
        exact mul_nonneg (by exact_mod_cast Nat.zero_le (ArithmeticFunction.cardFactors n + 1))
          (le_max_right (mangoldt_weight n) 0)
      _ = ENNReal.ofReal (∑' n : ℕ, S.indicator rterm n) := by
        rw [hreal_tsum]
  exact hsum_le.trans (le_of_eq hsub_eq)

lemma mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_constructed_path_data μ path ->
      mangoldt_adjoint_two_point_divisor_bound μ path := by
  intro hdata
  unfold mangoldt_adjoint_two_point_divisor_bound
  intro A
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
  constructor
  · have hlog_gt_one : 1 < Real.log x := by
      simpa using Real.log_lt_log (Real.exp_pos 1) hx
    simpa using Real.log_pos hlog_gt_one
  · classical
    let hit : ℕ → Set Ω := fun k => {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}
    have hpair_le :
        mangoldt_adjoint_hit_second_moment μ path A x ≤
          2 * (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (hit k)) := by
      simpa [mangoldt_adjoint_hit_second_moment, hit, Set.inter_def, and_assoc]
        using mangoldt_adjoint_pair_measure_tsum_le_index μ hit
    have hone_le :
        (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (hit k)) ≤
          ENNReal.ofReal
            (∑' n : ℕ,
              (A ∩ real_initial_segment x).indicator
                (fun n : ℕ =>
                  ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                    max (mangoldt_weight n) 0)) n) := by
      simpa [hit] using
        mangoldt_adjoint_weighted_hit_tsum_le_divisor_sum hdata.chain hdata.measurable
          hdata.visit A x
    have htwo_le :
        2 * (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (hit k)) ≤
          ENNReal.ofReal
            (2 * (∑' n : ℕ,
              (A ∩ real_initial_segment x).indicator
                (fun n : ℕ =>
                  ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                    max (mangoldt_weight n) 0)) n)) := by
      calc
        2 * (∑' k : ℕ, ((k + 1 : ℕ) : ENNReal) * μ (hit k)) ≤
            2 * ENNReal.ofReal
              (∑' n : ℕ,
                (A ∩ real_initial_segment x).indicator
                  (fun n : ℕ =>
                    ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                      max (mangoldt_weight n) 0)) n) := by
          exact mul_le_mul_of_nonneg_left hone_le zero_le
        _ = ENNReal.ofReal
            (2 * (∑' n : ℕ,
              (A ∩ real_initial_segment x).indicator
                (fun n : ℕ =>
                  ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                    max (mangoldt_weight n) 0)) n)) := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) by norm_num)]
          norm_num
    exact hpair_le.trans htwo_le

noncomputable def mangoldt_log_reciprocal_partial_sum (t : ℝ) : ℝ :=
  ∑' q : ℕ,
    if 2 ≤ q ∧ (q : ℝ) ≤ t then
      ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
    else 0

lemma mangoldt_log_reciprocal_real_log_increment_error_bound {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ Real.log b - Real.log a - (b - a) / b ∧
      Real.log b - Real.log a - (b - a) / b ≤ (b - a) ^ 2 / (a * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hratio_pos : 0 < b / a := div_pos hb ha
  have hlog_eq : Real.log b - Real.log a = Real.log (b / a) := by
    rw [Real.log_div hb.ne' ha.ne']
  have hlow := Real.one_sub_inv_le_log_of_pos hratio_pos
  have hlow' : (b - a) / b ≤ Real.log (b / a) := by
    have hleft : 1 - (b / a)⁻¹ = (b - a) / b := by
      field_simp [ha.ne', hb.ne']
    rw [← hleft]
    exact hlow
  have hupp := Real.log_le_sub_one_of_pos hratio_pos
  have hupp' : Real.log (b / a) - (b - a) / b ≤ (b - a) ^ 2 / (a * b) := by
    calc
      Real.log (b / a) - (b - a) / b ≤ b / a - 1 - (b - a) / b := by
        linarith
      _ = (b - a) ^ 2 / (a * b) := by
        field_simp [ha.ne', hb.ne']
  constructor
  · rw [hlog_eq]
    linarith
  · rw [hlog_eq]
    exact hupp'

lemma mangoldt_log_reciprocal_loglog_increment_error_bound (r : ℕ) (hr : 2 ≤ r) :
    0 ≤ Real.log (Real.log ((r + 1 : ℕ) : ℝ)) - Real.log (Real.log (r : ℝ)) -
        (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) /
          Real.log ((r + 1 : ℕ) : ℝ) ∧
      Real.log (Real.log ((r + 1 : ℕ) : ℝ)) - Real.log (Real.log (r : ℝ)) -
        (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) /
          Real.log ((r + 1 : ℕ) : ℝ) ≤
        1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr)
  have hr_one : (1 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hr)
  have hsucc_one : (1 : ℝ) < ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (Nat.le_succ_of_le hr))
  have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos hr_one
  have hlogsucc_pos : 0 < Real.log ((r + 1 : ℕ) : ℝ) := Real.log_pos hsucc_one
  have hr_le_succ : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ r
  have hlog_le : Real.log (r : ℝ) ≤ Real.log ((r + 1 : ℕ) : ℝ) :=
    Real.log_le_log hr_pos hr_le_succ
  have hmain := mangoldt_log_reciprocal_real_log_increment_error_bound hlogr_pos hlog_le
  constructor
  · exact hmain.1
  · set d : ℝ := Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)
    have hd_nonneg : 0 ≤ d := by
      dsimp [d]
      exact sub_nonneg.mpr hlog_le
    have hd_le : d ≤ 1 / (r : ℝ) := by
      have hratio_pos : 0 < ((r + 1 : ℕ) : ℝ) / (r : ℝ) :=
        div_pos (by positivity) hr_pos
      have hlogratio := Real.log_le_sub_one_of_pos hratio_pos
      have hlogratio_eq :
          Real.log (((r + 1 : ℕ) : ℝ) / (r : ℝ)) = d := by
        rw [Real.log_div (by positivity : ((r + 1 : ℕ) : ℝ) ≠ 0) hr_pos.ne']
      have hsub_eq : ((r + 1 : ℕ) : ℝ) / (r : ℝ) - 1 = 1 / (r : ℝ) := by
        field_simp [hr_pos.ne']
        norm_num
      rw [hlogratio_eq] at hlogratio
      rw [hsub_eq] at hlogratio
      simpa [one_div] using hlogratio
    have hsq_le : d ^ 2 ≤ (1 / (r : ℝ)) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hd_nonneg hd_le
    have hden_pos : 0 < Real.log (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ) :=
      mul_pos hlogr_pos hlogsucc_pos
    have htarget : d ^ 2 /
        (Real.log (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ)) ≤
        1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2) := by
      have hsq_log_le : (Real.log (r : ℝ)) ^ 2 ≤
          Real.log (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ) := by
        nlinarith
      have hmajor : d ^ 2 * (r : ℝ) ≤ 1 := by
        have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr)
        calc
          d ^ 2 * (r : ℝ) ≤ (1 / (r : ℝ)) ^ 2 * (r : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsq_le (le_of_lt hr_pos)
          _ = 1 / (r : ℝ) := by
            field_simp [hr_pos.ne']
          _ ≤ 1 := by
            rw [div_le_iff₀ hr_pos]
            nlinarith
      field_simp [hr_pos.ne', hlogr_pos.ne', hlogsucc_pos.ne']
      nlinarith [hmajor, hsq_log_le, hlogr_pos]
    exact hmain.2.trans (by simpa [d, mul_comm, mul_left_comm, mul_assoc] using htarget)

lemma mangoldt_log_reciprocal_main_term_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n ->
      |(∑ q ∈ Finset.Ico 2 (n + 1),
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
            Real.log (q : ℝ)) - Real.log (Real.log (n : ℝ))| ≤ K := by
  let majorant : ℕ → ℝ := fun r =>
    if 2 ≤ r then 1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2) else 0
  have hmajorant_summ : Summable majorant := by
    simpa [majorant] using log_square_tail_summable
  have hmajorant_nonneg : ∀ r : ℕ, 0 ≤ majorant r := by
    intro r
    dsimp [majorant]
    split_ifs with hr
    · positivity
    · norm_num
  refine ⟨|1 - Real.log (Real.log (2 : ℝ))| + ∑' r : ℕ, majorant r, ?_, ?_⟩
  · exact add_nonneg (abs_nonneg _) (tsum_nonneg hmajorant_nonneg)
  intro n hn
  let term : ℕ → ℝ := fun q =>
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)
  let ll : ℕ → ℝ := fun r => Real.log (Real.log (r : ℝ))
  let err : ℕ → ℝ := fun r => ll (r + 1) - ll r - term (r + 1)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hterm_two : term 2 = 1 := by
    dsimp [term]
    norm_num [Real.log_one]
  have hsum_reindex :
      (∑ q ∈ Finset.Ico 2 (n + 1), term q) =
        term 2 + ∑ r ∈ Finset.Ico 2 n, term (r + 1) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl]
    rw [← Finset.sum_Ico_add (f := term) (a := 1) (b := n) (c := 1)]
    have h1n : 1 < n := by omega
    rw [← Finset.add_sum_Ioo_eq_sum_Ico (f := fun r : ℕ => term (1 + r)) h1n]
    have hIoo : Finset.Ioo 1 n = Finset.Ico 2 n := by
      ext r
      simp [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    simp [hIoo, Nat.add_comm]
  have hll_telescope :
      (∑ r ∈ Finset.Ico 2 n, (ll (r + 1) - ll r)) = ll n - ll 2 := by
    simpa [ll] using Finset.sum_Ico_sub (m := 2) (n := n) (f := ll) hn
  have herr_sum :
      (∑ r ∈ Finset.Ico 2 n, err r) =
        (ll n - ll 2) - ∑ r ∈ Finset.Ico 2 n, term (r + 1) := by
    dsimp [err]
    rw [Finset.sum_sub_distrib, hll_telescope]
  have hdecomp :
      (∑ q ∈ Finset.Ico 2 (n + 1), term q) - ll n =
        (1 - ll 2) - ∑ r ∈ Finset.Ico 2 n, err r := by
    rw [hsum_reindex, hterm_two, herr_sum]
    ring
  have herr_nonneg : 0 ≤ ∑ r ∈ Finset.Ico 2 n, err r := by
    refine Finset.sum_nonneg ?_
    intro r hr
    exact (mangoldt_log_reciprocal_loglog_increment_error_bound r (Finset.mem_Ico.mp hr).1).1
  have herr_le_majorant :
      (∑ r ∈ Finset.Ico 2 n, err r) ≤ ∑' r : ℕ, majorant r := by
    calc
      (∑ r ∈ Finset.Ico 2 n, err r) ≤ ∑ r ∈ Finset.Ico 2 n, majorant r := by
        refine Finset.sum_le_sum ?_
        intro r hr
        have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
        have h := (mangoldt_log_reciprocal_loglog_increment_error_bound r hr2).2
        dsimp [err, ll, term, majorant]
        simp [hr2] at h ⊢
        linarith
      _ ≤ ∑' r : ℕ, majorant r :=
        hmajorant_summ.sum_le_tsum (Finset.Ico 2 n) (fun r _ => hmajorant_nonneg r)
  rw [show Real.log (Real.log (n : ℝ)) = ll n by rfl, hdecomp]
  calc
    |(1 - ll 2) - ∑ r ∈ Finset.Ico 2 n, err r| ≤
        |1 - ll 2| + |∑ r ∈ Finset.Ico 2 n, err r| := by
      simpa [sub_eq_add_neg] using abs_add_le (1 - ll 2) (-(∑ r ∈ Finset.Ico 2 n, err r))
    _ = |1 - ll 2| + ∑ r ∈ Finset.Ico 2 n, err r := by
      rw [abs_of_nonneg herr_nonneg]
    _ ≤ |1 - Real.log (Real.log (2 : ℝ))| + ∑' r : ℕ, majorant r := by
      simpa [ll, add_comm, add_left_comm, add_assoc] using
        add_le_add_right herr_le_majorant |1 - Real.log (Real.log (2 : ℝ))|

lemma mangoldt_log_reciprocal_mertens_error_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D) :
    ∀ n : ℕ, 2 ≤ n ->
      |∑ q ∈ Finset.Ico 2 (n + 1),
        (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
            Real.log (q : ℝ)| ≤ 4 * D / Real.log (2 : ℝ) := by
  intro n hn
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  let g : ℕ → ℝ := fun q => if 2 ≤ q then e q else 0
  let w : ℕ → ℝ := fun q => if q < 2 then 1 / Real.log (2 : ℝ) else 1 / Real.log (q : ℝ)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwoD_nonneg : 0 ≤ 2 * D := by positivity
  have hfourD_nonneg : 0 ≤ 4 * D := by positivity
  have hw0 : w 0 = 1 / Real.log (2 : ℝ) := by simp [w]
  have hw_nonneg : ∀ q : ℕ, 0 ≤ w q := by
    intro q
    dsimp [w]
    by_cases hq : q < 2
    · simp [hq, le_of_lt hlog2_pos]
    · have hq2 : 2 ≤ q := not_lt.mp hq
      have hq_one : (1 : ℝ) < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq2)
      have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_one
      simp [hq, hlogq_pos.le]
  have hw_le_w0 : ∀ q : ℕ, w q ≤ 1 / Real.log (2 : ℝ) := by
    intro q
    dsimp [w]
    by_cases hq : q < 2
    · simp [hq]
    · have hq2 : 2 ≤ q := not_lt.mp hq
      have hq_pos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hq2)
      have hq_one : (1 : ℝ) < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq2)
      have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_one
      have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (q : ℝ) := by
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
      simp [hq]
      simpa [one_div] using one_div_le_one_div_of_le hlog2_pos hlog2_le
  have hw_mono : ∀ i : ℕ, w (i + 1) ≤ w i := by
    intro i
    dsimp [w]
    by_cases hi0 : i = 0
    · subst i
      simp
    · have hi_pos_nat : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
      by_cases hi1 : i = 1
      · subst i
        simp
      · have hi2 : 2 ≤ i := by omega
        have hi2succ : 2 ≤ i + 1 := by omega
        have hi_pos : (0 : ℝ) < (i : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hi2)
        have hi_one : (1 : ℝ) < (i : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hi2)
        have hlogi_pos : 0 < Real.log (i : ℝ) := Real.log_pos hi_one
        have hi_le_succ : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ i
        have hlog_le : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
          Real.log_le_log hi_pos hi_le_succ
        simp [not_lt.mpr hi2, not_lt.mpr hi2succ]
        simpa [one_div, Nat.cast_add, Nat.cast_one] using
          one_div_le_one_div_of_le hlogi_pos hlog_le
  have hG_eq : ∀ k : ℕ, (∑ q ∈ Finset.range k, g q) = ∑ q ∈ Finset.Ico 2 k, e q := by
    intro k
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext q
      simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
    · intro q hq
      simp
  have hG_bound : ∀ k : ℕ, |∑ q ∈ Finset.range k, g q| ≤ 2 * D := by
    intro k
    rw [hG_eq k]
    exact mangoldt_mertens_error_partial_bound D hD_nonneg hD 2 k (by norm_num)
  have htarget :
      (∑ q ∈ Finset.Ico 2 (n + 1), e q / Real.log (q : ℝ)) =
        ∑ q ∈ Finset.range (n + 1), w q * g q := by
    symm
    dsimp [g]
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext q
      simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
    · intro q hq
      have hq2 : 2 ≤ q := (Finset.mem_Ico.mp hq).1
      dsimp [w]
      simp [not_lt.mpr hq2]
      ring
  rw [show (∑ q ∈ Finset.Ico 2 (n + 1),
        (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
            Real.log (q : ℝ)) =
      ∑ q ∈ Finset.Ico 2 (n + 1), e q / Real.log (q : ℝ) by rfl]
  rw [htarget]
  have hbp := Finset.sum_range_by_parts (f := w) (g := g) (n := n + 1)
  have hbp' : ∑ i ∈ Finset.range (n + 1), w i * g i =
      w n * (∑ i ∈ Finset.range (n + 1), g i) -
        ∑ i ∈ Finset.range n,
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) := by
    simpa only [smul_eq_mul, Nat.add_sub_cancel] using hbp
  rw [hbp']
  have hboundary : |w n * (∑ i ∈ Finset.range (n + 1), g i)| ≤
      2 * D * (1 / Real.log (2 : ℝ)) := by
    calc
      |w n * (∑ i ∈ Finset.range (n + 1), g i)| =
          w n * |∑ i ∈ Finset.range (n + 1), g i| := by
        rw [abs_mul, abs_of_nonneg (hw_nonneg n)]
      _ ≤ w n * (2 * D) := by
        exact mul_le_mul_of_nonneg_left (hG_bound (n + 1)) (hw_nonneg n)
      _ ≤ (1 / Real.log (2 : ℝ)) * (2 * D) := by
        exact mul_le_mul_of_nonneg_right (hw_le_w0 n) htwoD_nonneg
      _ = 2 * D * (1 / Real.log (2 : ℝ)) := by ring
  have hvariation :
      |∑ i ∈ Finset.range n,
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| ≤
        2 * D * (w 0 - w n) := by
    calc
      |∑ i ∈ Finset.range n,
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| ≤
          ∑ i ∈ Finset.range n,
            |(w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
            2 * D * (w i - w (i + 1)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hdiff_nonneg : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hw_mono i)
        have hdiff_abs : |w (i + 1) - w i| = w i - w (i + 1) := by
          rw [abs_of_nonpos (sub_nonpos.mpr (hw_mono i))]
          ring
        calc
          |(w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| =
              (w i - w (i + 1)) * |∑ j ∈ Finset.range (i + 1), g j| := by
            rw [abs_mul, hdiff_abs]
          _ ≤ (w i - w (i + 1)) * (2 * D) := by
            exact mul_le_mul_of_nonneg_left (hG_bound (i + 1)) hdiff_nonneg
          _ = 2 * D * (w i - w (i + 1)) := by ring
      _ = 2 * D * (∑ i ∈ Finset.range n, (w i - w (i + 1))) := by
        rw [Finset.mul_sum]
      _ = 2 * D * (w 0 - w n) := by
        have htel := Finset.sum_range_sub (f := w) n
        have htel' : (∑ i ∈ Finset.range n, (w i - w (i + 1))) = w 0 - w n := by
          calc
            (∑ i ∈ Finset.range n, (w i - w (i + 1))) =
                -∑ i ∈ Finset.range n, (w (i + 1) - w i) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = -(w n - w 0) := by rw [htel]
            _ = w 0 - w n := by ring
        rw [htel']
  calc
    |w n * (∑ i ∈ Finset.range (n + 1), g i) -
        ∑ i ∈ Finset.range n,
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| ≤
        |w n * (∑ i ∈ Finset.range (n + 1), g i)| +
          |∑ i ∈ Finset.range n,
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (w n * (∑ i ∈ Finset.range (n + 1), g i))
          (-(∑ i ∈ Finset.range n,
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)))
    _ ≤ 2 * D * (1 / Real.log (2 : ℝ)) + 2 * D * (w 0 - w n) := by
      exact add_le_add hboundary hvariation
    _ ≤ 4 * D / Real.log (2 : ℝ) := by
      have hwn_nonneg : 0 ≤ w n := hw_nonneg n
      rw [hw0]
      calc
        2 * D * (1 / Real.log (2 : ℝ)) +
            2 * D * (1 / Real.log (2 : ℝ) - w n) =
            4 * D / Real.log (2 : ℝ) - 2 * D * w n := by
          ring
        _ ≤ 4 * D / Real.log (2 : ℝ) := by
          nlinarith [mul_nonneg htwoD_nonneg hwn_nonneg]

lemma mangoldt_log_reciprocal_partial_sum_nat (n : ℕ) :
    mangoldt_log_reciprocal_partial_sum (n : ℝ) =
      ∑ q ∈ Finset.Ico 2 (n + 1),
        ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ)) := by
  rw [mangoldt_log_reciprocal_partial_sum]
  calc
    (∑' q : ℕ,
        if 2 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
          ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
        else 0) =
        ∑ q ∈ Finset.Ico 2 (n + 1),
          if 2 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.Ico 2 (n + 1))
        (f := fun q : ℕ =>
          if 2 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
          else 0) ?_
      intro q hq
      by_cases hcond : 2 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)
      · exfalso
        exact hq (Finset.mem_Ico.mpr ⟨hcond.1,
          Nat.lt_succ_iff.mpr (Nat.cast_le.mp hcond.2)⟩)
      · exact if_neg hcond
    _ = ∑ q ∈ Finset.Ico 2 (n + 1),
        ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rcases Finset.mem_Ico.mp hq with ⟨hq2, hqn⟩
      have hqr : (q : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hqn
      simp [hq2, hqr]

lemma mangoldt_log_reciprocal_partial_summation_nat :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n ->
      |mangoldt_log_reciprocal_partial_sum (n : ℝ) -
        Real.log (Real.log (n : ℝ))| ≤ C := by
  obtain ⟨D, hD_nonneg, hD⟩ := mertens_von_mangoldt_reciprocal
  obtain ⟨K, hK_nonneg, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨K + 4 * D / Real.log (2 : ℝ), by positivity, ?_⟩
  intro n hn
  let err : ℕ → ℝ := fun q =>
    (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
        Real.log (q : ℝ)
  let main : ℕ → ℝ := fun q =>
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)
  have hsplit :
      (∑ q ∈ Finset.Ico 2 (n + 1),
        ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))) =
        (∑ q ∈ Finset.Ico 2 (n + 1), err q) +
          ∑ q ∈ Finset.Ico 2 (n + 1), main q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro q hq
    dsimp [err, main]
    ring
  have herr := mangoldt_log_reciprocal_mertens_error_bound D hD_nonneg hD n hn
  have hmain := hK n hn
  rw [mangoldt_log_reciprocal_partial_sum_nat, hsplit]
  calc
    |((∑ q ∈ Finset.Ico 2 (n + 1), err q) +
        ∑ q ∈ Finset.Ico 2 (n + 1), main q) - Real.log (Real.log (n : ℝ))| =
        |(∑ q ∈ Finset.Ico 2 (n + 1), err q) +
          ((∑ q ∈ Finset.Ico 2 (n + 1), main q) - Real.log (Real.log (n : ℝ)))| := by
      ring_nf
    _ ≤ |∑ q ∈ Finset.Ico 2 (n + 1), err q| +
        |(∑ q ∈ Finset.Ico 2 (n + 1), main q) - Real.log (Real.log (n : ℝ))| :=
      abs_add_le _ _
    _ ≤ 4 * D / Real.log (2 : ℝ) + K := by
      exact add_le_add herr hmain
    _ = K + 4 * D / Real.log (2 : ℝ) := by ring

lemma mangoldt_log_reciprocal_partial_sum_floor (t : ℝ) (ht : 0 ≤ t) :
    mangoldt_log_reciprocal_partial_sum t =
      ∑ q ∈ Finset.Ico 2 (⌊t⌋₊ + 1),
        ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ)) := by
  rw [mangoldt_log_reciprocal_partial_sum]
  calc
    (∑' q : ℕ,
        if 2 ≤ q ∧ (q : ℝ) ≤ t then
          ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
        else 0) =
        ∑ q ∈ Finset.Ico 2 (⌊t⌋₊ + 1),
          if 2 ≤ q ∧ (q : ℝ) ≤ t then
            ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.Ico 2 (⌊t⌋₊ + 1))
        (f := fun q : ℕ =>
          if 2 ≤ q ∧ (q : ℝ) ≤ t then
            ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ))
          else 0) ?_
      intro q hq
      by_cases hcond : 2 ≤ q ∧ (q : ℝ) ≤ t
      · exfalso
        exact hq (Finset.mem_Ico.mpr ⟨hcond.1,
          Nat.lt_succ_iff.mpr (Nat.le_floor hcond.2)⟩)
      · exact if_neg hcond
    _ = ∑ q ∈ Finset.Ico 2 (⌊t⌋₊ + 1),
        ArithmeticFunction.vonMangoldt q / ((q : ℝ) * Real.log (q : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rcases Finset.mem_Ico.mp hq with ⟨hq2, hqfloor⟩
      have hq_le_floor : q ≤ ⌊t⌋₊ := Nat.lt_succ_iff.mp hqfloor
      have hqr : (q : ℝ) ≤ t := by
        have hq_le_floor_real : (q : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
          exact_mod_cast hq_le_floor
        exact hq_le_floor_real.trans (Nat.floor_le ht)
      simp [hq2, hqr]

lemma mangoldt_log_reciprocal_floor_loglog_bound (t : ℝ) (ht : 2 ≤ t) :
    |Real.log (Real.log (⌊t⌋₊ : ℝ)) - Real.log (Real.log t)| ≤ Real.log (2 : ℝ) := by
  let n : ℕ := ⌊t⌋₊
  have ht_nonneg : 0 ≤ t := by linarith
  have hn : 2 ≤ n := by
    simpa [n] using Nat.le_floor ht
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_one : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have ht_pos : 0 < t := by linarith
  have ht_one : 1 < t := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_one
  have hlogt_pos : 0 < Real.log t := Real.log_pos ht_one
  have hn_le_t : (n : ℝ) ≤ t := by
    simpa [n] using Nat.floor_le ht_nonneg
  have ht_lt_succ : t < (n : ℝ) + 1 := by
    simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hsucc_le_two_mul : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
    linarith
  have ht_le_two_mul : t ≤ 2 * (n : ℝ) := by
    linarith
  have hlogn_le_logt : Real.log (n : ℝ) ≤ Real.log t := Real.log_le_log hn_pos hn_le_t
  have hlogt_le_twologn : Real.log t ≤ 2 * Real.log (n : ℝ) := by
    have hlogt_le : Real.log t ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log ht_pos ht_le_two_mul
    have hlog_mul : Real.log (2 * (n : ℝ)) = Real.log (2 : ℝ) + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn_pos.ne']
    have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hloglog_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log t) :=
    Real.log_le_log hlogn_pos hlogn_le_logt
  have hratio_pos : 0 < Real.log t / Real.log (n : ℝ) := div_pos hlogt_pos hlogn_pos
  have hratio_le_two : Real.log t / Real.log (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hlogn_pos]
    exact hlogt_le_twologn
  have hdiff_eq : Real.log (Real.log t) - Real.log (Real.log (n : ℝ)) =
      Real.log (Real.log t / Real.log (n : ℝ)) := by
    rw [Real.log_div hlogt_pos.ne' hlogn_pos.ne']
  have hdiff_le : Real.log (Real.log t) - Real.log (Real.log (n : ℝ)) ≤ Real.log (2 : ℝ) := by
    rw [hdiff_eq]
    exact Real.log_le_log hratio_pos hratio_le_two
  have hnonpos : Real.log (Real.log (n : ℝ)) - Real.log (Real.log t) ≤ 0 := by
    linarith
  rw [show (⌊t⌋₊ : ℝ) = (n : ℝ) by rfl]
  rw [abs_of_nonpos hnonpos]
  linarith

lemma mangoldt_log_reciprocal_partial_summation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t ->
      |mangoldt_log_reciprocal_partial_sum t - Real.log (Real.log t)| ≤ C := by
  obtain ⟨C, hC_nonneg, hC⟩ := mangoldt_log_reciprocal_partial_summation_nat
  refine ⟨C + Real.log (2 : ℝ), by positivity, ?_⟩
  intro t ht
  let n : ℕ := ⌊t⌋₊
  have ht_nonneg : 0 ≤ t := by linarith
  have hn : 2 ≤ n := by
    simpa [n] using Nat.le_floor ht
  have hsum_eq : mangoldt_log_reciprocal_partial_sum t =
      mangoldt_log_reciprocal_partial_sum (n : ℝ) := by
    rw [mangoldt_log_reciprocal_partial_sum_floor t ht_nonneg,
      mangoldt_log_reciprocal_partial_sum_nat n]
  have hnat := hC n hn
  have hfloor := mangoldt_log_reciprocal_floor_loglog_bound t ht
  calc
    |mangoldt_log_reciprocal_partial_sum t - Real.log (Real.log t)| =
        |mangoldt_log_reciprocal_partial_sum (n : ℝ) - Real.log (Real.log t)| := by
      rw [hsum_eq]
    _ = |(mangoldt_log_reciprocal_partial_sum (n : ℝ) -
          Real.log (Real.log (n : ℝ))) +
          (Real.log (Real.log (n : ℝ)) - Real.log (Real.log t))| := by
      ring_nf
    _ ≤ |mangoldt_log_reciprocal_partial_sum (n : ℝ) -
          Real.log (Real.log (n : ℝ))| +
        |Real.log (Real.log (n : ℝ)) - Real.log (Real.log t)| :=
      abs_add_le _ _
    _ ≤ C + Real.log (2 : ℝ) :=
      add_le_add hnat (by simpa [n] using hfloor)

lemma prime_reciprocal_mangoldt_log_bridge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t ->
      |(∑' p : ℕ,
          (prime_layer ∩ real_initial_segment t).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
        mangoldt_log_reciprocal_partial_sum t| ≤ C := by
  classical
  have h := (ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (a := (0 : ZMod 1)))
  have hnonprime : Summable (fun n : ℕ =>
      (if Nat.Prime n then 0 else ArithmeticFunction.vonMangoldt n) / (n : ℝ)) := by
    simpa [ArithmeticFunction.vonMangoldt.residueClass, ZMod.natCast_eq_zero_iff] using h
  have hB : Summable (fun n : ℕ =>
      if 2 ≤ n ∧ ¬ Nat.Prime n then
        ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ))
      else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_
      ((hnonprime.mul_left ((Real.log (2 : ℝ))⁻¹)))
    · intro n
      split_ifs with hn
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (by positivity)
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)))
      · norm_num
    · intro n
      by_cases hn : 2 ≤ n ∧ ¬ Nat.Prime n
      · rw [if_pos hn, if_neg hn.2]
        have hn2 : 2 ≤ n := hn.1
        have hnp : ¬ Nat.Prime n := hn.2
        have hn_pos : 0 < (n : ℝ) := by positivity
        have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        have hlogn_pos : 0 < Real.log (n : ℝ) := by
          exact Real.log_pos
            (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn2) : (1 : ℝ) < n)
        have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
          exact Real.log_le_log (by norm_num) (by exact_mod_cast hn2 : (2 : ℝ) ≤ n)
        calc
          ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ))
              = (1 / Real.log (n : ℝ)) *
                  (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
                field_simp [hn_pos.ne', hlogn_pos.ne']
          _ ≤ (Real.log (2 : ℝ))⁻¹ *
                (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
                have hcoef : (Real.log (n : ℝ))⁻¹ ≤ (Real.log (2 : ℝ))⁻¹ := by
                  simpa [one_div] using one_div_le_one_div_of_le hlog2_pos hlog2_le
                have hbase : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
                  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn_pos.le
                simpa [one_div] using mul_le_mul_of_nonneg_right hcoef hbase
      · rw [if_neg hn]
        exact mul_nonneg
          (inv_nonneg.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
          (by
            by_cases hp : Nat.Prime n
            · rw [if_pos hp]
              exact div_nonneg le_rfl (Nat.cast_nonneg n)
            · rw [if_neg hp]
              exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
  let w : ℕ → ℝ := fun n => if Nat.Prime n then (1 : ℝ) / (n : ℝ) else 0
  let v : ℕ → ℝ := fun n =>
    if 2 ≤ n then ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ)) else 0
  let B : ℕ → ℝ := fun n =>
    if 2 ≤ n ∧ ¬ Nat.Prime n then
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ))
    else 0
  have hB' : Summable B := by
    simpa [B] using hB
  have hdiff_eq_B : (fun n : ℕ => |w n - v n|) = B := by
    funext n
    by_cases hp : Nat.Prime n
    · have hn2 : 2 ≤ n := hp.two_le
      have hn_pos : 0 < (n : ℝ) := by positivity
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        exact Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < n)
      have hΛ : ArithmeticFunction.vonMangoldt n = Real.log (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_apply_prime hp
      have hterm : (1 : ℝ) / (n : ℝ) -
          ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ)) = 0 := by
        rw [hΛ]
        field_simp [hn_pos.ne', hlog_pos.ne']
        ring
      have hterm' : (n : ℝ)⁻¹ -
          ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ)) = 0 := by
        simpa [one_div] using hterm
      simp [w, v, B, hp, hn2, hterm']
    · by_cases hn2 : 2 ≤ n
      · have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn2)
        have hlog_pos : 0 < Real.log (n : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn2) : (1 : ℝ) < n)
        have hterm_nonneg : 0 ≤
            ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log (n : ℝ)) := by
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (mul_nonneg hn_pos.le hlog_pos.le)
        simp [w, v, B, hp, hn2, abs_of_nonneg hterm_nonneg]
      · simp [w, v, B, hp, hn2]
  have hdiff_summ : Summable (fun n : ℕ => |w n - v n|) := by
    rw [hdiff_eq_B]
    exact hB'
  refine ⟨∑' n : ℕ, B n, ?_, ?_⟩
  · exact tsum_nonneg fun n => by
      by_cases hn : 2 ≤ n ∧ ¬ Nat.Prime n
      · have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn.1)
        have hlog_pos : 0 < Real.log (n : ℝ) := by
          exact Real.log_pos (by
            exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn.1) : (1 : ℝ) < n)
        simp [B, hn, div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg hn_pos.le hlog_pos.le)]
      · simp [B, hn]
  · intro t ht
    have htransfer :=
      summable_error_limsup_transfer_truncated_error_bound hdiff_summ (Set.univ : Set ℕ) t
    have hprime_eq :
        (∑' p : ℕ,
          (prime_layer ∩ real_initial_segment t).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) =
        ∑' n : ℕ, ((Set.univ : Set ℕ) ∩ real_initial_segment t).indicator w n := by
      apply tsum_congr
      intro n
      by_cases hseg : n ∈ real_initial_segment t
      · by_cases hp : Nat.Prime n
        · simp [prime_layer, w, hseg, hp]
        · simp [prime_layer, w, hseg, hp]
      · simp [prime_layer, w, hseg]
    have hmangoldt_eq : mangoldt_log_reciprocal_partial_sum t =
        ∑' n : ℕ, ((Set.univ : Set ℕ) ∩ real_initial_segment t).indicator v n := by
      rw [mangoldt_log_reciprocal_partial_sum]
      apply tsum_congr
      intro n
      by_cases hn2 : 2 ≤ n
      · have hn1 : 1 ≤ n := by omega
        by_cases hle : (n : ℝ) ≤ t
        · simp [v, real_initial_segment, hn2, hn1, hle]
        · simp [v, real_initial_segment, hn2, hle]
      · by_cases hseg : n ∈ real_initial_segment t
        · simp [v, hseg, hn2]
        · simp [v, hseg, hn2]
    calc
      |(∑' p : ℕ,
          (prime_layer ∩ real_initial_segment t).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
        mangoldt_log_reciprocal_partial_sum t| =
          |(∑' n : ℕ, ((Set.univ : Set ℕ) ∩ real_initial_segment t).indicator w n) -
            (∑' n : ℕ, ((Set.univ : Set ℕ) ∩ real_initial_segment t).indicator v n)| := by
            rw [hprime_eq, hmangoldt_eq]
      _ ≤ ∑' n : ℕ, |w n - v n| := htransfer
      _ = ∑' n : ℕ, B n := by rw [hdiff_eq_B]

lemma mertens_prime_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t ->
      |(∑' p : ℕ,
          (prime_layer ∩ real_initial_segment t).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
        Real.log (Real.log t)| ≤ C := by
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ := mangoldt_log_reciprocal_partial_summation
  obtain ⟨C₂, hC₂_nonneg, hC₂⟩ := prime_reciprocal_mangoldt_log_bridge
  refine ⟨C₂ + C₁, add_nonneg hC₂_nonneg hC₁_nonneg, ?_⟩
  intro t ht
  have hbridge := hC₂ t ht
  have hmangoldt := hC₁ t ht
  calc
    |(∑' p : ℕ,
        (prime_layer ∩ real_initial_segment t).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
      Real.log (Real.log t)| =
        |((∑' p : ℕ,
            (prime_layer ∩ real_initial_segment t).indicator
              (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
          mangoldt_log_reciprocal_partial_sum t) +
          (mangoldt_log_reciprocal_partial_sum t - Real.log (Real.log t))| := by
          congr 1
          ring
    _ ≤ |(∑' p : ℕ,
          (prime_layer ∩ real_initial_segment t).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) -
        mangoldt_log_reciprocal_partial_sum t| +
        |mangoldt_log_reciprocal_partial_sum t - Real.log (Real.log t)| :=
      abs_add_le _ _
    _ ≤ C₂ + C₁ := add_le_add hbridge hmangoldt

lemma mangoldt_adjoint_erdos_weight_le_log_increment_local (n : ℕ) (hn : 2 ≤ n) :
    erdos_weight n ≤
      (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_one : 1 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hn_sub_pos_nat : 0 < n - 1 := by omega
  have hn_sub_pos : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn_sub_pos_nat
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_one
  have hratio_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn_sub_pos
  have hlog_lower : 1 / (n : ℝ) ≤ Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    have hbase := Real.one_sub_inv_le_log_of_pos hratio_pos
    have hleft : 1 - ((n : ℝ) / ((n - 1 : ℕ) : ℝ))⁻¹ = 1 / (n : ℝ) := by
      have hsub_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
      rw [hsub_cast]
      field_simp [hn_pos.ne', sub_ne_zero.mpr (ne_of_gt hn_one)]
      nlinarith
    rw [hleft] at hbase
    simpa [one_div] using hbase
  have hlog_div : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) =
      Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
    rw [Real.log_div hn_pos.ne' hn_sub_pos.ne']
  rw [erdos_weight]
  calc
    1 / ((n : ℝ) * Real.log (n : ℝ)) = (1 / (n : ℝ)) / Real.log (n : ℝ) := by ring
    _ ≤ Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / Real.log (n : ℝ) := by
      exact div_le_div_of_nonneg_right hlog_lower hlog_pos.le
    _ = (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log (n : ℝ) := by
      rw [hlog_div]

lemma mangoldt_adjoint_erdos_weight_natural_terminal_sum_bound_local :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N ->
      (∑ n ∈ Finset.Ico 2 (N + 1), erdos_weight n) ≤
        K + Real.log (Real.log (N : ℝ)) := by
  obtain ⟨K, hK_nonneg, hK⟩ := mangoldt_log_reciprocal_main_term_bound
  refine ⟨K, hK_nonneg, ?_⟩
  intro N hN
  let main : ℕ → ℝ := fun q =>
    (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) / Real.log (q : ℝ)
  have hsum_le : (∑ n ∈ Finset.Ico 2 (N + 1), erdos_weight n) ≤
      ∑ q ∈ Finset.Ico 2 (N + 1), main q := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mangoldt_adjoint_erdos_weight_le_log_increment_local n (Finset.mem_Ico.mp hn).1
  have hmain_bound := hK N hN
  have hmain_le : (∑ q ∈ Finset.Ico 2 (N + 1), main q) ≤
      K + Real.log (Real.log (N : ℝ)) := by
    have hle_abs :
        (∑ q ∈ Finset.Ico 2 (N + 1), main q) - Real.log (Real.log (N : ℝ)) ≤
          |(∑ q ∈ Finset.Ico 2 (N + 1), main q) - Real.log (Real.log (N : ℝ))| :=
      le_abs_self _
    linarith
  exact hsum_le.trans hmain_le

lemma mangoldt_adjoint_card_factors_le_prime_power_divisor_count_local
    (n N : ℕ) (hn_two : 2 ≤ n) (hnN : n ≤ N) :
    ArithmeticFunction.cardFactors n ≤
      ∑ p ∈ Finset.Ico 2 (N + 1),
        if Nat.Prime p then
          ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ n then 1 else 0
        else 0 := by
  classical
  have hn_ne : n ≠ 0 := by omega
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  change n.factorization.sum (fun p k => k) ≤
      ∑ p ∈ Finset.Ico 2 (N + 1),
        if Nat.Prime p then
          ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ n then 1 else 0
        else 0
  calc
    n.factorization.sum (fun p k => k) =
        ∑ p ∈ n.factorization.support, n.factorization p := by rfl
    _ ≤ ∑ p ∈ n.factorization.support,
        (if Nat.Prime p then
          ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ n then 1 else 0
        else 0) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        have hp_mem_primeFactors : p ∈ n.primeFactors := by simpa using hp
        have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem_primeFactors).1
        have hp_exp_le_N : n.factorization p ≤ N := by
          exact (le_of_lt (Nat.factorization_lt p hn_ne)).trans hnN
        rw [if_pos hp_prime]
        calc
          n.factorization p = ∑ j ∈ Finset.Icc 1 (n.factorization p), 1 := by
            simp
          _ ≤ ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ n then 1 else 0 := by
            have hleft_eq : (∑ j ∈ Finset.Icc 1 (n.factorization p), 1) =
                ∑ j ∈ Finset.Icc 1 (n.factorization p), if p ^ j ∣ n then 1 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj_le : j ≤ n.factorization p := (Finset.mem_Icc.mp hj).2
              have hdvd : p ^ j ∣ n := (hp_prime.pow_dvd_iff_le_factorization hn_ne).mpr hj_le
              simp [hdvd]
            rw [hleft_eq]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro j hj
              exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
                (Finset.mem_Icc.mp hj).2.trans hp_exp_le_N⟩
            · intro j hjN hjnot
              by_cases hdvd : p ^ j ∣ n <;> simp [hdvd]
    _ ≤ ∑ p ∈ Finset.Ico 2 (N + 1),
        (if Nat.Prime p then
          ∑ j ∈ Finset.Icc 1 N, if p ^ j ∣ n then 1 else 0
        else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          have hp_mem_primeFactors : p ∈ n.primeFactors := by simpa using hp
          have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem_primeFactors).2.1
          have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem_primeFactors).1
          have hp_two : 2 ≤ p := hp_prime.two_le
          have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
          exact Finset.mem_Ico.mpr ⟨hp_two, Nat.lt_succ_iff.mpr (hp_le_n.trans hnN)⟩
        · intro p hpI hpnot
          by_cases hp_prime : Nat.Prime p
          · simp [hp_prime]
          · simp [hp_prime]

lemma mangoldt_adjoint_erdos_weight_mul_le_local (q m : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) :
    erdos_weight (q * m) ≤
      (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) := by
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hq)
  have hq_one : 1 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq)
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqm_pos : 0 < ((q * m : ℕ) : ℝ) := by positivity
  have hqm_one : 1 < ((q * m : ℕ) : ℝ) := by
    have hqm_two : 2 ≤ q * m := Nat.mul_le_mul hq hm
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hqm_two)
  have hlogqm_pos : 0 < Real.log ((q * m : ℕ) : ℝ) := Real.log_pos hqm_one
  by_cases hm_one : m = 1
  · subst m
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (q : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hq : (2 : ℝ) ≤ q)
    rw [erdos_weight]
    simp only [mul_one, one_div, mul_inv_rev, ↓reduceIte, ge_iff_le]
    have hinv_log_le : (Real.log (q : ℝ))⁻¹ ≤ (Real.log (2 : ℝ))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog2_pos hlog2_le
    calc
      (Real.log (q : ℝ))⁻¹ * (q : ℝ)⁻¹ ≤
          (Real.log (2 : ℝ))⁻¹ * (q : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hinv_log_le (inv_nonneg.mpr hq_pos.le)
      _ = (q : ℝ)⁻¹ * (Real.log (2 : ℝ))⁻¹ := by ring
  · have hm_two : 2 ≤ m := by omega
    have hm_one_real : 1 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm_two)
    have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_one_real
    have hm_le_qm_nat : m ≤ q * m := by
      simpa [one_mul] using Nat.mul_le_mul_right m (by omega : 1 ≤ q)
    have hm_le_qm : (m : ℝ) ≤ ((q * m : ℕ) : ℝ) := by exact_mod_cast hm_le_qm_nat
    have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((q * m : ℕ) : ℝ) :=
      Real.log_le_log hm_pos hm_le_qm
    rw [erdos_weight]
    simp only [Nat.cast_mul, one_div, mul_inv_rev, mul_ite, ge_iff_le]
    rw [if_neg hm_one]
    rw [erdos_weight]
    simp only [one_div, mul_inv_rev]
    have hinv_log_le :
        (Real.log ((q : ℝ) * (m : ℝ)))⁻¹ ≤ (Real.log (m : ℝ))⁻¹ := by
      have hlogqm_eq :
          Real.log ((q : ℝ) * (m : ℝ)) = Real.log ((q * m : ℕ) : ℝ) := by
        norm_num
      rw [hlogqm_eq]
      simpa [one_div] using one_div_le_one_div_of_le hlogm_pos hlogm_le
    have hcoef_nonneg : 0 ≤ (m : ℝ)⁻¹ * (q : ℝ)⁻¹ := by positivity
    calc
      (Real.log ((q : ℝ) * (m : ℝ)))⁻¹ * ((m : ℝ)⁻¹ * (q : ℝ)⁻¹) ≤
          (Real.log (m : ℝ))⁻¹ * ((m : ℝ)⁻¹ * (q : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_right hinv_log_le hcoef_nonneg
      _ = (q : ℝ)⁻¹ * ((Real.log (m : ℝ))⁻¹ * (m : ℝ)⁻¹) := by ring

lemma mangoldt_adjoint_erdos_weight_multiples_sum_le_local (q N : ℕ) (hq : 2 ≤ q) :
    (∑ n ∈ Finset.Ico 2 (N + 1), if q ∣ n then erdos_weight n else 0) ≤
      (1 / (q : ℝ)) *
        (1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m) := by
  classical
  let S : Finset ℕ := (Finset.Ico 2 (N + 1)).filter (fun n => q ∣ n)
  let T : Finset ℕ := (Finset.Icc 1 N).filter (fun m => q * m ∈ Finset.Ico 2 (N + 1))
  have hleft : (∑ n ∈ Finset.Ico 2 (N + 1), if q ∣ n then erdos_weight n else 0) =
      ∑ n ∈ S, erdos_weight n := by
    dsimp [S]
    rw [← Finset.sum_filter]
  have hbij : (∑ n ∈ S, erdos_weight n) = ∑ m ∈ T, erdos_weight (q * m) := by
    refine Finset.sum_bij' (fun n _ => n / q) (fun m _ => q * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      dsimp [S, T] at hn ⊢
      simp only [Finset.mem_filter] at hn ⊢
      rcases hn with ⟨hnI, hdvd⟩
      rcases Finset.mem_Ico.mp hnI with ⟨hn_two, hn_lt⟩
      have hq_pos_nat : 0 < q := by omega
      have hq_le_n : q ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hdiv_pos : 1 ≤ n / q := Nat.div_pos hq_le_n hq_pos_nat
      constructor
      · exact Finset.mem_Icc.mpr ⟨hdiv_pos, (Nat.div_le_self n q).trans (Nat.le_of_lt_succ hn_lt)⟩
      · have hmul : q * (n / q) = n := by
          rw [mul_comm]
          exact Nat.div_mul_cancel hdvd
        simpa [hmul] using hnI
    · intro m hm
      dsimp [S, T] at hm ⊢
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.2, dvd_mul_right q m⟩
    · intro n hn
      dsimp [S] at hn
      simp only [Finset.mem_filter] at hn
      have hdvd : q ∣ n := hn.2
      simpa [mul_comm] using Nat.div_mul_cancel hdvd
    · intro m hm
      have hq_pos_nat : 0 < q := by omega
      exact Nat.mul_div_right m hq_pos_nat
    · intro n hn
      dsimp [S] at hn
      simp only [Finset.mem_filter] at hn
      have hdvd : q ∣ n := hn.2
      have hmul : q * (n / q) = n := by simpa [mul_comm] using Nat.div_mul_cancel hdvd
      simp [hmul]
  have hpoint : ∀ m ∈ T,
      erdos_weight (q * m) ≤
        (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) := by
    intro m hm
    dsimp [T] at hm
    have hm_one : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact mangoldt_adjoint_erdos_weight_mul_le_local q m hq hm_one
  have hT_le : (∑ m ∈ T, erdos_weight (q * m)) ≤
      ∑ m ∈ T, (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) := by
    exact Finset.sum_le_sum hpoint
  have hT_subset : T ⊆ Finset.Icc 1 N := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hnonneg_extra : ∀ m ∈ Finset.Icc 1 N, m ∉ T ->
      0 ≤ (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) := by
    intro m hm hmnot
    apply mul_nonneg
    · positivity
    · by_cases hm1 : m = 1
      · rw [if_pos hm1]
        exact div_nonneg zero_le_one (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
      · have hm_two : 2 ≤ m := by
          have hm_ge_one : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          omega
        rw [if_neg hm1]
        have hm_pos : 0 < (m : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm_two)
        have hlog_pos : 0 < Real.log (m : ℝ) := by
          exact Real.log_pos
            (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hm_two) : (1 : ℝ) < m)
        rw [erdos_weight]
        exact div_nonneg zero_le_one (mul_nonneg hm_pos.le hlog_pos.le)
  have hT_enlarge : (∑ m ∈ T,
      (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m)) ≤
      ∑ m ∈ Finset.Icc 1 N,
        (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hT_subset hnonneg_extra
  have hIcc_bound : (∑ m ∈ Finset.Icc 1 N,
        (1 / (q : ℝ)) * (if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m)) ≤
      (1 / (q : ℝ)) *
        (1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      (∑ m ∈ Finset.Icc 1 N, if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) ≤
          (if 1 ∈ Finset.Icc 1 N then 1 / Real.log (2 : ℝ) else 0) +
            ∑ m ∈ (Finset.Icc 1 N).erase 1, erdos_weight m := by
        by_cases hmem : 1 ∈ Finset.Icc 1 N
        · have hsum_erase :
              (∑ m ∈ (Finset.Icc 1 N).erase 1,
                if m = 1 then 1 / Real.log (2 : ℝ) else erdos_weight m) =
              ∑ m ∈ (Finset.Icc 1 N).erase 1, erdos_weight m := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            have hm_ne : m ≠ 1 := Finset.ne_of_mem_erase hm
            simp [hm_ne]
          rw [← Finset.sum_erase_add _ _ hmem, hsum_erase]
          simp only [Finset.Icc_erase_left, one_div, Finset.mem_Icc, Std.le_refl,
            true_and]
          have hN : 1 ≤ N := (Finset.mem_Icc.mp hmem).2
          rw [if_pos hN]
          rw [if_true]
          rw [add_comm (∑ x ∈ Finset.Ioc 1 N, erdos_weight x) ((Real.log 2)⁻¹)]
        · have herase : (Finset.Icc 1 N).erase 1 = Finset.Icc 1 N := by
            exact Finset.erase_eq_of_notMem hmem
          have hempty : Finset.Icc 1 N = ∅ := by
            ext m
            simp [Finset.mem_Icc] at hmem ⊢
            omega
          simp [hempty]
      _ ≤ 1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m := by
        apply add_le_add
        · by_cases hmem : 1 ∈ Finset.Icc 1 N
          · rw [if_pos hmem]
          · rw [if_neg hmem]
            exact div_nonneg zero_le_one
              (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro m hm
            have hmIcc := Finset.mem_of_mem_erase hm
            have hm_ne : m ≠ 1 := Finset.ne_of_mem_erase hm
            rcases Finset.mem_Icc.mp hmIcc with ⟨hm_ge_one, hm_le_N⟩
            have hm_two : 2 ≤ m := by omega
            exact Finset.mem_Ico.mpr ⟨hm_two, Nat.lt_succ_iff.mpr hm_le_N⟩
          · intro m hmIco hmnot
            rw [erdos_weight]
            positivity
  rw [hleft, hbij]
  exact (hT_le.trans hT_enlarge).trans hIcc_bound

lemma mangoldt_adjoint_prime_power_reciprocal_sum_le_prime_sum_local (N : ℕ) :
    (∑ p ∈ Finset.Ico 2 (N + 1),
        if Nat.Prime p then ∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / (p : ℝ)) ^ j else 0) ≤
      2 * (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) := by
  classical
  have hprime_finite :
      (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) =
        ∑ p ∈ Finset.Ico 2 (N + 1), if Nat.Prime p then (1 : ℝ) / (p : ℝ) else 0 := by
    rw [tsum_eq_sum (s := Finset.Ico 2 (N + 1))]
    · refine Finset.sum_congr rfl ?_
      intro p hpI
      rcases Finset.mem_Ico.mp hpI with ⟨hp_two, hp_lt⟩
      have hp_one : 1 ≤ p := by omega
      have hp_le_N : p ≤ N := Nat.lt_succ_iff.mp hp_lt
      have hp_le_N_real : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp_le_N
      by_cases hp_prime : Nat.Prime p
      · have hpseg : p ∈ prime_layer ∩ real_initial_segment (N : ℝ) :=
          ⟨hp_prime, hp_one, hp_le_N_real⟩
        simp [Set.indicator_of_mem hpseg, hp_prime]
      · have hpnotseg : p ∉ prime_layer ∩ real_initial_segment (N : ℝ) := by
          intro h
          exact hp_prime h.1
        simp [Set.indicator_of_notMem hpnotseg, hp_prime]
    · intro p hpnot
      by_cases hpseg : p ∈ prime_layer ∩ real_initial_segment (N : ℝ)
      · have hp_prime : Nat.Prime p := hpseg.1
        have hp_two : 2 ≤ p := hp_prime.two_le
        have hp_le_N : p ≤ N := by exact_mod_cast hpseg.2.2
        exact False.elim (hpnot (Finset.mem_Ico.mpr ⟨hp_two, Nat.lt_succ_iff.mpr hp_le_N⟩))
      · simp [Set.indicator_of_notMem hpseg]
  have hpoint : ∀ p ∈ Finset.Ico 2 (N + 1),
      (if Nat.Prime p then ∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / (p : ℝ)) ^ j else 0) ≤
        2 * (if Nat.Prime p then (1 : ℝ) / (p : ℝ) else 0) := by
    intro p hpI
    by_cases hp_prime : Nat.Prime p
    · have hp_two : 2 ≤ p := hp_prime.two_le
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp_two)
      have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_two
      have hbase_nonneg : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
      have hbase_lt_one : (1 : ℝ) / (p : ℝ) < 1 := by
        rw [div_lt_one₀ hp_pos]
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hp_two)
      have hIcc_eq :
          (∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / (p : ℝ)) ^ j) =
            ∑ j ∈ Finset.Ico 1 (N + 1), ((1 : ℝ) / (p : ℝ)) ^ j := by
        refine Finset.sum_congr ?_ ?_
        · ext j
          simp [Finset.mem_Icc, Finset.mem_Ico]
        · intro j hj
          rfl
      have hgeom := geom_sum_Ico_le_of_lt_one (m := 1) (n := N + 1) hbase_nonneg hbase_lt_one
      have hgeom' :
          (∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / (p : ℝ)) ^ j) ≤
            ((1 : ℝ) / (p : ℝ)) / (1 - (1 : ℝ) / (p : ℝ)) := by
        rw [hIcc_eq]
        simpa [one_div, inv_pow] using hgeom
      have hmajor : ((1 : ℝ) / (p : ℝ)) / (1 - (1 : ℝ) / (p : ℝ)) ≤
          2 * ((1 : ℝ) / (p : ℝ)) := by
        have hp_minus_pos : 0 < (p : ℝ) - 1 := by linarith
        have hden_pos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by
          rw [sub_pos]
          exact hbase_lt_one
        field_simp [hp_pos.ne', hden_pos.ne', hp_minus_pos.ne']
        nlinarith
      simpa [hp_prime] using hgeom'.trans hmajor
    · simp [hp_prime]
  calc
    (∑ p ∈ Finset.Ico 2 (N + 1),
        if Nat.Prime p then ∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / (p : ℝ)) ^ j else 0) ≤
        ∑ p ∈ Finset.Ico 2 (N + 1), 2 * (if Nat.Prime p then (1 : ℝ) / (p : ℝ) else 0) := by
      exact Finset.sum_le_sum hpoint
    _ = 2 * (∑ p ∈ Finset.Ico 2 (N + 1), if Nat.Prime p then (1 : ℝ) / (p : ℝ) else 0) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) := by
      rw [hprime_finite]

lemma mangoldt_adjoint_card_factors_erdos_natural_product_bound_local (N : ℕ) :
    (∑ n ∈ Finset.Ico 2 (N + 1),
        ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n)) ≤
      4 *
        (1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m) *
          (∑' p : ℕ,
            (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
              (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) := by
  classical
  let I : Finset ℕ := Finset.Ico 2 (N + 1)
  let J : Finset ℕ := Finset.Icc 1 N
  let E : ℝ := 1 / Real.log (2 : ℝ) + ∑ m ∈ I, erdos_weight m
  let P : ℝ := ∑' p : ℕ,
    (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
      (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, I]
    apply add_nonneg
    · positivity
    · refine Finset.sum_nonneg ?_
      intro m hm
      rw [erdos_weight]
      positivity
  have hpoint : ∀ n ∈ I,
      ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n) ≤
        2 * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := by
    intro n hnI
    rcases Finset.mem_Ico.mp hnI with ⟨hn_two, hn_lt⟩
    have hn_le_N : n ≤ N := Nat.lt_succ_iff.mp hn_lt
    have homega_pos : 1 ≤ ArithmeticFunction.cardFactors n := by
      exact Nat.succ_le_of_lt (ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega : 1 < n))
    have hcoeff_le_nat :
        ArithmeticFunction.cardFactors n + 1 ≤ 2 * ArithmeticFunction.cardFactors n := by
      nlinarith
    have hcount :=
      mangoldt_adjoint_card_factors_le_prime_power_divisor_count_local n N hn_two hn_le_N
    have herd_nonneg : 0 ≤ erdos_weight n := by
      rw [erdos_weight]
      positivity
    have hcoeff_le : ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ)) ≤
        2 * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) := by
      have hcount2 : ArithmeticFunction.cardFactors n + 1 ≤
          2 * (∑ p ∈ I,
            if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) := by
        exact hcoeff_le_nat.trans (Nat.mul_le_mul_left 2 hcount)
      exact_mod_cast hcount2
    calc
      ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n) ≤
          (2 * (∑ p ∈ I,
            if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) : ℝ) *
            erdos_weight n := by
        exact mul_le_mul_of_nonneg_right hcoeff_le herd_nonneg
      _ = 2 * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := by
        have hcast_mul :
            ((∑ p ∈ I,
              if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) : ℝ) *
              erdos_weight n =
            ∑ p ∈ I,
              if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0
              else 0 := by
          rw [Nat.cast_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro p hp
          by_cases hp_prime : Nat.Prime p
          · rw [if_pos hp_prime]
            rw [if_pos hp_prime]
            conv_rhs => rw [← Finset.sum_filter]
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
          · simp [hp_prime]
        calc
          (2 * (∑ p ∈ I,
            if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) : ℝ) *
              erdos_weight n =
              2 * (((∑ p ∈ I,
                if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then 1 else 0 else 0 : ℕ) : ℝ) *
                  erdos_weight n) := by ring
          _ = 2 * (∑ p ∈ I,
              if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := by
            rw [hcast_mul]
  have hsum_point :
      (∑ n ∈ I,
        ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n)) ≤
        ∑ n ∈ I, 2 * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := by
    exact Finset.sum_le_sum hpoint
  have hcomm :
      (∑ n ∈ I, ∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) =
        ∑ p ∈ I, if Nat.Prime p then
          ∑ j ∈ J, ∑ n ∈ I, if p ^ j ∣ n then erdos_weight n else 0
        else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p hp
    by_cases hp_prime : Nat.Prime p
    · simp only [hp_prime, if_true]
      rw [Finset.sum_comm]
    · simp only [hp_prime, if_false, Finset.sum_const_zero]
  have hinner :
      (∑ p ∈ I, if Nat.Prime p then
          ∑ j ∈ J, ∑ n ∈ I, if p ^ j ∣ n then erdos_weight n else 0
        else 0) ≤
        E * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, ((1 : ℝ) / (p : ℝ)) ^ j else 0) := by
    calc
      (∑ p ∈ I, if Nat.Prime p then
          ∑ j ∈ J, ∑ n ∈ I, if p ^ j ∣ n then erdos_weight n else 0
        else 0) ≤
          ∑ p ∈ I, if Nat.Prime p then ∑ j ∈ J, ((1 : ℝ) / (p : ℝ)) ^ j * E else 0 := by
        refine Finset.sum_le_sum ?_
        intro p hpI
        by_cases hp_prime : Nat.Prime p
        · rw [if_pos hp_prime, if_pos hp_prime]
          refine Finset.sum_le_sum ?_
          intro j hjJ
          rcases Finset.mem_Icc.mp hjJ with ⟨hj_one, hj_le_N⟩
          have hp_two : 2 ≤ p := hp_prime.two_le
          have hq_two : 2 ≤ p ^ j := by
            have hj_ne : j ≠ 0 := by omega
            have hp_pow_ge : p ≤ p ^ j := Nat.le_self_pow hj_ne p
            exact hp_two.trans hp_pow_ge
          have hmult := mangoldt_adjoint_erdos_weight_multiples_sum_le_local (p ^ j) N hq_two
          have hpow_eq : (1 / ((p ^ j : ℕ) : ℝ)) = ((1 : ℝ) / (p : ℝ)) ^ j := by
            rw [Nat.cast_pow]
            simp [one_div, inv_pow]
          dsimp [E, I] at hmult ⊢
          simpa [hpow_eq, mul_comm, mul_left_comm, mul_assoc] using hmult
        · simp [hp_prime]
      _ = E * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, ((1 : ℝ) / (p : ℝ)) ^ j else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        by_cases hp_prime : Nat.Prime p
        · simp [hp_prime, Finset.mul_sum, mul_comm]
        · simp [hp_prime]
  have hpp := mangoldt_adjoint_prime_power_reciprocal_sum_le_prime_sum_local N
  calc
    (∑ n ∈ I,
        ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n)) ≤
        ∑ n ∈ I, 2 * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := hsum_point
    _ = 2 * (∑ n ∈ I, ∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, if p ^ j ∣ n then erdos_weight n else 0 else 0) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ p ∈ I, if Nat.Prime p then
          ∑ j ∈ J, ∑ n ∈ I, if p ^ j ∣ n then erdos_weight n else 0
        else 0) := by
      rw [hcomm]
    _ ≤ 2 * (E * (∑ p ∈ I,
          if Nat.Prime p then ∑ j ∈ J, ((1 : ℝ) / (p : ℝ)) ^ j else 0)) := by
      exact mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ 2 * (E * (2 * P)) := by
      dsimp [P]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpp hE_nonneg) (by norm_num)
    _ = 4 * E * P := by ring

lemma mangoldt_adjoint_card_factors_erdos_real_terminal_sum_bound_local :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x in Filter.atTop,
      (∑' n : ℕ,
        (real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              erdos_weight n)) n) ≤
        K * (Real.log (Real.log x)) ^ 2 := by
  obtain ⟨B, hB_nonneg, hB⟩ := mangoldt_adjoint_erdos_weight_natural_terminal_sum_bound_local
  obtain ⟨C, hC_nonneg, hC⟩ := mertens_prime_reciprocal
  let A : ℝ := 1 / Real.log (2 : ℝ) + B
  let K : ℝ := 4 * (A + 1) * (C + 1)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K, A]
    positivity
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards
    [Filter.eventually_ge_atTop (3 : ℝ), hloglog.eventually_ge_atTop (1 : ℝ)] with
    x hx hll
  let N : ℕ := ⌊x⌋₊
  have hx_nonneg : 0 ≤ x := by linarith
  have hN_two : 2 ≤ N := by
    simpa [N] using Nat.le_floor (by linarith : (2 : ℝ) ≤ x)
  have hN_le_x : (N : ℝ) ≤ x := by
    simpa [N] using Nat.floor_le hx_nonneg
  have hsum_eq :
      (∑' n : ℕ,
        (real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              erdos_weight n)) n) =
        ∑ n ∈ Finset.Ico 2 (N + 1),
          ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n) := by
    rw [tsum_eq_sum (s := Finset.Ico 2 (N + 1))]
    · refine Finset.sum_congr rfl ?_
      intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hn_two, hn_lt⟩
      have hn_one : 1 ≤ n := by omega
      have hn_le_N : n ≤ N := Nat.lt_succ_iff.mp hn_lt
      have hn_le_x : (n : ℝ) ≤ x := by
        have hn_le_N_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_le_N
        exact hn_le_N_real.trans hN_le_x
      simp [real_initial_segment, hn_one, hn_le_x]
    · intro n hn
      by_cases hseg : n ∈ real_initial_segment x
      · by_cases hn_two : 2 ≤ n
        · have hn_le_N : n ≤ N := Nat.le_floor hseg.2
          exfalso
          exact hn (Finset.mem_Ico.mpr ⟨hn_two, Nat.lt_succ_iff.mpr hn_le_N⟩)
        · have hn_cases : n = 0 ∨ n = 1 := by omega
          rcases hn_cases with rfl | rfl
          · simp [real_initial_segment] at hseg
          · simp [erdos_weight]
      · simp [Set.indicator_of_notMem hseg]
  have hloglog_mono : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log x) := by
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN_two)
    have hN_one : 1 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hN_two)
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_one
    have hlog_le : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hN_pos hN_le_x
    exact Real.log_le_log hlogN_pos hlog_le
  have hE_nat := hB N hN_two
  have hprime_abs := hC (N : ℝ) (by exact_mod_cast hN_two : (2 : ℝ) ≤ N)
  have hprime_le :
      (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) ≤ C + Real.log (Real.log (N : ℝ)) := by
    have hdiff_le :
        (∑' p : ℕ,
          (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) - Real.log (Real.log (N : ℝ)) ≤ C := by
      exact (le_abs_self _).trans hprime_abs
    linarith
  have hprod := mangoldt_adjoint_card_factors_erdos_natural_product_bound_local N
  have hE_bound :
      1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m ≤
        A + Real.log (Real.log x) := by
    dsimp [A]
    linarith
  have hP_bound :
      (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) ≤ C + Real.log (Real.log x) := by
    linarith
  have hE_nonneg : 0 ≤ 1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m := by
    apply add_nonneg
    · positivity
    · refine Finset.sum_nonneg ?_
      intro m hm
      rw [erdos_weight]
      positivity
  have hP_nonneg : 0 ≤ (∑' p : ℕ,
        (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) := by
    apply tsum_nonneg
    intro p
    by_cases hp : p ∈ prime_layer ∩ real_initial_segment (N : ℝ)
    · have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp.1.two_le)
      simp [Set.indicator_of_mem hp, le_of_lt hp_pos]
    · simp [Set.indicator_of_notMem hp]
  calc
    (∑' n : ℕ,
        (real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              erdos_weight n)) n) =
        ∑ n ∈ Finset.Ico 2 (N + 1),
          ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n) := hsum_eq
    _ ≤ 4 *
        (1 / Real.log (2 : ℝ) + ∑ m ∈ Finset.Ico 2 (N + 1), erdos_weight m) *
          (∑' p : ℕ,
            (prime_layer ∩ real_initial_segment (N : ℝ)).indicator
              (fun p : ℕ => (1 : ℝ) / (p : ℝ)) p) := hprod
    _ ≤ 4 * (A + Real.log (Real.log x)) * (C + Real.log (Real.log x)) := by
      nlinarith [hE_bound, hP_bound, hE_nonneg, hP_nonneg]
    _ ≤ K * (Real.log (Real.log x)) ^ 2 := by
      dsimp [K]
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        positivity
      let L : ℝ := Real.log (Real.log x)
      have hL : 1 ≤ L := by simpa [L] using hll
      have hA_fac : A + L ≤ (A + 1) * L := by nlinarith [hA_nonneg, hL]
      have hC_fac : C + L ≤ (C + 1) * L := by nlinarith [hC_nonneg, hL]
      have hCL_nonneg : 0 ≤ C + L := by nlinarith [hC_nonneg, hL]
      calc
        4 * (A + Real.log (Real.log x)) * (C + Real.log (Real.log x)) =
            4 * (A + L) * (C + L) := by simp [L]
        _ ≤ 4 * ((A + 1) * L) * ((C + 1) * L) := by
          have hmul : (A + L) * (C + L) ≤ ((A + 1) * L) * ((C + 1) * L) := by
            exact mul_le_mul hA_fac hC_fac hCL_nonneg (by nlinarith [hA_nonneg, hL])
          nlinarith
        _ = 4 * (A + 1) * (C + 1) * L ^ 2 := by ring
        _ = 4 * (A + 1) * (C + 1) * Real.log (Real.log x) ^ 2 := by simp [L]

lemma mangoldt_adjoint_mangoldt_positive_part_le_erdos_local :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, 2 ≤ n ->
      max (mangoldt_weight n) 0 ≤ M * erdos_weight n := by
  obtain ⟨C, hC_nonneg, hC⟩ := mangoldt_weight_erdos_pointwise_error_bound
  let M : ℝ := 1 + C / Real.log (2 : ℝ)
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    positivity
  intro n hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_one : 1 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_one
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  have herd_nonneg : 0 ≤ erdos_weight n := by
    rw [erdos_weight]
    positivity
  have herr := hC n hn
  have herr_scaled : C * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) ≤
      (C / Real.log (2 : ℝ)) * erdos_weight n := by
    rw [erdos_weight]
    have hden_pos : 0 < (n : ℝ) * Real.log (n : ℝ) ^ 2 :=
      mul_pos hn_pos (pow_pos hlog_pos 2)
    have htarget_nonneg : 0 ≤ C / Real.log (2 : ℝ) := div_nonneg hC_nonneg hlog2_pos.le
    calc
      C * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) =
          (C / Real.log (n : ℝ)) * (1 / ((n : ℝ) * Real.log (n : ℝ))) := by
        field_simp [hn_pos.ne', hlog_pos.ne']
      _ ≤ (C / Real.log (2 : ℝ)) * (1 / ((n : ℝ) * Real.log (n : ℝ))) := by
        have hcoef : C / Real.log (n : ℝ) ≤ C / Real.log (2 : ℝ) := by
          exact div_le_div_of_nonneg_left hC_nonneg hlog2_pos hlog2_le
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hmw_le : mangoldt_weight n ≤ M * erdos_weight n := by
    have hdiff_le : mangoldt_weight n - erdos_weight n ≤
        C * (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) :=
      (le_abs_self _).trans herr
    dsimp [M]
    nlinarith
  have hMerdos_nonneg : 0 ≤ M * erdos_weight n := mul_nonneg (by dsimp [M]; positivity) herd_nonneg
  exact max_le hmw_le hMerdos_nonneg

lemma mangoldt_adjoint_terminal_sum_le_one_add_erdos_local (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hM : ∀ n : ℕ, 2 ≤ n -> max (mangoldt_weight n) 0 ≤ M * erdos_weight n)
    (A : Set ℕ) (x : ℝ) :
    (∑' n : ℕ,
      (A ∩ real_initial_segment x).indicator
        (fun n : ℕ =>
          ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
            max (mangoldt_weight n) 0)) n) ≤
      1 + M * (∑' n : ℕ,
        (real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              erdos_weight n)) n) := by
  classical
  let S : Set ℕ := A ∩ real_initial_segment x
  let f : ℕ → ℝ := fun n => S.indicator
    (fun n : ℕ => ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
      max (mangoldt_weight n) 0)) n
  let e : ℕ → ℝ := fun n => (real_initial_segment x).indicator
    (fun n : ℕ => ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n)) n
  let single : ℕ → ℝ := fun n => if n = 1 then 1 else 0
  let g : ℕ → ℝ := fun n => single n + M * e n
  have hSfinite : S.Finite := by
    exact (((Set.finite_le_nat ⌊x⌋₊).subset (by
      intro n hn
      exact Nat.le_floor hn.2)).inter_of_right A)
  have hsegfinite : (real_initial_segment x).Finite := by
    exact (Set.finite_le_nat ⌊x⌋₊).subset (by
      intro n hn
      exact Nat.le_floor hn.2)
  have hf_summ : Summable f := by
    refine summable_of_ne_finset_zero (s := hSfinite.toFinset) ?_
    intro n hn
    have hnS : n ∉ S := fun hmem => hn (hSfinite.mem_toFinset.mpr hmem)
    simp [f, Set.indicator_of_notMem hnS]
  have he_summ : Summable e := by
    refine summable_of_ne_finset_zero (s := hsegfinite.toFinset) ?_
    intro n hn
    have hnseg : n ∉ real_initial_segment x := fun hmem => hn (hsegfinite.mem_toFinset.mpr hmem)
    simp [e, Set.indicator_of_notMem hnseg]
  have hsingle_summ : Summable single := by
    refine summable_of_ne_finset_zero (s := ({1} : Finset ℕ)) ?_
    intro n hn
    have hn_ne : n ≠ 1 := by
      intro h
      apply hn
      simp [h]
    simp [single, hn_ne]
  have hg_summ : Summable g := by
    exact hsingle_summ.add (he_summ.mul_left M)
  have he_nonneg_all : ∀ n : ℕ, 0 ≤ e n := by
    intro n
    by_cases hnseg : n ∈ real_initial_segment x
    · have hcoeff_nonneg : 0 ≤ ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.zero_le (ArithmeticFunction.cardFactors n + 1)
      have herd_nonneg : 0 ≤ erdos_weight n := by
        rw [erdos_weight]
        positivity
      simpa [e, Set.indicator_of_mem hnseg, Nat.cast_add, Nat.cast_one] using
        mul_nonneg hcoeff_nonneg herd_nonneg
    · simp [e, Set.indicator_of_notMem hnseg]
  have hfg : ∀ n : ℕ, f n ≤ g n := by
    intro n
    by_cases hnS : n ∈ S
    · have hnseg : n ∈ real_initial_segment x := hnS.2
      by_cases hn_one : n = 1
      · subst n
        simp [f, g, single, e, S, hnS, hnseg, erdos_weight, mangoldt_weight]
      · have hn_two : 2 ≤ n := by
          have hn_ge_one : 1 ≤ n := hnseg.1
          omega
        have hcoeff_nonneg : 0 ≤ ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ)) := by
          exact_mod_cast Nat.zero_le (ArithmeticFunction.cardFactors n + 1)
        have hdom := hM n hn_two
        have herd_nonneg : 0 ≤ erdos_weight n := by
          rw [erdos_weight]
          positivity
        have hterm :
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * max (mangoldt_weight n) 0) ≤
              M * ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * erdos_weight n) := by
          calc
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * max (mangoldt_weight n) 0) ≤
                (((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) * (M * erdos_weight n) := by
              exact mul_le_mul_of_nonneg_left hdom hcoeff_nonneg
            _ = M *
                ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                  erdos_weight n) := by
              ring
        simp [f, g, single, e, S, hnS, hnseg, hn_one]
        simpa [Nat.cast_add, Nat.cast_one] using hterm
    · have hf_zero : f n = 0 := by
        simp [f, Set.indicator_of_notMem hnS]
      have hg_nonneg : 0 ≤ g n := by
        by_cases hn_one : n = 1
        · have hnonneg := add_nonneg zero_le_one (mul_nonneg hM_nonneg (he_nonneg_all 1))
          simpa [g, single, hn_one] using hnonneg
        · have he_nonneg : 0 ≤ e n := by
            exact he_nonneg_all n
          simp [g, single, hn_one, mul_nonneg hM_nonneg he_nonneg]
      rw [hf_zero]
      exact hg_nonneg
  have hle := Summable.tsum_le_tsum hfg hf_summ hg_summ
  have hsingle_tsum : (∑' n : ℕ, single n) = 1 := by
    rw [tsum_eq_sum (s := ({1} : Finset ℕ))]
    · simp [single]
    · intro n hn
      have hn_ne : n ≠ 1 := by
        intro h
        apply hn
        simp [h]
      simp [single, hn_ne]
  have hg_tsum : (∑' n : ℕ, g n) = 1 + M * (∑' n : ℕ, e n) := by
    dsimp [g]
    rw [hsingle_summ.tsum_add (he_summ.mul_left M), hsingle_tsum]
    rw [tsum_mul_left]
  change (∑' n : ℕ, f n) ≤ 1 + M * (∑' n : ℕ, e n)
  rwa [hg_tsum] at hle

lemma mangoldt_adjoint_card_factors_weighted_terminal_sum_bound :
    ∀ A : Set ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x in Filter.atTop,
      (∑' n : ℕ,
        (A ∩ real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              max (mangoldt_weight n) 0)) n) ≤
        K * (Real.log (Real.log x)) ^ 2 := by
  obtain ⟨M, hM_nonneg, hM⟩ := mangoldt_adjoint_mangoldt_positive_part_le_erdos_local
  obtain ⟨K, hK_nonneg, hK⟩ :=
    mangoldt_adjoint_card_factors_erdos_real_terminal_sum_bound_local
  intro A
  refine ⟨1 + M * K, by positivity, ?_⟩
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hK, hloglog.eventually_ge_atTop (1 : ℝ)] with x hE hll
  have hcompare := mangoldt_adjoint_terminal_sum_le_one_add_erdos_local M hM_nonneg hM A x
  let L : ℝ := Real.log (Real.log x)
  calc
    (∑' n : ℕ,
        (A ∩ real_initial_segment x).indicator
          (fun n : ℕ =>
            ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
              max (mangoldt_weight n) 0)) n) ≤
        1 + M * (∑' n : ℕ,
          (real_initial_segment x).indicator
            (fun n : ℕ =>
              ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                erdos_weight n)) n) := hcompare
    _ ≤ 1 + M * (K * L ^ 2) := by
      dsimp [L] at hE ⊢
      nlinarith
    _ ≤ (1 + M * K) * L ^ 2 := by
      have hLsq : 1 ≤ L ^ 2 := by nlinarith
      nlinarith

lemma mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_two_point_divisor_bound μ path ->
      mangoldt_adjoint_second_moment_bound μ path := by
  intro htwo A
  rcases htwo A with ⟨C, hC_nonneg, hC_eventually⟩
  rcases mangoldt_adjoint_card_factors_weighted_terminal_sum_bound A with
    ⟨K, hK_nonneg, hK_eventually⟩
  refine ⟨C * K, mul_nonneg hC_nonneg hK_nonneg, ?_⟩
  filter_upwards [hC_eventually, hK_eventually] with x hx hsum
  rcases hx with ⟨hloglog_pos, hmoment⟩
  refine ⟨hloglog_pos, hmoment.trans ?_⟩
  exact ENNReal.ofReal_le_ofReal <| by
    calc
      C * (∑' n : ℕ,
          (A ∩ real_initial_segment x).indicator
            (fun n : ℕ =>
              ((((ArithmeticFunction.cardFactors n : ℕ) + 1 : ℕ) : ℝ) *
                max (mangoldt_weight n) 0)) n) ≤
          C * (K * (Real.log (Real.log x)) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum hC_nonneg
      _ = (C * K) * (Real.log (Real.log x)) ^ 2 := by
            ring

abbrev mangoldt_adjoint_normalized_hit_expectation_limsup {Ω : Type}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ,
    Filter.limsup
      (fun x : ℝ =>
        ENNReal.toReal
          (∑' k : ℕ,
            μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) /
          Real.log (Real.log x))
      Filter.atTop = mangoldt_weight_upper_density A

lemma mangoldt_adjoint_normalized_hit_expectation_limsup_from_visit_identity
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_constructed_path_data μ path ->
      mangoldt_adjoint_normalized_hit_expectation_limsup μ path := by
  intro hdata
  rcases hdata with ⟨hprob, hchain, hmeas, hvisit⟩
  unfold mangoldt_adjoint_visit_identity at hvisit
  intro A
  apply congrArg (fun f : ℝ → ℝ => Filter.limsup f Filter.atTop)
  funext x
  congr 1
  let S : Set ℕ := A ∩ real_initial_segment x
  have hpath_pos : ∀ (ω : Ω) (k : ℕ), 1 ≤ path ω k := by
    intro ω k
    have hzero_pos : 0 < path ω 0 := by
      by_contra hnot
      have hzero : path ω 0 = 0 := by omega
      rcases (hchain ω).2 0 with ⟨c, hc⟩
      have hnext_zero : path ω 1 = 0 := by
        simpa [hzero] using hc
      have hlt : path ω 0 < path ω 1 := (hchain ω).1 (Nat.zero_lt_succ 0)
      omega
    have hbase : 1 ≤ path ω 0 := hzero_pos
    have hle : path ω 0 + k ≤ path ω k := by
      simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 k 0
    exact le_trans hbase (le_trans (Nat.le_add_right (path ω 0) k) hle)
  have hfin : S.Finite := by
    dsimp [S]
    exact (((Set.finite_le_nat ⌊x⌋₊).subset (by
      intro n hn
      exact Nat.le_floor hn.2)).inter_of_right A)
  have hmeasure_k : ∀ k : ℕ,
      μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
        ∑ n ∈ hfin.toFinset, μ {ω : Ω | path ω k = n} := by
    intro k
    have hcover : {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
        ⋃ n ∈ hfin.toFinset, {ω : Ω | path ω k = n} := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.mpr ⟨path ω k, ?_⟩
        refine Set.mem_iUnion.mpr ⟨?_, rfl⟩
        exact hfin.mem_toFinset.mpr ⟨hω.1, ⟨hpath_pos ω k, hω.2⟩⟩
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
        rcases Set.mem_iUnion.mp hn with ⟨hnF, hnω⟩
        have hnS : n ∈ S := hfin.mem_toFinset.mp hnF
        have hnS' : n ∈ A ∩ real_initial_segment x := by simpa [S] using hnS
        have hpath_eq : path ω k = n := hnω
        exact ⟨by simpa [hpath_eq] using hnS'.1, by
          have hnle : (n : ℝ) ≤ x := hnS'.2.2
          simpa [hpath_eq] using hnle⟩
    have hdisj : Set.PairwiseDisjoint (↑(hfin.toFinset))
        (fun n : ℕ => {ω : Ω | path ω k = n}) := by
      intro m hm n hn hmn
      change Disjoint {ω : Ω | path ω k = m} {ω : Ω | path ω k = n}
      exact Set.disjoint_left.mpr (by
        intro ω hmω hnω
        exact hmn (by rw [← hmω, hnω]))
    have hmeas_exact : ∀ n ∈ hfin.toFinset,
        MeasurableSet {ω : Ω | path ω k = n} := by
      intro n hn
      exact measurableSet_eq_fun (hmeas k) measurable_const
    calc
      μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
          μ (⋃ n ∈ hfin.toFinset, {ω : Ω | path ω k = n}) := by
        rw [hcover]
      _ = ∑ n ∈ hfin.toFinset, μ {ω : Ω | path ω k = n} := by
        exact MeasureTheory.measure_biUnion_finset hdisj hmeas_exact
  have hmeasure_k_tsum : ∀ k : ℕ,
      μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} =
        ∑' n : ℕ, if n ∈ hfin.toFinset then μ {ω : Ω | path ω k = n} else 0 := by
    intro k
    rw [hmeasure_k k]
    symm
    calc
      (∑' n : ℕ, if n ∈ hfin.toFinset then μ {ω : Ω | path ω k = n} else 0) =
          ∑ n ∈ hfin.toFinset,
            (if n ∈ hfin.toFinset then μ {ω : Ω | path ω k = n} else 0) := by
        refine tsum_eq_sum (s := hfin.toFinset) ?_
        intro n hn
        simp [hn]
      _ = ∑ n ∈ hfin.toFinset, μ {ω : Ω | path ω k = n} := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [hn]
  have hleft_enn :
      (∑' k : ℕ, μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) =
        ∑' n : ℕ, if n ∈ hfin.toFinset then ENNReal.ofReal (mangoldt_weight n) else 0 := by
    calc
      (∑' k : ℕ, μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) =
          ∑' k : ℕ, ∑' n : ℕ,
            if n ∈ hfin.toFinset then μ {ω : Ω | path ω k = n} else 0 := by
        apply tsum_congr
        intro k
        exact hmeasure_k_tsum k
      _ = ∑' n : ℕ, ∑' k : ℕ,
            if n ∈ hfin.toFinset then μ {ω : Ω | path ω k = n} else 0 := by
        rw [ENNReal.tsum_comm]
      _ = ∑' n : ℕ, if n ∈ hfin.toFinset then
            (∑' k : ℕ, μ {ω : Ω | path ω k = n}) else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ hfin.toFinset <;> simp [hn]
      _ = ∑' n : ℕ, if n ∈ hfin.toFinset then ENNReal.ofReal (mangoldt_weight n) else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ hfin.toFinset <;> simp [hn, hvisit n]
  have hright_real :
      mangoldt_weight_sum_up_to A x =
        ∑' n : ℕ, if n ∈ hfin.toFinset then mangoldt_weight n else 0 := by
    unfold mangoldt_weight_sum_up_to
    change (∑' n : ℕ, S.indicator mangoldt_weight n) =
      ∑' n : ℕ, if n ∈ hfin.toFinset then mangoldt_weight n else 0
    apply tsum_congr
    intro n
    by_cases hn : n ∈ hfin.toFinset
    · have hnS : n ∈ S := hfin.mem_toFinset.mp hn
      simp [hn, Set.indicator_of_mem hnS]
    · have hnS : n ∉ S := fun h => hn (hfin.mem_toFinset.mpr h)
      simp [hn, Set.indicator_of_notMem hnS]
  rw [hleft_enn, hright_real]
  have hleft_fin :
      (∑' n : ℕ, if n ∈ hfin.toFinset then ENNReal.ofReal (mangoldt_weight n) else 0) =
        ∑ n ∈ hfin.toFinset, ENNReal.ofReal (mangoldt_weight n) := by
    calc
      (∑' n : ℕ, if n ∈ hfin.toFinset then ENNReal.ofReal (mangoldt_weight n) else 0) =
          ∑ n ∈ hfin.toFinset,
            (if n ∈ hfin.toFinset then ENNReal.ofReal (mangoldt_weight n) else 0) := by
        refine tsum_eq_sum (s := hfin.toFinset) ?_
        intro n hn
        simp [hn]
      _ = ∑ n ∈ hfin.toFinset, ENNReal.ofReal (mangoldt_weight n) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [hn]
  have hright_fin :
      (∑' n : ℕ, if n ∈ hfin.toFinset then mangoldt_weight n else 0) =
        ∑ n ∈ hfin.toFinset, mangoldt_weight n := by
    calc
      (∑' n : ℕ, if n ∈ hfin.toFinset then mangoldt_weight n else 0) =
          ∑ n ∈ hfin.toFinset,
            (if n ∈ hfin.toFinset then mangoldt_weight n else 0) := by
        refine tsum_eq_sum (s := hfin.toFinset) ?_
        intro n hn
        simp [hn]
      _ = ∑ n ∈ hfin.toFinset, mangoldt_weight n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [hn]
  rw [hleft_fin, hright_fin]
  have hweight_nonneg : ∀ n ∈ hfin.toFinset, 0 ≤ mangoldt_weight n := by
    intro n hn
    have hnS : n ∈ S := hfin.mem_toFinset.mp hn
    have hnS' : n ∈ A ∩ real_initial_segment x := by simpa [S] using hnS
    exact (mangoldt_weight_positive n hnS'.2.1).le
  have hsum_enn :
      (∑ n ∈ hfin.toFinset, ENNReal.ofReal (mangoldt_weight n)) =
        ENNReal.ofReal (∑ n ∈ hfin.toFinset, mangoldt_weight n) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro n hn
    exact hweight_nonneg n hn
  rw [hsum_enn]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg hweight_nonneg)

noncomputable def mangoldt_adjoint_normalized_hit_count {Ω : Type}
    (path : Ω → ℕ → ℕ) (A : Set ℕ) (x : ℝ) (ω : Ω) : ℝ :=
  (chain_hits_count_up_to (path ω) A x : ℝ) / Real.log (Real.log x)

abbrev mangoldt_adjoint_hit_count_moment_bridge {Ω : Type}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (path : Ω → ℕ → ℕ) : Prop :=
  ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
    ∃ xseq : ℕ → ℝ,
      Filter.Tendsto xseq Filter.atTop Filter.atTop ∧
        (∀ j : ℕ, 2 ≤ xseq j ∧ 0 < Real.log (Real.log (xseq j))) ∧
        (∀ j : ℕ,
          ∀ᵐ ω ∂μ,
            ({i : ℕ | path ω i ∈ A ∧ (path ω i : ℝ) ≤ xseq j} : Set ℕ).Finite) ∧
        (∀ j : ℕ,
          AEMeasurable
            (fun ω : Ω =>
              ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            μ) ∧
        Filter.limsup
          (fun j : ℕ =>
            (∫⁻ ω,
              ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω) ∂μ).toReal)
          Filter.atTop =
          mangoldt_weight_upper_density A ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
          ∫⁻ ω,
            ((ENNReal.ofReal
              (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ)) ∂μ ≤
            ENNReal.ofReal C

lemma mangoldt_adjoint_of_real_normalized_finset_count
    (F : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal (((∑ i ∈ F, if p i then (1 : ℕ) else 0 : ℕ) : ℝ) / L) =
      ∑ i ∈ F, if p i then (ENNReal.ofReal L)⁻¹ else 0 := by
  classical
  have hbase :
      ENNReal.ofReal (((∑ i ∈ F, if p i then (1 : ℕ) else 0 : ℕ) : ℝ) / L) =
        ∑ i ∈ F, if p i then ENNReal.ofReal (1 / L) else 0 := by
    have hreal :
        ((∑ i ∈ F, if p i then (1 : ℕ) else 0 : ℕ) : ℝ) / L =
          ∑ i ∈ F, if p i then (1 / L : ℝ) else 0 := by
      simp only [Finset.sum_boole]
      change ((F.filter p).card : ℝ) / L =
        ∑ i ∈ F, if p i then (1 / L : ℝ) else 0
      calc
        ((F.filter p).card : ℝ) / L = ((F.filter p).card : ℝ) * (1 / L) := by
          ring
        _ = ∑ i ∈ F, if p i then (1 / L : ℝ) else 0 := by
          calc
            ((F.filter p).card : ℝ) * (1 / L) =
                (∑ i ∈ F, if p i then (1 : ℝ) else 0) * (1 / L) := by
              rw [Finset.sum_boole]
            _ = ∑ i ∈ F, (if p i then (1 : ℝ) else 0) * (1 / L) := by
              rw [Finset.sum_mul]
            _ = ∑ i ∈ F, if p i then (1 / L : ℝ) else 0 := by
              simp
    rw [hreal, ENNReal.ofReal_sum_of_nonneg]
    · exact Finset.sum_congr rfl (by
        intro i hi
        by_cases hpi : p i <;> simp [hpi])
    · intro i hi
      by_cases hpi : p i <;> simp [hpi, hL.le]
  simpa [one_div, ENNReal.ofReal_inv_of_pos hL] using hbase

lemma mangoldt_adjoint_finset_indicator_sum_square
    (F : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (c : ENNReal) :
    (∑ i ∈ F, if p i then c else 0) ^ (2 : ℕ) =
      ∑ i ∈ F, ∑ j ∈ F, if p i ∧ p j then c ^ (2 : ℕ) else 0 := by
  classical
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hpi : p i <;> by_cases hpj : p j <;> simp [hpi, hpj, pow_two]

lemma mangoldt_adjoint_log_normalization_second_moment_cancel
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) :
    ((ENNReal.ofReal L)⁻¹) ^ (2 : ℕ) * ENNReal.ofReal (C * L ^ 2) =
      ENNReal.ofReal C := by
  let a : ENNReal := ENNReal.ofReal L
  have ha0 : a ≠ 0 := by
    simpa [a] using (ENNReal.ofReal_ne_zero_iff.mpr hL)
  have hatop : a ≠ ⊤ := by
    simp [a]
  have hcancel : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha0 hatop
  have hL2 : ENNReal.ofReal (L ^ 2) = a ^ (2 : ℕ) := by
    simp [a, pow_two, ENNReal.ofReal_mul hL.le]
  rw [ENNReal.ofReal_mul hC, hL2]
  rw [pow_two, pow_two]
  calc
    a⁻¹ * a⁻¹ * (ENNReal.ofReal C * (a * a)) =
        ENNReal.ofReal C * ((a⁻¹ * a) * (a⁻¹ * a)) := by
      ac_rfl
    _ = ENNReal.ofReal C := by
      simp [hcancel]

lemma mangoldt_adjoint_hit_index_count_finite_sum_from_chain
    {Ω : Type} {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω))
    (A : Set ℕ) (x : ℝ) (ω : Ω)
    [DecidablePred (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x)] :
    ({i : ℕ | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} : Set ℕ).ncard =
      (∑ i ∈ Finset.range (⌊x⌋₊ + 1),
        if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℕ) else 0) := by
  classical
  let S : Set ℕ := {i : ℕ | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x}
  let F : Finset ℕ := Finset.range (⌊x⌋₊ + 1)
  have hindex : ∀ i : ℕ, path ω i ∈ A -> (path ω i : ℝ) ≤ x -> i ≤ ⌊x⌋₊ := by
    intro i hiA hix
    apply Nat.le_floor
    have hi_le_path_nat : i ≤ path ω i := by
      exact Nat.le_trans (Nat.le_add_right i (path ω 0))
        (by simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 i 0)
    have hi_le_path_real : (i : ℝ) ≤ (path ω i : ℝ) := by
      exact_mod_cast hi_le_path_nat
    exact hi_le_path_real.trans hix
  have hsubset : S ⊆ (F : Set ℕ) := by
    intro i hi
    simpa [F, Finset.mem_range, Nat.lt_succ_iff] using hindex i hi.1 hi.2
  have hfin : S.Finite := F.finite_toSet.subset hsubset
  have hto : hfin.toFinset = F.filter (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x) := by
    ext i
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro hiS
      exact ⟨hsubset hiS, hiS⟩
    · intro hi
      exact hi.2
  calc
    S.ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card S hfin
    _ = (F.filter (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x)).card := by
      rw [hto]
    _ = ∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℕ) else 0 := by
      simp

lemma mangoldt_adjoint_hit_index_finite_from_chain
    {Ω : Type} {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω)) :
    ∀ (A : Set ℕ) (x : ℝ) (ω : Ω),
      ({i : ℕ | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} : Set ℕ).Finite := by
  intro A x ω
  refine (Set.finite_le_nat ⌊x⌋₊).subset ?_
  intro i hi
  change i ≤ ⌊x⌋₊
  apply Nat.le_floor
  have hi_le_path_nat : i ≤ path ω i := by
    exact Nat.le_trans (Nat.le_add_right i (path ω 0))
      (by simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 i 0)
  have hi_le_path_real : (i : ℝ) ≤ (path ω i : ℝ) := by
    exact_mod_cast hi_le_path_nat
  exact hi_le_path_real.trans hi.2

lemma mangoldt_adjoint_normalized_hit_count_aemeasurable_from_coordinates
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω))
    (hmeas : ∀ k : ℕ, Measurable fun ω : Ω => path ω k) :
    ∀ (A : Set ℕ) (x : ℝ),
      AEMeasurable
        (fun ω : Ω => ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) μ := by
  classical
  intro A x
  let F : Finset ℕ := Finset.range (⌊x⌋₊ + 1)
  have hhit_meas : ∀ i : ℕ,
      MeasurableSet {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} := by
    intro i
    exact MeasurableSet.preimage
      (by simp : MeasurableSet {n : ℕ | n ∈ A ∧ (n : ℝ) ≤ x}) (hmeas i)
  have hfun :
      (fun ω : Ω => ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) =
        fun ω : Ω =>
          ENNReal.ofReal
            ((∑ i ∈ F,
              if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℝ) else 0) /
                Real.log (Real.log x)) := by
    funext ω
    unfold mangoldt_adjoint_normalized_hit_count chain_hits_count_up_to
    rw [mangoldt_adjoint_hit_index_count_finite_sum_from_chain hchain A x ω]
    congr 1
    norm_cast
  rw [hfun]
  have hsum :
      AEMeasurable
        (fun ω : Ω =>
          ∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℝ) else 0) μ := by
    exact Finset.aemeasurable_fun_sum _ fun i _ =>
      (Measurable.ite (hhit_meas i) measurable_const measurable_const).aemeasurable
  exact (hsum.div_const (Real.log (Real.log x))).ennreal_ofReal

lemma mangoldt_adjoint_normalized_hit_first_integral_from_chain
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω))
    (hmeas : ∀ k : ℕ, Measurable fun ω : Ω => path ω k) :
    ∀ (A : Set ℕ) (x : ℝ), 0 < Real.log (Real.log x) ->
      (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ).toReal =
        ENNReal.toReal (∑' k : ℕ,
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) /
          Real.log (Real.log x) := by
  classical
  intro A x hx
  let F : Finset ℕ := Finset.range (⌊x⌋₊ + 1)
  let c : ENNReal := (ENNReal.ofReal (Real.log (Real.log x)))⁻¹
  have hhit_meas : ∀ i : ℕ,
      MeasurableSet {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} := by
    intro i
    exact (MeasurableSet.preimage
      (by simp : MeasurableSet {n : ℕ | n ∈ A ∧ (n : ℝ) ≤ x}) (hmeas i))
  have hterm_integral : ∀ (i : ℕ),
      (∫⁻ ω,
        (if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0) ∂μ) =
        c * μ {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} := by
    intro i
    simpa [Set.indicator] using
      MeasureTheory.lintegral_indicator_const (μ := μ) (hhit_meas i) c
  have hfun :
      (fun ω : Ω => ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) =
        fun ω : Ω => ∑ i ∈ F,
          if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0 := by
    funext ω
    unfold mangoldt_adjoint_normalized_hit_count chain_hits_count_up_to
    rw [mangoldt_adjoint_hit_index_count_finite_sum_from_chain hchain A x ω]
    change ENNReal.ofReal
        (((∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℕ) else 0 : ℕ) : ℝ) /
          Real.log (Real.log x)) =
      ∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0
    simpa [c] using mangoldt_adjoint_of_real_normalized_finset_count F
      (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x) hx
  have htsum :
      (∑' k : ℕ, μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) =
        ∑ k ∈ F, μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} := by
    refine tsum_eq_sum (s := F) ?_
    intro k hk
    have hempty : {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x} = ∅ := by
      ext ω
      constructor
      · intro hω
        have hk_le : k ≤ ⌊x⌋₊ := by
          apply Nat.le_floor
          have hk_le_path_nat : k ≤ path ω k := by
            exact Nat.le_trans (Nat.le_add_right k (path ω 0))
              (by simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 k 0)
          have hk_le_path_real : (k : ℝ) ≤ (path ω k : ℝ) := by
            exact_mod_cast hk_le_path_nat
          exact hk_le_path_real.trans hω.2
        have hkF : k ∈ F := by
          simpa [F, Finset.mem_range, Nat.lt_succ_iff] using hk_le
        exact False.elim (hk hkF)
      · intro h
        cases h
    simp [hempty]
  calc
    (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ).toReal =
        (∫⁻ ω, (∑ i ∈ F,
          if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0) ∂μ).toReal := by
      rw [hfun]
    _ = (∑ i ∈ F, c * μ {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x}).toReal := by
      rw [MeasureTheory.lintegral_finsetSum']
      · simp [hterm_integral, c]
      · intro i hi
        exact (Measurable.ite (hhit_meas i) measurable_const measurable_const).aemeasurable
    _ = (c * (∑ i ∈ F, μ {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x})).toReal := by
      rw [Finset.mul_sum]
    _ = (c * (∑' k : ℕ, μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x})).toReal := by
      rw [htsum]
    _ = ENNReal.toReal (∑' k : ℕ,
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) /
          Real.log (Real.log x) := by
      simp [c, hx.le, div_eq_mul_inv, mul_comm]

lemma mangoldt_adjoint_normalized_hit_second_integral_bound_from_chain
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ}
    (hchain : ∀ ω : Ω, strictly_increasing_divisibility_chain (path ω))
    (hmeas : ∀ k : ℕ, Measurable fun ω : Ω => path ω k) :
    ∀ (A : Set ℕ) (x C : ℝ), 0 ≤ C ->
      0 < Real.log (Real.log x) ->
        mangoldt_adjoint_hit_second_moment μ path A x ≤
          ENNReal.ofReal (C * (Real.log (Real.log x)) ^ 2) ->
          ∫⁻ ω,
            ((ENNReal.ofReal
              (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) ∂μ ≤
            ENNReal.ofReal C := by
  classical
  intro A x C hC hx hbound
  let F : Finset ℕ := Finset.range (⌊x⌋₊ + 1)
  let c : ENNReal := (ENNReal.ofReal (Real.log (Real.log x)))⁻¹
  have hhit_meas : ∀ i : ℕ,
      MeasurableSet {ω : Ω | path ω i ∈ A ∧ (path ω i : ℝ) ≤ x} := by
    intro i
    exact (MeasurableSet.preimage
      (by simp : MeasurableSet {n : ℕ | n ∈ A ∧ (n : ℝ) ≤ x}) (hmeas i))
  have hpair_meas : ∀ (i j : ℕ),
      MeasurableSet {ω : Ω |
        path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
          path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
    intro i j
    simpa [Set.inter_def, and_assoc] using (hhit_meas i).inter (hhit_meas j)
  have hpair_integral : ∀ (i j : ℕ),
      (∫⁻ ω,
        (if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
            path ω j ∈ A ∧ (path ω j : ℝ) ≤ x then c ^ (2 : ℕ) else 0) ∂μ) =
        c ^ (2 : ℕ) * μ {ω : Ω |
          path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
            path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
    intro i j
    simpa [Set.indicator] using
      MeasureTheory.lintegral_indicator_const (μ := μ) (hpair_meas i j) (c ^ (2 : ℕ))
  have hfun :
      (fun ω : Ω => ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) =
        fun ω : Ω => ∑ i ∈ F,
          if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0 := by
    funext ω
    unfold mangoldt_adjoint_normalized_hit_count chain_hits_count_up_to
    rw [mangoldt_adjoint_hit_index_count_finite_sum_from_chain hchain A x ω]
    change ENNReal.ofReal
        (((∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then (1 : ℕ) else 0 : ℕ) : ℝ) /
          Real.log (Real.log x)) =
      ∑ i ∈ F, if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x then c else 0
    simpa [c] using mangoldt_adjoint_of_real_normalized_finset_count F
      (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x) hx
  have hsqfun :
      (fun ω : Ω =>
        (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) =
        fun ω : Ω => ∑ i ∈ F, ∑ j ∈ F,
          if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
              path ω j ∈ A ∧ (path ω j : ℝ) ≤ x then c ^ (2 : ℕ) else 0 := by
    funext ω
    rw [congrFun hfun ω]
    simpa [and_assoc] using
      mangoldt_adjoint_finset_indicator_sum_square F
        (fun i => path ω i ∈ A ∧ (path ω i : ℝ) ≤ x) c
  have hinner_tsum : ∀ i : ℕ,
      (∑' j : ℕ, μ {ω : Ω |
        path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
          path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}) =
        ∑ j ∈ F, μ {ω : Ω |
          path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
            path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
    intro i
    refine tsum_eq_sum (s := F) ?_
    intro j hj
    have hempty : {ω : Ω |
        path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
          path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} = ∅ := by
      ext ω
      constructor
      · intro hω
        have hj_le : j ≤ ⌊x⌋₊ := by
          apply Nat.le_floor
          have hj_le_path_nat : j ≤ path ω j := by
            exact Nat.le_trans (Nat.le_add_right j (path ω 0))
              (by simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 j 0)
          have hj_le_path_real : (j : ℝ) ≤ (path ω j : ℝ) := by
            exact_mod_cast hj_le_path_nat
          exact hj_le_path_real.trans hω.2.2.2
        have hjF : j ∈ F := by
          simpa [F, Finset.mem_range, Nat.lt_succ_iff] using hj_le
        exact False.elim (hj hjF)
      · intro h
        cases h
    simp [hempty]
  have houter_tsum :
      (∑' i : ℕ, ∑' j : ℕ, μ {ω : Ω |
        path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
          path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}) =
        ∑ i ∈ F, ∑' j : ℕ, μ {ω : Ω |
          path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
            path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
    refine tsum_eq_sum (s := F) ?_
    intro i hi
    rw [ENNReal.tsum_eq_zero]
    intro j
    have hempty : {ω : Ω |
        path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
          path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} = ∅ := by
      ext ω
      constructor
      · intro hω
        have hi_le : i ≤ ⌊x⌋₊ := by
          apply Nat.le_floor
          have hi_le_path_nat : i ≤ path ω i := by
            exact Nat.le_trans (Nat.le_add_right i (path ω 0))
              (by simpa [Nat.add_comm] using StrictMono.add_le_nat (hchain ω).1 i 0)
          have hi_le_path_real : (i : ℝ) ≤ (path ω i : ℝ) := by
            exact_mod_cast hi_le_path_nat
          exact hi_le_path_real.trans hω.2.1
        have hiF : i ∈ F := by
          simpa [F, Finset.mem_range, Nat.lt_succ_iff] using hi_le
        exact False.elim (hi hiF)
      · intro h
        cases h
    simp [hempty]
  have hmoment_finite :
      mangoldt_adjoint_hit_second_moment μ path A x =
        ∑ i ∈ F, ∑ j ∈ F, μ {ω : Ω |
          path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
            path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
    unfold mangoldt_adjoint_hit_second_moment
    rw [houter_tsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hinner_tsum i]
  have hlin_eq :
      (∫⁻ ω,
        ((ENNReal.ofReal
          (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) ∂μ) =
        c ^ (2 : ℕ) *
          (∑ i ∈ F, ∑ j ∈ F, μ {ω : Ω |
            path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
              path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}) := by
    calc
      (∫⁻ ω,
        ((ENNReal.ofReal
          (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) ∂μ) =
          ∫⁻ ω, (∑ i ∈ F, ∑ j ∈ F,
            if path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
                path ω j ∈ A ∧ (path ω j : ℝ) ≤ x then c ^ (2 : ℕ) else 0) ∂μ := by
        rw [hsqfun]
      _ = ∑ i ∈ F, ∑ j ∈ F,
            c ^ (2 : ℕ) * μ {ω : Ω |
              path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
                path ω j ∈ A ∧ (path ω j : ℝ) ≤ x} := by
        rw [MeasureTheory.lintegral_finsetSum']
        · apply Finset.sum_congr rfl
          intro i hi
          rw [MeasureTheory.lintegral_finsetSum']
          · simp [hpair_integral, c]
          · intro j hj
            exact (Measurable.ite (hpair_meas i j) measurable_const measurable_const).aemeasurable
        · intro i hi
          exact Finset.aemeasurable_fun_sum _ (fun j hj =>
            (Measurable.ite (hpair_meas i j) measurable_const measurable_const).aemeasurable)
      _ = c ^ (2 : ℕ) *
          (∑ i ∈ F, ∑ j ∈ F, μ {ω : Ω |
            path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
              path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}) := by
        simp [Finset.mul_sum]
  calc
    (∫⁻ ω,
      ((ENNReal.ofReal
        (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) ∂μ) =
        c ^ (2 : ℕ) *
          (∑ i ∈ F, ∑ j ∈ F, μ {ω : Ω |
            path ω i ∈ A ∧ (path ω i : ℝ) ≤ x ∧
              path ω j ∈ A ∧ (path ω j : ℝ) ≤ x}) := hlin_eq
    _ = c ^ (2 : ℕ) * mangoldt_adjoint_hit_second_moment μ path A x := by
      rw [hmoment_finite]
    _ ≤ c ^ (2 : ℕ) * ENNReal.ofReal (C * (Real.log (Real.log x)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hbound zero_le
    _ = ENNReal.ofReal C := by
      simpa [c] using mangoldt_adjoint_log_normalization_second_moment_cancel hC hx

/-- From a bounded real-valued function on `Filter.atTop`, extract a sequence
converging to its limsup. -/
lemma exists_seq_tendsto_limsup (u : ℝ → ℝ)
    (hc : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u)
    (hb : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u) :
    ∃ (v : ℕ → ℝ),
      Filter.Tendsto (u ∘ v) Filter.atTop (nhds (Filter.limsup u Filter.atTop)) ∧
      Filter.Tendsto v Filter.atTop Filter.atTop := by
  set L := Filter.limsup u Filter.atTop
  have hfreq : ∀ n : ℕ, ∃ x : ℝ, (n : ℝ) ≤ x ∧ L - 1 / ((n : ℝ) + 1) < u x ∧
      u x < L + 1 / ((n : ℝ) + 1) := by
    intro n
    have heps : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hf1 := Filter.frequently_lt_of_lt_limsup hc (show L - 1 / ((n : ℝ) + 1) < L by linarith)
    have hf2 := Filter.eventually_lt_of_limsup_lt (show L < L + 1 / ((n : ℝ) + 1) by linarith) hb
    rw [Filter.frequently_atTop] at hf1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hf2
    obtain ⟨x, hxn, hx1⟩ := hf1 (max n N)
    exact ⟨x, le_trans (le_max_left _ _) hxn, hx1, hN x (le_trans (le_max_right _ _) hxn)⟩
  choose v hv_ge hv_lower hv_upper using hfreq
  refine ⟨v, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith [div_pos one_pos hε]
    refine ⟨N, fun n hn => ?_⟩
    simp only [Function.comp_apply, Real.dist_eq]
    have hbound : |u (v n) - L| < 1 / ((n : ℝ) + 1) := by
      rw [abs_lt]; exact ⟨by linarith [hv_lower n], by linarith [hv_upper n]⟩
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      calc 1 / ((N : ℝ) + 1) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hN_pos (by linarith)
        _ < ε := by rw [one_div, inv_lt_comm₀ hN_pos hε]; rwa [one_div] at hN
    linarith
  · exact Filter.tendsto_atTop_atTop.mpr (fun b => by
      obtain ⟨N, hN⟩ := exists_nat_ge b
      exact ⟨N, fun n hn => le_trans hN (le_trans (Nat.cast_le.mpr hn) (hv_ge n))⟩)

/-
Converting between real-valued limsup and ENNReal limsup under a bound.
-/
lemma ENNReal.ofReal_limsup_toReal {f : Filter ℕ} {u : ℕ → ENNReal} {C : NNReal}
    (hbound : ∀ᶠ n in f, u n ≤ C) :
    ENNReal.ofReal (Filter.limsup (fun n => (u n).toReal) f) = Filter.limsup u f := by
  refine le_antisymm ?_ ?_
  · by_cases hfbot : f = ⊥
    · subst f
      simp only [Filter.limsup_eq, Filter.eventually_bot, Set.setOf_true]
      have hreal_univ : ¬ BddBelow (Set.univ : Set ℝ) := by
        rintro ⟨a, ha⟩
        have := ha (show a - 1 ∈ (Set.univ : Set ℝ) from trivial)
        linarith
      rw [csInf_of_not_bddBelow hreal_univ]
      simp
    · rw [Filter.limsup_eq, Filter.limsup_eq]
      refine le_sInf ?_
      intro b hb
      by_cases hbtop : b = ⊤
      · rw [hbtop]
        exact le_top
      · rw [ENNReal.ofReal_le_iff_le_toReal hbtop]
        refine csInf_le ?_ ?_
        · refine ⟨0, ?_⟩
          intro x hx
          rcases f.eq_or_neBot with hf_eq | hne
          · exact False.elim (hfbot hf_eq)
          · haveI : Filter.NeBot f := hne
            rcases hx.exists with ⟨n, hn⟩
            exact ENNReal.toReal_nonneg.trans hn
        · filter_upwards [hb] with n hn
          exact ENNReal.toReal_mono hbtop hn
  · rw [Filter.limsup_eq, Filter.limsup_eq]
    refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
    rcases ENNReal.lt_iff_exists_real_btwn.mp hx with ⟨y, hy⟩
    refine le_trans ?_ hy.2.2.le
    refine sInf_le ?_
    have hreal_event : ∀ᶠ n in f, (u n).toReal ≤ y := by
      have hy_pos : 0 < y := hy.1.lt_of_ne' fun h => by
        norm_num [h] at hy
      have hreal_lt :
          sInf {a : ℝ | ∀ᶠ n in f, (u n).toReal ≤ a} < y :=
        (ENNReal.ofReal_lt_ofReal_iff hy_pos).mp hy.2.1
      have hnonempty :
          {a : ℝ | ∀ᶠ n in f, (u n).toReal ≤ a}.Nonempty := by
        refine ⟨(C : ℝ), ?_⟩
        exact hbound.mono fun n hn => by
          simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hn
      rcases exists_lt_of_csInf_lt hnonempty hreal_lt with ⟨a, ha_event, hay⟩
      exact ha_event.mono fun n hn => le_trans hn hay.le
    filter_upwards [hbound, hreal_event] with n hn_bound hn_real
    exact
      (ENNReal.le_ofReal_iff_toReal_le
        (ne_top_of_le_ne_top ENNReal.coe_ne_top hn_bound) hy.1).2 hn_real

/-- If `h` tends from `f` to `g`, then `limsup (u ∘ h) f ≤ limsup u g`. -/
lemma Filter.Tendsto.limsup_comp_le_limsup {α β γ : Type*} [ConditionallyCompleteLattice γ]
    {f : Filter α} {g : Filter β} {h : α → β} (ht : Filter.Tendsto h f g)
    {u : β → γ} (hf : Filter.IsCoboundedUnder (· ≤ ·) f (u ∘ h) := by isBoundedDefault)
    (hg : Filter.IsBoundedUnder (· ≤ ·) g u := by isBoundedDefault) :
    Filter.limsup (u ∘ h) f ≤ Filter.limsup u g := by
  rw [Filter.limsup_comp]
  exact Filter.limsup_le_limsup_of_le ht hf hg

lemma mangoldt_adjoint_hit_count_moment_bridge_from_first_second
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    μ Set.univ = 1 ->
      (∀ ω : Ω, strictly_increasing_divisibility_chain (path ω)) ->
        (∀ k : ℕ, Measurable fun ω : Ω => path ω k) ->
          mangoldt_adjoint_normalized_hit_expectation_limsup μ path ->
            mangoldt_adjoint_second_moment_bound μ path ->
              mangoldt_adjoint_hit_count_moment_bridge μ path := by
  classical
  intro hμ hchain hmeas hfirst hsecond
  have hfirst_integral : ∀ (A : Set ℕ) (x : ℝ), 0 < Real.log (Real.log x) ->
      (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ).toReal =
        ENNReal.toReal (∑' k : ℕ,
          μ {ω : Ω | path ω k ∈ A ∧ (path ω k : ℝ) ≤ x}) /
          Real.log (Real.log x) :=
    mangoldt_adjoint_normalized_hit_first_integral_from_chain hchain hmeas
  have hsecond_integral : ∀ (A : Set ℕ) (x C : ℝ), 0 ≤ C ->
      0 < Real.log (Real.log x) ->
        mangoldt_adjoint_hit_second_moment μ path A x ≤
          ENNReal.ofReal (C * (Real.log (Real.log x)) ^ 2) ->
          ∫⁻ ω,
            ((ENNReal.ofReal
              (mangoldt_adjoint_normalized_hit_count path A x ω)) ^ (2 : ℕ)) ∂μ ≤
            ENNReal.ofReal C :=
    mangoldt_adjoint_normalized_hit_second_integral_bound_from_chain hchain hmeas
  unfold mangoldt_adjoint_hit_count_moment_bridge
  intro A hA
  rcases hsecond A with ⟨C, hC, hCevent⟩
  let g : ℝ → ℝ := fun x =>
    (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ).toReal
  have hlimsup_g : Filter.limsup g Filter.atTop = mangoldt_weight_upper_density A := by
    rw [← hfirst A]
    apply Filter.limsup_congr
    filter_upwards [hCevent] with x hx
    exact hfirst_integral A x hx.1
  have hcobound : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop g := by
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun x => ENNReal.toReal_nonneg)
  have hpoint_le_square :
      ∀ y : ℝ, 0 ≤ y -> ENNReal.ofReal y ≤ (ENNReal.ofReal y) ^ (2 : ℕ) + 1 := by
    intro y hy
    have hreal : y ≤ y ^ 2 + 1 := by
      nlinarith [sq_nonneg y, sq_nonneg (y - 1)]
    simpa [pow_two, ENNReal.ofReal_mul, ENNReal.ofReal_add, hy, mul_nonneg hy hy]
      using ENNReal.ofReal_le_ofReal hreal
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop g := by
    refine ⟨C + 1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hCevent] with x hx
    have hsq := hsecond_integral A x C hC hx.1 hx.2
    have hlin : (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ) ≤
        ENNReal.ofReal (C + 1) := by
      calc
        (∫⁻ ω, ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω) ∂μ) ≤
            ∫⁻ ω,
              (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) ^
                (2 : ℕ) + 1 ∂μ := by
          apply MeasureTheory.lintegral_mono
          intro ω
          apply hpoint_le_square
          unfold mangoldt_adjoint_normalized_hit_count chain_hits_count_up_to
          exact div_nonneg (Nat.cast_nonneg _) hx.1.le
        _ = (∫⁻ ω,
              (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A x ω)) ^
                (2 : ℕ) ∂μ) + μ Set.univ := by
          rw [MeasureTheory.lintegral_add_left']
          · simp
          · exact
              (mangoldt_adjoint_normalized_hit_count_aemeasurable_from_coordinates
                hchain hmeas A x).pow_const (2 : ℕ)
        _ ≤ ENNReal.ofReal C + 1 := by
          rw [hμ]
          exact add_le_add hsq le_rfl
        _ = ENNReal.ofReal (C + 1) := by
          rw [ENNReal.ofReal_add hC zero_le_one]
          norm_num
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hlin
  obtain ⟨u, hgu, hu⟩ := exists_seq_tendsto_limsup (u := g)
    (hc := hcobound) (hb := hbdd)
  have hgu_density :
      Filter.Tendsto (g ∘ u) Filter.atTop (nhds (mangoldt_weight_upper_density A)) := by
    simpa [hlimsup_g] using hgu
  have hgood_event : ∀ᶠ x in Filter.atTop,
      2 ≤ x ∧ 0 < Real.log (Real.log x) ∧
        mangoldt_adjoint_hit_second_moment μ path A x ≤
          ENNReal.ofReal (C * (Real.log (Real.log x)) ^ 2) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hCevent] with x hx2 hxC
    exact ⟨hx2, hxC.1, hxC.2⟩
  have hgood_u : ∀ᶠ n in Filter.atTop,
      2 ≤ u n ∧ 0 < Real.log (Real.log (u n)) ∧
        mangoldt_adjoint_hit_second_moment μ path A (u n) ≤
          ENNReal.ofReal (C * (Real.log (Real.log (u n))) ^ 2) := hu hgood_event
  rcases (Filter.eventually_atTop.1 hgood_u) with ⟨N, hN⟩
  let xseq : ℕ → ℝ := fun j => u (j + N)
  refine ⟨xseq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hu.comp (Filter.tendsto_add_atTop_nat N)
  · intro j
    have hgood := hN (j + N) (by omega)
    exact ⟨hgood.1, hgood.2.1⟩
  · intro j
    exact Filter.Eventually.of_forall (fun ω =>
      mangoldt_adjoint_hit_index_finite_from_chain hchain A (xseq j) ω)
  · intro j
    exact mangoldt_adjoint_normalized_hit_count_aemeasurable_from_coordinates
      hchain hmeas A (xseq j)
  · have hseq_tendsto : Filter.Tendsto (fun j => g (u (j + N))) Filter.atTop
        (nhds (mangoldt_weight_upper_density A)) := by
      exact hgu_density.comp (Filter.tendsto_add_atTop_nat N)
    simpa [g, xseq] using hseq_tendsto.limsup_eq
  · refine ⟨C, hC, ?_⟩
    intro j
    have hgood := hN (j + N) (by omega)
    exact hsecond_integral A (xseq j) C hC hgood.2.1 hgood.2.2

abbrev mangoldt_adjoint_reverse_fatou_uniform_integrability_bridge
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (path : Ω → ℕ → ℕ) : Prop :=
  μ Set.univ = 1 ->
    (∀ k : ℕ, Measurable fun ω : Ω => path ω k) ->
      mangoldt_adjoint_hit_count_moment_bridge μ path ->
        mangoldt_adjoint_reverse_fatou_extraction_principle μ path

lemma mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_reverse_fatou_uniform_integrability_bridge μ path := by
  intro hμ hmeas hbridge A hA
  classical
  haveI : MeasureTheory.IsProbabilityMeasure μ := ⟨hμ⟩
  rcases hbridge A hA with
    ⟨xseq, hxseq_tendsto, hxseq_pos, hfinite, hf_meas, hlim, C, hC_nonneg, hC⟩
  let U : ℕ → ENNReal := fun j : ℕ =>
    ∫⁻ ω,
      ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω) ∂μ
  let F : Ω → ENNReal := fun ω : Ω =>
    Filter.limsup
      (fun j : ℕ => ENNReal.ofReal
        (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
      Filter.atTop
  let Y : ENNReal := ∫⁻ ω, F ω ∂μ
  have hnonneg : ∀ j : ℕ, ∀ ω : Ω,
      0 ≤ mangoldt_adjoint_normalized_hit_count path A (xseq j) ω := by
    intro j ω
    rw [mangoldt_adjoint_normalized_hit_count]
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hxseq_pos j).2)
  have htail_real : ∀ R y : ℝ, 0 < R -> 0 ≤ y ->
      y ≤ min y R + y ^ 2 / R := by
    intro R y hR hy
    by_cases hyR : y ≤ R
    · rw [min_eq_left hyR]
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg y) (le_of_lt hR))
    · have hRy : R ≤ y := le_of_not_ge hyR
      rw [min_eq_right hRy]
      have hdiv : y ≤ y ^ 2 / R := by
        rw [le_div_iff₀ hR]
        nlinarith
      exact hdiv.trans (le_add_of_nonneg_left (le_of_lt hR))
  have htail_enn : ∀ R y : ℝ, 0 < R -> 0 ≤ y ->
      ENNReal.ofReal y ≤
        min (ENNReal.ofReal y) (ENNReal.ofReal R) +
          (ENNReal.ofReal R)⁻¹ * (ENNReal.ofReal y) ^ (2 : ℕ) := by
    intro R y hR hy
    calc
      ENNReal.ofReal y ≤ ENNReal.ofReal (min y R + y ^ 2 / R) :=
        ENNReal.ofReal_le_ofReal (htail_real R y hR hy)
      _ = min (ENNReal.ofReal y) (ENNReal.ofReal R) +
            (ENNReal.ofReal R)⁻¹ * (ENNReal.ofReal y) ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_add (le_min hy (le_of_lt hR))
          (div_nonneg (sq_nonneg y) (le_of_lt hR))]
        rw [ENNReal.ofReal_min, ENNReal.ofReal_div_of_pos hR, ENNReal.ofReal_pow hy]
        rw [div_eq_mul_inv, mul_comm]
  have h_integral_tail : ∀ (N j : ℕ),
      U j ≤
        ∫⁻ (ω : Ω),
          min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ +
          (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ *
            ∫⁻ (ω : Ω),
              (ENNReal.ofReal
                (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ) ∂μ := by
    intro N j
    have hRpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    calc
      U j =
          ∫⁻ (ω : Ω),
            ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω) ∂μ := rfl
      _ ≤ ∫⁻ (ω : Ω),
            min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
              (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) +
            (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ *
              (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^
                (2 : ℕ) ∂μ := by
        refine MeasureTheory.lintegral_mono fun ω => ?_
        exact htail_enn _ _ hRpos (hnonneg j ω)
      _ = ∫⁻ (ω : Ω),
            min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
              (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ +
          ∫⁻ (ω : Ω),
            (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ *
              (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^
                (2 : ℕ) ∂μ := by
        rw [MeasureTheory.lintegral_add_left']
        exact (hf_meas j).min aemeasurable_const
      _ = ∫⁻ (ω : Ω),
            min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
              (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ +
          (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ *
            ∫⁻ (ω : Ω),
              (ENNReal.ofReal
                (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ) ∂μ := by
        rw [MeasureTheory.lintegral_const_mul'']
        exact (hf_meas j).pow_const (2 : ℕ)
  have htrunc_rev : ∀ N : ℕ,
      Filter.limsup
        (fun j : ℕ => ∫⁻ (ω : Ω),
          min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ)
        Filter.atTop ≤ Y := by
    intro N
    let R : ENNReal := ENNReal.ofReal ((N + 1 : ℕ) : ℝ)
    let fmin : ℕ → Ω → ENNReal := fun j ω =>
      min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) R
    have hfmin : ∀ j : ℕ, AEMeasurable (fmin j) μ := by
      intro j
      exact (hf_meas j).min aemeasurable_const
    let fmk : ℕ → Ω → ENNReal := fun j => (hfmin j).mk (fmin j)
    have hfmk_meas : ∀ j : ℕ, Measurable (fmk j) := by
      intro j
      exact (hfmin j).measurable_mk
    have hbound : ∀ j : ℕ, fmk j ≤ᵐ[μ] fun _ : Ω => R := by
      intro j
      filter_upwards [(hfmin j).ae_eq_mk] with ω hω
      change (hfmin j).mk (fmin j) ω ≤ R
      rw [← hω]
      exact min_le_right _ _
    have hfin : (∫⁻ _ : Ω, R ∂μ) ≠ (⊤ : ENNReal) := by
      simp [R]
    have hrev := MeasureTheory.limsup_lintegral_le (μ := μ) (f := fmk)
      (g := fun _ : Ω => R) hfmk_meas hbound hfin
    have hleft :
        Filter.limsup (fun j : ℕ => ∫⁻ (ω : Ω), fmin j ω ∂μ) Filter.atTop =
          Filter.limsup (fun j : ℕ => ∫⁻ (ω : Ω), fmk j ω ∂μ) Filter.atTop := by
      refine Filter.limsup_congr ?_
      exact Filter.Eventually.of_forall fun j =>
        MeasureTheory.lintegral_congr_ae ((hfmin j).ae_eq_mk)
    have hlim_eq :
        (fun ω : Ω => Filter.limsup (fun j : ℕ => fmk j ω) Filter.atTop) =ᵐ[μ]
          fun ω : Ω => Filter.limsup (fun j : ℕ => fmin j ω) Filter.atTop := by
      filter_upwards [MeasureTheory.ae_all_iff.2 (fun j => (hfmin j).ae_eq_mk)] with ω hω
      exact Filter.limsup_congr (Filter.Eventually.of_forall fun j => (hω j).symm)
    calc
      Filter.limsup (fun j : ℕ => ∫⁻ (ω : Ω),
          min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ)
          Filter.atTop =
          Filter.limsup (fun j : ℕ => ∫⁻ (ω : Ω), fmin j ω ∂μ) Filter.atTop := rfl
      _ = Filter.limsup (fun j : ℕ => ∫⁻ (ω : Ω), fmk j ω ∂μ) Filter.atTop := hleft
      _ ≤ ∫⁻ (ω : Ω), Filter.limsup (fun j : ℕ => fmk j ω) Filter.atTop ∂μ := hrev
      _ = ∫⁻ (ω : Ω), Filter.limsup (fun j : ℕ => fmin j ω) Filter.atTop ∂μ :=
        MeasureTheory.lintegral_congr_ae hlim_eq
      _ ≤ Y := by
        refine MeasureTheory.lintegral_mono fun ω => ?_
        dsimp [Y, F, fmin]
        refine Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)
        intro j
        exact min_le_left _ _
  have hinv_cast : Filter.Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ENNReal))⁻¹) Filter.atTop (nhds 0) := by
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv : Filter.Tendsto
      (fun N : ℕ => (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹) Filter.atTop (nhds 0) := by
    convert hinv_cast with N
    rw [ENNReal.ofReal_natCast]
  have htail_left : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal C *
        (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hinv (a := ENNReal.ofReal C) (Or.inr (by simp))
  have htail_tendsto : Filter.Tendsto
      (fun N : ℕ => (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹ * ENNReal.ofReal C)
      Filter.atTop (nhds 0) := by
    simpa [mul_comm] using htail_left
  have hL_le_Y : Filter.limsup U Filter.atTop ≤ Y := by
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε hYfin
    let η : NNReal := ε / 2
    have hηpos : 0 < η := by
      exact half_pos hε
    have hηsum : (η : ENNReal) + (η : ENNReal) = (ε : ENNReal) := by
      rw [← ENNReal.coe_add]
      congr
      exact add_halves ε
    have hηenn : (0 : ENNReal) < (η : ENNReal) := by
      exact_mod_cast hηpos
    have htail_event := (ENNReal.tendsto_nhds_zero.mp htail_tendsto) (η : ENNReal) hηenn
    rcases Filter.Eventually.exists htail_event with ⟨N, htailN⟩
    let V : ℕ → ENNReal := fun j : ℕ =>
      ∫⁻ (ω : Ω),
        min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
          (ENNReal.ofReal ((N + 1 : ℕ) : ℝ)) ∂μ
    have hV_bdd : Filter.IsBoundedUnder LE.le Filter.atTop V := by
      simpa [Filter.IsBoundedUnder] using
        (Filter.isBounded_le_of_top (f := Filter.map V Filter.atTop))
    have hV_limsup : Filter.limsup V Filter.atTop ≤ Y := by
      simpa [V] using htrunc_rev N
    have hY_lt_add : Y < Y + (η : ENNReal) := by
      exact ENNReal.lt_add_right (ne_of_lt hYfin) (ne_of_gt hηenn)
    have hV_event_lt : ∀ᶠ j : ℕ in Filter.atTop, V j < Y + (η : ENNReal) :=
      Filter.eventually_lt_of_limsup_lt (f := Filter.atTop) (u := V)
        (hV_limsup.trans_lt hY_lt_add) hV_bdd
    have hU_event : ∀ᶠ j : ℕ in Filter.atTop, U j ≤ Y + (ε : ENNReal) := by
      filter_upwards [hV_event_lt] with j hVj
      have hmain : U j ≤ V j +
          (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹ * ENNReal.ofReal C := by
        calc
          U j ≤ V j +
              (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹ *
                ∫⁻ (ω : Ω),
                  (ENNReal.ofReal
                    (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ) ∂μ := by
            simpa [V] using h_integral_tail N j
          _ ≤ V j +
              (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹ * ENNReal.ofReal C := by
            exact add_le_add (le_refl (V j))
              (mul_le_mul_of_nonneg_left (hC j)
                zero_le)
      calc
        U j ≤ V j + (ENNReal.ofReal (((N + 1 : ℕ) : ℝ)))⁻¹ * ENNReal.ofReal C := hmain
        _ ≤ V j + (η : ENNReal) := add_le_add (le_refl (V j)) htailN
        _ ≤ (Y + (η : ENNReal)) + (η : ENNReal) :=
          add_le_add (le_of_lt hVj) (le_refl (η : ENNReal))
        _ = Y + (ε : ENNReal) := by
          rw [add_assoc, hηsum]
    exact Filter.limsup_le_of_le (f := Filter.atTop) (u := U)
      (a := Y + (ε : ENNReal)) (h := hU_event)
  let B : NNReal := ⟨C + 2, by linarith⟩
  have hU_bound : ∀ j : ℕ, U j ≤ (B : ENNReal) := by
    intro j
    have hmin_le_one :
        (∫⁻ (ω : Ω),
          min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            (ENNReal.ofReal (((0 + 1 : ℕ) : ℝ))) ∂μ) ≤ (1 : ENNReal) := by
      calc
        (∫⁻ (ω : Ω),
          min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
            (ENNReal.ofReal (((0 + 1 : ℕ) : ℝ))) ∂μ) ≤
            ∫⁻ (_ : Ω), (1 : ENNReal) ∂μ := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          simp
        _ = (1 : ENNReal) := by
          simp
    have htailmul :
        (ENNReal.ofReal (((0 + 1 : ℕ) : ℝ)))⁻¹ *
          ∫⁻ (ω : Ω),
            (ENNReal.ofReal
              (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ) ∂μ ≤
          ENNReal.ofReal C := by
      simpa using hC j
    have hBbound : (1 : ENNReal) + ENNReal.ofReal C ≤ (B : ENNReal) := by
      calc
        (1 : ENNReal) + ENNReal.ofReal C = ENNReal.ofReal (1 + C) := by
          rw [ENNReal.ofReal_add zero_le_one hC_nonneg]
          norm_num
        _ ≤ ENNReal.ofReal (C + 2) := ENNReal.ofReal_le_ofReal (by linarith)
        _ = (B : ENNReal) := by
          change ENNReal.ofReal (B : ℝ) = (B : ENNReal)
          exact ENNReal.ofReal_coe_nnreal
    calc
      U j ≤
          (∫⁻ (ω : Ω),
            min (ENNReal.ofReal (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω))
              (ENNReal.ofReal (((0 + 1 : ℕ) : ℝ))) ∂μ) +
            (ENNReal.ofReal (((0 + 1 : ℕ) : ℝ)))⁻¹ *
              ∫⁻ (ω : Ω),
                (ENNReal.ofReal
                  (mangoldt_adjoint_normalized_hit_count path A (xseq j) ω)) ^ (2 : ℕ) ∂μ := by
        simpa using h_integral_tail 0 j
      _ ≤ (1 : ENNReal) + ENNReal.ofReal C := add_le_add hmin_le_one htailmul
      _ ≤ (B : ENNReal) := hBbound
  have hL_eq :
      ENNReal.ofReal (mangoldt_weight_upper_density A) = Filter.limsup U Filter.atTop := by
    have htmp := ENNReal.ofReal_limsup_toReal (f := Filter.atTop) (u := U) (C := B)
      (Filter.Eventually.of_forall hU_bound)
    simpa [U, hlim] using htmp
  have hY_lower : ENNReal.ofReal (mangoldt_weight_upper_density A) ≤ Y := by
    rw [hL_eq]
    exact hL_le_Y
  have hpath_limsup : ∃ ω : Ω, ENNReal.ofReal (mangoldt_weight_upper_density A) ≤ F ω := by
    by_cases hYtop : Y = (⊤ : ENNReal)
    · by_contra hnone
      have hle_point : ∀ ω : Ω, F ω ≤ ENNReal.ofReal (mangoldt_weight_upper_density A) := by
        intro ω
        by_contra hle
        have hge : ENNReal.ofReal (mangoldt_weight_upper_density A) ≤ F ω :=
          le_of_lt (not_le.mp hle)
        exact hnone ⟨ω, hge⟩
      have hYle : Y ≤ ENNReal.ofReal (mangoldt_weight_upper_density A) := by
        dsimp [Y]
        calc
          ∫⁻ (ω : Ω), F ω ∂μ ≤
              ∫⁻ (_ : Ω), ENNReal.ofReal (mangoldt_weight_upper_density A) ∂μ := by
            exact MeasureTheory.lintegral_mono fun ω => hle_point ω
          _ = ENNReal.ofReal (mangoldt_weight_upper_density A) := by
            simp
      have htop_le : (⊤ : ENNReal) ≤ ENNReal.ofReal (mangoldt_weight_upper_density A) := by
        simp [Y, hYtop] at hYle
      have hfinite_top : ENNReal.ofReal (mangoldt_weight_upper_density A) < (⊤ : ENNReal) := by
        simp
      exact (not_lt_of_ge htop_le) hfinite_top
    · have hYne : (∫⁻ (ω : Ω), F ω ∂μ) ≠ (⊤ : ENNReal) := by
        simpa [Y] using hYtop
      rcases MeasureTheory.exists_lintegral_le (μ := μ) (f := F) hYne with ⟨ω, hωY⟩
      exact ⟨ω, hY_lower.trans hωY⟩
  rcases hpath_limsup with ⟨ω, hω⟩
  refine ⟨ω, ?_⟩
  unfold chain_hits_density_at_least upper_chain_hit_density at *
  exact hω.trans (by
    simpa [F, Function.comp_def, mangoldt_adjoint_normalized_hit_count] using
      Filter.Tendsto.limsup_comp_le_limsup hxseq_tendsto
        (u := fun x : ℝ => ENNReal.ofReal
          ((chain_hits_count_up_to (path ω) A x : ℝ) / Real.log (Real.log x))))

lemma mangoldt_adjoint_second_moment_bound_from_constructed_path_data {Ω : Type}
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_constructed_path_data μ path ->
      mangoldt_adjoint_second_moment_bound μ path := by
  intro hdata
  exact mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound
    (mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data hdata)

lemma mangoldt_adjoint_reverse_fatou_extraction_principle_from_constructed_path_data
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_constructed_path_data μ path ->
      mangoldt_adjoint_second_moment_bound μ path ->
        mangoldt_adjoint_reverse_fatou_extraction_principle μ path := by
  exact fun hdata hsecond =>
    (mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability (μ := μ) (path := path))
      hdata.mass hdata.measurable
      (mangoldt_adjoint_hit_count_moment_bridge_from_first_second
        hdata.mass hdata.chain hdata.measurable
        (mangoldt_adjoint_normalized_hit_expectation_limsup_from_visit_identity hdata) hsecond)

lemma mangoldt_adjoint_constructed_path_data_from_kernel_path_data {Ω : Type}
    [MeasurableSpace Ω] {P U : ℕ → ℕ → ℝ} {μ : MeasureTheory.Measure Ω}
    {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_kernel_package P U ->
      mangoldt_adjoint_kernel_path_data U μ path ->
        mangoldt_adjoint_constructed_path_data μ path := by
  intro hpack hdata
  rcases hdata with ⟨hμ, hstart, hchain, hmeas, hsupp, hmarkov⟩
  exact ⟨hμ, hchain, hmeas,
    mangoldt_adjoint_visit_identity_from_kernel_path_data hpack
      ⟨hμ, hstart, hchain, hmeas, hsupp, hmarkov⟩⟩

lemma mangoldt_adjoint_constructed_path_data_exists :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
      (path : Ω → ℕ → ℕ), @mangoldt_adjoint_constructed_path_data Ω mΩ μ path := by
  rcases mangoldt_adjoint_kernel_path_data_exists with
    ⟨P, U, Ω, mΩ, μ, path, hpack, hdata⟩
  exact ⟨Ω, mΩ, μ, path,
    mangoldt_adjoint_constructed_path_data_from_kernel_path_data hpack hdata⟩

lemma mangoldt_adjoint_random_model_from_constructed_path_data {Ω : Type}
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_constructed_path_data μ path ->
      mangoldt_adjoint_second_moment_bound μ path ->
        mangoldt_adjoint_reverse_fatou_extraction_principle μ path ->
          mangoldt_adjoint_random_model μ path := by
  intro hdata hsecond hfatou
  exact ⟨hdata.mass, hdata.chain, hdata.measurable, hdata.visit, hsecond, hfatou⟩

lemma mangoldt_adjoint_reverse_fatou_extraction_principle_from_model {Ω : Type}
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_random_model μ path ->
      mangoldt_adjoint_reverse_fatou_extraction_principle μ path := by
  intro hmodel
  exact hmodel.reverse_fatou

lemma mangoldt_adjoint_random_model_exists :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
      (path : Ω → ℕ → ℕ), @mangoldt_adjoint_random_model Ω mΩ μ path := by
  rcases mangoldt_adjoint_constructed_path_data_exists with ⟨Ω, mΩ, μ, path, hdata⟩
  let hsecond := @mangoldt_adjoint_second_moment_bound_from_constructed_path_data
    Ω mΩ μ path hdata
  let hfatou := @mangoldt_adjoint_reverse_fatou_extraction_principle_from_constructed_path_data
    Ω mΩ μ path hdata hsecond
  exact ⟨Ω, mΩ, μ, path,
    @mangoldt_adjoint_random_model_from_constructed_path_data Ω mΩ μ path hdata hsecond hfatou⟩

lemma mangoldt_adjoint_reverse_fatou_path_extraction {Ω : Type} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_random_model μ path ->
      ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
        ∃ n : ℕ → ℕ,
          strictly_increasing_divisibility_chain n ∧
          chain_hits_density_at_least n A (mangoldt_weight_upper_density A) := by
  intro hmodel A hA
  exact Exists.elim
    (mangoldt_adjoint_reverse_fatou_extraction_principle_from_model hmodel A hA)
    (fun omega hhit =>
      Exists.intro (path omega) (And.intro (hmodel.chain omega) hhit))

lemma mangoldt_adjoint_chain_density_selection :
    ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_hits_density_at_least n A (mangoldt_weight_upper_density A) := by
  rcases mangoldt_adjoint_random_model_exists with ⟨Ω, mΩ, μ, path, hmodel⟩
  exact @mangoldt_adjoint_reverse_fatou_path_extraction Ω mΩ μ path hmodel

lemma probabilistic_dense_ambient_chain :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_hits_density_at_least n A (upper_doubly_log_density A) := by
  intro A hA
  have hdensity : mangoldt_weight_upper_density A = upper_doubly_log_density A := by
    simpa [mangoldt_weight_upper_density] using mangoldt_weight_aggregate_comparison A
  have hpos : 0 < mangoldt_weight_upper_density A := by
    rwa [hdensity]
  rcases mangoldt_adjoint_chain_density_selection A hpos with ⟨n, hchain, hhit⟩
  exact ⟨n, hchain, by simpa [hdensity] using hhit⟩

lemma dense_hits_subchain_in_set :
    ∀ (A : Set ℕ) (ambient : ℕ → ℕ),
      0 < upper_doubly_log_density A ->
      strictly_increasing_divisibility_chain ambient ->
      chain_hits_density_at_least ambient A (upper_doubly_log_density A) ->
        ∃ n : ℕ → ℕ,
          strictly_increasing_divisibility_chain n ∧
          chain_in_set n A ∧
          upper_chain_density_at_least n (upper_doubly_log_density A) := by
  classical
  intro A ambient hApos hambient hhit
  let p : ℕ → Prop := fun i => ambient i ∈ A
  have hpinf : (setOf p).Infinite := by
    by_contra hpinf
    have hpfin : (setOf p).Finite := Set.not_infinite.mp hpinf
    have hbound : ∀ x : ℝ,
        chain_hits_count_up_to ambient A x ≤ (setOf p).ncard := by
      intro x
      have hsubset : {i : ℕ | ambient i ∈ A ∧ (ambient i : ℝ) ≤ x} ⊆ setOf p := by
        intro i hi
        exact hi.1
      simpa [chain_hits_count_up_to, p] using Set.ncard_le_ncard hsubset hpfin
    have hloglog_tendsto :
        Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have htend_real :
        Filter.Tendsto
          (fun x : ℝ => ((setOf p).ncard : ℝ) / Real.log (Real.log x))
          Filter.atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hloglog_tendsto ((setOf p).ncard : ℝ)
    have htend_bound :
        Filter.Tendsto
          (fun x : ℝ => ENNReal.ofReal
            (((setOf p).ncard : ℝ) / Real.log (Real.log x)))
          Filter.atTop (nhds 0) := by
      change Filter.Tendsto
        (ENNReal.ofReal ∘ fun x : ℝ => ((setOf p).ncard : ℝ) / Real.log (Real.log x))
        Filter.atTop (nhds 0)
      simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp htend_real
    have hlim_bound :
        Filter.limsup
            (fun x : ℝ => ENNReal.ofReal
              (((setOf p).ncard : ℝ) / Real.log (Real.log x)))
            Filter.atTop = 0 :=
      htend_bound.limsup_eq
    have heventually_le :
        ∀ᶠ x : ℝ in Filter.atTop,
          ENNReal.ofReal
              ((chain_hits_count_up_to ambient A x : ℝ) / Real.log (Real.log x)) ≤
            ENNReal.ofReal
              (((setOf p).ncard : ℝ) / Real.log (Real.log x)) := by
      filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hx
      apply ENNReal.ofReal_mono
      have hlog_gt_one : 1 < Real.log x := by
        simpa using Real.log_lt_log (Real.exp_pos 1) hx
      have hden_pos : 0 < Real.log (Real.log x) := by
        simpa using Real.log_lt_log (show (0 : ℝ) < 1 by norm_num) hlog_gt_one
      exact div_le_div_of_nonneg_right (by exact_mod_cast hbound x) (le_of_lt hden_pos)
    have hhit_zero : upper_chain_hit_density ambient A = 0 := by
      unfold upper_chain_hit_density
      exact le_antisymm
        ((Filter.limsup_le_limsup heventually_le).trans (le_of_eq hlim_bound)) bot_le
    have hpos_enn : 0 < ENNReal.ofReal (upper_doubly_log_density A) := by
      exact ENNReal.ofReal_pos.mpr hApos
    have hle_zero : ENNReal.ofReal (upper_doubly_log_density A) ≤ 0 := by
      simpa [chain_hits_density_at_least, hhit_zero] using hhit
    exact (not_lt_of_ge hle_zero) hpos_enn
  let e : ℕ → ℕ := Nat.nth p
  let n : ℕ → ℕ := fun k => ambient (e k)
  have he_strict : StrictMono e := by
    simpa [e] using Nat.nth_strictMono hpinf
  have hdvd_le : ∀ {i j : ℕ}, i ≤ j -> ambient i ∣ ambient j := by
    intro i j hij
    exact Nat.le_induction (m := i) (P := fun j _ => ambient i ∣ ambient j)
      dvd_rfl (fun j _ ih => dvd_trans ih (hambient.2 j)) j hij
  refine ⟨n, ?_, ?_, ?_⟩
  · constructor
    · simpa [n, Function.comp_def] using hambient.1.comp he_strict
    · intro i
      exact hdvd_le (le_of_lt (he_strict (Nat.lt_succ_self i)))
  · intro i
    simpa [n, e, p] using Nat.nth_mem_of_infinite hpinf i
  · have hcount : ∀ x : ℝ, chain_count_up_to n x = chain_hits_count_up_to ambient A x := by
      intro x
      have himage :
          e '' {k : ℕ | (ambient (e k) : ℝ) ≤ x} =
            {i : ℕ | p i ∧ (ambient i : ℝ) ≤ x} := by
        ext i
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact ⟨by simpa [e, p] using Nat.nth_mem_of_infinite hpinf k, hk⟩
        · intro hi
          have hi_range : i ∈ Set.range e := by
            change i ∈ Set.range (Nat.nth p)
            rw [Nat.range_nth_of_infinite hpinf]
            exact hi.1
          rcases hi_range with ⟨k, rfl⟩
          exact ⟨k, hi.2, rfl⟩
      have hinj : Function.Injective e := by
        simpa [e] using Nat.nth_injective hpinf
      have hncard :
          Set.ncard {k : ℕ | (ambient (e k) : ℝ) ≤ x} =
            Set.ncard {i : ℕ | p i ∧ (ambient i : ℝ) ≤ x} := by
        rw [← himage, Set.ncard_image_of_injective _ hinj]
      simpa [chain_count_up_to, chain_hits_count_up_to, n, p] using hncard
    have hdensity : upper_chain_density n = upper_chain_hit_density ambient A := by
      simp [upper_chain_density, upper_chain_hit_density, hcount]
    simpa [upper_chain_density_at_least, chain_hits_density_at_least, hdensity] using hhit

theorem erdos_sarkozy_szemeredi_1217 :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_in_set n A ∧
        upper_chain_density_at_least n (upper_doubly_log_density A) := by
  intro A hA
  rcases probabilistic_dense_ambient_chain A hA with ⟨ambient, hambient, hhit⟩
  exact dense_hits_subchain_in_set A ambient hA hambient hhit

/-!
## First public paper statements

The declarations below expose the first three headline results.  The later
Odd Banks--Martin, AKS, and `2`-strong aliases follow their respective proofs.
-/

theorem theorem_1196 :
    ∃ C : ℝ, erdos1196_bound C :=
  erdos_sarkozy_szemeredi_1196

theorem theorem_164 :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer :=
  erdos_primitive_set_conjecture_164

theorem theorem_1217 :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_in_set n A ∧
        upper_chain_density_at_least n (upper_doubly_log_density A) :=
  erdos_sarkozy_szemeredi_1217

/-!
## Bounded-height primitive decompositions

This formalizes the decomposition assertion in TeX Remark `GPT-rem-1`.
-/

/-- A set is `h`-primitive when it contains no strictly increasing divisibility
chain with `h + 1` elements. -/
abbrev h_primitive (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ chain : Fin (h + 1) → ℕ,
    (∀ i, chain i ∈ A) →
    (∀ i j, i < j → chain i ∣ chain j ∧ chain i ≠ chain j) →
    False

/-- A primitive set is `1`-primitive. -/
lemma primitive_set_is_one_h_primitive {A : Set ℕ} (hA : primitive_set A) :
    h_primitive A 1 := by
  intro chain hchain horder
  obtain ⟨hdvd, hne⟩ :=
    horder ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  exact hA (hchain ⟨0, by omega⟩) (hchain ⟨1, by omega⟩) hne hdvd

set_option maxHeartbeats 800000 in
-- Dependent `Fin.cons` simplification in the inductive chain argument is expensive.
/-- TeX Remark `GPT-rem-1`: an `h`-primitive set is covered by `h` primitive
sets, obtained by repeatedly removing its divisibility-minimal elements. -/
theorem h_primitive_decomposition {A : Set ℕ} {h : ℕ} (hh : 0 < h)
    (hA : h_primitive A h) :
    ∃ layers : Fin h → Set ℕ,
      (∀ i, primitive_set (layers i)) ∧ A ⊆ ⋃ i, layers i := by
  induction h generalizing A with
  | zero => contradiction
  | succ h ih =>
    by_cases hh' : 0 < h
    · set layer₀ := {n ∈ A | ∀ m ∈ A, m ∣ n → m = n} with hlayer₀_def
      obtain ⟨layers, hlayers⟩ :
          ∃ layers : Fin h → Set ℕ,
            (∀ i, primitive_set (layers i)) ∧
              A \ layer₀ ⊆ ⋃ i, layers i := by
        apply ih hh'
        intro chain hchain hchain_div
        by_contra hcontra
        obtain ⟨m, hmA, hm_div, hm_ne⟩ :
            ∃ m ∈ A, m ∣ chain 0 ∧ m ≠ chain 0 := by
          exact not_forall_not.mp fun contra =>
            (hchain 0).2
              ⟨(hchain 0).1, fun m hm hm' =>
                Classical.not_not.mp fun hmne => contra m (by tauto)⟩
        specialize hA (Fin.cons m chain)
        simp_all +decide only [forall_const, lt_add_iff_pos_left,
          Order.lt_add_one_iff, zero_le, Set.sdiff_sep_self, not_forall,
          Set.mem_setOf_eq, Fin.forall_fin_succ, ne_eq,
          not_lt_zero, Fin.cons_zero, Fin.cons_succ, implies_true, and_self,
          IsEmpty.forall_iff, true_and, Fin.succ_pos, Fin.succ_lt_succ_iff,
          Fin.succ_zero_eq_one, Fin.lt_one_iff, not_false_eq_true,
          and_true, imp_false, not_and, Decidable.not_not]
        obtain ⟨x, hx⟩ := hA
        specialize hx (dvd_trans hm_div (hchain_div.1 x).1)
        simp_all +decide only [exists_prop]
        exact hm_ne (Nat.dvd_antisymm hm_div (hchain_div.1 x).1)
      refine ⟨Fin.cons layer₀ layers, ?_, ?_⟩
      · simp_all +decide only [Set.subset_def, Set.mem_iUnion, forall_const,
          lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
          Set.sdiff_sep_self, not_forall, Set.mem_setOf_eq,
          and_imp, forall_exists_index, Fin.forall_fin_succ, Fin.cons_zero,
          Fin.cons_succ, implies_true, and_true]
        intro a ha b hb hab
        exact fun h => hab <| hb.2 a ha.1 h ▸ rfl
      · intro x hx
        by_cases hx' : x ∈ layer₀
        · exact Set.mem_iUnion.2 ⟨0, hx'⟩
        · have hxrem : x ∈ A \ layer₀ := ⟨hx, hx'⟩
          rcases Set.mem_iUnion.1 (hlayers.2 hxrem) with ⟨i, hi⟩
          exact Set.mem_iUnion.2 ⟨Fin.succ i, hi⟩
    · refine ⟨fun _ => A, ?_, ?_⟩
      · simp_all +decide only [not_isEmpty_of_nonempty, IsEmpty.forall_iff,
          IsAntichain, IsEmpty.exists_iff, ne_eq, implies_true,
          lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, not_lt,
          nonpos_iff_eq_zero, forall_const, zero_add]
        intro a ha b hb hab
        exact fun h => hab <| by
          have hbad := hA (fun i => if i = 0 then a else b)
          aesop
      · intro x hx
        exact Set.mem_iUnion.2 ⟨0, hx⟩

/-!
## Named finite-cutoff lemmas for Theorem 1196
-/

lemma lemma_1196_finite_large_primitive_bound :
    ∃ C : ℝ, erdos1196_finite_bound C :=
  finite_large_primitive_bound

lemma lemma_1196_finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C :=
  finite_truncation_principle

lemma lemma_1196_initial_mass_bound (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ ∑' n : ℕ, finite_chain_initial_mass x X n :=
  finite_chain_erdos_le_initial_mass A x X hx hprim hsupp

lemma lemma_1196_fA_bound (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ cut_capacity x X :=
  finite_chain_cut_bound A x X hx hprim hsupp

lemma lemma_1196_initial_mass_sum_eq_cut_capacity (x X : ℝ) (hx : 2 ≤ x) :
    (∑' n : ℕ, finite_chain_initial_mass x X n) = cut_capacity x X :=
  finite_chain_initial_mass_sum_eq_cut_capacity x X hx

lemma lemma_1196_cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x :=
  cut_capacity_le_tail_majorant x X hx

lemma lemma_1196_filip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x X : ℝ, 2 ≤ x -> x ≤ X ->
      cut_capacity x X ≤ 1 + C / Real.log x := by
  rcases tail_majorant_bound with ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro x X hx _hX
  exact (cut_capacity_le_tail_majorant x X hx).trans (hC_bound x hx)

/-!
## Named analytic lemmas from the paper
-/

/-- TeX equation `\eqref{vmi}`: the divisor sum of the von Mangoldt function. -/
lemma equation_vmi (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q) = Real.log (n : ℝ) :=
  von_mangoldt_divisor_sum n

/-- TeX equation `\eqref{nu-dilate}` on the nondegenerate domain of the
real-valued Erdős weight. -/
lemma equation_nu_dilate {d n : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n) :
    erdos_weight (d * n) ≤ (1 / (d : ℝ)) * erdos_weight n := by
  have hd_two_or_one : d = 1 ∨ 2 ≤ d := by omega
  rcases hd_two_or_one with rfl | hd_two
  · simp
  · have hn_ne_one : n ≠ 1 := by omega
    simpa [hn_ne_one] using mangoldt_adjoint_erdos_weight_mul_le_local d n hd_two
      (le_trans (by norm_num : 1 ≤ 2) hn)

lemma theorem_mertens_von_mangoldt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ C :=
  mertens_von_mangoldt_reciprocal

lemma theorem_mertens_prime_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t ->
      |(∑' n : ℕ, (prime_layer ∩ real_initial_segment t).indicator
          (fun p : ℕ => 1 / (p : ℝ)) n) -
        Real.log (Real.log t)| ≤ C :=
  mertens_prime_reciprocal

lemma lemma_phi_zeta_log_derivative :
    ∀ u : ℝ, 0 < u ->
      (mangoldt_dirichlet_series u : ℂ) =
        - deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ) :=
  mangoldt_dirichlet_series_eq_zeta_log_derivative

lemma lemma_phi_geometric_bound :
    ∀ u : ℝ, 0 < u ->
      mangoldt_dirichlet_series u ≤
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
  intro u hu
  have hseries :
      mangoldt_dirichlet_series u =
        ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
    simpa using congrArg Complex.re
      (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu)
  calc
    mangoldt_dirichlet_series u =
        ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := hseries
    _ ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
      zeta_log_derivative_geometric_bound u hu

lemma lemma_phi_geometric_le_inv :
    ∀ u : ℝ, 0 < u ->
      Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤ 1 / u :=
  zeta_geometric_bound_le_inv

lemma lemma_phi_upper_bound :
    ∀ u : ℝ, 0 < u -> mangoldt_dirichlet_series u ≤ 1 / u :=
  von_mangoldt_dirichlet_series_upper_bound

lemma lemma_mangoldt_tail_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      Summable (fun q : ℕ => if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ∧
        mangoldt_tail_sum m y ≤
          1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 :=
  mangoldt_tail_upper_bound

lemma lemma_mangoldt_tail_subinvariant :
    ∀ n : ℕ, 2 ≤ n -> Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤ 1 :=
  mangoldt_subinvariant_bound

lemma lemma_mangoldt_tail_prime_sharp :
    ∀ p : ℕ, p ∈ prime_layer ->
      Real.log (p : ℝ) * mangoldt_tail_sum p 2 ≤
        (Real.log (p : ℝ) / Real.log 2) /
          (Real.log (p : ℝ) / Real.log 2 + (1 / 2 : ℝ)) :=
  mangoldt_tail_sharp_prime_slack

/-!
## Named Markov-chain consequences from the paper
-/

lemma lemma_eps_modified_chain_subinvariant :
    ∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P :=
  eps_modified_chain_subinvariant

lemma lemma_eps_adjoint_hitting_mass_package_from_subinvariant :
    (∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P) ->
      ∃ P : ℕ → ℕ → ℝ,
        ∃ U : Option ℕ → Option ℕ → ℝ,
          ∃ h : ℕ → ℝ,
            eps_modified_chain_kernel_subinvariant P ∧
              eps_adjoint_kernel_package P U ∧
                eps_adjoint_hitting_mass_facts U h ∧
                  eps_adjoint_primitive_chain_antichain_facts h :=
  eps_adjoint_hitting_mass_package_from_subinvariant

lemma lemma_eps_modified_chain_hitting_mass_identity :
    (∃ P : ℕ → ℕ → ℝ, eps_modified_chain_kernel_subinvariant P) ->
      Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
        ∀ A : Set ℕ, primitive_set A ->
          Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
            erdos_sum A ≤ erdos_sum prime_layer :=
  eps_modified_chain_hitting_mass_identity

lemma lemma_eps_chain_antichain_bound :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer :=
  eps_chain_antichain_bound

lemma lemma_mangoldt_weight_density_comparison :
    ∀ A : Set ℕ, mangoldt_weight_upper_density A = upper_doubly_log_density A :=
  mangoldt_weight_aggregate_comparison

lemma lemma_mangoldt_adjoint_random_model_exists :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
      (path : Ω → ℕ → ℕ), @mangoldt_adjoint_random_model Ω mΩ μ path :=
  mangoldt_adjoint_random_model_exists

lemma lemma_mangoldt_adjoint_reverse_fatou_extraction_principle_from_model
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_random_model μ path ->
      mangoldt_adjoint_reverse_fatou_extraction_principle μ path :=
  mangoldt_adjoint_reverse_fatou_extraction_principle_from_model

lemma lemma_mangoldt_adjoint_reverse_fatou_path_extraction
    {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {path : Ω → ℕ → ℕ} :
    mangoldt_adjoint_random_model μ path ->
      ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
        ∃ n : ℕ → ℕ,
          strictly_increasing_divisibility_chain n ∧
          chain_hits_density_at_least n A (mangoldt_weight_upper_density A) :=
  mangoldt_adjoint_reverse_fatou_path_extraction

lemma lemma_mangoldt_adjoint_chain_density_selection :
    ∀ A : Set ℕ, 0 < mangoldt_weight_upper_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_hits_density_at_least n A (mangoldt_weight_upper_density A) :=
  mangoldt_adjoint_chain_density_selection

lemma lemma_probabilistic_dense_ambient_chain :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_hits_density_at_least n A (upper_doubly_log_density A) :=
  probabilistic_dense_ambient_chain

lemma lemma_dense_hits_subchain_in_set :
    ∀ (A : Set ℕ) (ambient : ℕ → ℕ),
      0 < upper_doubly_log_density A ->
      strictly_increasing_divisibility_chain ambient ->
      chain_hits_density_at_least ambient A (upper_doubly_log_density A) ->
        ∃ n : ℕ → ℕ,
          strictly_increasing_divisibility_chain n ∧
          chain_in_set n A ∧
          upper_chain_density_at_least n (upper_doubly_log_density A) :=
  dense_hits_subchain_in_set

/-- The layer `ℕ_k = {n : ℕ | Ω(n) = k}`, using Mathlib's `cardFactors`
for the number of prime factors counted with multiplicity. -/
def omega_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | ArithmeticFunction.cardFactors n = k}

/-- The upper layer `ℕ_{≥ k}`. -/
def omega_ge_layer (k : ℕ) : Set ℕ :=
  {n : ℕ | k ≤ ArithmeticFunction.cardFactors n}

/-- A layer is contained in the corresponding upper layer. -/
lemma omega_layer_subset_omega_ge_layer (k : ℕ) :
    omega_layer k ⊆ omega_ge_layer k :=
  fun _ hn => le_of_eq (Eq.symm hn)

/-- On positive integers, a fixed `Ω`-layer is an antichain in the divisibility
poset.  This is the combinatorial fact behind the terminal layer in the
Odd Banks--Martin chain. -/
lemma omega_layer_positive_primitive (k : ℕ) :
    primitive_set ({n : ℕ | 0 < n} ∩ omega_layer k) := by
  intro a ha b hb hne hdvd
  have ha_pos : 0 < a := ha.1
  have hb_pos : 0 < b := hb.1
  have hle : a ≤ b := Nat.le_of_dvd hb_pos hdvd
  have hlt : a < b := lt_of_le_of_ne hle hne
  have homega_lt :
      ArithmeticFunction.cardFactors a < ArithmeticFunction.cardFactors b :=
    mangoldt_adjoint_card_factors_strict_of_dvd_lt (Nat.ne_of_gt ha_pos) hdvd hlt
  have haOmega : ArithmeticFunction.cardFactors a = k := ha.2
  have hbOmega : ArithmeticFunction.cardFactors b = k := hb.2
  omega

/-- The subset of `A` whose prime factors all lie in `Q`. -/
def restrict_to_primes (A Q : Set ℕ) : Set ℕ :=
  {n : ℕ | n ∈ A ∧ ∀ p : ℕ, Nat.Prime p -> p ∣ n -> p ∈ Q}

/-- Restricting to a set of primes gives a subset of the original set. -/
lemma restrict_to_primes_subset_left (A Q : Set ℕ) :
    restrict_to_primes A Q ⊆ A :=
  fun _ hn => hn.1

/-- Prime restriction preserves primitivity. -/
lemma restrict_to_primes_primitive {A Q : Set ℕ} (hA : primitive_set A) :
    primitive_set (restrict_to_primes A Q) :=
  primitive_set_of_subset hA (restrict_to_primes_subset_left A Q)

/-- If `A` lies in an upper layer, then so does its prime restriction. -/
lemma restrict_to_primes_subset_omega_ge {A Q : Set ℕ} {k : ℕ}
    (hA : A ⊆ omega_ge_layer k) :
    restrict_to_primes A Q ⊆ omega_ge_layer k :=
  fun _ hn => hA hn.1

/-- The prime restriction is monotone in the ambient set. -/
lemma restrict_to_primes_mono_left {A B Q : Set ℕ} (hAB : A ⊆ B) :
    restrict_to_primes A Q ⊆ restrict_to_primes B Q :=
  fun _ hn => ⟨hAB hn.1, hn.2⟩

/-- The prime restriction is monotone in the allowed prime set. -/
lemma restrict_to_primes_mono_right {A Q R : Set ℕ} (hQR : Q ⊆ R) :
    restrict_to_primes A Q ⊆ restrict_to_primes A R :=
  fun _ hn => ⟨hn.1, fun p hp hpn => hQR (hn.2 p hp hpn)⟩

/-- Restricting twice to the same prime set is the same as restricting once. -/
lemma restrict_to_primes_idempotent (A Q : Set ℕ) :
    restrict_to_primes (restrict_to_primes A Q) Q = restrict_to_primes A Q :=
  Set.ext fun _ => ⟨fun hn => hn.1, fun hn => ⟨hn, hn.2⟩⟩

lemma restrict_to_primes.divisor_prime_factors {A Q : Set ℕ} {n d : ℕ}
    (hn : n ∈ restrict_to_primes A Q) (hdvd : d ∣ n) :
    ∀ p : ℕ, Nat.Prime p -> p ∣ n / d -> p ∈ Q :=
  fun p hp hpd => hn.2 p hp (dvd_trans hpd (Nat.div_dvd_of_dvd hdvd))

lemma restrict_to_primes.div_mem_univ {A Q : Set ℕ} {n d : ℕ}
    (hn : n ∈ restrict_to_primes A Q) (hdvd : d ∣ n) :
    n / d ∈ restrict_to_primes (Set.univ : Set ℕ) Q :=
  ⟨Set.mem_univ _, restrict_to_primes.divisor_prime_factors hn hdvd⟩

/-- A set of odd primes, as used in the Odd Banks--Martin theorem. -/
abbrev IsSetOfOddPrimes (Q : Set ℕ) : Prop :=
  ∀ p : ℕ, p ∈ Q -> Nat.Prime p ∧ p ≠ 2

/-- A set of odd primes is, in particular, a subset of the prime layer. -/
lemma IsSetOfOddPrimes.subset_prime_layer {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) :
    Q ⊆ prime_layer :=
  fun p hp => (hQ p hp).1

/-- Members of a set of odd primes are not equal to `2`. -/
lemma IsSetOfOddPrimes.ne_two {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    p ≠ 2 :=
  (hQ p hp).2

lemma IsSetOfOddPrimes.prime {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    Nat.Prime p :=
  (hQ p hp).1

lemma IsSetOfOddPrimes.two_lt {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    2 < p :=
  lt_of_le_of_ne (hQ.prime hp).two_le (hQ.ne_two hp).symm

lemma IsSetOfOddPrimes.one_lt {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    1 < p :=
  lt_trans Nat.one_lt_two (hQ.two_lt hp)

lemma IsSetOfOddPrimes.pos {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    0 < p :=
  Nat.lt_trans Nat.zero_lt_one (hQ.one_lt hp)

lemma restrict_to_primes_positive_of_odd_primes {A Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) {n : ℕ}
    (hn : n ∈ restrict_to_primes A Q) :
    0 < n := by
  by_contra hnpos
  have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hnpos
  have htwoQ : 2 ∈ Q := by
    exact hn.2 2 Nat.prime_two (by rw [hn_zero]; exact dvd_zero 2)
  exact (hQ.ne_two htwoQ) rfl

/-!
### Odd Banks--Martin layer vocabulary
-/

/-- The Odd Banks--Martin state space above the `k`th prime-factor layer,
restricted to the allowed set of odd primes. -/
def oddBM_state (k : ℕ) (Q : Set ℕ) : Set ℕ :=
  restrict_to_primes (omega_ge_layer k) Q

/-- The terminal Odd Banks--Martin layer, restricted to the allowed set of odd
primes. -/
def oddBM_terminal (k : ℕ) (Q : Set ℕ) : Set ℕ :=
  restrict_to_primes (omega_layer k) Q

/-- Upper prime-factor layers are antitone in the layer index. -/
lemma omega_ge_layer_antitone {k l : ℕ} (hkl : k ≤ l) :
    omega_ge_layer l ⊆ omega_ge_layer k := by
  intro n hn
  change l ≤ ArithmeticFunction.cardFactors n at hn
  change k ≤ ArithmeticFunction.cardFactors n
  exact hkl.trans hn

/-- The terminal Odd Banks--Martin layer is contained in the corresponding state
space. -/
lemma oddBM_terminal_subset_state (k : ℕ) (Q : Set ℕ) :
    oddBM_terminal k Q ⊆ oddBM_state k Q :=
  restrict_to_primes_mono_left (omega_layer_subset_omega_ge_layer k)

/-- The positive part of the Odd Banks--Martin terminal layer is primitive. -/
lemma oddBM_terminal_positive_primitive (k : ℕ) (Q : Set ℕ) :
    primitive_set ({n : ℕ | 0 < n} ∩ oddBM_terminal k Q) := by
  exact primitive_set_of_subset (omega_layer_positive_primitive k) (by
    intro n hn
    exact ⟨hn.1, (restrict_to_primes_subset_left (omega_layer k) Q hn.2)⟩)

lemma oddBM_state_positive_of_odd_primes {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state k Q) :
    0 < n := by
  exact restrict_to_primes_positive_of_odd_primes hQ (by
    simpa [oddBM_state] using hn)

lemma oddBM_terminal_positive_of_odd_primes {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_terminal k Q) :
    0 < n := by
  exact restrict_to_primes_positive_of_odd_primes hQ (by
    simpa [oddBM_terminal] using hn)

lemma oddBM_terminal_primitive (k : ℕ) {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) :
    primitive_set (oddBM_terminal k Q) := by
  exact primitive_set_of_subset (oddBM_terminal_positive_primitive k Q) (by
    intro n hn
    exact ⟨oddBM_terminal_positive_of_odd_primes hQ hn, hn⟩)

lemma oddBM_terminal_erdos_bound (k : ℕ) {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) :
    Summable (fun n : ℕ => (oddBM_terminal k Q).indicator erdos_weight n) ∧
      erdos_sum (oddBM_terminal k Q) ≤ erdos_sum prime_layer :=
  (erdos_primitive_set_conjecture_164.2
    (oddBM_terminal k Q) (oddBM_terminal_primitive k hQ))

/-- Odd Banks--Martin state spaces are antitone in the layer index. -/
lemma oddBM_state_antitone {k l : ℕ} (hkl : k ≤ l) (Q : Set ℕ) :
    oddBM_state l Q ⊆ oddBM_state k Q :=
  restrict_to_primes_mono_left (omega_ge_layer_antitone hkl)

lemma oddBM_state_restrict_to_primes (k : ℕ) (Q : Set ℕ) :
    restrict_to_primes (oddBM_state k Q) Q = oddBM_state k Q := by
  simpa [oddBM_state] using restrict_to_primes_idempotent (omega_ge_layer k) Q

lemma oddBM_terminal_restrict_to_primes (k : ℕ) (Q : Set ℕ) :
    restrict_to_primes (oddBM_terminal k Q) Q = oddBM_terminal k Q := by
  simpa [oddBM_terminal] using restrict_to_primes_idempotent (omega_layer k) Q

lemma oddBM_mul_prime_mem_state_succ {k m p : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hm : m ∈ oddBM_state k Q) (hpQ : p ∈ Q) :
    m * p ∈ oddBM_state (k + 1) Q := by
  have hmpos := oddBM_state_positive_of_odd_primes hQ hm
  refine ⟨?_, ?_⟩
  · change k + 1 ≤ ArithmeticFunction.cardFactors (m * p)
    rw [ArithmeticFunction.cardFactors_mul hmpos.ne' (hQ.prime hpQ).ne_zero]
    have hmk : k ≤ ArithmeticFunction.cardFactors m := hm.1
    simpa [hQ.prime hpQ] using Nat.add_le_add_right hmk 1
  · intro q hq hqdiv
    rcases hq.dvd_mul.mp hqdiv with hqm | hqp
    · exact hm.2 q hq hqm
    · have : q = p := (Nat.dvd_prime (hQ.prime hpQ)).mp hqp |>.resolve_left hq.ne_one
      simpa [this] using hpQ

lemma oddBM_mul_prime_not_terminal {k m p : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hm : m ∈ oddBM_state k Q) (hpQ : p ∈ Q) :
    m * p ∉ oddBM_terminal k Q := by
  intro hterm
  have hsucc := oddBM_mul_prime_mem_state_succ hQ hm hpQ
  have hk : k + 1 ≤ ArithmeticFunction.cardFactors (m * p) := hsucc.1
  have heq : ArithmeticFunction.cardFactors (m * p) = k := hterm.1
  omega

lemma oddBM_state_div_mem_restrict_to_primes_univ {k n d : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_state k Q) (hdvd : d ∣ n) :
    n / d ∈ restrict_to_primes (Set.univ : Set ℕ) Q :=
  restrict_to_primes.div_mem_univ (by simpa [oddBM_state] using hn) hdvd

lemma oddBM_terminal_div_mem_restrict_to_primes_univ {k n d : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_terminal k Q) (hdvd : d ∣ n) :
    n / d ∈ restrict_to_primes (Set.univ : Set ℕ) Q :=
  restrict_to_primes.div_mem_univ (by simpa [oddBM_terminal] using hn) hdvd

/-!
### Odd Banks--Martin kernel data
-/

/-- The odd-prime correction factor `β_p = p / (p - 2)`. -/
noncomputable def oddBM_beta (p : ℕ) : ℝ :=
  (p : ℝ) / ((p : ℝ) - 2)

lemma oddBM_beta_pos {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    0 < oddBM_beta p := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  exact div_pos (by linarith) (by linarith)

lemma oddBM_beta_one_lt {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    1 < oddBM_beta p := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  rw [oddBM_beta, lt_div_iff₀ (by linarith)]
  linarith

lemma oddBM_beta_ge_one {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    1 ≤ oddBM_beta p :=
  (oddBM_beta_one_lt hp hp2).le

lemma oddBM_beta_sub_one_pos {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    0 < oddBM_beta p - 1 := by
  have hlt := oddBM_beta_one_lt hp hp2
  linarith

lemma oddBM_beta_sub_one_eq_two_div {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    oddBM_beta p - 1 = 2 / ((p : ℝ) - 2) := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  rw [oddBM_beta]
  field_simp [show (p : ℝ) - 2 ≠ 0 from by linarith]
  ring

lemma oddBM_beta_div_natCast {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    oddBM_beta p / (p : ℝ) = 1 / ((p : ℝ) - 2) := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  rw [oddBM_beta]
  field_simp [show (p : ℝ) ≠ 0 from by linarith,
    show (p : ℝ) - 2 ≠ 0 from by linarith]

lemma oddBM_beta_div_eq_sub_one_half {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    oddBM_beta p / (p : ℝ) = (oddBM_beta p - 1) / 2 := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  rw [oddBM_beta]
  field_simp [show (p : ℝ) ≠ 0 from by linarith,
    show (p : ℝ) - 2 ≠ 0 from by linarith]
  ring

lemma oddBM_beta_sub_one_half_eq_inv {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (oddBM_beta p - 1) / 2 = 1 / ((p : ℝ) - 2) := by
  rw [← oddBM_beta_div_eq_sub_one_half hp hp2]
  exact oddBM_beta_div_natCast hp hp2

lemma oddBM_beta_pos_of_mem {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    0 < oddBM_beta p :=
  oddBM_beta_pos (hQ.prime hp) (hQ.ne_two hp)

lemma oddBM_beta_one_lt_of_mem {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    1 < oddBM_beta p :=
  oddBM_beta_one_lt (hQ.prime hp) (hQ.ne_two hp)

lemma oddBM_beta_ge_one_of_mem {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    1 ≤ oddBM_beta p :=
  oddBM_beta_ge_one (hQ.prime hp) (hQ.ne_two hp)

lemma oddBM_beta_sub_one_pos_of_mem {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q)
    {p : ℕ} (hp : p ∈ Q) :
    0 < oddBM_beta p - 1 :=
  oddBM_beta_sub_one_pos (hQ.prime hp) (hQ.ne_two hp)

lemma oddBM_beta_div_natCast_of_mem {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) {p : ℕ}
    (hp : p ∈ Q) :
    oddBM_beta p / (p : ℝ) = 1 / ((p : ℝ) - 2) :=
  oddBM_beta_div_natCast (hQ.prime hp) (hQ.ne_two hp)

lemma oddBM_beta_sub_one_half_eq_inv_of_mem {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) {p : ℕ} (hp : p ∈ Q) :
    (oddBM_beta p - 1) / 2 = 1 / ((p : ℝ) - 2) :=
  oddBM_beta_sub_one_half_eq_inv (hQ.prime hp) (hQ.ne_two hp)

/-- The odd-prime Dirichlet series used in the Odd Banks--Martin analytic
estimate. -/
noncomputable def oddBM_primeBetaSeries (u : ℝ) : ℝ :=
  ∑' p : ℕ,
    if Nat.Prime p ∧ p ≠ 2 then
      Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
    else 0

lemma oddBM_primeBetaSeries_term_eq_beta_div {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) (u : ℝ) :
    Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) =
      (oddBM_beta p / (p : ℝ)) * Real.log (p : ℝ) / Real.rpow (p : ℝ) u := by
  rw [oddBM_beta_div_natCast hp hp2]
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  have hrpow_pos : 0 < Real.rpow (p : ℝ) u :=
    Real.rpow_pos_of_pos (by linarith) u
  field_simp [show (p : ℝ) - 2 ≠ 0 from by linarith, hrpow_pos.ne']

lemma oddBM_primeBetaSeries_term_nonneg {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) (u : ℝ) :
    0 ≤ Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) := by
  have h2 : (2 : ℝ) < (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp.two_le hp2.symm
  have hrpow_pos : 0 < Real.rpow (p : ℝ) u :=
    Real.rpow_pos_of_pos (by linarith) u
  exact div_nonneg (Real.log_nonneg (by linarith))
    (mul_nonneg (by linarith) hrpow_pos.le)

lemma oddBM_primeBetaSeries_eq_beta_form (u : ℝ) :
    oddBM_primeBetaSeries u =
      ∑' p : ℕ,
        if Nat.Prime p ∧ p ≠ 2 then
          (oddBM_beta p / (p : ℝ)) * Real.log (p : ℝ) / Real.rpow (p : ℝ) u
        else 0 := by
  rw [oddBM_primeBetaSeries]
  congr 1
  ext p
  split_ifs with h
  · exact oddBM_primeBetaSeries_term_eq_beta_div h.1 h.2 u
  · rfl

lemma prime_ne_two_iff_three_le {p : ℕ} (hp : Nat.Prime p) :
    p ≠ 2 ↔ 3 ≤ p := by
  have := hp.two_le
  omega

lemma oddBM_primeBetaSeries_eq_three_le_form (u : ℝ) :
    oddBM_primeBetaSeries u =
      ∑' p : ℕ,
        if Nat.Prime p ∧ 3 ≤ p then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
        else 0 := by
  refine tsum_congr fun p => ?_
  by_cases hp : Nat.Prime p
  · exact if_congr (and_congr_right fun _ => prime_ne_two_iff_three_le hp) rfl rfl
  · simp [hp]

lemma oddBM_primeBetaSeries_bound_three_le_form
    (h : ∀ u : ℝ, 0 < u -> u * oddBM_primeBetaSeries u ≤ 1) :
    ∀ u : ℝ, 0 < u ->
      u * (∑' p : ℕ,
        if Nat.Prime p ∧ 3 ≤ p then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
        else 0) ≤ 1 := by
  intro u hu
  rw [← oddBM_primeBetaSeries_eq_three_le_form u]
  exact h u hu

/-!
## Unconditional Lemma `lem:oddzeta`

TeX Lemma `lem:oddzeta`: for every `u > 0`,
`u * ∑_{p ≥ 3} log p / ((p − 2) p^u) ≤ 1`.

Following the paper: reduce to `0 < u ≤ 0.92` by per-term monotonicity of
`u ↦ u p^{-u}`; split each summand against the von Mangoldt Dirichlet-series
bound `Φ(u) ≤ log 2/(2^u − 1)` (Lemma `lem:phi`); bound the correction terms
for `p > 7` by their values at `u = 0` (an explicit prime sum to `300` plus a
telescoping tail, TeX constant `C = 0.111… ≤ 0.137`); and verify the residual
explicit inequality `\eqref{analytic}` by interval arithmetic on 15
subintervals of `(0, 0.92]`, using the convexity bound `\eqref{spot}` in the
`sinh` form `2 sinh x ≥ 2x`.
-/

/-- Rational lower bounds for real powers from integer power comparisons:
if `c ^ m ≤ b ^ k` then `c ≤ b ^ (k/m)`. -/
lemma oddzeta_le_rpow (b c e : ℝ) (k m : ℕ) (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hm : 0 < m) (he : e * (m : ℝ) = (k : ℝ)) (h : c ^ m ≤ b ^ k) :
    c ≤ Real.rpow b e := by
  have hb0 : (0 : ℝ) ≤ b := zero_le_one.trans hb
  have key : Real.rpow b e ^ m = b ^ k := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast (b ^ e) m, ← Real.rpow_mul hb0, he,
      Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ hc (Real.rpow_nonneg hb0 e) hm.ne').mp (key ▸ h)

/-- Rational upper bounds for real powers from integer power comparisons:
if `b ^ k ≤ c ^ m` then `b ^ (k/m) ≤ c`. -/
lemma oddzeta_rpow_le (b c e : ℝ) (k m : ℕ) (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hm : 0 < m) (he : e * (m : ℝ) = (k : ℝ)) (h : b ^ k ≤ c ^ m) :
    Real.rpow b e ≤ c := by
  have hb0 : (0 : ℝ) ≤ b := zero_le_one.trans hb
  have key : Real.rpow b e ^ m = b ^ k := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast (b ^ e) m, ← Real.rpow_mul hb0, he,
      Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0 e) hc hm.ne').mp (key ▸ h)

/-- Rational upper bounds on logarithms from power-of-two comparisons. -/
lemma oddzeta_log_le (x c : ℝ) (k m : ℕ) (hx : 0 < x) (hk : 0 < k)
    (h : x ^ k ≤ 2 ^ m) (hc : (m : ℝ) * 0.6931471808 ≤ (k : ℝ) * c) :
    Real.log x ≤ c := by
  have h1 : Real.log (x ^ k) ≤ Real.log ((2 : ℝ) ^ m) :=
    Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 : (m : ℝ) * Real.log 2 ≤ (m : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg m)
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h3 : (k : ℝ) * Real.log x ≤ (k : ℝ) * c := by linarith
  exact le_of_mul_le_mul_left h3 hk'

/-- Rational lower bounds on logarithms from power-of-two comparisons. -/
lemma oddzeta_le_log (x c : ℝ) (k m : ℕ) (_hx : 0 < x) (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ x ^ k) (hc : (k : ℝ) * c ≤ (m : ℝ) * 0.6931471803) :
    c ≤ Real.log x := by
  have h1 : Real.log ((2 : ℝ) ^ m) ≤ Real.log (x ^ k) :=
    Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 : (m : ℝ) * 0.6931471803 ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg m)
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h3 : (k : ℝ) * c ≤ (k : ℝ) * Real.log x := by linarith
  exact le_of_mul_le_mul_left h3 hk'

set_option exponentiation.threshold 520 in
lemma oddzeta_log_three_le : Real.log 3 ≤ 1.0986157 :=
  oddzeta_log_le 3 1.0986157 306 485 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma oddzeta_le_log_three : 1.0974 ≤ Real.log 3 :=
  oddzeta_le_log 3 1.0974 12 19 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma oddzeta_log_five_le : Real.log 5 ≤ 1.6095113 :=
  oddzeta_log_le 5 1.6095113 59 137 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma oddzeta_log_seven_le : Real.log 7 ≤ 1.9461441 :=
  oddzeta_log_le 7 1.9461441 26 73 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- TeX Lemma `lem:phi` form used here: the von Mangoldt Dirichlet series is at
most `log 2/(2^u − 1)`, by monotonicity of the Dirichlet eta function. -/
lemma oddzeta_mangoldt_series_le (u : ℝ) (hu : 0 < u) :
    mangoldt_dirichlet_series u ≤ Real.log 2 / ((2 : ℝ) ^ u - 1) := by
  calc mangoldt_dirichlet_series u
      = ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
        simpa using congrArg Complex.re
          (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu)
    _ ≤ Real.log 2 / ((2 : ℝ) ^ u - 1) := zeta_log_derivative_geometric_bound u hu

/-- The prime-power tower identity `(p^(j+1))^(1+u) = (p^(1+u))^(j+1)`. -/
lemma oddzeta_pow_rpow (p j : ℕ) (u : ℝ) :
    ((p ^ (j+1) : ℕ) : ℝ) ^ (1+u) = ((p : ℝ) ^ (1+u)) ^ (j+1) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast ((p : ℝ)) (j+1), ← Real.rpow_mul hp0,
    ← Real.rpow_natCast (((p : ℝ)) ^ (1+u)) (j+1), ← Real.rpow_mul hp0,
    mul_comm ((j+1 : ℕ) : ℝ) (1+u)]

/-- TeX Lemma `lem:phi` in finite form over primes: for a finite set `s` of
primes, `∑_{p ∈ s} log p/(p^{1+u} − 1) ≤ log 2/(2^u − 1)`, by regrouping the
prime-power geometric series inside the von Mangoldt Dirichlet series. -/
lemma oddzeta_prime_phi_sum_le (u : ℝ) (hu : 0 < u) (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    (∑ p ∈ s, Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) ≤
      Real.log 2 / ((2 : ℝ) ^ u - 1) := by
  classical
  have hgeom : ∀ p ∈ s, HasSum
      (fun j : ℕ => Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1))
      (Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hs p hp).two_le
    have hR : 1 < (p : ℝ) ^ (1+u) :=
      Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr
        (Or.inl ⟨by linarith, by linarith⟩)
    have hR0 : (0 : ℝ) < (p : ℝ) ^ (1+u) := by linarith
    have hr0 : 0 ≤ ((p : ℝ) ^ (1+u))⁻¹ := by positivity
    have hr1 : ((p : ℝ) ^ (1+u))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
      (Real.log (p : ℝ) * ((p : ℝ) ^ (1+u))⁻¹)
    have h2 : HasSum (fun j : ℕ => Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1))
        (Real.log (p : ℝ) * ((p : ℝ) ^ (1+u))⁻¹ * (1 - ((p : ℝ) ^ (1+u))⁻¹)⁻¹) := by
      rw [show (fun j : ℕ => Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1))
          = (fun j : ℕ => Real.log (p : ℝ) * ((p : ℝ) ^ (1+u))⁻¹ *
            (((p : ℝ) ^ (1+u))⁻¹) ^ j) from
        funext fun j => by rw [pow_succ]; ring]
      exact h
    have hval : Real.log (p : ℝ) * ((p : ℝ) ^ (1+u))⁻¹ *
        (1 - ((p : ℝ) ^ (1+u))⁻¹)⁻¹ = Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1) := by
      have hRne : ((p : ℝ) ^ (1+u)) ≠ 0 := ne_of_gt hR0
      have hR1ne : ((p : ℝ) ^ (1+u)) - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    exact hval ▸ h2
  have hFsum : HasSum
      (fun j : ℕ => ∑ p ∈ s, Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1))
      (∑ p ∈ s, Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) :=
    hasSum_sum hgeom
  have hMnonneg : 0 ≤ mangoldt_dirichlet_series u := by
    rw [mangoldt_dirichlet_series]
    exact tsum_nonneg fun q => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hFle : ∀ J : Finset ℕ,
      (∑ j ∈ J, ∑ p ∈ s, Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1)) ≤
        mangoldt_dirichlet_series u := by
    intro J
    have hswap : (∑ j ∈ J, ∑ p ∈ s, Real.log (p : ℝ) * (((p : ℝ) ^ (1+u))⁻¹) ^ (j+1))
        = ∑ x ∈ s ×ˢ J, Real.log (x.1 : ℝ) * (((x.1 : ℝ) ^ (1+u))⁻¹) ^ (x.2+1) := by
      rw [Finset.sum_product]
      exact Finset.sum_comm
    have hinj : ∀ x ∈ s ×ˢ J, ∀ y ∈ s ×ˢ J,
        x.1 ^ (x.2+1) = y.1 ^ (y.2+1) → x = y := by
      rintro ⟨p, i⟩ hx ⟨q, j⟩ hy h
      simp only [Finset.mem_product] at hx hy
      have hp := hs p hx.1
      have hq := hs q hy.1
      have hpq : p = q := by
        have hdvd : p ∣ q ^ (j+1) := by
          rw [← h]; exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
      subst hpq
      have hij : i + 1 = j + 1 := Nat.pow_right_injective hp.two_le h
      exact Prod.ext rfl (by omega)
    have himg : (∑ x ∈ s ×ˢ J, Real.log (x.1 : ℝ) * (((x.1 : ℝ) ^ (1+u))⁻¹) ^ (x.2+1))
        = ∑ q ∈ (s ×ˢ J).image (fun x : ℕ × ℕ => x.1 ^ (x.2+1)),
            ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1+u) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl ?_
      rintro ⟨p, j⟩ hx
      simp only [Finset.mem_product] at hx
      have hp := hs p hx.1
      rw [Real.rpow_eq_pow, ArithmeticFunction.vonMangoldt_apply_pow (by omega : j+1 ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp, oddzeta_pow_rpow,
        div_eq_mul_inv, ← inv_pow]
    rw [hswap, himg, mangoldt_dirichlet_series]
    exact (mangoldt_dirichlet_series_summable_local u hu).sum_le_tsum _
      (fun q _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have hle : (∑ p ∈ s, Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) ≤
      mangoldt_dirichlet_series u := by
    rw [← hFsum.tsum_eq]
    exact tsum_le_of_sum_le' hMnonneg hFle
  exact hle.trans (oddzeta_mangoldt_series_le u hu)

/-- The odd-prime form of `lem:phi`: subtracting the `p = 2` term. -/
lemma oddzeta_odd_phi_sum_le (u : ℝ) (hu : 0 < u) (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) :
    (∑ p ∈ s, Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) ≤
      Real.log 2 / ((2 : ℝ) ^ u - 1) - Real.log 2 / ((2 : ℝ) ^ (1+u) - 1) := by
  classical
  have h2s : (2 : ℕ) ∉ s := fun h => (hs 2 h).2 rfl
  have hall : ∀ p ∈ insert 2 s, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h' | h'
    · exact h' ▸ Nat.prime_two
    · exact (hs p h').1
  have h := oddzeta_prime_phi_sum_le u hu (insert 2 s) hall
  rw [Finset.sum_insert h2s] at h
  push_cast at h
  linarith

/-- The correction term `corr_P(u) = log P (2P^u − 1)/((P−2) P^u (P^{1+u} − 1))`
in the splitting of `log P/((P−2) P^u)` (TeX proof of `lem:oddzeta`). -/
noncomputable def oddzeta_corr (P u : ℝ) : ℝ :=
  Real.log P * ((2 * P ^ u - 1) / ((P - 2) * (P ^ u * (P * P ^ u - 1))))

/-- Rational majorant for `oddcorr_P(u)` after replacing `P^u` by a certified
lower bound `x`; this is the expression used in the interval checks for TeX
Lemma `lem:oddzeta`, equation `\eqref{analytic}`. -/
noncomputable def oddzeta_corrMajorant (P x : ℝ) : ℝ :=
  Real.log P * ((2 * x - 1) / ((P - 2) * (x * (P * x - 1))))

/-- The function `x ↦ (2x−1)/((P−2) x (Px−1))` is decreasing on `x ≥ 1`. -/
lemma oddzeta_phi_aux {P x y : ℝ} (hP : 3 ≤ P) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (2*y - 1) / ((P - 2) * (y * (P*y - 1))) ≤
      (2*x - 1) / ((P - 2) * (x * (P*x - 1))) := by
  have hy : 1 ≤ y := hx.trans hxy
  have hPx : (3:ℝ) * 1 ≤ P * x := mul_le_mul hP hx zero_le_one (by linarith)
  have hPy : (3:ℝ) * 1 ≤ P * y := mul_le_mul hP hy zero_le_one (by linarith)
  have h1 : 0 < (P - 2) * (x * (P*x - 1)) :=
    mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
  have h2 : 0 < (P - 2) * (y * (P*y - 1)) :=
    mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ h2 h1]
  have hkey : 0 ≤ P*x*(y-1) + P*y*(x-1) + 1 := by
    have k1 : 0 ≤ P*x*(y-1) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ P*y*(x-1) := mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ P - 2)
    (by linarith : (0:ℝ) ≤ y - x)) hkey]

/-- Monotone bound for the correction term from a rational lower bound on
`P^u`. -/
lemma oddzeta_corr_le {P : ℝ} (hP : 3 ≤ P) {x u : ℝ} (hx : 1 ≤ x)
    (hxu : x ≤ P ^ u) :
    oddzeta_corr P u ≤ oddzeta_corrMajorant P x :=
  mul_le_mul_of_nonneg_left (oddzeta_phi_aux hP hx hxu)
    (Real.log_nonneg (by linarith))

lemma oddzeta_corr_nonneg {P : ℝ} (hP : 3 ≤ P) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ oddzeta_corr P u := by
  have hX : 1 ≤ P ^ u := Real.one_le_rpow (by linarith) hu
  have hPX : (3:ℝ) * 1 ≤ P * P ^ u := mul_le_mul hP hX zero_le_one (by linarith)
  have h1 : 0 < (P - 2) * (P ^ u * (P * P ^ u - 1)) :=
    mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
  exact mul_nonneg (Real.log_nonneg (by linarith))
    (div_nonneg (by linarith) h1.le)

/-- The value of the correction bound at `x = 1`: TeX
`corr_P(u) ≤ log P/((P−1)(P−2))`. -/
lemma oddzeta_corr_le_one {P : ℝ} (hP : 3 ≤ P) {u : ℝ} (hu : 0 ≤ u) :
    oddzeta_corr P u ≤ Real.log P / ((P - 1) * (P - 2)) := by
  have h := oddzeta_corr_le hP le_rfl (Real.one_le_rpow (by linarith) hu)
  calc oddzeta_corr P u
      ≤ oddzeta_corrMajorant P 1 := h
    _ = Real.log P / ((P - 1) * (P - 2)) := by
        rw [oddzeta_corrMajorant]
        rw [show (P - 2) * (1 * (P*1 - 1)) = (P - 1) * (P - 2) by ring,
          show (2*(1:ℝ) - 1) = 1 by norm_num, mul_one_div]

/-- The splitting `log p/((p−2) p^u) = log p/(p^{1+u} − 1) + corr_p(u)`. -/
lemma oddzeta_term_split {p : ℕ} (hp3 : 3 ≤ p) {u : ℝ} (hu : 0 < u) :
    Real.log (p : ℝ) / (((p : ℝ) - 2) * (p : ℝ) ^ u)
      = Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1) + oddzeta_corr (p : ℝ) u := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hX : 1 ≤ (p : ℝ) ^ u := Real.one_le_rpow (by linarith) hu.le
  have hX0 : (0 : ℝ) < (p : ℝ) ^ u := by linarith
  have hsplit : (p : ℝ) ^ (1+u) = (p : ℝ) * (p : ℝ) ^ u := by
    rw [Real.rpow_add hp0, Real.rpow_one]
  rw [oddzeta_corr, hsplit]
  have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) * (p : ℝ) ^ u - 1 := by nlinarith
  field_simp
  ring

/-- The per-term tail estimate for the constant `C`:
`log t/((t−1)(t−2)) ≤ 2/(t−1)^{3/4} − 2/t^{3/4}` for `t ≥ 301`. -/
lemma oddzeta_tail_term_le {t : ℝ} (ht : 301 ≤ t) :
    Real.log t / ((t - 1) * (t - 2)) ≤
      2 / (t - 1) ^ ((3:ℝ)/4) - 2 / t ^ ((3:ℝ)/4) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have ht2 : (0 : ℝ) < t - 2 := by linarith
  set Q := t ^ ((1:ℝ)/4) with hQdef
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos ht0 _
  have hQ4 : Q ^ 4 = t := by
    rw [hQdef, ← Real.rpow_natCast (t ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul ht0.le]
    norm_num
  have hT3 : t ^ ((3:ℝ)/4) = Q ^ 3 := by
    rw [hQdef, ← Real.rpow_natCast (t ^ ((1:ℝ)/4)) 3, ← Real.rpow_mul ht0.le]
    norm_num
  set P := (t - 1) ^ ((3:ℝ)/4) with hPdef
  have hP0 : 0 < P := Real.rpow_pos_of_pos ht1 _
  have hPQ3 : P ≤ Q ^ 3 := by
    rw [hPdef, ← hT3]
    exact Real.rpow_le_rpow ht1.le (by linarith) (by norm_num)
  have hAM : P * Q ≤ t - 3/4 := by
    have h := Real.geom_mean_le_arith_mean2_weighted
      (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (0:ℝ) ≤ 1/4) ht1.le ht0.le
      (by norm_num)
    rw [← hPdef, ← hQdef] at h
    linarith
  have hlog : Real.log t ≤ 1.48 * Q := by
    have hQe : Real.log Q = (1/4) * Real.log t := by
      rw [hQdef, Real.log_rpow ht0]
    have h1 : Real.log (0.37 * Q) ≤ 0.37 * Q - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul (by norm_num : (0.37:ℝ) ≠ 0) hQ0.ne'] at h1
    have h2 : Real.log ((100:ℝ)/37) ≤ 1 := by
      have h3 : ((100:ℝ)/37) < Real.exp 1 :=
        lt_trans (by norm_num) Real.exp_one_gt_d9
      have h4 := Real.log_lt_log (by norm_num : (0:ℝ) < (100:ℝ)/37) h3
      rw [Real.log_exp] at h4
      exact h4.le
    have h5 : Real.log (0.37 : ℝ) = - Real.log ((100:ℝ)/37) := by
      rw [show (0.37 : ℝ) = ((100:ℝ)/37)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hgap : 3/4 ≤ Q * (Q^3 - P) := by
    have hQQ : Q * Q^3 = t := by rw [← hQ4]; ring
    nlinarith [hAM]
  have hgap2 : (3/4) * Q^3 ≤ t * (Q^3 - P) := by
    nlinarith [mul_le_mul_of_nonneg_right hgap (by positivity : (0:ℝ) ≤ Q^3), hQ4]
  rw [hT3, div_sub_div _ _ hP0.ne' (by positivity : (Q:ℝ)^3 ≠ 0),
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- goal : log t * (P * Q^3) ≤ (2 * Q^3 - P * 2) * ((t-1)*(t-2))
  have hfinal : t * (Real.log t * (P * Q^3)) ≤
      t * ((2 * Q^3 - P * 2) * ((t - 1) * (t - 2))) := by
    have c1 : Real.log t * (P * Q^3) ≤ 1.48 * Q * (P * Q^3) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have c3 : 1.48 * (P * Q) * Q^3 ≤ 1.48 * (t - 3/4) * Q^3 := by
      have := mul_le_mul_of_nonneg_right hAM (by positivity : (0:ℝ) ≤ Q^3)
      nlinarith [this]
    have harith : 1.48 * t^2 ≤ (3/2) * ((t-1) * (t-2)) := by
      nlinarith [sq_nonneg (t - 301)]
    have c6 : 1.48 * t^2 * Q^3 ≤ (3/2) * ((t-1)*(t-2)) * Q^3 :=
      mul_le_mul_of_nonneg_right harith (by positivity)
    have c7 : (3/2) * ((t-1)*(t-2)) * Q^3 ≤
        t * ((2 * Q^3 - P * 2) * ((t-1)*(t-2))) := by
      have h8 := mul_le_mul_of_nonneg_right hgap2
        (by positivity : (0:ℝ) ≤ (t-1)*(t-2))
      nlinarith [h8]
    calc t * (Real.log t * (P * Q^3))
        ≤ t * (1.48 * Q * (P * Q^3)) :=
          mul_le_mul_of_nonneg_left c1 ht0.le
      _ = t * (1.48 * (P * Q) * Q^3) := by ring
      _ ≤ t * (1.48 * (t - 3/4) * Q^3) :=
          mul_le_mul_of_nonneg_left c3 ht0.le
      _ ≤ 1.48 * t^2 * Q^3 := by
          nlinarith [mul_nonneg ht0.le (by positivity : (0:ℝ) ≤ Q^3)]
      _ ≤ (3/2) * ((t-1)*(t-2)) * Q^3 := c6
      _ ≤ t * ((2 * Q^3 - P * 2) * ((t-1)*(t-2))) := c7
  exact le_of_mul_le_mul_left hfinal ht0

/-- Telescoping tail bound: any finite sum of `log n/((n−1)(n−2))` over
integers `n ≥ 301` is at most `2/300^{3/4} ≤ 0.0278`. -/
lemma oddzeta_tail_sum_le (s : Finset ℕ) (hs : ∀ n ∈ s, 301 ≤ n) :
    (∑ n ∈ s, Real.log (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2))) ≤ 0.0278 := by
  classical
  set g : ℕ → ℝ := fun m => 2 / (m : ℝ) ^ ((3:ℝ)/4) with hgdef
  have hg300 : g 300 ≤ 0.0278 := by
    simp only [hgdef]
    have h1 : (71.943 : ℝ) ≤ ((300 : ℕ) : ℝ) ^ ((3:ℝ)/4) := by
      have h := oddzeta_le_rpow 300 71.943 ((3:ℝ)/4) 3 4 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [Real.rpow_eq_pow] at h
      have hcast : ((300 : ℕ) : ℝ) = (300 : ℝ) := by norm_num
      rw [hcast]
      exact h
    have h2 : (0 : ℝ) < ((300 : ℕ) : ℝ) ^ ((3:ℝ)/4) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [div_le_iff₀ h2]
    nlinarith [h1]
  have hgnonneg : ∀ m : ℕ, 0 ≤ g m := by
    intro m
    simp only [hgdef]
    positivity
  have hganti : ∀ a b : ℕ, 0 < a → a ≤ b → g b ≤ g a := by
    intro a b ha hab
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    simp only [hgdef]
    exact div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos ha0 _)
      (Real.rpow_le_rpow ha0.le (by exact_mod_cast hab) (by norm_num))
  have hterm : ∀ n ∈ s, Real.log (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) ≤
      g (n - 1) - g n := by
    intro n hn
    have h301 := hs n hn
    have hc : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    simp only [hgdef]
    rw [hc]
    exact oddzeta_tail_term_le (by exact_mod_cast h301)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · norm_num
  set M := s.max' hne with hM
  have hsub : s ⊆ Finset.Ico 301 (M + 1) := by
    intro n hn
    rw [Finset.mem_Ico]
    exact ⟨hs n hn, Nat.lt_succ_of_le (Finset.le_max' s n hn)⟩
  calc (∑ n ∈ s, Real.log (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)))
      ≤ ∑ n ∈ s, (g (n-1) - g n) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ico 301 (M+1), (g (n-1) - g n) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro n hn _
        have hn301 : 301 ≤ n := (Finset.mem_Ico.mp hn).1
        have := hganti (n-1) n (by omega) (by omega)
        linarith
    _ = g 300 - g (300 + (M + 1 - 301)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        calc (∑ i ∈ Finset.range (M + 1 - 301), (g (301 + i - 1) - g (301 + i)))
            = ∑ i ∈ Finset.range (M + 1 - 301),
                ((fun k => g (300 + k)) i - (fun k => g (300 + k)) (i+1)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              have h1 : 301 + i - 1 = 300 + i := by omega
              have h2 : 301 + i = 300 + (i + 1) := by omega
              rw [h1, h2]
          _ = g (300 + 0) - g (300 + (M + 1 - 301)) := Finset.sum_range_sub' _ _
          _ = g 300 - g (300 + (M + 1 - 301)) := by norm_num
    _ ≤ g 300 := by linarith [hgnonneg (300 + (M + 1 - 301))]
    _ ≤ 0.0278 := hg300

set_option maxRecDepth 8000 in
/-- Every prime in `(7, 300]` belongs to the explicit list. -/
lemma oddzeta_mem_E {p : ℕ} (hp : Nat.Prime p) (h7 : 7 < p) (h300 : p ≤ 300) :
    p ∈ ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
      79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
      157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
      233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293} : Finset ℕ) := by
  by_contra hpE
  have key : ∀ q : ℕ, q < 301 →
      (q ≤ 7 ∨
        q ∈ ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
          73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
          151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
          229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293} :
          Finset ℕ) ∨
        2 ∣ q ∨ 3 ∣ q ∨ 5 ∣ q ∨ 7 ∣ q ∨ 11 ∣ q ∨ 13 ∣ q ∨ 17 ∣ q) := by decide
  have hdvd : 2 ∣ p ∨ 3 ∣ p ∨ 5 ∣ p ∨ 7 ∣ p ∨ 11 ∣ p ∨ 13 ∣ p ∨ 17 ∣ p := by
    rcases key p (by omega) with h | h | h
    · omega
    · exact absurd h hpE
    · exact h
  rcases hdvd with h | h | h | h | h | h | h
  · rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h1 <;> omega
  · rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h1 <;> omega
  · rcases hp.eq_one_or_self_of_dvd 5 h with h1 | h1 <;> omega
  · rcases hp.eq_one_or_self_of_dvd 7 h with h1 | h1 <;> omega
  · rcases hp.eq_one_or_self_of_dvd 11 h with h1 | h1
    · omega
    · exact hpE (h1 ▸ (by decide))
  · rcases hp.eq_one_or_self_of_dvd 13 h with h1 | h1
    · omega
    · exact hpE (h1 ▸ (by decide))
  · rcases hp.eq_one_or_self_of_dvd 17 h with h1 | h1
    · omega
    · exact hpE (h1 ▸ (by decide))

set_option maxHeartbeats 1600000 in
-- Normalizing all 59 explicit prime certificates requires extra kernel reduction.
/-- The explicit part of the TeX constant `C`: the primes in `(7, 300]`
contribute at most `0.109`. -/
lemma oddzeta_E_sum_le :
    (∑ p ∈ ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
        151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
        229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293} :
        Finset ℕ),
      Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤ 0.109 := by
  have l11 : Real.log 11 ≤ 2.3979146 :=
    oddzeta_log_le 11 2.3979146 37 128
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l13 : Real.log 13 ≤ 2.5672118 :=
    oddzeta_log_le 13 2.5672118 27 100
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l17 : Real.log 17 ≤ 2.8592322 :=
    oddzeta_log_le 17 2.8592322 8 33
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l19 : Real.log 19 ≤ 2.9458756 :=
    oddzeta_log_le 19 2.9458756 4 17
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l23 : Real.log 23 ≤ 3.1506691 :=
    oddzeta_log_le 23 3.1506691 11 50
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l29 : Real.log 29 ≤ 3.3817181 :=
    oddzeta_log_le 29 3.3817181 33 161
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l31 : Real.log 31 ≤ 3.4342293 :=
    oddzeta_log_le 31 3.4342293 22 109
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l37 : Real.log 37 ≤ 3.6142675 :=
    oddzeta_log_le 37 3.6142675 14 73
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l41 : Real.log 41 ≤ 3.7177895 :=
    oddzeta_log_le 41 3.7177895 11 59
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l43 : Real.log 43 ≤ 3.7627990 :=
    oddzeta_log_le 43 3.7627990 7 38
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l47 : Real.log 47 ≤ 3.8508177 :=
    oddzeta_log_le 47 3.8508177 9 50
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l53 : Real.log 53 ≤ 4.0013497 :=
    oddzeta_log_le 53 4.0013497 22 127
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l59 : Real.log 59 ≤ 4.1181098 :=
    oddzeta_log_le 59 4.1181098 17 101
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l61 : Real.log 61 ≤ 4.1110799 :=
    oddzeta_log_le 61 4.1110799 29 172
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l67 : Real.log 67 ≤ 4.2050929 :=
    oddzeta_log_le 67 4.2050929 15 91
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l71 : Real.log 71 ≤ 4.2628552 :=
    oddzeta_log_le 71 4.2628552 20 123
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l73 : Real.log 73 ≤ 4.2909112 :=
    oddzeta_log_le 73 4.2909112 21 130
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l79 : Real.log 79 ≤ 4.3698410 :=
    oddzeta_log_le 79 4.3698410 23 145
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l83 : Real.log 83 ≤ 4.4404742 :=
    oddzeta_log_le 83 4.4404742 32 205
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l89 : Real.log 89 ≤ 4.5054567 :=
    oddzeta_log_le 89 4.5054567 4 26
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l97 : Real.log 97 ≤ 4.5747714 :=
    oddzeta_log_le 97 4.5747714 10 66
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l101 : Real.log 101 ≤ 4.8520303 :=
    oddzeta_log_le 101 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l103 : Real.log 103 ≤ 4.8520303 :=
    oddzeta_log_le 103 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l107 : Real.log 107 ≤ 4.8520303 :=
    oddzeta_log_le 107 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l109 : Real.log 109 ≤ 4.8520303 :=
    oddzeta_log_le 109 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l113 : Real.log 113 ≤ 4.8520303 :=
    oddzeta_log_le 113 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l127 : Real.log 127 ≤ 4.8520303 :=
    oddzeta_log_le 127 4.8520303 1 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l131 : Real.log 131 ≤ 5.5451775 :=
    oddzeta_log_le 131 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l137 : Real.log 137 ≤ 5.5451775 :=
    oddzeta_log_le 137 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l139 : Real.log 139 ≤ 5.5451775 :=
    oddzeta_log_le 139 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l149 : Real.log 149 ≤ 5.5451775 :=
    oddzeta_log_le 149 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l151 : Real.log 151 ≤ 5.5451775 :=
    oddzeta_log_le 151 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l157 : Real.log 157 ≤ 5.5451775 :=
    oddzeta_log_le 157 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l163 : Real.log 163 ≤ 5.5451775 :=
    oddzeta_log_le 163 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l167 : Real.log 167 ≤ 5.5451775 :=
    oddzeta_log_le 167 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l173 : Real.log 173 ≤ 5.5451775 :=
    oddzeta_log_le 173 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l179 : Real.log 179 ≤ 5.5451775 :=
    oddzeta_log_le 179 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l181 : Real.log 181 ≤ 5.5451775 :=
    oddzeta_log_le 181 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l191 : Real.log 191 ≤ 5.5451775 :=
    oddzeta_log_le 191 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l193 : Real.log 193 ≤ 5.5451775 :=
    oddzeta_log_le 193 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l197 : Real.log 197 ≤ 5.5451775 :=
    oddzeta_log_le 197 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l199 : Real.log 199 ≤ 5.5451775 :=
    oddzeta_log_le 199 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l211 : Real.log 211 ≤ 5.5451775 :=
    oddzeta_log_le 211 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l223 : Real.log 223 ≤ 5.5451775 :=
    oddzeta_log_le 223 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l227 : Real.log 227 ≤ 5.5451775 :=
    oddzeta_log_le 227 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l229 : Real.log 229 ≤ 5.5451775 :=
    oddzeta_log_le 229 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l233 : Real.log 233 ≤ 5.5451775 :=
    oddzeta_log_le 233 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l239 : Real.log 239 ≤ 5.5451775 :=
    oddzeta_log_le 239 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l241 : Real.log 241 ≤ 5.5451775 :=
    oddzeta_log_le 241 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l251 : Real.log 251 ≤ 5.5451775 :=
    oddzeta_log_le 251 5.5451775 1 8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l257 : Real.log 257 ≤ 6.2383247 :=
    oddzeta_log_le 257 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l263 : Real.log 263 ≤ 6.2383247 :=
    oddzeta_log_le 263 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l269 : Real.log 269 ≤ 6.2383247 :=
    oddzeta_log_le 269 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l271 : Real.log 271 ≤ 6.2383247 :=
    oddzeta_log_le 271 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l277 : Real.log 277 ≤ 6.2383247 :=
    oddzeta_log_le 277 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l281 : Real.log 281 ≤ 6.2383247 :=
    oddzeta_log_le 281 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l283 : Real.log 283 ≤ 6.2383247 :=
    oddzeta_log_le 283 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have l293 : Real.log 293 ≤ 6.2383247 :=
    oddzeta_log_le 293 6.2383247 1 9
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
  linarith [l11, l13, l17, l19, l23, l29, l31, l37, l41, l43, l47, l53, l59,
    l61, l67, l71, l73, l79, l83, l89, l97, l101, l103, l107, l109, l113,
    l127, l131, l137, l139, l149, l151, l157, l163, l167, l173, l179, l181,
    l191, l193, l197, l199, l211, l223, l227, l229, l233, l239, l241, l251,
    l257, l263, l269, l271, l277, l281, l283, l293]

set_option maxRecDepth 4000 in
/-- The TeX constant `C = ∑_{p > 7} log p/((p−1)(p−2)) = 0.111… ≤ 0.137`,
in finite form: explicit primes up to `300` plus the telescoping tail. -/
lemma oddzeta_C_bound (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p ∧ 7 < p) :
    (∑ p ∈ s, Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤ 0.137 := by
  classical
  have hsplit := (Finset.sum_filter_add_sum_filter_not s (fun p => p ≤ 300)
    (fun p => Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)))).symm
  have hsmall : (∑ p ∈ s.filter (fun p => p ≤ 300),
      Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤ 0.109 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) oddzeta_E_sum_le
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hps := hs p hp'.1
      exact oddzeta_mem_E hps.1 hps.2 hp'.2
    · intro p hp _
      have h11 : 11 ≤ p := by
        have hall : ∀ q ∈ ({11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
            61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
            137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
            199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
            277, 281, 283, 293} : Finset ℕ), 11 ≤ q := by decide
        exact hall p hp
      have hpR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
      have hden : (0 : ℝ) ≤ ((p : ℝ) - 1) * ((p : ℝ) - 2) := by nlinarith
      exact div_nonneg hlog hden
  have hbig : (∑ p ∈ s.filter (fun p => ¬ p ≤ 300),
      Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤ 0.0278 := by
    refine oddzeta_tail_sum_le _ ?_
    intro p hp
    have h := Finset.mem_filter.mp hp
    omega
  linarith [hsplit, hsmall, hbig]

/-- The auxiliary function `G(u)` from the TeX proof of `lem:oddzeta`:
`G(u) = log 2 (2^{3u/4}/2 + 2^{u/2})/(2^{1+u} − 1)`. -/
noncomputable def oddzeta_G (u : ℝ) : ℝ :=
  Real.log 2 * (((2:ℝ) ^ (3*u/4) / 2 + (2:ℝ) ^ (u/2)) / ((2:ℝ) ^ (1+u) - 1))

/-- TeX `\eqref{spot}` in product form: `v log 2 · 2^{v/2} ≤ 2^v − 1`. -/
lemma oddzeta_spot {v : ℝ} (hv : 0 ≤ v) :
    v * Real.log 2 * (2:ℝ) ^ (v/2) ≤ (2:ℝ) ^ v - 1 := by
  have h1 : (2:ℝ) ^ v = Real.exp (v * Real.log 2) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  have h2 : (2:ℝ) ^ (v/2) = Real.exp (v * Real.log 2 / 2) := by
    rw [Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  rw [h1, h2]
  set y := v * Real.log 2 with hy
  have hy0 : 0 ≤ y := mul_nonneg hv (Real.log_nonneg one_le_two)
  have hsinh : y / 2 ≤ Real.sinh (y/2) := by
    rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ y/2) with h | h
    · rw [← h]
      simp
    · exact (Real.self_lt_sinh_iff.mpr h).le
  rw [Real.sinh_eq, Real.exp_neg] at hsinh
  have hE : 0 < Real.exp (y/2) := Real.exp_pos _
  have hsq : Real.exp (y/2) * Real.exp (y/2) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp (y/2) * (Real.exp (y/2))⁻¹ = 1 := mul_inv_cancel₀ hE.ne'
  nlinarith [mul_le_mul_of_nonneg_left hsinh hE.le]

/-- `G` is non-increasing on `[0, ∞)`. -/
lemma oddzeta_G_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    oddzeta_G v ≤ oddzeta_G u := by
  have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  set t := (2:ℝ) ^ (v - u) with htdef
  have ht1 : 1 ≤ t := by
    rw [htdef]
    exact Real.one_le_rpow one_le_two (by linarith)
  have ht0 : (0:ℝ) < t := by linarith
  have h34 : (2:ℝ) ^ (3*v/4) ≤ (2:ℝ) ^ (3*u/4) * t := by
    rw [htdef, ← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have h12 : (2:ℝ) ^ (v/2) ≤ (2:ℝ) ^ (u/2) * t := by
    rw [htdef, ← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hDv : (2:ℝ) ^ (1+v) = (2:ℝ) ^ (1+u) * t := by
    rw [htdef, ← Real.rpow_add two_pos]
    congr 1
    ring
  have hDu2 : (2:ℝ) ≤ (2:ℝ) ^ (1+u) := by
    calc (2:ℝ) = (2:ℝ) ^ (1:ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hDu : (0:ℝ) < (2:ℝ) ^ (1+u) - 1 := by linarith
  have hNu : (0:ℝ) ≤ (2:ℝ) ^ (3*u/4) / 2 + (2:ℝ) ^ (u/2) := by positivity
  rw [oddzeta_G, oddzeta_G]
  refine mul_le_mul_of_nonneg_left ?_ hl2
  have step1 : ((2:ℝ) ^ (3*v/4) / 2 + (2:ℝ) ^ (v/2)) / ((2:ℝ) ^ (1+v) - 1)
      ≤ (t * ((2:ℝ) ^ (3*u/4) / 2 + (2:ℝ) ^ (u/2))) /
        (t * ((2:ℝ) ^ (1+u) - 1)) := by
    refine div_le_div₀ (mul_nonneg ht0.le hNu) (by nlinarith [h34, h12])
      (mul_pos ht0 hDu) ?_
    rw [hDv]
    nlinarith [ht1]
  have step2 : (t * ((2:ℝ) ^ (3*u/4) / 2 + (2:ℝ) ^ (u/2))) /
      (t * ((2:ℝ) ^ (1+u) - 1))
      = ((2:ℝ) ^ (3*u/4) / 2 + (2:ℝ) ^ (u/2)) / ((2:ℝ) ^ (1+u) - 1) :=
    mul_div_mul_left _ _ ht0.ne'
  exact step1.trans (le_of_eq step2)

/-- The analytic lower bound for `1/u` from the TeX proof of `lem:oddzeta`:
`G(u) + log 2 · 2^u/((2^u − 1)(2^{1+u} − 1)) ≤ 1/u`, via three applications
of `\eqref{spot}`. -/
lemma oddzeta_G_le {u : ℝ} (hu : 0 < u) :
    oddzeta_G u + Real.log 2 * (2:ℝ) ^ u / (((2:ℝ) ^ u - 1) * ((2:ℝ) ^ (1+u) - 1))
      ≤ 1 / u := by
  set A := (2:ℝ) ^ (u/4) with hA
  have hA1 : 1 < A := by
    rw [hA]
    exact (Real.one_lt_rpow_iff_of_pos two_pos).mpr
      (Or.inl ⟨one_lt_two, by positivity⟩)
  have e2 : (2:ℝ) ^ (u/2) = A * A := by
    rw [hA, ← Real.rpow_add two_pos]
    congr 1
    ring
  have e3 : (2:ℝ) ^ (3*u/4) = A * A * A := by
    rw [hA, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1
    ring
  have e4 : (2:ℝ) ^ u = A * A * A * A := by
    rw [hA, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos,
      ← Real.rpow_add two_pos]
    congr 1
    ring
  have e5 : (2:ℝ) ^ (1+u) = 2 * (A * A * A * A) := by
    rw [Real.rpow_add two_pos, Real.rpow_one, e4]
  have spot1 : u * Real.log 2 * (A * A) ≤ A * A * A * A - 1 := by
    have h := oddzeta_spot hu.le
    rwa [e2, e4] at h
  have spot2 : u/2 * Real.log 2 * A ≤ A * A - 1 := by
    have h := oddzeta_spot (v := u/2) (by positivity)
    rw [show u/2/2 = u/4 by ring] at h
    rwa [← hA, e2] at h
  have hAA : (1:ℝ) < A * A := by nlinarith [sq_nonneg (A - 1)]
  have hAAAA : (1:ℝ) < (A * A) * (A * A) := by nlinarith [sq_nonneg (A * A - 1)]
  have hD2 : (0:ℝ) < 2 * (A * A * A * A) - 1 := by nlinarith [hAAAA]
  have hA4 : (0:ℝ) < A * A * A * A - 1 := by nlinarith [hAAAA]
  have huD : (0:ℝ) < u * (2 * (A * A * A * A) - 1) := mul_pos hu hD2
  rw [oddzeta_G, e2, e3, e4, e5]
  have hfirst : Real.log 2 * ((A*A*A/2 + A*A) / (2*(A*A*A*A) - 1))
      = u * Real.log 2 * (A*A*A/2 + A*A) / (u * (2*(A*A*A*A) - 1)) := by
    have hstep : u * Real.log 2 * (A*A*A/2 + A*A) / (u * (2*(A*A*A*A) - 1))
        = (Real.log 2 * (A*A*A/2 + A*A)) / (2*(A*A*A*A) - 1) := by
      rw [show u * Real.log 2 * (A*A*A/2 + A*A)
          = u * (Real.log 2 * (A*A*A/2 + A*A)) by ring,
        mul_div_mul_left _ _ hu.ne']
    rw [hstep]
    exact (mul_div_assoc _ _ _).symm
  have hsecond : Real.log 2 * (A*A*A*A) / ((A*A*A*A - 1) * (2*(A*A*A*A) - 1))
      ≤ A*A / (u * (2*(A*A*A*A) - 1)) := by
    rw [div_le_div_iff₀ (mul_pos hA4 hD2) huD]
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right spot1 (by positivity : (0:ℝ) ≤ A*A)) hD2.le]
  have hkey : u * Real.log 2 * (A*A*A/2 + A*A) + A*A ≤ 2*(A*A*A*A) - 1 := by
    nlinarith [spot1, mul_le_mul_of_nonneg_right spot2
      (by positivity : (0:ℝ) ≤ A*A), hA1]
  calc Real.log 2 * ((A*A*A/2 + A*A) / (2*(A*A*A*A) - 1)) +
      Real.log 2 * (A*A*A*A) / ((A*A*A*A - 1) * (2*(A*A*A*A) - 1))
      ≤ u * Real.log 2 * (A*A*A/2 + A*A) / (u * (2*(A*A*A*A) - 1)) +
        A*A / (u * (2*(A*A*A*A) - 1)) := add_le_add (le_of_eq hfirst) hsecond
    _ = (u * Real.log 2 * (A*A*A/2 + A*A) + A*A) / (u * (2*(A*A*A*A) - 1)) :=
        (add_div _ _ _).symm
    _ ≤ (2*(A*A*A*A) - 1) / (u * (2*(A*A*A*A) - 1)) :=
        div_le_div_of_nonneg_right hkey huD.le
    _ = 1 / u := by
        rw [mul_comm u (2*(A*A*A*A) - 1), ← div_div, div_self hD2.ne']

set_option maxHeartbeats 800000 in
-- Rewriting the interval bounds into a single rational inequality is elaboration-heavy.
/-- One interval check of TeX `\eqref{analytic}`: on `[a, b]`, rational lower
bounds for `3^a, 5^a, 7^a` (decreasing factors) and for the terms of `G(b)`
reduce the inequality to rational arithmetic and the logarithm bounds. -/
lemma oddzeta_interval_step {a b u x3 x5 x7 y34 y12 z : ℝ}
    (ha : 0 ≤ a) (hau : a ≤ u) (hub : u ≤ b)
    (hx3 : 1 ≤ x3) (hx5 : 1 ≤ x5) (hx7 : 1 ≤ x7)
    (_hy34 : 0 ≤ y34) (_hy12 : 0 ≤ y12)
    (hx3' : x3 ≤ Real.rpow 3 a) (hx5' : x5 ≤ Real.rpow 5 a)
    (hx7' : x7 ≤ Real.rpow 7 a)
    (hy34' : y34 ≤ Real.rpow 2 (3 * b / 4))
    (hy12' : y12 ≤ Real.rpow 2 (b / 2))
    (hz' : Real.rpow 2 (1 + b) ≤ z)
    (hnum :
      oddzeta_corrMajorant 3 x3 + oddzeta_corrMajorant 5 x5 +
        oddzeta_corrMajorant 7 x7 + 0.137 ≤
          Real.log 2 * ((y34 / 2 + y12) / (z - 1))) :
    oddzeta_corr 3 u + oddzeta_corr 5 u + oddzeta_corr 7 u + 0.137 ≤
      oddzeta_G u := by
  rw [Real.rpow_eq_pow] at hx3' hx5' hx7' hy34' hy12' hz'
  have hb0 : (0 : ℝ) ≤ b := ha.trans (hau.trans hub)
  have h3 : oddzeta_corr 3 u ≤ oddzeta_corrMajorant 3 x3 :=
    oddzeta_corr_le (by norm_num) hx3
      (hx3'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hau))
  have h5 : oddzeta_corr 5 u ≤ oddzeta_corrMajorant 5 x5 :=
    oddzeta_corr_le (by norm_num) hx5
      (hx5'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hau))
  have h7 : oddzeta_corr 7 u ≤ oddzeta_corrMajorant 7 x7 :=
    oddzeta_corr_le (by norm_num) hx7
      (hx7'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hau))
  have hGb : oddzeta_G b ≤ oddzeta_G u := oddzeta_G_antitone (ha.trans hau) hub
  have h2b : (2 : ℝ) ≤ (2 : ℝ) ^ (1 + b) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hDb : (0 : ℝ) < (2 : ℝ) ^ (1 + b) - 1 := by linarith
  have hGlow : Real.log 2 * ((y34 / 2 + y12) / (z - 1)) ≤ oddzeta_G b := by
    rw [oddzeta_G]
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg one_le_two)
    exact div_le_div₀ (by positivity) (by linarith) hDb (by linarith)
  linarith [h3, h5, h7, hGb, hGlow, hnum]

set_option maxHeartbeats 3200000 in
-- The 15 certified subinterval applications create a large elaboration term.
/-- The interval-arithmetic verification of TeX `\eqref{analytic}` on
`(0, 0.92]`, by the 15 subinterval checks. -/
lemma oddzeta_corr_C_le_G {u : ℝ} (hu0 : 0 ≤ u) (hu92 : u ≤ 0.92) :
    oddzeta_corr 3 u + oddzeta_corr 5 u + oddzeta_corr 7 u + 0.137 ≤
      oddzeta_G u := by
  rcases le_or_gt u (1/16) with hcur | h0
  · exact oddzeta_interval_step (a := 0) (b := 1/16) (by norm_num) hu0 hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.0000 (0) 0 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.0000 (0) 0 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.0000 (0) 0 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.03302 (3*(1/16)/4) 3 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.02189 ((1/16)/2) 1 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.08855 (1+(1/16)) 17 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (2/16) with hcur | h1
  · exact oddzeta_interval_step (a := 1/16) (b := 2/16) (by norm_num) h0.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.0710 (1/16) 1 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.1058 (1/16) 1 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.1293 (1/16) 1 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.06714 (3*(2/16)/4) 6 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.04427 ((2/16)/2) 2 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.18102 (1+(2/16)) 18 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (3/16) with hcur | h2
  · exact oddzeta_interval_step (a := 2/16) (b := 3/16) (by norm_num) h1.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.1472 (2/16) 2 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.2228 (2/16) 2 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.2753 (2/16) 2 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.10238 (3*(3/16)/4) 9 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.06714 ((3/16)/2) 3 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.27758 (1+(3/16)) 19 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (4/16) with hcur | h3
  · exact oddzeta_interval_step (a := 3/16) (b := 4/16) (by norm_num) h2.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.2287 (3/16) 3 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.3522 (3/16) 3 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.4403 (3/16) 3 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.13878 (3*(4/16)/4) 12 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.09050 ((4/16)/2) 4 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.37842 (1+(4/16)) 20 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (5/16) with hcur | h4
  · exact oddzeta_interval_step (a := 4/16) (b := 5/16) (by norm_num) h3.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.3160 (4/16) 4 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.4953 (4/16) 4 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.6265 (4/16) 4 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.17639 (3*(5/16)/4) 15 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.11438 ((5/16)/2) 5 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.48372 (1+(5/16)) 21 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (6/16) with hcur | h5
  · exact oddzeta_interval_step (a := 5/16) (b := 6/16) (by norm_num) h4.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.4096 (5/16) 5 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.6535 (5/16) 5 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 1.8369 (5/16) 5 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.21524 (3*(6/16)/4) 18 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.13878 ((6/16)/2) 6 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.59368 (1+(6/16)) 22 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (7/16) with hcur | h6
  · exact oddzeta_interval_step (a := 6/16) (b := 7/16) (by norm_num) h5.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.5098 (6/16) 6 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 1.8285 (6/16) 6 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 2.0744 (6/16) 6 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.25538 (3*(7/16)/4) 21 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.16372 ((7/16)/2) 7 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.70852 (1+(7/16)) 23 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (8/16) with hcur | h7
  · exact oddzeta_interval_step (a := 7/16) (b := 8/16) (by norm_num) h6.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.6171 (7/16) 7 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 2.0220 (7/16) 7 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 2.3427 (7/16) 7 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.29683 (3*(8/16)/4) 24 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.18920 ((8/16)/2) 8 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.82843 (1+(8/16)) 24 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (9/16) with hcur | h8
  · exact oddzeta_interval_step (a := 8/16) (b := 9/16) (by norm_num) h7.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.7320 (8/16) 8 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 2.2360 (8/16) 8 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 2.6457 (8/16) 8 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.33966 (3*(9/16)/4) 27 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.21524 ((9/16)/2) 9 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 2.95366 (1+(9/16)) 25 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (10/16) with hcur | h9
  · exact oddzeta_interval_step (a := 9/16) (b := 10/16) (by norm_num) h8.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.8551 (9/16) 9 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 2.4726 (9/16) 9 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 2.9879 (9/16) 9 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.38390 (3*(10/16)/4) 30 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.24185 ((10/16)/2) 10 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.08443 (1+(10/16)) 26 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (11/16) with hcur | h10
  · exact oddzeta_interval_step (a := 10/16) (b := 11/16) (by norm_num) h9.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 1.9870 (10/16) 10 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 2.7343 (10/16) 10 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 3.3743 (10/16) 10 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.42961 (3*(11/16)/4) 33 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.26905 ((11/16)/2) 11 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.22099 (1+(11/16)) 27 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (12/16) with hcur | h11
  · exact oddzeta_interval_step (a := 11/16) (b := 12/16) (by norm_num) h10.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 2.1282 (11/16) 11 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 3.0237 (11/16) 11 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 3.8107 (11/16) 11 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.47682 (3*(12/16)/4) 36 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.29683 ((12/16)/2) 12 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.36359 (1+(12/16)) 28 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (13/16) with hcur | h12
  · exact oddzeta_interval_step (a := 12/16) (b := 13/16) (by norm_num) h11.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 2.2795 (12/16) 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 3.3437 (12/16) 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 4.3035 (12/16) 12 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.52559 (3*(13/16)/4) 39 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.32523 ((13/16)/2) 13 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.51251 (1+(13/16)) 29 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  rcases le_or_gt u (14/16) with hcur | h13
  · exact oddzeta_interval_step (a := 13/16) (b := 14/16) (by norm_num) h12.le hcur
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 2.4415 (13/16) 13 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 3.6975 (13/16) 13 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 4.8600 (13/16) 13 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.57598 (3*(14/16)/4) 42 64 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.35425 ((14/16)/2) 14 32 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.66802 (1+(14/16)) 30 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
  · exact oddzeta_interval_step (a := 14/16) (b := 0.92) (by norm_num) h13.le hu92
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (oddzeta_le_rpow 3 2.6150 (14/16) 14 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 5 4.0888 (14/16) 14 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 7 5.4885 (14/16) 14 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.61328 (3*(0.92)/4) 69 100 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_le_rpow 2 1.37554 ((0.92)/2) 23 50 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (oddzeta_rpow_le 2 3.78424 (1+(0.92)) 48 25 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
      (by
        simp only [oddzeta_corrMajorant]
        linarith [Real.log_two_gt_d9, oddzeta_log_three_le, oddzeta_log_five_le,
          oddzeta_log_seven_le])
/-- The partial-sum form of TeX `lem:oddzeta` for `0 < u ≤ 0.92`: every finite
partial sum of the odd-prime series is at most `1/u`. -/
lemma oddzeta_partial_sum_le (u : ℝ) (hu : 0 < u) (hu92 : u ≤ 0.92)
    (s : Finset ℕ) :
    (∑ p ∈ s, if Nat.Prime p ∧ p ≠ 2 then
      Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) ≤ 1 / u := by
  classical
  rw [← Finset.sum_filter]
  set s' := s.filter (fun p => Nat.Prime p ∧ p ≠ 2) with hs'def
  have hs'mem : ∀ p ∈ s', Nat.Prime p ∧ p ≠ 2 :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have h3le : ∀ p ∈ s', 3 ≤ p := by
    intro p hp
    have h1 := (hs'mem p hp).1.two_le
    have h2 := (hs'mem p hp).2
    omega
  have hsplit : (∑ p ∈ s', Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u))
      = (∑ p ∈ s', Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) +
        ∑ p ∈ s', oddzeta_corr (p : ℝ) u := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p hp => oddzeta_term_split (h3le p hp) hu
  have hphi := oddzeta_odd_phi_sum_le u hu s' hs'mem
  have hcorr : (∑ p ∈ s', oddzeta_corr (p : ℝ) u) ≤
      oddzeta_corr 3 u + oddzeta_corr 5 u + oddzeta_corr 7 u + 0.137 := by
    have hsplit2 := (Finset.sum_filter_add_sum_filter_not s' (fun p => p ≤ 7)
      (fun p => oddzeta_corr (p : ℝ) u)).symm
    have hsmall : (∑ p ∈ s'.filter (fun p => p ≤ 7), oddzeta_corr (p : ℝ) u) ≤
        oddzeta_corr 3 u + oddzeta_corr 5 u + oddzeta_corr 7 u := by
      have hsub : s'.filter (fun p => p ≤ 7) ⊆ ({3, 5, 7} : Finset ℕ) := by
        intro p hp
        have h1 := Finset.mem_filter.mp hp
        have h2 := hs'mem p h1.1
        have h3 := h3le p h1.1
        have h7 : p ≤ 7 := h1.2
        have h4 : p = 3 ∨ p = 5 ∨ p = 7 := by
          have hp' := h2.1
          interval_cases p
          · exact Or.inl rfl
          · exact absurd hp' (by norm_num)
          · exact Or.inr (Or.inl rfl)
          · exact absurd hp' (by norm_num)
          · exact Or.inr (Or.inr rfl)
        rcases h4 with rfl | rfl | rfl <;> decide
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · intro p hp _
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
          fin_cases hp <;> norm_num
        exact oddzeta_corr_nonneg hp3 hu.le
      · have h35 : (3 : ℕ) ∉ ({5, 7} : Finset ℕ) := by decide
        have h57 : (5 : ℕ) ∉ ({7} : Finset ℕ) := by decide
        rw [Finset.sum_insert h35, Finset.sum_insert h57, Finset.sum_singleton]
        push_cast
        linarith
    have hbig : (∑ p ∈ s'.filter (fun p => ¬ p ≤ 7), oddzeta_corr (p : ℝ) u) ≤
        0.137 := by
      have hstep : (∑ p ∈ s'.filter (fun p => ¬ p ≤ 7), oddzeta_corr (p : ℝ) u) ≤
          ∑ p ∈ s'.filter (fun p => ¬ p ≤ 7),
            Real.log (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        have h7 : 7 < p := by
          have := (Finset.mem_filter.mp hp).2
          omega
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
        exact oddzeta_corr_le_one hp3 hu.le
      refine hstep.trans (oddzeta_C_bound _ ?_)
      intro p hp
      have h1 := Finset.mem_filter.mp hp
      exact ⟨(hs'mem p h1.1).1, by omega⟩
    linarith [hsplit2, hsmall, hbig]
  have hG := oddzeta_corr_C_le_G hu.le hu92
  have hGle := oddzeta_G_le hu
  have h2u1 : (1:ℝ) < (2:ℝ) ^ u :=
    (Real.one_lt_rpow_iff_of_pos two_pos).mpr (Or.inl ⟨one_lt_two, hu⟩)
  have h2u1' : (1:ℝ) < (2:ℝ) ^ (1+u) :=
    (Real.one_lt_rpow_iff_of_pos two_pos).mpr (Or.inl ⟨one_lt_two, by linarith⟩)
  have hD : Real.log 2 / ((2:ℝ) ^ u - 1) - Real.log 2 / ((2:ℝ) ^ (1+u) - 1)
      = Real.log 2 * (2:ℝ) ^ u / (((2:ℝ) ^ u - 1) * ((2:ℝ) ^ (1+u) - 1)) := by
    have h3 : (2:ℝ) ^ (1+u) = 2 * (2:ℝ) ^ u := by
      rw [Real.rpow_add two_pos, Real.rpow_one]
    have hne1 : (2:ℝ) ^ u - 1 ≠ 0 := ne_of_gt (by linarith)
    have hne2 : 2 * (2:ℝ) ^ u - 1 ≠ 0 := by
      rw [← h3]
      exact ne_of_gt (by linarith)
    rw [h3, div_sub_div _ _ hne1 hne2]
    congr 1
    ring
  calc (∑ p ∈ s', Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u))
      = (∑ p ∈ s', Real.log (p : ℝ) / ((p : ℝ) ^ (1+u) - 1)) +
        ∑ p ∈ s', oddzeta_corr (p : ℝ) u := hsplit
    _ ≤ (Real.log 2 / ((2:ℝ) ^ u - 1) - Real.log 2 / ((2:ℝ) ^ (1+u) - 1)) +
        (oddzeta_corr 3 u + oddzeta_corr 5 u + oddzeta_corr 7 u + 0.137) :=
      add_le_add hphi hcorr
    _ ≤ Real.log 2 * (2:ℝ) ^ u / (((2:ℝ) ^ u - 1) * ((2:ℝ) ^ (1+u) - 1)) +
        oddzeta_G u := by
      rw [← hD]
      linarith [hG]
    _ ≤ 1 / u := by linarith [hGle]

/-- The per-term shift inequality reducing `u > 0.92` to `u = 0.92`:
`u p^{-u} ≤ 0.92 p^{-0.92}` for `p ≥ 3`. -/
lemma oddzeta_term_shift {p : ℕ} (hp3 : 3 ≤ p) {u : ℝ} (hu : 0.92 ≤ u) :
    u * (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)) ≤
      0.92 * (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92)) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 1.0974 ≤ Real.log (p : ℝ) :=
    le_trans oddzeta_le_log_three (Real.log_le_log (by norm_num) hpR)
  have hsplit : Real.rpow (p : ℝ) u = Real.rpow (p : ℝ) 0.92 * (p : ℝ) ^ (u - 0.92) := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_add hp0]
    congr 1
    ring
  have hexp : 1 + (u - 0.92) * Real.log (p : ℝ) ≤ (p : ℝ) ^ (u - 0.92) := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log (p : ℝ) * (u - 0.92))
    calc 1 + (u - 0.92) * Real.log (p : ℝ)
        = Real.log (p : ℝ) * (u - 0.92) + 1 := by ring
      _ ≤ Real.exp (Real.log (p : ℝ) * (u - 0.92)) := h
  have hkey : u ≤ 0.92 * (p : ℝ) ^ (u - 0.92) := by
    have hcoeff : (0:ℝ) ≤ 0.92 * Real.log (p : ℝ) - 1 := by nlinarith [hlogp]
    have hprod : 0 ≤ (u - 0.92) * (0.92 * Real.log (p : ℝ) - 1) :=
      mul_nonneg (by linarith) hcoeff
    nlinarith [hexp, hprod]
  have hX92 : (0:ℝ) < Real.rpow (p : ℝ) 0.92 := Real.rpow_pos_of_pos hp0 _
  have hY : (0:ℝ) < (p : ℝ) ^ (u - 0.92) := Real.rpow_pos_of_pos hp0 _
  have hT : (0:ℝ) ≤ Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) := by
    have h1 : (0:ℝ) < (p : ℝ) - 2 := by linarith
    have h2 : (0:ℝ) ≤ Real.log (p : ℝ) := by linarith
    positivity
  have h2 : Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
      = (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92)) /
        (p : ℝ) ^ (u - 0.92) := by
    rw [hsplit]
    have hne1 : ((p : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
    have hne2 : Real.rpow (p : ℝ) 0.92 ≠ 0 := ne_of_gt hX92
    have hne3 : ((p : ℝ)) ^ (u - 0.92) ≠ 0 := ne_of_gt hY
    rw [Real.rpow_eq_pow] at hne2 ⊢
    field_simp
  rw [h2, ← mul_div_assoc, div_le_iff₀ hY]
  calc u * (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92))
      ≤ (0.92 * (p : ℝ) ^ (u - 0.92)) *
        (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92)) :=
      mul_le_mul_of_nonneg_right hkey hT
    _ = 0.92 * (Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92)) *
        (p : ℝ) ^ (u - 0.92) := by ring

/-- TeX Lemma `lem:oddzeta`, unconditional core form:
`u * oddBM_primeBetaSeries u ≤ 1` for all `u > 0`. -/
lemma oddzeta_beta_series_bound :
    ∀ u : ℝ, 0 < u -> u * oddBM_primeBetaSeries u ≤ 1 := by
  have hnonneg : ∀ v : ℝ, ∀ p : ℕ,
      0 ≤ (if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) v) else 0) := by
    intro v p
    split_ifs with h
    · exact oddBM_primeBetaSeries_term_nonneg h.1 h.2 v
    · exact le_rfl
  have hmain : ∀ u : ℝ, 0 < u → u ≤ 0.92 → u * oddBM_primeBetaSeries u ≤ 1 := by
    intro u hu hu92
    have htsum : oddBM_primeBetaSeries u ≤ 1 / u := by
      rw [oddBM_primeBetaSeries]
      exact tsum_le_of_sum_le' (by positivity)
        (fun s => oddzeta_partial_sum_le u hu hu92 s)
    calc u * oddBM_primeBetaSeries u ≤ u * (1 / u) :=
          mul_le_mul_of_nonneg_left htsum hu.le
      _ = 1 := by field_simp
  intro u hu
  rcases le_or_gt u 0.92 with h | h
  · exact hmain u hu h
  · have h92 : (0:ℝ) < 0.92 := by norm_num
    have hterm : ∀ p : ℕ,
        u * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) ≤
        0.92 * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
      intro p
      split_ifs with hp
      · have hp3 : 3 ≤ p := by
          have h1 := hp.1.two_le
          have h2 := hp.2
          omega
        exact oddzeta_term_shift hp3 h.le
      · simp
    have hsum92 : Summable (fun p : ℕ =>
        if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
      refine summable_of_sum_le (c := 1 / 0.92) (fun p => hnonneg 0.92 p) ?_
      intro v
      exact oddzeta_partial_sum_le 0.92 h92 le_rfl v
    have hsumu : Summable (fun p : ℕ =>
        u * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0)) := by
      refine Summable.of_nonneg_of_le
        (fun p => mul_nonneg (by linarith) (hnonneg u p)) hterm
        (hsum92.mul_left 0.92)
    calc u * oddBM_primeBetaSeries u
        = ∑' p : ℕ, u * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) := by
          rw [oddBM_primeBetaSeries, tsum_mul_left]
      _ ≤ ∑' p : ℕ, 0.92 * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) :=
          hsumu.tsum_le_tsum hterm (hsum92.mul_left 0.92)
      _ = 0.92 * oddBM_primeBetaSeries 0.92 := by
          rw [oddBM_primeBetaSeries, tsum_mul_left]
      _ ≤ 1 := hmain 0.92 h92 le_rfl

/-- Paper Lemma `lem:oddzeta` (TeX `\eqref{om2}`), now unconditional: for every
`u > 0`, `u * ∑_{p ≥ 3} log p / ((p − 2) p^u) ≤ 1`. -/
lemma lemma_oddzeta :
    ∀ u : ℝ, 0 < u ->
      u * (∑' p : ℕ,
        if Nat.Prime p ∧ 3 ≤ p then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
        else 0) ≤ 1 :=
  oddBM_primeBetaSeries_bound_three_le_form oddzeta_beta_series_bound

/-- Finite-sum form of `lemma_oddzeta`, convenient under an integral. -/
lemma oddzeta_finset_sum_bound (u : ℝ) (hu : 0 < u) (S : Finset ℕ) :
    u * (∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
      Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) ≤ 1 := by
  rcases le_or_gt u 0.92 with hu92 | hu92
  · exact (mul_le_mul_of_nonneg_left
      (oddzeta_partial_sum_le u hu hu92 S) hu.le).trans_eq (by field_simp)
  · have hterm : ∀ p : ℕ,
        u * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) ≤
        0.92 * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
      intro p
      split_ifs with hp
      · exact oddzeta_term_shift (by have := hp.1.two_le; omega) hu92.le
      · simp
    calc
      u * (∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) =
          ∑ p ∈ S, u * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) /
              (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ S, 0.92 * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) /
              (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) :=
        Finset.sum_le_sum fun p _ => hterm p
      _ = 0.92 * (∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) /
              (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left
          (oddzeta_partial_sum_le 0.92 (by norm_num) le_rfl S)
          (by norm_num)).trans_eq (by norm_num)

/-- The odd-prime series of `lem:oddzeta` is summable for every `u > 0`. -/
lemma oddzeta_series_summable (u : ℝ) (hu : 0 < u) :
    Summable (fun p : ℕ =>
      if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
      else 0) := by
  have hnonneg : ∀ v : ℝ, ∀ p : ℕ,
      0 ≤ (if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) v) else 0) := by
    intro v p
    split_ifs with h
    · exact oddBM_primeBetaSeries_term_nonneg h.1 h.2 v
    · exact le_rfl
  rcases le_or_gt u 0.92 with h | h
  · exact summable_of_sum_le (hnonneg u) (fun v => oddzeta_partial_sum_le u hu h v)
  · have hsum92 : Summable (fun p : ℕ =>
        if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) :=
      summable_of_sum_le (hnonneg 0.92)
        (fun v => oddzeta_partial_sum_le 0.92 (by norm_num) le_rfl v)
    refine Summable.of_nonneg_of_le (hnonneg u) (fun p => ?_)
      (hsum92.mul_left (0.92 / u))
    have h1 : u * (if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) ≤
        0.92 * (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
      split_ifs with hp
      · exact oddzeta_term_shift (by have := hp.1.two_le; have := hp.2; omega) h.le
      · simp
    calc (if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0)
        = u * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u) else 0) / u := by
          field_simp
      _ ≤ 0.92 * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) / u :=
          div_le_div_of_nonneg_right h1 hu.le
      _ = 0.92 / u * (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) 0.92) else 0) := by
          ring

/-- The `tsum` form of `lemma_oddzeta`: the odd-prime series is at most `1/u`. -/
lemma oddzeta_series_le_inv (u : ℝ) (hu : 0 < u) :
    (∑' p : ℕ,
      if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) u)
      else 0) ≤ 1 / u := by
  have h := oddzeta_beta_series_bound u hu
  rw [oddBM_primeBetaSeries] at h
  rw [le_div_iff₀ hu]
  linarith

/-- The aggregated exponential-sum estimate feeding the Odd Banks--Martin
sub-invariance bound (TeX lines 863--867): for `s ≥ 0` with `t + s > 0`,
`∑_{p ∈ Q} log p/((p−2) p^{t + β_p s}) ≤ 1/(t + s)`, since `β_p ≥ 1` lets each
term be compared with the `lem:oddzeta` series at `u = t + s`. -/
lemma oddBM_beta_exponential_sum_le {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q)
    [DecidablePred (fun p : ℕ => p ∈ Q)]
    {t s : ℝ} (hs : 0 ≤ s) (hts : 0 < t + s) :
    (∑' p : ℕ,
      if p ∈ Q then
        Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) (t + oddBM_beta p * s))
      else 0) ≤ 1 / (t + s) := by
  have hbound : ∀ p : ℕ,
      (if p ∈ Q then
        Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) (t + oddBM_beta p * s))
      else 0) ≤
      (if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * Real.rpow (p : ℝ) (t + s))
      else 0) := by
    intro p
    by_cases hp : p ∈ Q
    · have hprime := hQ.prime hp
      have hne2 := hQ.ne_two hp
      rw [if_pos hp, if_pos ⟨hprime, hne2⟩]
      have h2 : (2 : ℝ) < (p : ℝ) := by
        exact_mod_cast lt_of_le_of_ne hprime.two_le hne2.symm
      have hβ : 1 ≤ oddBM_beta p := oddBM_beta_ge_one hprime hne2
      have hexp : t + s ≤ t + oddBM_beta p * s := by nlinarith
      have hX : Real.rpow (p : ℝ) (t + s) ≤
          Real.rpow (p : ℝ) (t + oddBM_beta p * s) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      have hXpos : 0 < Real.rpow (p : ℝ) (t + s) :=
        Real.rpow_pos_of_pos (by linarith) _
      exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith))
        (mul_pos (by linarith) hXpos)
        (mul_le_mul_of_nonneg_left hX (by linarith))
    · rw [if_neg hp]
      split_ifs with h
      · exact oddBM_primeBetaSeries_term_nonneg h.1 h.2 _
      · exact le_rfl
  have hQnonneg : ∀ p : ℕ,
      0 ≤ (if p ∈ Q then
        Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) (t + oddBM_beta p * s))
      else 0) := by
    intro p
    split_ifs with hp
    · exact oddBM_primeBetaSeries_term_nonneg (hQ.prime hp) (hQ.ne_two hp) _
    · exact le_rfl
  have hsumR := oddzeta_series_summable (t + s) hts
  have hsumL : Summable (fun p : ℕ =>
      if p ∈ Q then
        Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) (t + oddBM_beta p * s))
      else 0) :=
    Summable.of_nonneg_of_le hQnonneg hbound hsumR
  exact (hsumL.tsum_le_tsum hbound hsumR).trans (oddzeta_series_le_inv (t + s) hts)

/-- The normalization factor
`λ(n) = ∑_{p ∣ n} v_p(n) β_p log p` for the Odd Banks--Martin chain,
restricted to primes in `Q`. -/
noncomputable def oddBM_lambda (Q : Set ℕ) (n : ℕ) : ℝ :=
  by
    classical
    exact
      ∑ p ∈ n.factorization.support,
        if p ∈ Q then (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) else 0

lemma oddBM_lambda_nonneg {Q : Set ℕ} (hQ : IsSetOfOddPrimes Q) (n : ℕ) :
    0 ≤ oddBM_lambda Q n := by
  classical
  rw [oddBM_lambda]
  refine Finset.sum_nonneg ?_
  intro p hp
  by_cases hpQ : p ∈ Q
  · have hfac_nonneg : 0 ≤ (n.factorization p : ℝ) := by
      exact_mod_cast Nat.zero_le (n.factorization p)
    have hbeta_nonneg : 0 ≤ oddBM_beta p :=
      le_of_lt (oddBM_beta_pos_of_mem hQ hpQ)
    have hp_one_real : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (hQ.one_lt hpQ)
    have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
      le_of_lt (Real.log_pos hp_one_real)
    have hterm :
        0 ≤ (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) :=
      mul_nonneg (mul_nonneg hfac_nonneg hbeta_nonneg) hlog_nonneg
    simpa [hpQ] using hterm
  · simp [hpQ]

lemma oddBM_lambda_eq_finsupp_sum (Q : Set ℕ) (n : ℕ) :
    oddBM_lambda Q n = n.factorization.sum (fun p e =>
      Q.indicator (fun p => (e : ℝ) * oddBM_beta p * Real.log (p : ℝ)) p) := by
  classical
  rw [oddBM_lambda]
  rfl

lemma oddBM_lambda_prime {Q : Set ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hpQ : p ∈ Q) :
    oddBM_lambda Q p = oddBM_beta p * Real.log (p : ℝ) := by
  classical
  rw [oddBM_lambda_eq_finsupp_sum, hp.factorization,
    Finsupp.sum_single_index (by simp [Set.indicator_of_mem hpQ])]
  simp [Set.indicator_of_mem hpQ]

/-- Multiplying by an allowed prime adds one `βₚ log p` increment to the
Odd Banks--Martin normalization. -/
lemma oddBM_lambda_mul_prime {Q : Set ℕ} {m p : ℕ}
    (hm : m ≠ 0) (hp : Nat.Prime p) (hpQ : p ∈ Q) :
    oddBM_lambda Q (m * p) =
      oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ) := by
  classical
  rw [oddBM_lambda_eq_finsupp_sum, Nat.factorization_mul hm hp.ne_zero,
    Finsupp.sum_add_index]
  · rw [← oddBM_lambda_eq_finsupp_sum, ← oddBM_lambda_eq_finsupp_sum,
      oddBM_lambda_prime hp hpQ]
  · intro q hq
    simp [Set.indicator]
  · intro q hq a b
    by_cases hqQ : q ∈ Q
    · simp [Set.indicator_of_mem hqQ, Nat.cast_add]
      ring
    · simp [Set.indicator_of_notMem hqQ]

/-- For an integer composed of primes in `Q`, the Odd Banks--Martin
normalization is `log n` plus the correction coming from `β_p - 1`. -/
lemma oddBM_lambda_eq_log_add_correction {Q : Set ℕ} {n : ℕ}
    (hn : n ∈ restrict_to_primes (Set.univ : Set ℕ) Q) :
    oddBM_lambda Q n =
      Real.log (n : ℝ) +
        ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (oddBM_beta p - 1) *
            Real.log (p : ℝ) := by
  classical
  have hpQ : ∀ p ∈ n.factorization.support, p ∈ Q := by
    intro p hp
    have hp_mem : p ∈ n.primeFactors := by simpa using hp
    exact hn.2 p (Nat.mem_primeFactors.mp hp_mem).1
      (Nat.mem_primeFactors.mp hp_mem).2.1
  rw [oddBM_lambda]
  calc
    (∑ p ∈ n.factorization.support,
        if p ∈ Q then
          (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
        else 0) =
        ∑ p ∈ n.factorization.support,
          ((n.factorization p : ℝ) * Real.log (p : ℝ) +
            (n.factorization p : ℝ) * (oddBM_beta p - 1) *
              Real.log (p : ℝ)) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [if_pos (hpQ p hp)]
      ring
    _ = (∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * Real.log (p : ℝ)) +
        ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (oddBM_beta p - 1) *
            Real.log (p : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = Real.log (n : ℝ) +
        ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (oddBM_beta p - 1) *
            Real.log (p : ℝ) := by
      congr 1
      simpa [Finsupp.sum] using (Real.log_nat_eq_sum_factorization n).symm

/-- The algebraic first half of the Odd Banks--Martin sub-invariance estimate
(TeX lines 846--850): the `β_p / p` contribution is exactly
`(λ(n) - log n) / 2`. -/
lemma oddBM_beta_over_prime_sum_eq_half_correction {Q : Set ℕ} {n : ℕ}
    [DecidablePred (fun p : ℕ => p ∈ Q)]
    (hQ : IsSetOfOddPrimes Q)
    (hn : n ∈ restrict_to_primes (Set.univ : Set ℕ) Q) :
    (∑ p ∈ n.factorization.support,
      if p ∈ Q then
        (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) / (p : ℝ)
      else 0) =
      (oddBM_lambda Q n - Real.log (n : ℝ)) / 2 := by
  classical
  have hpQ : ∀ p ∈ n.factorization.support, p ∈ Q := by
    intro p hp
    have hp_mem : p ∈ n.primeFactors := by simpa using hp
    exact hn.2 p (Nat.mem_primeFactors.mp hp_mem).1
      (Nat.mem_primeFactors.mp hp_mem).2.1
  rw [oddBM_lambda_eq_log_add_correction hn]
  calc
    (∑ p ∈ n.factorization.support,
        if p ∈ Q then
          (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) / (p : ℝ)
        else 0) =
        ∑ p ∈ n.factorization.support,
          ((n.factorization p : ℝ) * (oddBM_beta p - 1) *
            Real.log (p : ℝ)) / 2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpQ' := hpQ p hp
      rw [if_pos hpQ']
      calc
        (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) / (p : ℝ) =
            (n.factorization p : ℝ) * (oddBM_beta p / (p : ℝ)) *
              Real.log (p : ℝ) := by ring
        _ = (n.factorization p : ℝ) * ((oddBM_beta p - 1) / 2) *
              Real.log (p : ℝ) := by
            rw [oddBM_beta_div_eq_sub_one_half
              (hQ.prime hpQ') (hQ.ne_two hpQ')]
        _ = ((n.factorization p : ℝ) * (oddBM_beta p - 1) *
              Real.log (p : ℝ)) / 2 := by ring
    _ = (∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (oddBM_beta p - 1) *
            Real.log (p : ℝ)) / 2 := by
      rw [Finset.sum_div]
    _ = (Real.log (n : ℝ) +
          (∑ p ∈ n.factorization.support,
            (n.factorization p : ℝ) * (oddBM_beta p - 1) *
              Real.log (p : ℝ)) - Real.log (n : ℝ)) / 2 := by
      ring

/-- Normalized form of the first Odd Banks--Martin contribution. -/
lemma oddBM_normalized_beta_over_prime_sum {Q : Set ℕ} {n : ℕ}
    [DecidablePred (fun p : ℕ => p ∈ Q)]
    (hQ : IsSetOfOddPrimes Q)
    (hn : n ∈ restrict_to_primes (Set.univ : Set ℕ) Q)
    (hlambda : oddBM_lambda Q n ≠ 0) :
    (∑ p ∈ n.factorization.support,
      if p ∈ Q then
        (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
          ((p : ℝ) * oddBM_lambda Q n)
      else 0) =
      1 / 2 - Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
  classical
  calc
    (∑ p ∈ n.factorization.support,
        if p ∈ Q then
          (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
            ((p : ℝ) * oddBM_lambda Q n)
        else 0) =
        (∑ p ∈ n.factorization.support,
          if p ∈ Q then
            (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
              (p : ℝ)
          else 0) / oddBM_lambda Q n := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun p hp => ?_
      by_cases hpQ : p ∈ Q
      · rw [if_pos hpQ, if_pos hpQ]
        ring
      · rw [if_neg hpQ, if_neg hpQ, zero_div]
    _ = ((oddBM_lambda Q n - Real.log (n : ℝ)) / 2) /
        oddBM_lambda Q n := by
      rw [oddBM_beta_over_prime_sum_eq_half_correction hQ hn]
    _ = 1 / 2 - Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
      field_simp [hlambda]

/-- The first sum in the Odd Banks--Martin sub-invariance calculation
(TeX line 846), restricted to the finite prime support of `n`. -/
noncomputable def oddBM_firstContribution (Q : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ p ∈ n.factorization.support,
      if p ∈ Q then
        Real.log (n : ℝ) * (n.factorization p : ℝ) * oddBM_beta p *
            Real.log (p : ℝ) /
          ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
            (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)))
      else 0

/-- The infinite incoming-prime sum in the second Odd Banks--Martin
sub-invariance contribution (TeX line 852). -/
noncomputable def oddBM_secondContribution (Q : Set ℕ) (n : ℕ) : ℝ :=
  by
    classical
    exact ∑' p : ℕ, if p ∈ Q then
      Real.log (n : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
        ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
          (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)))
      else 0

lemma oddBM_lambda_pos_of_allowed_factor {Q : Set ℕ} {n p : ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hp : p ∈ n.factorization.support) (hpQ : p ∈ Q) :
    0 < oddBM_lambda Q n := by
  classical
  rw [oddBM_lambda]
  refine Finset.sum_pos' ?_ ?_
  · intro q hq
    by_cases hqQ : q ∈ Q
    · have hfac_nonneg : 0 ≤ (n.factorization q : ℝ) := by
        exact_mod_cast Nat.zero_le (n.factorization q)
      have hbeta_nonneg : 0 ≤ oddBM_beta q :=
        le_of_lt (oddBM_beta_pos_of_mem hQ hqQ)
      have hq_one_real : (1 : ℝ) < (q : ℝ) := by
        exact_mod_cast (hQ.one_lt hqQ)
      have hlog_nonneg : 0 ≤ Real.log (q : ℝ) :=
        le_of_lt (Real.log_pos hq_one_real)
      have hterm :
          0 ≤ (n.factorization q : ℝ) * oddBM_beta q * Real.log (q : ℝ) :=
        mul_nonneg (mul_nonneg hfac_nonneg hbeta_nonneg) hlog_nonneg
      simpa [hqQ] using hterm
    · simp [hqQ]
  · refine ⟨p, hp, ?_⟩
    have hfac_ne : n.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    have hfac_pos_nat : 0 < n.factorization p :=
      Nat.pos_of_ne_zero hfac_ne
    have hfac_pos : 0 < (n.factorization p : ℝ) := by
      exact_mod_cast hfac_pos_nat
    have hbeta_pos : 0 < oddBM_beta p := oddBM_beta_pos_of_mem hQ hpQ
    have hp_one_real : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (hQ.one_lt hpQ)
    have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_one_real
    have hterm :
        0 < (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) :=
      mul_pos (mul_pos hfac_pos hbeta_pos) hlog_pos
    simpa [hpQ] using hterm

lemma oddBM_state_succ_exists_allowed_factor {k n : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_state (k + 1) Q) :
    ∃ p : ℕ, p ∈ n.factorization.support ∧ p ∈ Q := by
  have hn' : n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q := by
    simpa [oddBM_state] using hn
  have hnOmega : k + 1 ≤ ArithmeticFunction.cardFactors n := by
    simpa [omega_ge_layer] using hn'.1
  have hcard_pos : 0 < ArithmeticFunction.cardFactors n := by
    omega
  have hsum_pos :
      0 < n.factorization.sum fun _ k => k := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization] at hcard_pos
    exact hcard_pos
  have hsupport_nonempty : ∃ p : ℕ, p ∈ n.factorization.support := by
    by_contra hnone
    have hsum_zero :
        n.factorization.sum (fun _ k => k) = 0 := by
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero ?_
      intro p hp
      exact False.elim (hnone ⟨p, hp⟩)
    exact (Nat.ne_of_gt hsum_pos) hsum_zero
  rcases hsupport_nonempty with ⟨p, hp⟩
  have hp_mem_primeFactors : p ∈ n.primeFactors := by
    simpa using hp
  have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem_primeFactors).1
  have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem_primeFactors).2.1
  exact ⟨p, hp, hn'.2 p hp_prime hp_dvd⟩

lemma oddBM_state_one_lt {k n : ℕ} {Q : Set ℕ} (hk : 1 ≤ k)
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state k Q) : 1 < n := by
  have hn' : n ∈ oddBM_state (k - 1 + 1) Q := by
    simpa [Nat.sub_add_cancel hk] using hn
  rcases oddBM_state_succ_exists_allowed_factor hn' with ⟨p, hp, hpQ⟩
  exact (hQ.one_lt hpQ).trans_le (Nat.le_of_dvd
    (oddBM_state_positive_of_odd_primes hQ hn)
    (Nat.mem_primeFactors.mp (by simpa using hp)).2.1)

lemma oddBM_lambda_ne_zero_of_mem_oddBM_state_succ {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state (k + 1) Q) :
    oddBM_lambda Q n ≠ 0 := by
  rcases oddBM_state_succ_exists_allowed_factor hn with ⟨p, hp, hpQ⟩
  exact ne_of_gt (oddBM_lambda_pos_of_allowed_factor hQ hp hpQ)

/-- The complete estimate for the first contribution in the Odd
Banks--Martin sub-invariance proof (TeX lines 846--850). -/
lemma oddBM_firstContribution_le {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state (k + 1) Q) :
    oddBM_firstContribution Q n ≤
      1 / 2 - Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
  classical
  have hn' : n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q := by
    simpa [oddBM_state] using hn
  have hnQ : n ∈ restrict_to_primes (Set.univ : Set ℕ) Q :=
    ⟨by simp, hn'.2⟩
  rcases oddBM_state_succ_exists_allowed_factor hn with ⟨p₀, hp₀, hp₀Q⟩
  have hn_pos : 0 < n := oddBM_state_positive_of_odd_primes hQ hn
  have hp₀_dvd : p₀ ∣ n :=
    (Nat.mem_primeFactors.mp (by simpa using hp₀)).2.1
  have hn_one : 1 < n :=
    (hQ.one_lt hp₀Q).trans_le (Nat.le_of_dvd hn_pos hp₀_dvd)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn_one)
  have hlambda : 0 < oddBM_lambda Q n :=
    oddBM_lambda_pos_of_allowed_factor hQ hp₀ hp₀Q
  calc
    oddBM_firstContribution Q n ≤
        ∑ p ∈ n.factorization.support,
          if p ∈ Q then
            (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
              ((p : ℝ) * oddBM_lambda Q n)
          else 0 := by
      rw [oddBM_firstContribution]
      refine Finset.sum_le_sum fun p hp => ?_
      have hp' := Nat.mem_primeFactors.mp (by simpa using hp)
      have hp_prime : Nat.Prime p := hp'.1
      have hp_dvd : p ∣ n := hp'.2.1
      have hpQ : p ∈ Q := hn'.2 p hp_prime hp_dvd
      rw [if_pos hpQ, if_pos hpQ]
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_prime.pos
      have hlogp : 0 < Real.log (p : ℝ) :=
        Real.log_pos (by exact_mod_cast hQ.one_lt hpQ)
      have hbeta : 0 < oddBM_beta p := oddBM_beta_pos_of_mem hQ hpQ
      have hbetaLog : 0 ≤ oddBM_beta p * Real.log (p : ℝ) :=
        mul_nonneg hbeta.le hlogp.le
      rw [div_le_div_iff₀
        (mul_pos (mul_pos hp_pos (add_pos hlogn hlogp))
          (add_pos_of_pos_of_nonneg hlambda hbetaLog))
        (mul_pos hp_pos hlambda)]
      have hcore :
          Real.log (n : ℝ) * oddBM_lambda Q n ≤
            (Real.log (n : ℝ) + Real.log (p : ℝ)) *
              (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)) :=
        mul_le_mul (le_add_of_nonneg_right hlogp.le)
          (le_add_of_nonneg_right hbetaLog) hlambda.le
            (add_pos hlogn hlogp).le
      calc
        Real.log (n : ℝ) * (n.factorization p : ℝ) * oddBM_beta p *
              Real.log (p : ℝ) * ((p : ℝ) * oddBM_lambda Q n) =
            ((n.factorization p : ℝ) * oddBM_beta p *
              Real.log (p : ℝ) * (p : ℝ)) *
                (Real.log (n : ℝ) * oddBM_lambda Q n) := by ring
        _ ≤ ((n.factorization p : ℝ) * oddBM_beta p *
              Real.log (p : ℝ) * (p : ℝ)) *
                ((Real.log (n : ℝ) + Real.log (p : ℝ)) *
                  (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ))) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) *
              ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
                (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ))) := by ring
    _ = 1 / 2 - Real.log (n : ℝ) / (2 * oddBM_lambda Q n) :=
      oddBM_normalized_beta_over_prime_sum hQ hnQ hlambda.ne'

lemma oddBM_firstContribution_finset_le {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state (k + 1) Q)
    (S : Finset ℕ) :
    (∑ p ∈ S, Q.indicator (fun p =>
      Real.log (n : ℝ) * (n.factorization p : ℝ) * oddBM_beta p *
          Real.log (p : ℝ) /
        ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
          (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)))) p) ≤
      oddBM_firstContribution Q n := by
  classical
  let f : ℕ → ℝ := fun p => Q.indicator (fun p =>
    Real.log (n : ℝ) * (n.factorization p : ℝ) * oddBM_beta p *
        Real.log (p : ℝ) /
      ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
        (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)))) p
  have hnonneg : ∀ p, 0 ≤ f p := by
    intro p
    by_cases hpQ : p ∈ Q
    · simp only [f, Set.indicator_of_mem hpQ]
      have hn_pos := oddBM_state_positive_of_odd_primes hQ hn
      have hn_one : 1 < n := by
        rcases oddBM_state_succ_exists_allowed_factor hn with ⟨q, hq, hqQ⟩
        exact (hQ.one_lt hqQ).trans_le (Nat.le_of_dvd hn_pos
          (Nat.mem_primeFactors.mp (by simpa using hq)).2.1)
      have hlogn := Real.log_pos (by exact_mod_cast hn_one : (1 : ℝ) < n)
      have hlogp := Real.log_pos (by exact_mod_cast hQ.one_lt hpQ : (1 : ℝ) < p)
      have hppos : 0 < (p : ℝ) := by exact_mod_cast hQ.pos hpQ
      have hbeta : 0 < oddBM_beta p := oddBM_beta_pos_of_mem hQ hpQ
      have hlambda : 0 < oddBM_lambda Q n := by
        rcases oddBM_state_succ_exists_allowed_factor hn with ⟨q, hq, hqQ⟩
        exact oddBM_lambda_pos_of_allowed_factor hQ hq hqQ
      exact div_nonneg
        (mul_nonneg (mul_nonneg
          (mul_nonneg hlogn.le (Nat.cast_nonneg _)) hbeta.le) hlogp.le)
        (mul_nonneg (mul_pos hppos (add_pos hlogn hlogp)).le
          (add_pos_of_pos_of_nonneg hlambda
            (mul_nonneg hbeta.le hlogp.le)).le)
    · simp [f, Set.indicator_of_notMem hpQ]
  rw [oddBM_firstContribution]
  calc
    (∑ p ∈ S, f p) = ∑ p ∈ S.filter (· ∈ n.factorization.support), f p := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hpS hpnot
      have hpnot' : p ∉ n.factorization.support := fun hps =>
        hpnot (Finset.mem_filter.mpr ⟨hpS, hps⟩)
      by_cases hpQ : p ∈ Q
      · simp only [f, Set.indicator_of_mem hpQ,
          show n.factorization p = 0 from Finsupp.notMem_support_iff.mp hpnot']
        simp
      · simp [f, Set.indicator_of_notMem hpQ]
    _ ≤ ∑ p ∈ n.factorization.support, f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hpnot
        exact hnonneg p
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpQ : p ∈ Q <;> simp [f, hpQ]

/-- Positivity of the affine denominator in the Odd Banks--Martin integral. -/
lemma oddBM_affine_pos {L lambda theta : ℝ}
    (hL : 0 < L) (hlambda : 0 < lambda)
    (htheta₀ : 0 ≤ theta) (htheta₁ : theta ≤ 1) :
    0 < L + (lambda - L) * theta := by
  rw [show L + (lambda - L) * theta =
    (1 - theta) * L + theta * lambda by ring]
  by_cases htheta : theta = 0
  · simp [htheta, hL]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr htheta₁) hL.le)
      (mul_pos (lt_of_le_of_ne htheta₀ (Ne.symm htheta)) hlambda)

/-- The convex chord estimate used in the final one-dimensional integral of
the second Odd Banks--Martin contribution (TeX lines 873--875). -/
lemma oddBM_reciprocal_affine_le_chord {L lambda theta : ℝ}
    (hL : 0 < L) (hlambda : 0 < lambda)
    (htheta₀ : 0 ≤ theta) (htheta₁ : theta ≤ 1) :
    1 / (L + (lambda - L) * theta) ≤
      (1 - theta) / L + theta / lambda := by
  have hden := oddBM_affine_pos hL hlambda htheta₀ htheta₁
  have hrewrite :
      (1 - theta) / L + theta / lambda =
        ((1 - theta) * lambda + theta * L) / (L * lambda) := by
    field_simp [hL.ne', hlambda.ne']
  rw [hrewrite, div_le_div_iff₀ hden (mul_pos hL hlambda)]
  have htheta_prod : 0 ≤ theta * (1 - theta) :=
    mul_nonneg htheta₀ (sub_nonneg.mpr htheta₁)
  nlinarith [mul_nonneg htheta_prod (sq_nonneg (lambda - L))]

/-- Algebraic evaluation of the endpoint average after multiplying by `L`. -/
lemma oddBM_chord_endpoint_average {L lambda : ℝ}
    (hL : L ≠ 0) (hlambda : lambda ≠ 0) :
    L * ((1 / L + 1 / lambda) / 2) =
      1 / 2 + L / (2 * lambda) := by
  field_simp [hL, hlambda]

/-- Integrated convex endpoint estimate from TeX lines 873--875. -/
lemma oddBM_reciprocal_affine_intervalIntegral_le {L lambda : ℝ}
    (hL : 0 < L) (hlambda : 0 < lambda) :
    L * (∫ theta : ℝ in 0..1, 1 / (L + (lambda - L) * theta)) ≤
      1 / 2 + L / (2 * lambda) := by
  have hden : ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      L + (lambda - L) * theta ≠ 0 :=
    fun theta htheta => (oddBM_affine_pos hL hlambda htheta.1 htheta.2).ne'
  have hf : IntervalIntegrable
      (fun theta : ℝ => 1 / (L + (lambda - L) * theta))
        MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_const.div (by fun_prop) hden
  have hg : IntervalIntegrable
      (fun theta : ℝ => (1 - theta) / L + theta / lambda)
        MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun theta : ℝ =>
      (1 - theta) / L + theta / lambda).intervalIntegrable 0 1
  have hint :
      (∫ theta : ℝ in 0..1, 1 / (L + (lambda - L) * theta)) ≤
        ∫ theta : ℝ in 0..1, (1 - theta) / L + theta / lambda :=
    intervalIntegral.integral_mono_on (by norm_num) hf hg fun theta htheta =>
      oddBM_reciprocal_affine_le_chord hL hlambda htheta.1 htheta.2
  have heval :
      (∫ theta : ℝ in 0..1, (1 - theta) / L + theta / lambda) =
        (1 / L + 1 / lambda) / 2 := by
    calc
      (∫ theta : ℝ in 0..1, (1 - theta) / L + theta / lambda) =
          ∫ theta : ℝ in 0..1,
            theta * (1 / lambda - 1 / L) + 1 / L := by
        apply intervalIntegral.integral_congr
        intro theta _
        ring
      _ = (∫ theta : ℝ in 0..1, theta) * (1 / lambda - 1 / L) +
          ∫ _theta : ℝ in 0..1, 1 / L := by
        rw [intervalIntegral.integral_add, intervalIntegral.integral_mul_const]
        · exact (continuous_id.mul continuous_const).intervalIntegrable 0 1
        · exact continuous_const.intervalIntegrable 0 1
      _ = (1 / L + 1 / lambda) / 2 := by
        rw [integral_id]
        norm_num
        ring
  calc
    L * (∫ theta : ℝ in 0..1, 1 / (L + (lambda - L) * theta)) ≤
        L * (∫ theta : ℝ in 0..1, (1 - theta) / L + theta / lambda) :=
      mul_le_mul_of_nonneg_left hint hL.le
    _ = L * ((1 / L + 1 / lambda) / 2) := by rw [heval]
    _ = 1 / 2 + L / (2 * lambda) :=
      oddBM_chord_endpoint_average hL.ne' hlambda.ne'

/-- First moment of an exponentially decaying density on the positive
half-line. -/
lemma integral_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(a * t))) = 1 / a ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := a) (by norm_num) ha
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_one, div_pow] at h ⊢
  exact h

lemma oddBM_resolvent_integrand_eq {C t : ℝ} {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    Real.exp (-(C * t)) * t *
        (Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) t)) =
      (Real.log (p : ℝ) / ((p : ℝ) - 2)) *
        (t * Real.exp (-((C + Real.log (p : ℝ)) * t))) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2pos : 0 < (p : ℝ) - 2 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact sub_pos.mpr (by exact_mod_cast (show 2 < p by omega))
  rw [show Real.rpow (p : ℝ) t =
    Real.exp (Real.log (p : ℝ) * t) from Real.rpow_def_of_pos hp0 t]
  field_simp [ne_of_gt hp2pos, Real.exp_ne_zero]
  have hexp : Real.exp (t * Real.log (p : ℝ)) *
      Real.exp (-(t * (C + Real.log (p : ℝ)))) =
      Real.exp (-(C * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show t * Real.log (p : ℝ) * Real.exp (t * Real.log (p : ℝ)) *
    Real.exp (-(t * (C + Real.log (p : ℝ)))) =
      t * Real.log (p : ℝ) *
        (Real.exp (t * Real.log (p : ℝ)) *
          Real.exp (-(t * (C + Real.log (p : ℝ))))) by ring, hexp]
  ring

/-- Laplace representation of the squared resolvent occurring in the second
Odd Banks--Martin contribution. -/
lemma oddBM_resolvent_square_term_integral {C : ℝ} (hC : 0 < C)
    {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    Real.log (p : ℝ) / (((p : ℝ) - 2) * (C + Real.log (p : ℝ)) ^ 2) =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(C * t)) * t *
          (Real.log (p : ℝ) /
            (((p : ℝ) - 2) * Real.rpow (p : ℝ) t)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0 < (p : ℝ) := zero_lt_one.trans hp1
  have hp2pos : 0 < (p : ℝ) - 2 := by
    have hp3 : 3 ≤ p := by
      have hpge := hp.two_le
      omega
    have : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (show 2 < p by omega)
    linarith
  have hA : 0 < C + Real.log (p : ℝ) :=
    add_pos hC (Real.log_pos hp1)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => oddBM_resolvent_integrand_eq hp hp2), MeasureTheory.integral_const_mul,
    integral_mul_exp_neg_mul_Ioi hA]
  field_simp [ne_of_gt hp2pos]

/-- The odd-zeta estimate integrated against an exponential density. -/
lemma oddBM_resolvent_square_finset_sum_le {C : ℝ} (hC : 0 < C)
    (S : Finset ℕ) :
    (∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
      Real.log (p : ℝ) / (((p : ℝ) - 2) * (C + Real.log (p : ℝ)) ^ 2)
      else 0) ≤ 1 / C := by
  classical
  let F : ℕ → ℝ → ℝ := fun p t =>
    if Nat.Prime p ∧ p ≠ 2 then
      Real.exp (-(C * t)) * t *
        (Real.log (p : ℝ) /
          (((p : ℝ) - 2) * Real.rpow (p : ℝ) t))
    else 0
  have hFint : ∀ p ∈ S, MeasureTheory.IntegrableOn (F p) (Set.Ioi 0) := by
    intro p hp
    by_cases hprime : Nat.Prime p ∧ p ≠ 2
    · have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.1.one_lt
      have hA : 0 < C + Real.log (p : ℝ) := add_pos hC (Real.log_pos hp1)
      have hbase : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.exp (-((C + Real.log (p : ℝ)) * t)))
          (Set.Ioi 0) := by
        refine MeasureTheory.Integrable.of_integral_ne_zero ?_
        rw [integral_mul_exp_neg_mul_Ioi hA]
        positivity
      have hcint : MeasureTheory.IntegrableOn
          (fun t : ℝ => (Real.log (p : ℝ) / ((p : ℝ) - 2)) *
            (t * Real.exp (-((C + Real.log (p : ℝ)) * t)))) (Set.Ioi 0) :=
        hbase.const_mul _
      exact hcint.congr_fun (fun t _ => by
        simp only [F, if_pos hprime]
        exact (oddBM_resolvent_integrand_eq hprime.1 hprime.2).symm) measurableSet_Ioi
    · simp [F, hprime]
  calc
    (∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
        Real.log (p : ℝ) / (((p : ℝ) - 2) * (C + Real.log (p : ℝ)) ^ 2)
        else 0) = ∑ p ∈ S, ∫ t : ℝ in Set.Ioi 0, F p t := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : Nat.Prime p ∧ p ≠ 2
      · rw [if_pos hprime, oddBM_resolvent_square_term_integral hC hprime.1 hprime.2]
        simp [F, hprime]
      · simp [F, hprime]
    _ = ∫ t : ℝ in Set.Ioi 0, ∑ p ∈ S, F p t := by
      rw [MeasureTheory.integral_finsetSum S hFint]
    _ ≤ ∫ t : ℝ in Set.Ioi 0, Real.exp (-(C * t)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact Finset.sum_nonneg fun p hp => by
          dsimp [F]
          split_ifs with hprime
          · exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) ht.le)
              (oddBM_primeBetaSeries_term_nonneg hprime.1 hprime.2 t)
          · exact le_rfl
      · have h := integrableOn_exp_mul_Ioi (a := -C) (by linarith) 0
        exact h.congr_fun (fun t _ => by simp [neg_mul]) measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have hz := oddzeta_finset_sum_bound t ht S
        have hexp := Real.exp_nonneg (-(C * t))
        calc
          (∑ p ∈ S, F p t) = Real.exp (-(C * t)) *
              (t * ∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
                Real.log (p : ℝ) /
                  (((p : ℝ) - 2) * Real.rpow (p : ℝ) t) else 0) := by
            rw [← mul_assoc, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hprime : Nat.Prime p ∧ p ≠ 2 <;> simp [F, hprime]
          _ ≤ Real.exp (-(C * t)) * 1 := mul_le_mul_of_nonneg_left hz hexp
          _ = Real.exp (-(C * t)) := mul_one _
    _ = 1 / C := by
      convert integral_exp_mul_Ioi (a := -C) (by linarith) 0 using 1 <;>
        simp [div_eq_mul_inv]

lemma oddBM_secondContribution_term_le {L lambda : ℝ}
    (hL : 0 < L) (hlambda : 0 < lambda) {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    L * oddBM_beta p * Real.log (p : ℝ) /
        ((p : ℝ) * (L + Real.log (p : ℝ)) *
          (lambda + oddBM_beta p * Real.log (p : ℝ))) ≤
      L / 2 *
        (Real.log (p : ℝ) /
            (((p : ℝ) - 2) * (L + Real.log (p : ℝ)) ^ 2) +
          Real.log (p : ℝ) /
            (((p : ℝ) - 2) * (lambda + Real.log (p : ℝ)) ^ 2)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp2pos : 0 < (p : ℝ) - 2 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact sub_pos.mpr (by exact_mod_cast (show 2 < p by omega))
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hbeta : 1 ≤ oddBM_beta p := oddBM_beta_ge_one hp hp2
  let a := L + Real.log (p : ℝ)
  let b := lambda + oddBM_beta p * Real.log (p : ℝ)
  let d := lambda + Real.log (p : ℝ)
  have ha : 0 < a := add_pos hL hlog
  have hd : 0 < d := add_pos hlambda hlog
  have hdb : d ≤ b := by
    dsimp [b, d]
    nlinarith
  have hb : 0 < b := lt_of_lt_of_le hd hdb
  have ham : 1 / (a * b) ≤ (1 / a ^ 2 + 1 / b ^ 2) / 2 := by
    rw [div_le_iff₀ (mul_pos ha hb)]
    field_simp [ha.ne', hb.ne']
    nlinarith [sq_nonneg (a - b)]
  have hbd : 1 / b ^ 2 ≤ 1 / d ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hb) (sq_pos_of_pos hd)]
    nlinarith
  have hfrac : 1 / (a * b) ≤ (1 / a ^ 2 + 1 / d ^ 2) / 2 :=
    ham.trans (by linarith)
  dsimp [a, b, d] at hfrac
  have heq : L * oddBM_beta p * Real.log (p : ℝ) /
        ((p : ℝ) * (L + Real.log (p : ℝ)) *
          (lambda + oddBM_beta p * Real.log (p : ℝ))) =
      (L * (Real.log (p : ℝ) / ((p : ℝ) - 2))) *
        (1 / ((L + Real.log (p : ℝ)) *
          (lambda + oddBM_beta p * Real.log (p : ℝ)))) := by
    rw [oddBM_beta]
    field_simp [(by exact_mod_cast hp.ne_zero : (p : ℝ) ≠ 0), ne_of_gt hp2pos]
  calc
    L * oddBM_beta p * Real.log (p : ℝ) /
          ((p : ℝ) * (L + Real.log (p : ℝ)) *
            (lambda + oddBM_beta p * Real.log (p : ℝ))) =
        (L * (Real.log (p : ℝ) / ((p : ℝ) - 2))) *
          (1 / ((L + Real.log (p : ℝ)) *
            (lambda + oddBM_beta p * Real.log (p : ℝ)))) := heq
    _ ≤ (L * (Real.log (p : ℝ) / ((p : ℝ) - 2))) *
        ((1 / (L + Real.log (p : ℝ)) ^ 2 +
          1 / (lambda + Real.log (p : ℝ)) ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hfrac (mul_nonneg hL.le (div_nonneg hlog.le hp2pos.le))
    _ = _ := by
      field_simp [ne_of_gt hp2pos, ne_of_gt (add_pos hL hlog),
        ne_of_gt (add_pos hlambda hlog)]

/-- Finite partial sums of the second contribution satisfy the complementary
half-bound from the Odd Banks--Martin proof. -/
lemma oddBM_secondContribution_finset_le {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) {n : ℕ}
    (hlog : 0 < Real.log (n : ℝ)) (hlambda : 0 < oddBM_lambda Q n)
    (S : Finset ℕ) :
    (∑ p ∈ S, Q.indicator (fun p =>
      Real.log (n : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
        ((p : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) *
          (oddBM_lambda Q n + oddBM_beta p * Real.log (p : ℝ)))) p) ≤
        1 / 2 + Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
  classical
  let L := Real.log (n : ℝ)
  let lambda := oddBM_lambda Q n
  calc
    (∑ p ∈ S, Q.indicator (fun p =>
        L * oddBM_beta p * Real.log (p : ℝ) /
          ((p : ℝ) * (L + Real.log (p : ℝ)) *
            (lambda + oddBM_beta p * Real.log (p : ℝ)))) p) ≤
        ∑ p ∈ S, L / 2 *
          ((if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) / (((p : ℝ) - 2) * (L + Real.log (p : ℝ)) ^ 2)
            else 0) +
          (if Nat.Prime p ∧ p ≠ 2 then
            Real.log (p : ℝ) /
              (((p : ℝ) - 2) * (lambda + Real.log (p : ℝ)) ^ 2)
            else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpQ : p ∈ Q
      · rw [Set.indicator_of_mem hpQ, if_pos ⟨hQ.prime hpQ, hQ.ne_two hpQ⟩,
          if_pos ⟨hQ.prime hpQ, hQ.ne_two hpQ⟩]
        exact oddBM_secondContribution_term_le hlog hlambda
          (hQ.prime hpQ) (hQ.ne_two hpQ)
      · rw [Set.indicator_of_notMem hpQ]
        split_ifs with hprime
        · have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.1.one_lt
          have hp2pos : 0 < (p : ℝ) - 2 := by
            have hp3 : 3 ≤ p := by have := hprime.1.two_le; omega
            exact sub_pos.mpr (by exact_mod_cast (show 2 < p by omega))
          have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
          positivity
        · norm_num
    _ = L / 2 *
        ((∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) / (((p : ℝ) - 2) * (L + Real.log (p : ℝ)) ^ 2)
          else 0) +
        ∑ p ∈ S, if Nat.Prime p ∧ p ≠ 2 then
          Real.log (p : ℝ) /
            (((p : ℝ) - 2) * (lambda + Real.log (p : ℝ)) ^ 2)
          else 0) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ L / 2 * (1 / L + 1 / lambda) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add (oddBM_resolvent_square_finset_sum_le hlog S)
          (oddBM_resolvent_square_finset_sum_le hlambda S)
      · exact div_nonneg hlog.le (by norm_num)
    _ = 1 / 2 + Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
      dsimp [L, lambda]
      field_simp [ne_of_gt hlog, ne_of_gt hlambda]

/-- The complete estimate for the second contribution in the Odd
Banks--Martin sub-invariance proof. -/
lemma oddBM_secondContribution_le {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) {n : ℕ}
    (hlog : 0 < Real.log (n : ℝ)) (hlambda : 0 < oddBM_lambda Q n) :
    oddBM_secondContribution Q n ≤
      1 / 2 + Real.log (n : ℝ) / (2 * oddBM_lambda Q n) := by
  rw [oddBM_secondContribution]
  apply tsum_le_of_sum_le'
  · positivity
  · intro S
    simpa [Set.indicator] using
      oddBM_secondContribution_finset_le hQ hlog hlambda S

/-- TeX equation `\eqref{task}`: the two incoming contributions sum to at
most one. -/
lemma oddBM_contributions_le_one {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_state (k + 1) Q) :
    oddBM_firstContribution Q n + oddBM_secondContribution Q n ≤ 1 := by
  rcases oddBM_state_succ_exists_allowed_factor hn with ⟨p, hp, hpQ⟩
  have hn_pos : 0 < n := oddBM_state_positive_of_odd_primes hQ hn
  have hp_dvd : p ∣ n :=
    (Nat.mem_primeFactors.mp (by simpa using hp)).2.1
  have hn_one : 1 < n :=
    (hQ.one_lt hpQ).trans_le (Nat.le_of_dvd hn_pos hp_dvd)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn_one)
  have hlambda : 0 < oddBM_lambda Q n :=
    oddBM_lambda_pos_of_allowed_factor hQ hp hpQ
  linarith [oddBM_firstContribution_le hQ hn,
    oddBM_secondContribution_le hQ hlog hlambda]

lemma oddBM_lambda_eq_zero_of_no_allowed_factor {Q : Set ℕ} {n : ℕ}
    (hdisj : ∀ p : ℕ, p ∈ n.factorization.support -> p ∉ Q) :
    oddBM_lambda Q n = 0 := by
  classical
  rw [oddBM_lambda]
  refine Finset.sum_eq_zero ?_
  intro p hp
  simp [hdisj p hp]

lemma oddBM_lambda_congr_on_support {Q R : Set ℕ} {n : ℕ}
    (hQR : ∀ p : ℕ, p ∈ n.factorization.support -> (p ∈ Q ↔ p ∈ R)) :
    oddBM_lambda Q n = oddBM_lambda R n := by
  classical
  rw [oddBM_lambda, oddBM_lambda]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hiff := hQR p hp
  by_cases hpQ : p ∈ Q
  · have hpR : p ∈ R := hiff.mp hpQ
    simp [hpQ, hpR]
  · have hpR : p ∉ R := fun hpR => hpQ (hiff.mpr hpR)
    simp [hpQ, hpR]

lemma oddBM_lambda_normalized_sum {Q : Set ℕ} {n : ℕ}
    [DecidablePred (fun p : ℕ => p ∈ Q)]
    (hlambda : oddBM_lambda Q n ≠ 0) :
    (∑ p ∈ n.factorization.support,
      (if p ∈ Q then
        (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
      else 0) / oddBM_lambda Q n) = 1 := by
  classical
  rw [← Finset.sum_div]
  have hdef : (∑ p ∈ n.factorization.support,
      if p ∈ Q then (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
      else 0) = oddBM_lambda Q n := by
    congr 1
    ext p
    simp
  rw [hdef, div_self hlambda]

/-- The prime-step downward kernel used for Odd Banks--Martin.  It is absorbing
on `ℕ_k(Q)` and, above that layer, divides out one allowed prime at a time. -/
noncomputable def oddBM_downward_kernel (k : ℕ) (Q : Set ℕ) (n m : ℕ) : ℝ :=
  by
    classical
    exact
      if n ∈ restrict_to_primes (omega_layer k) Q then
        if m = n then 1 else 0
      else if n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q then
        ∑ p ∈ n.factorization.support,
          if p ∈ Q ∧ m = n / p then
            (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) / oddBM_lambda Q n
          else 0
      else 0

lemma factorization_mul_prime_apply {m p : ℕ} (hm : m ≠ 0)
    (hp : Nat.Prime p) :
    (m * p).factorization p = m.factorization p + 1 := by
  rw [Nat.factorization_mul hm hp.ne_zero, Finsupp.add_apply, hp.factorization]
  simp

/-- Explicit transition from the parent `mp` down to `m`. -/
lemma oddBM_downward_kernel_mul_prime {k m p : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hm : m ∈ oddBM_state k Q) (hpQ : p ∈ Q) :
    oddBM_downward_kernel k Q (m * p) m =
      ((m.factorization p + 1 : ℕ) : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
        (oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ)) := by
  classical
  have hmpos := oddBM_state_positive_of_odd_primes hQ hm
  have hp := hQ.prime hpQ
  have hstate := oddBM_mul_prime_mem_state_succ hQ hm hpQ
  have hterm := oddBM_mul_prime_not_terminal hQ hm hpQ
  have hp_support : p ∈ (m * p).factorization.support := by
    rw [Finsupp.mem_support_iff, factorization_mul_prime_apply hmpos.ne' hp]
    omega
  rw [oddBM_downward_kernel, if_neg (by simpa [oddBM_terminal] using hterm),
    if_pos (by simpa [oddBM_state] using hstate)]
  rw [Finset.sum_eq_single p]
  · rw [if_pos ⟨hpQ, by rw [Nat.mul_div_cancel m hp.pos]⟩,
      factorization_mul_prime_apply hmpos.ne' hp,
      oddBM_lambda_mul_prime hmpos.ne' hp hpQ]
  · intro q hq hqp
    have hqprime : Nat.Prime q := by
      have : q ∈ (m * p).primeFactors := by simpa using hq
      exact (Nat.mem_primeFactors.mp this).1
    by_cases hcond : q ∈ Q ∧ m = m * p / q
    · have hqdiv : q ∣ m * p := by
        have : q ∈ (m * p).primeFactors := by simpa using hq
        exact (Nat.mem_primeFactors.mp this).2.1
      have hmul : m * q = m * p := by
        calc
          m * q = (m * p / q) * q := by rw [← hcond.2]
          _ = m * p := Nat.div_mul_cancel hqdiv
      exact False.elim (hqp (Nat.mul_left_cancel hmpos hmul))
    · simp [hcond]
  · intro hpnot
    exact False.elim (hpnot hp_support)

/-- After normalization by the Erdős weight, the parent transition splits
into the valuation contribution and the new-prime contribution in TeX
equation `\eqref{task}`. -/
lemma oddBM_weighted_parent_term {k m p : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hm : m ∈ oddBM_state k Q)
    (hm1 : 1 < m) (hpQ : p ∈ Q)
    (hlambda : 0 < oddBM_lambda Q m) :
    erdos_weight (m * p) * oddBM_downward_kernel k Q (m * p) m =
      erdos_weight m *
        (Real.log (m : ℝ) * (m.factorization p : ℝ) * oddBM_beta p *
              Real.log (p : ℝ) /
            ((p : ℝ) * (Real.log (m : ℝ) + Real.log (p : ℝ)) *
              (oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ))) +
          Real.log (m : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
            ((p : ℝ) * (Real.log (m : ℝ) + Real.log (p : ℝ)) *
              (oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ)))) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hQ.prime hpQ).ne_zero
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm1)
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hQ.one_lt hpQ)
  have hden : 0 < oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ) :=
    add_pos_of_pos_of_nonneg hlambda
      (mul_nonneg (oddBM_beta_pos_of_mem hQ hpQ).le hlogp.le)
  rw [oddBM_downward_kernel_mul_prime hQ hm hpQ, erdos_weight, erdos_weight,
    show (((m * p : ℕ) : ℝ)) = (m : ℝ) * (p : ℝ) by norm_num,
    Real.log_mul hm0 hp0]
  push_cast
  field_simp [hm0, hp0, hlogm.ne', hden.ne']

/-- Finite sub-invariance over parents obtained by multiplying by allowed
primes. -/
lemma oddBM_weighted_prime_parents_le {k m : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hm : m ∈ oddBM_state k Q)
    (S : Finset ℕ) :
    (∑ p ∈ S, Q.indicator (fun p =>
      erdos_weight (m * p) * oddBM_downward_kernel k Q (m * p) m) p) ≤
      erdos_weight m := by
  classical
  have hm' : m ∈ oddBM_state (k - 1 + 1) Q := by
    simpa [Nat.sub_add_cancel hk] using hm
  rcases oddBM_state_succ_exists_allowed_factor hm' with ⟨q, hq, hqQ⟩
  have hmpos := oddBM_state_positive_of_odd_primes hQ hm
  have hm1 := oddBM_state_one_lt hk hQ hm
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm1)
  have hlambda : 0 < oddBM_lambda Q m :=
    oddBM_lambda_pos_of_allowed_factor hQ hq hqQ
  let f₁ : ℕ → ℝ := fun p => Q.indicator (fun p =>
    Real.log (m : ℝ) * (m.factorization p : ℝ) * oddBM_beta p *
        Real.log (p : ℝ) /
      ((p : ℝ) * (Real.log (m : ℝ) + Real.log (p : ℝ)) *
        (oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ)))) p
  let f₂ : ℕ → ℝ := fun p => Q.indicator (fun p =>
    Real.log (m : ℝ) * oddBM_beta p * Real.log (p : ℝ) /
      ((p : ℝ) * (Real.log (m : ℝ) + Real.log (p : ℝ)) *
        (oddBM_lambda Q m + oddBM_beta p * Real.log (p : ℝ)))) p
  have hf₁ : (∑ p ∈ S, f₁ p) ≤ oddBM_firstContribution Q m := by
    simpa [f₁] using oddBM_firstContribution_finset_le hQ hm' S
  have hf₂ : (∑ p ∈ S, f₂ p) ≤
      1 / 2 + Real.log (m : ℝ) / (2 * oddBM_lambda Q m) := by
    simpa [f₂] using oddBM_secondContribution_finset_le hQ hlog hlambda S
  have htotal : (∑ p ∈ S, f₁ p) + ∑ p ∈ S, f₂ p ≤ 1 := by
    linarith [oddBM_firstContribution_le hQ hm']
  calc
    (∑ p ∈ S, Q.indicator (fun p =>
        erdos_weight (m * p) * oddBM_downward_kernel k Q (m * p) m) p) =
        ∑ p ∈ S, erdos_weight m * (f₁ p + f₂ p) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpQ : p ∈ Q
      · rw [Set.indicator_of_mem hpQ]
        simp only [f₁, f₂, Set.indicator_of_mem hpQ]
        exact oddBM_weighted_parent_term hQ hm hm1 hpQ hlambda
      · simp [f₁, f₂, Set.indicator_of_notMem hpQ]
    _ = erdos_weight m * ((∑ p ∈ S, f₁ p) + ∑ p ∈ S, f₂ p) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ erdos_weight m * 1 :=
      mul_le_mul_of_nonneg_left htotal (by
        rw [erdos_weight]
        positivity)
    _ = erdos_weight m := mul_one _

/-- The Odd Banks--Martin kernel is absorbing on the terminal layer. -/
lemma oddBM_downward_kernel_terminal_self {k n : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_terminal k Q) :
    oddBM_downward_kernel k Q n n = 1 := by
  have hn' : n ∈ restrict_to_primes (omega_layer k) Q := by
    simpa [oddBM_terminal] using hn
  simp [oddBM_downward_kernel, hn']

/-- From a terminal state, the Odd Banks--Martin kernel assigns no mass to any
different target. -/
lemma oddBM_downward_kernel_terminal_ne {k n m : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_terminal k Q) (hmn : m ≠ n) :
    oddBM_downward_kernel k Q n m = 0 := by
  have hn' : n ∈ restrict_to_primes (omega_layer k) Q := by
    simpa [oddBM_terminal] using hn
  simp [oddBM_downward_kernel, hn', hmn]

/-- Outside the terminal layer and the next state layer, the Odd Banks--Martin
kernel vanishes. -/
lemma oddBM_downward_kernel_outside {k n m : ℕ} {Q : Set ℕ}
    (hterm : n ∉ oddBM_terminal k Q) (hstate : n ∉ oddBM_state (k + 1) Q) :
    oddBM_downward_kernel k Q n m = 0 := by
  have hterm' : n ∉ restrict_to_primes (omega_layer k) Q := by
    simpa [oddBM_terminal] using hterm
  have hstate' : n ∉ restrict_to_primes (omega_ge_layer (k + 1)) Q := by
    simpa [oddBM_state] using hstate
  simp [oddBM_downward_kernel, hterm', hstate']

lemma oddBM_downward_kernel_no_allowed_step {k n m : ℕ} {Q : Set ℕ}
    (hterm : n ∉ oddBM_terminal k Q) (hstate : n ∈ oddBM_state (k + 1) Q)
    (hno : ∀ p : ℕ, p ∈ n.factorization.support -> p ∈ Q -> m ≠ n / p) :
    oddBM_downward_kernel k Q n m = 0 := by
  classical
  have hterm' : n ∉ restrict_to_primes (omega_layer k) Q := by
    simpa [oddBM_terminal] using hterm
  have hstate' : n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q := by
    simpa [oddBM_state] using hstate
  have hsum :
      (∑ p ∈ n.factorization.support,
        if p ∈ Q ∧ m = n / p then
          (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) / oddBM_lambda Q n
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    by_cases hpQ : p ∈ Q
    · have hneq : ¬ m = n / p := fun hm => hno p hp hpQ hm
      simp [hpQ, hneq]
    · simp [hpQ]
  simp only [oddBM_downward_kernel, hterm', hstate', ite_false, ite_true]
  convert hsum using 1

lemma oddBM_downward_kernel_eq_zero_of_not_supported {k n m : ℕ} {Q : Set ℕ}
    (hterminal : n ∈ oddBM_terminal k Q -> m ≠ n)
    (hstep : ∀ p : ℕ, p ∈ n.factorization.support -> p ∈ Q -> m ≠ n / p) :
    oddBM_downward_kernel k Q n m = 0 := by
  by_cases hterm : n ∈ oddBM_terminal k Q
  · exact oddBM_downward_kernel_terminal_ne hterm (hterminal hterm)
  · by_cases hstate : n ∈ oddBM_state (k + 1) Q
    · exact oddBM_downward_kernel_no_allowed_step hterm hstate hstep
    · exact oddBM_downward_kernel_outside hterm hstate

lemma oddBM_downward_kernel_support {k n m : ℕ} {Q : Set ℕ}
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    (n ∈ oddBM_terminal k Q ∧ m = n) ∨
      (n ∉ oddBM_terminal k Q ∧ n ∈ oddBM_state (k + 1) Q ∧
        ∃ p : ℕ, p ∈ n.factorization.support ∧ p ∈ Q ∧ m = n / p) := by
  classical
  by_cases hterm : n ∈ oddBM_terminal k Q
  · by_cases hmn : m = n
    · exact Or.inl ⟨hterm, hmn⟩
    · exact False.elim (hker (oddBM_downward_kernel_terminal_ne hterm hmn))
  · by_cases hstate : n ∈ oddBM_state (k + 1) Q
    · by_cases hstep :
        ∃ p : ℕ, p ∈ n.factorization.support ∧ p ∈ Q ∧ m = n / p
      · exact Or.inr ⟨hterm, hstate, hstep⟩
      · have hzero : oddBM_downward_kernel k Q n m = 0 := by
          apply oddBM_downward_kernel_no_allowed_step hterm hstate
          intro p hp hpQ hm
          exact hstep ⟨p, hp, hpQ, hm⟩
        exact False.elim (hker hzero)
    · exact False.elim (hker (oddBM_downward_kernel_outside hterm hstate))

lemma oddBM_downward_kernel_support_of_nonterminal {k n m : ℕ} {Q : Set ℕ}
    (hterm : n ∉ oddBM_terminal k Q)
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    n ∈ oddBM_state (k + 1) Q ∧
      ∃ p : ℕ, p ∈ n.factorization.support ∧ p ∈ Q ∧ m = n / p := by
  rcases oddBM_downward_kernel_support hker with hterminal | hstep
  · exact False.elim (hterm hterminal.1)
  · exact ⟨hstep.2.1, hstep.2.2⟩

/-- A nonterminal positive-mass transition is exactly division by an allowed
prime factor. -/
lemma oddBM_downward_kernel_support_prime_step {k n m : ℕ} {Q : Set ℕ}
    (hterm : n ∉ oddBM_terminal k Q)
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∈ Q ∧ p ∣ n ∧ m = n / p := by
  rcases oddBM_downward_kernel_support_of_nonterminal hterm hker with
    ⟨_hstate, p, hp, hpQ, hm⟩
  have hp_mem_primeFactors : p ∈ n.primeFactors := by
    simpa using hp
  have hp_data := Nat.mem_primeFactors.mp hp_mem_primeFactors
  exact ⟨p, hp_data.1, hpQ, hp_data.2.1, hm⟩

/-- Nonterminal transitions preserve the restriction to the allowed set of
prime factors. -/
lemma oddBM_downward_kernel_support_target_restrict_to_primes_univ
    {k n m : ℕ} {Q : Set ℕ}
    (hterm : n ∉ oddBM_terminal k Q)
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m ∈ restrict_to_primes (Set.univ : Set ℕ) Q := by
  rcases oddBM_downward_kernel_support_of_nonterminal hterm hker with
    ⟨hstate, p, hp, _hpQ, rfl⟩
  have hp_mem_primeFactors : p ∈ n.primeFactors := by
    simpa using hp
  have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem_primeFactors).2.1
  exact oddBM_state_div_mem_restrict_to_primes_univ hstate hp_dvd

lemma oddBM_downward_kernel_nonneg {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) :
    0 ≤ oddBM_downward_kernel k Q n m := by
  classical
  rw [oddBM_downward_kernel]
  by_cases hterm : n ∈ restrict_to_primes (omega_layer k) Q
  · rw [if_pos hterm]
    by_cases hmn : m = n
    · simp [hmn]
    · simp [hmn]
  · rw [if_neg hterm]
    by_cases hstate : n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q
    · rw [if_pos hstate]
      refine Finset.sum_nonneg ?_
      intro p hp
      by_cases hcond : p ∈ Q ∧ m = n / p
      · have hpQ : p ∈ Q := hcond.1
        have hfac_nonneg : 0 ≤ (n.factorization p : ℝ) := by
          exact_mod_cast Nat.zero_le (n.factorization p)
        have hbeta_nonneg : 0 ≤ oddBM_beta p :=
          le_of_lt (oddBM_beta_pos_of_mem hQ hpQ)
        have hp_one_real : (1 : ℝ) < (p : ℝ) := by
          exact_mod_cast (hQ.one_lt hpQ)
        have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
          le_of_lt (Real.log_pos hp_one_real)
        have hnum_nonneg :
            0 ≤ (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ) :=
          mul_nonneg (mul_nonneg hfac_nonneg hbeta_nonneg) hlog_nonneg
        simpa [hcond] using div_nonneg hnum_nonneg (oddBM_lambda_nonneg hQ n)
      · simp [hcond]
    · simp [hstate]

lemma oddBM_downward_kernel_eq_zero_of_not_divisor {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hm : m ∉ n.divisors) :
    oddBM_downward_kernel k Q n m = 0 := by
  classical
  by_cases hterm : n ∈ oddBM_terminal k Q
  · have hn_ne_zero : n ≠ 0 :=
      Nat.ne_of_gt (oddBM_terminal_positive_of_odd_primes hQ hterm)
    by_cases hmn : m = n
    · have hn_div : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn_ne_zero⟩
      exact False.elim (hm (by simpa [hmn] using hn_div))
    · exact oddBM_downward_kernel_terminal_ne hterm hmn
  · by_cases hstate : n ∈ oddBM_state (k + 1) Q
    · apply oddBM_downward_kernel_no_allowed_step hterm hstate
      intro p hp _hpQ hmp
      have hn_ne_zero : n ≠ 0 :=
        Nat.ne_of_gt (oddBM_state_positive_of_odd_primes hQ hstate)
      have hp_mem_primeFactors : p ∈ n.primeFactors := by
        simpa using hp
      have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem_primeFactors).2.1
      have hdiv_mem : n / p ∈ n.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hp_dvd, hn_ne_zero⟩
      exact hm (by simpa [hmp] using hdiv_mem)
    · exact oddBM_downward_kernel_outside hterm hstate

lemma oddBM_downward_kernel_tsum_eq_sum_divisors {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) :
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) =
      ∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m := by
  classical
  exact tsum_eq_sum
    (f := fun m : ℕ => oddBM_downward_kernel k Q n m)
    (s := n.divisors)
    (fun m hm => oddBM_downward_kernel_eq_zero_of_not_divisor hQ hm)

lemma oddBM_downward_kernel_support_divisor {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m ∈ n.divisors := by
  by_contra hm
  exact hker (oddBM_downward_kernel_eq_zero_of_not_divisor hQ hm)

/-- Every transition carrying positive mass in the Odd Banks--Martin kernel
follows divisibility downward. -/
lemma oddBM_downward_kernel_support_dvd {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m ∣ n :=
  (Nat.mem_divisors.mp (oddBM_downward_kernel_support_divisor hQ hker)).1

/-- Away from the absorbing layer, every transition carrying positive mass is
strictly downward. -/
lemma oddBM_downward_kernel_support_lt_of_nonterminal {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hterm : n ∉ oddBM_terminal k Q)
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m < n := by
  rcases oddBM_downward_kernel_support_of_nonterminal hterm hker with
    ⟨hstate, p, _hp, hpQ, rfl⟩
  exact Nat.div_lt_self
    (oddBM_state_positive_of_odd_primes hQ hstate)
    (hQ.one_lt hpQ)

/-- A positive-mass transition is either the absorbing self-loop or a strict
divisibility descent. -/
lemma oddBM_downward_kernel_support_eq_or_lt {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m = n ∨ m < n := by
  by_cases hterm : n ∈ oddBM_terminal k Q
  · rcases oddBM_downward_kernel_support hker with hself | hstep
    · exact Or.inl hself.2
    · exact False.elim (hstep.1 hterm)
  · exact Or.inr (oddBM_downward_kernel_support_lt_of_nonterminal hQ hterm hker)

lemma oddBM_downward_kernel_terminal_row_sum {k n : ℕ} {Q : Set ℕ}
    (hn : n ∈ oddBM_terminal k Q) :
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) = 1 := by
  calc
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) =
        oddBM_downward_kernel k Q n n := by
      rw [tsum_eq_single n]
      intro m hm
      exact oddBM_downward_kernel_terminal_ne hn hm
    _ = 1 := oddBM_downward_kernel_terminal_self hn

lemma oddBM_downward_kernel_terminal_divisor_row_sum {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hn : n ∈ oddBM_terminal k Q) :
    (∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m) = 1 := by
  rw [← oddBM_downward_kernel_tsum_eq_sum_divisors hQ]
  exact oddBM_downward_kernel_terminal_row_sum hn

/-- For a prime `p` in the support of `n`, the cofactor `n / p` is a divisor of
`n`.  This is the divisibility book-keeping needed for the non-terminal row sum. -/
lemma oddBM_div_prime_mem_divisors {n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ n.factorization.support) :
    n / p ∈ n.divisors := by
  have hp_mem_primeFactors : p ∈ n.primeFactors := by
    simpa using hp
  have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp_mem_primeFactors).2.1
  exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hp_dvd, hn⟩

/-- On the next-state layer the Odd Banks--Martin kernel is stochastic: dividing
out one allowed prime at a time, weighted by `v_p β_p log p / λ(n)`, gives total
mass `1`.  Together with `oddBM_downward_kernel_terminal_row_sum` this is the row
normalization law (TeX `\eqref{searrow}`) for the chain of paper Lemma
`\ref{conj:oddBM}`.

The proof swaps the order of summation, collapses the inner `m = n / p` indicator
against the divisor set, and applies the normalization identity for `λ`. -/
lemma oddBM_downward_kernel_nonterminal_row_sum {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hterm : n ∉ oddBM_terminal k Q) (hstate : n ∈ oddBM_state (k + 1) Q) :
    (∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m) = 1 := by
  classical
  have hterm' : n ∉ restrict_to_primes (omega_layer k) Q := by
    simpa [oddBM_terminal] using hterm
  have hstate' : n ∈ restrict_to_primes (omega_ge_layer (k + 1)) Q := by
    simpa [oddBM_state] using hstate
  have hn_pos : 0 < n := restrict_to_primes_positive_of_odd_primes hQ hstate'
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  have hlambda : oddBM_lambda Q n ≠ 0 :=
    oddBM_lambda_ne_zero_of_mem_oddBM_state_succ hQ hstate
  -- On every divisor `m`, expand the kernel on its non-terminal branch.
  have hexpand : ∀ m ∈ n.divisors,
      oddBM_downward_kernel k Q n m =
        ∑ p ∈ n.factorization.support,
          if p ∈ Q ∧ m = n / p then
            (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
              / oddBM_lambda Q n
          else 0 := by
    intro m _
    rw [oddBM_downward_kernel, if_neg hterm', if_pos hstate']
  -- For each allowed prime `p`, the inner divisor sum collapses to its single
  -- nonzero term at `m = n / p`, recovering the `λ`-normalization summand.
  have hcollapse : ∀ p ∈ n.factorization.support,
      (∑ m ∈ n.divisors,
        if p ∈ Q ∧ m = n / p then
          (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
            / oddBM_lambda Q n
        else 0) =
      (if p ∈ Q then
        (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
      else 0) / oddBM_lambda Q n := by
    intro p hp
    by_cases hpQ : p ∈ Q
    · have hdiv : n / p ∈ n.divisors := oddBM_div_prime_mem_divisors hn_ne hp
      have hsingle :
          (∑ m ∈ n.divisors,
            if p ∈ Q ∧ m = n / p then
              (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
                / oddBM_lambda Q n
            else 0) =
          (if p ∈ Q ∧ (n / p) = n / p then
              (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
                / oddBM_lambda Q n
            else 0) := by
        refine Finset.sum_eq_single_of_mem (n / p) hdiv ?_
        intro m _ hm
        have hcond : ¬ (p ∈ Q ∧ m = n / p) := fun h => hm h.2
        simp [hcond]
      rw [hsingle]
      simp [hpQ]
    · refine (Finset.sum_eq_zero ?_).trans ?_
      · intro m _
        have hcond : ¬ (p ∈ Q ∧ m = n / p) := fun h => hpQ h.1
        simp [hcond]
      · simp [hpQ]
  calc
    (∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m)
        = ∑ m ∈ n.divisors,
            ∑ p ∈ n.factorization.support,
              if p ∈ Q ∧ m = n / p then
                (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
                  / oddBM_lambda Q n
              else 0 :=
          Finset.sum_congr rfl hexpand
    _ = ∑ p ∈ n.factorization.support,
            ∑ m ∈ n.divisors,
              if p ∈ Q ∧ m = n / p then
                (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
                  / oddBM_lambda Q n
              else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ p ∈ n.factorization.support,
            (if p ∈ Q then
              (n.factorization p : ℝ) * oddBM_beta p * Real.log (p : ℝ)
            else 0) / oddBM_lambda Q n :=
          Finset.sum_congr rfl hcollapse
    _ = 1 := oddBM_lambda_normalized_sum hlambda

/-- Combined row-sum statement: the Odd Banks--Martin kernel is stochastic at every
state of the chain, terminal or not.  This is the full normalization law
`\eqref{searrow}` for paper Lemma `\ref{conj:oddBM}`. -/
lemma oddBM_downward_kernel_row_sum {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hmem : n ∈ oddBM_state (k + 1) Q ∨ n ∈ oddBM_terminal k Q) :
    (∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m) = 1 := by
  by_cases hterm : n ∈ oddBM_terminal k Q
  · exact oddBM_downward_kernel_terminal_divisor_row_sum hQ hterm
  · rcases hmem with hstate | hterm'
    · exact oddBM_downward_kernel_nonterminal_row_sum hQ hterm hstate
    · exact absurd hterm' hterm

/-- The full real-line `tsum` form of the non-terminal row sum. -/
lemma oddBM_downward_kernel_nonterminal_tsum_row_sum {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hterm : n ∉ oddBM_terminal k Q) (hstate : n ∈ oddBM_state (k + 1) Q) :
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) = 1 := by
  calc
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) =
        ∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m :=
      oddBM_downward_kernel_tsum_eq_sum_divisors hQ
    _ = 1 := oddBM_downward_kernel_nonterminal_row_sum hQ hterm hstate

/-- The full `tsum` row normalization for every state of the Odd
Banks--Martin chain. -/
lemma oddBM_downward_kernel_tsum_row_sum {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hmem : n ∈ oddBM_state (k + 1) Q ∨ n ∈ oddBM_terminal k Q) :
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) = 1 := by
  calc
    (∑' m : ℕ, oddBM_downward_kernel k Q n m) =
        ∑ m ∈ n.divisors, oddBM_downward_kernel k Q n m :=
      oddBM_downward_kernel_tsum_eq_sum_divisors hQ
    _ = 1 := oddBM_downward_kernel_row_sum hQ hmem

/-- The elementary Markov laws for the prime-step kernel in the Odd
Banks--Martin argument: nonnegative transition weights, total mass one, and
support on downward divisibility transitions. -/
lemma oddBM_downward_kernel_markov_laws {k n : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q)
    (hmem : n ∈ oddBM_state (k + 1) Q ∨ n ∈ oddBM_terminal k Q) :
    (∀ m : ℕ, 0 ≤ oddBM_downward_kernel k Q n m) ∧
      (∑' m : ℕ, oddBM_downward_kernel k Q n m) = 1 ∧
        ∀ m : ℕ, oddBM_downward_kernel k Q n m ≠ 0 ->
          m ∣ n ∧ (m = n ∨ m < n) := by
  refine ⟨fun m => oddBM_downward_kernel_nonneg hQ, ?_⟩
  refine ⟨oddBM_downward_kernel_tsum_row_sum hQ hmem, ?_⟩
  intro m hker
  exact ⟨oddBM_downward_kernel_support_dvd hQ hker,
    oddBM_downward_kernel_support_eq_or_lt hQ hker⟩

lemma oddBM_strict_parent_eq_mul_prime {k m n : ℕ} {Q : Set ℕ}
    (hmn : m < n) (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    ∃ p ∈ Q, n = m * p := by
  rcases oddBM_downward_kernel_support hker with hterm | hstep
  · exact False.elim (Nat.ne_of_lt hmn hterm.2)
  · rcases hstep.2.2 with ⟨p, hp, hpQ, hmp⟩
    have hpdiv : p ∣ n := by
      have : p ∈ n.primeFactors := by simpa using hp
      exact (Nat.mem_primeFactors.mp this).2.1
    refine ⟨p, hpQ, ?_⟩
    calc
      n = n / p * p := (Nat.div_mul_cancel hpdiv).symm
      _ = m * p := by rw [hmp]

lemma oddBM_downward_kernel_support_source_state {k n m : ℕ} {Q : Set ℕ}
    (hQ : IsSetOfOddPrimes Q) (hterm : n ∉ oddBM_terminal k Q)
    (hker : oddBM_downward_kernel k Q n m ≠ 0) :
    m ∈ oddBM_state k Q := by
  rcases oddBM_downward_kernel_support_of_nonterminal hterm hker with
    ⟨hn, p, hp, hpQ, rfl⟩
  have hp' : Nat.Prime p := hQ.prime hpQ
  have hpdiv : p ∣ n :=
    (Nat.mem_primeFactors.mp (by simpa using hp)).2.1
  have hm := oddBM_state_div_mem_restrict_to_primes_univ hn hpdiv
  have hmpos := restrict_to_primes_positive_of_odd_primes hQ hm
  refine ⟨?_, hm.2⟩
  have hcard := hn.1
  change k + 1 ≤ ArithmeticFunction.cardFactors n at hcard
  change k ≤ ArithmeticFunction.cardFactors (n / p)
  rw [← Nat.div_mul_cancel hpdiv,
    ArithmeticFunction.cardFactors_mul hmpos.ne' hp'.ne_zero] at hcard
  simpa [hp'] using hcard

/-- Strict adjoint of the Odd Banks--Martin downward kernel with respect to
the Erdős weight.  Absorbing self-loops are omitted. -/
noncomputable def oddBM_upward_kernel (k : ℕ) (Q : Set ℕ) :
    Option ℕ → Option ℕ → ℝ := by
  classical
  exact fun a b => match a, b with
    | some m, some n =>
        if m ∈ oddBM_state k Q ∧ n ∈ oddBM_state (k + 1) Q ∧ m < n then
          erdos_weight n * oddBM_downward_kernel k Q n m / erdos_weight m
        else 0
    | _, _ => 0

lemma oddBM_upward_kernel_nonneg {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) :
    ∀ a b, 0 ≤ oddBM_upward_kernel k Q a b := by
  classical
  intro a b
  rcases a with _ | m <;> rcases b with _ | n
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · simp only [oddBM_upward_kernel]
    split_ifs with h
    · have hm1 := oddBM_state_one_lt hk hQ h.1
      exact div_nonneg
        (mul_nonneg (by rw [erdos_weight]; positivity)
          (oddBM_downward_kernel_nonneg hQ))
        (by rw [erdos_weight]; positivity)
    · exact le_rfl

lemma oddBM_upward_kernel_finite_row {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) :
    ∀ m, 1 ≤ m → ∀ s : Finset ℕ,
      (∑ n ∈ s, if 1 ≤ n then
        oddBM_upward_kernel k Q (some m) (some n) else 0) ≤ 1 := by
  intro m hm s
  classical
  by_cases hmstate : m ∈ oddBM_state k Q
  · have hmpos := oddBM_state_positive_of_odd_primes hQ hmstate
    have hm1 := oddBM_state_one_lt hk hQ hmstate
    have hwpos : 0 < erdos_weight m := by
      rw [erdos_weight]
      exact one_div_pos.mpr (mul_pos (by exact_mod_cast hmpos)
        (Real.log_pos (by exact_mod_cast hm1)))
    let T := s.filter fun n => m < n ∧ oddBM_downward_kernel k Q n m ≠ 0
    let g : ℕ → ℝ := fun p => Q.indicator (fun p =>
      erdos_weight (m * p) * oddBM_downward_kernel k Q (m * p) m) p
    calc
      (∑ n ∈ s, if 1 ≤ n then
          oddBM_upward_kernel k Q (some m) (some n) else 0) =
          ∑ n ∈ T, oddBM_upward_kernel k Q (some m) (some n) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hlt : m < n
        · by_cases hker : oddBM_downward_kernel k Q n m = 0
          · simp [hlt, hker, oddBM_upward_kernel, hmstate]
          · have hnstate : n ∈ oddBM_state (k + 1) Q := by
              rcases oddBM_downward_kernel_support hker with hterm | hstep
              · exact False.elim (Nat.ne_of_lt hlt hterm.2)
              · exact hstep.2.1
            simp [hlt, hker, oddBM_upward_kernel, hmstate, hnstate,
              hm.trans hlt.le]
        · simp [hlt, oddBM_upward_kernel, hmstate]
      _ = ∑ n ∈ T, g (n / m) / erdos_weight m := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := (Finset.mem_filter.mp hn).2
        rcases oddBM_strict_parent_eq_mul_prime hn'.1 hn'.2 with ⟨p, hpQ, rfl⟩
        have hdiv : m * p / m = p := Nat.mul_div_cancel_left p hmpos
        have hlt : m < m * p := hn'.1
        have hstate := oddBM_mul_prime_mem_state_succ hQ hmstate hpQ
        simp [oddBM_upward_kernel, hmstate, hstate, hlt, g, hpQ, hdiv]
      _ = (∑ p ∈ T.image (fun n => n / m), g p) / erdos_weight m := by
        rw [← Finset.sum_div, Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        have hadvd := oddBM_downward_kernel_support_dvd hQ ha'.2
        have hbdvd := oddBM_downward_kernel_support_dvd hQ hb'.2
        calc
          a = m * (a / m) := (Nat.mul_div_cancel' hadvd).symm
          _ = m * (b / m) := congrArg (fun q => m * q) hab
          _ = b := Nat.mul_div_cancel' hbdvd
      _ ≤ erdos_weight m / erdos_weight m := by
        exact div_le_div_of_nonneg_right
          (oddBM_weighted_prime_parents_le hk hQ hmstate
            (T.image fun n => n / m)) hwpos.le
      _ = 1 := div_self hwpos.ne'
  · simp [oddBM_upward_kernel, hmstate]

noncomputable def oddBM_hittingWeight (k : ℕ) (Q : Set ℕ) (n : ℕ) : ℝ :=
  (oddBM_state k Q).indicator erdos_weight n

lemma oddBM_hittingWeight_nonneg {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (n : ℕ) :
    0 ≤ oddBM_hittingWeight k Q n := by
  classical
  rw [oddBM_hittingWeight]
  by_cases hn : n ∈ oddBM_state k Q
  · rw [Set.indicator_of_mem hn, erdos_weight]
    have hnpos := oddBM_state_positive_of_odd_primes hQ hn
    have hn1 := oddBM_state_one_lt hk hQ hn
    positivity
  · rw [Set.indicator_of_notMem hn]

lemma oddBM_hittingWeight_recurrence {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) : ∀ n, 1 ≤ n →
    oddBM_hittingWeight k Q n =
      (oddBM_terminal k Q).indicator (oddBM_hittingWeight k Q) n +
        ∑' q : ℕ, if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          oddBM_hittingWeight k Q (n / q) *
            oddBM_upward_kernel k Q (some (n / q)) (some n)
        else 0 := by
  intro n hn
  classical
  by_cases hnstate : n ∈ oddBM_state k Q
  · by_cases hterm : n ∈ oddBM_terminal k Q
    · have hnnext : n ∉ oddBM_state (k + 1) Q := by
        intro h
        have hge := h.1
        have heq := hterm.1
        change k + 1 ≤ ArithmeticFunction.cardFactors n at hge
        change ArithmeticFunction.cardFactors n = k at heq
        omega
      have hzero : ∀ q : ℕ, (if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          oddBM_hittingWeight k Q (n / q) *
            oddBM_upward_kernel k Q (some (n / q)) (some n)
        else 0) = 0 := by
        intro q
        split_ifs
        · simp [oddBM_upward_kernel, hnnext]
        · rfl
      rw [tsum_congr hzero, tsum_zero, add_zero,
        Set.indicator_of_mem hterm]
    · have hnnext : n ∈ oddBM_state (k + 1) Q := by
        refine ⟨?_, hnstate.2⟩
        change k + 1 ≤ ArithmeticFunction.cardFactors n
        have hge := hnstate.1
        change k ≤ ArithmeticFunction.cardFactors n at hge
        have hne : ArithmeticFunction.cardFactors n ≠ k := fun h =>
          hterm ⟨h, hnstate.2⟩
        omega
      have hnpos := oddBM_state_positive_of_odd_primes hQ hnstate
      have hn0 : n ≠ 0 := hnpos.ne'
      have hdiag : oddBM_downward_kernel k Q n n = 0 := by
        by_contra h
        exact (Nat.lt_irrefl n)
          (oddBM_downward_kernel_support_lt_of_nonterminal hQ hterm h)
      have hfinite : (∑' q : ℕ, if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          oddBM_hittingWeight k Q (n / q) *
            oddBM_upward_kernel k Q (some (n / q)) (some n)
        else 0) = ∑ q ∈ n.divisors, if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          oddBM_hittingWeight k Q (n / q) *
            oddBM_upward_kernel k Q (some (n / q)) (some n)
        else 0 := by
        refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
          (s := n.divisors) ?_
        intro q hq
        rw [if_neg]
        exact fun h => hq (Nat.mem_divisors.mpr ⟨h.2.1, hn0⟩)
      have hterm_eq : ∀ q ∈ n.divisors,
          (if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
            oddBM_hittingWeight k Q (n / q) *
              oddBM_upward_kernel k Q (some (n / q)) (some n)
          else 0) = erdos_weight n * oddBM_downward_kernel k Q n (n / q) := by
        intro q hq
        have hqdvd := (Nat.mem_divisors.mp hq).1
        have hqpos := Nat.pos_of_mem_divisors hq
        by_cases hq1 : q = 1
        · subst q
          simp [hdiag]
        · have hqgt : 1 < q := by omega
          have hdivpos : 0 < n / q := Nat.div_pos
            (Nat.le_of_dvd hnpos hqdvd) hqpos
          rw [if_pos ⟨hqgt, hqdvd, hdivpos⟩]
          by_cases hker : oddBM_downward_kernel k Q n (n / q) = 0
          · simp [hker, oddBM_upward_kernel]
          · have hmstate := oddBM_downward_kernel_support_source_state hQ hterm hker
            have hlt := oddBM_downward_kernel_support_lt_of_nonterminal hQ hterm hker
            have hwpos : 0 < erdos_weight (n / q) := by
              rw [erdos_weight]
              have hm1 := oddBM_state_one_lt hk hQ hmstate
              exact one_div_pos.mpr (mul_pos (by exact_mod_cast hdivpos)
                (Real.log_pos (by exact_mod_cast hm1)))
            rw [oddBM_hittingWeight, Set.indicator_of_mem hmstate,
              oddBM_upward_kernel, if_pos ⟨hmstate, hnnext, hlt⟩]
            field_simp [hwpos.ne']
      rw [Set.indicator_of_notMem hterm, zero_add, hfinite,
        Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum,
        Nat.sum_div_divisors n (oddBM_downward_kernel k Q n),
        oddBM_downward_kernel_nonterminal_row_sum hQ hterm hnnext, mul_one,
        oddBM_hittingWeight, Set.indicator_of_mem hnstate]
  · have hterm : n ∉ oddBM_terminal k Q := fun h =>
      hnstate (oddBM_terminal_subset_state k Q h)
    have hnnext : n ∉ oddBM_state (k + 1) Q := fun h =>
      hnstate (oddBM_state_antitone (Nat.le_succ k) Q h)
    have hzero : ∀ q : ℕ, (if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
        oddBM_hittingWeight k Q (n / q) *
          oddBM_upward_kernel k Q (some (n / q)) (some n)
      else 0) = 0 := by
      intro q
      split_ifs
      · simp [oddBM_upward_kernel, hnnext]
      · rfl
    rw [oddBM_hittingWeight, Set.indicator_of_notMem hnstate,
      Set.indicator_of_notMem hterm, zero_add, tsum_congr hzero, tsum_zero]

/-- `p` is the least prime factor of `n`, stated without committing to a
particular least-prime-factor implementation. -/
abbrev IsLeastPrimeFactor (p n : ℕ) : Prop :=
  n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q -> q ∣ n -> p ≤ q

lemma IsLeastPrimeFactor.ne_zero {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    n ≠ 0 :=
  h.1

/-- A least prime factor is prime. -/
lemma IsLeastPrimeFactor.prime {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    Nat.Prime p :=
  h.2.1

/-- A least prime factor divides the number. -/
lemma IsLeastPrimeFactor.dvd {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    p ∣ n :=
  h.2.2.1

/-- A least prime factor is no larger than any other prime divisor. -/
lemma IsLeastPrimeFactor.le_of_prime_dvd {p q n : ℕ}
    (h : IsLeastPrimeFactor p n) (hq : Nat.Prime q) (hqn : q ∣ n) :
    p ≤ q :=
  h.2.2.2 q hq hqn

lemma IsLeastPrimeFactor.ne_one {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    n ≠ 1 := by
  intro hn
  have hp_dvd_one : p ∣ 1 := by
    simpa [hn] using IsLeastPrimeFactor.dvd h
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hp_dvd_one
  have hp_two : 2 ≤ p := (IsLeastPrimeFactor.prime h).two_le
  omega

lemma IsLeastPrimeFactor.one_lt {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    1 < n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (IsLeastPrimeFactor.ne_zero h)
  have hne_one : n ≠ 1 := IsLeastPrimeFactor.ne_one h
  omega

lemma IsLeastPrimeFactor.two_dvd {n : ℕ} (h : IsLeastPrimeFactor 2 n) :
    2 ∣ n :=
  IsLeastPrimeFactor.dvd h

/-- The paper's notion that a prime is Erdős-strong. -/
abbrev erdos_strong (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∀ A : Set ℕ, primitive_set A ->
      (∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_weight p

/-- An Erdős-strong number is prime. -/
lemma erdos_strong.prime {p : ℕ} (hp : erdos_strong p) :
    Nat.Prime p :=
  hp.1

/-- The bound supplied by an Erdős-strong prime. -/
lemma erdos_strong.bound {p : ℕ} (hp : erdos_strong p) {A : Set ℕ}
    (hA : primitive_set A) (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) :
    Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
      erdos_sum A ≤ erdos_weight p :=
  hp.2 A hA hlpf

/-!
### Shifted weights for Erdős-strong primes
-/

/-- The shifted Erdős weight `1 / (n log (p n))` used in the proof that `p` is
Erdős-strong. -/
noncomputable def erdos_shift_weight (p n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log ((p * n : ℕ) : ℝ))

lemma erdos_shift_weight_pos {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    0 < erdos_shift_weight p n := by
  rw [erdos_shift_weight]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpn_gt_one_nat : 1 < p * n := by
    have hn_one : 1 ≤ n := Nat.succ_le_of_lt hn
    have hp_le_pn : p ≤ p * n := by
      simpa using Nat.mul_le_mul_left p hn_one
    exact lt_of_lt_of_le hp hp_le_pn
  have hpn_gt_one : (1 : ℝ) < ((p * n : ℕ) : ℝ) := by
    exact_mod_cast hpn_gt_one_nat
  have hlog_pos : 0 < Real.log (((p * n : ℕ) : ℝ)) :=
    Real.log_pos hpn_gt_one
  exact one_div_pos.mpr (mul_pos hn_real_pos hlog_pos)

lemma erdos_shift_weight_nonneg {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    0 ≤ erdos_shift_weight p n :=
  (erdos_shift_weight_pos hp hn).le

lemma erdos_weight_mul_eq_inv_mul_shift {p n : ℕ}
    (hp : p ≠ 0) (hn : n ≠ 0) (hpn : 1 < p * n) :
    erdos_weight (p * n) = (1 / (p : ℝ)) * erdos_shift_weight p n := by
  rw [erdos_weight, erdos_shift_weight]
  have hp_real_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hn_real_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hlog_ne : Real.log (((p * n : ℕ) : ℝ)) ≠ 0 := by
    have hpn_real : (1 : ℝ) < ((p * n : ℕ) : ℝ) := by exact_mod_cast hpn
    exact (Real.log_pos hpn_real).ne'
  norm_num [Nat.cast_mul]
  field_simp [hp_real_ne, hn_real_ne, hlog_ne]

/-- The shifted weight needed for the statement that `2` is Erdős-strong. -/
noncomputable def erdos_two_shift_weight (n : ℕ) : ℝ :=
  erdos_shift_weight 2 n

lemma erdos_two_shift_weight_eq (n : ℕ) :
    erdos_two_shift_weight n = erdos_shift_weight 2 n :=
  rfl

lemma erdos_two_shift_weight_one :
    erdos_two_shift_weight 1 = 1 / Real.log (2 : ℝ) := by
  norm_num [erdos_two_shift_weight, erdos_shift_weight]

lemma erdos_two_shift_weight_pos {n : ℕ} (hn : 0 < n) :
    0 < erdos_two_shift_weight n := by
  rw [erdos_two_shift_weight, erdos_shift_weight]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have htwo_n_gt_one : (1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have hn_one : 1 ≤ n := Nat.succ_le_of_lt hn
    have htwo_le : 2 ≤ 2 * n := by
      simpa using Nat.mul_le_mul_left 2 hn_one
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo_le)
  have hlog_pos : 0 < Real.log (((2 * n : ℕ) : ℝ)) :=
    Real.log_pos htwo_n_gt_one
  exact one_div_pos.mpr (mul_pos hn_real_pos hlog_pos)

lemma erdos_two_shift_weight_nonneg_of_pos {n : ℕ} (hn : 0 < n) :
    0 ≤ erdos_two_shift_weight n :=
  (erdos_two_shift_weight_pos hn).le

lemma erdos_two_shift_weight_nonneg_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ erdos_two_shift_weight n :=
  erdos_two_shift_weight_nonneg_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)

lemma erdos_weight_two_mul_eq_half_shift {n : ℕ} (hn : n ≠ 0) :
    erdos_weight (2 * n) = (1 / 2 : ℝ) * erdos_two_shift_weight n := by
  rw [erdos_weight, erdos_two_shift_weight, erdos_shift_weight]
  have hn_real_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have htwo_n_gt_one : (1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_one : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    have htwo_le : 2 ≤ 2 * n := by
      simpa using Nat.mul_le_mul_left 2 hn_one
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo_le)
  have hlog_ne : Real.log (((2 * n : ℕ) : ℝ)) ≠ 0 :=
    (Real.log_pos htwo_n_gt_one).ne'
  norm_num [Nat.cast_mul]
  field_simp [hn_real_ne, hlog_ne]

lemma erdos_two_shift_weight_one_eq_two_mul_erdos_weight_two :
    erdos_two_shift_weight 1 = 2 * erdos_weight 2 := by
  have h := erdos_weight_two_mul_eq_half_shift (n := 1) (by norm_num : (1 : ℕ) ≠ 0)
  norm_num at h
  linarith

/-- The von Mangoldt tail kernel with a fixed multiplicative shift in the
second logarithm. The case `c = 2` is the analytic kernel used for the
2-strong argument. -/
noncomputable def mangoldt_shifted_tail_term (c m q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q /
    ((q : ℝ) * Real.log (((m * q : ℕ) : ℝ)) *
      Real.log (((c * m * q : ℕ) : ℝ)))

lemma mangoldt_shifted_tail_term_nonneg {c m q : ℕ}
    (hmq : 1 < m * q) (hcmq : 1 < c * m * q) :
    0 ≤ mangoldt_shifted_tail_term c m q := by
  rw [mangoldt_shifted_tail_term]
  have hq_pos_nat : 0 < q := by
    by_contra hq
    have hq_zero : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    simp at hmq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hmq_real : (1 : ℝ) < ((m * q : ℕ) : ℝ) := by exact_mod_cast hmq
  have hcmq_real : (1 : ℝ) < ((c * m * q : ℕ) : ℝ) := by exact_mod_cast hcmq
  have hlog_mq_pos : 0 < Real.log (((m * q : ℕ) : ℝ)) := Real.log_pos hmq_real
  have hlog_cmq_pos : 0 < Real.log (((c * m * q : ℕ) : ℝ)) := Real.log_pos hcmq_real
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (mul_nonneg hq_pos.le hlog_mq_pos.le) hlog_cmq_pos.le)

/-- The shifted von Mangoldt tail sum above a lower cutoff. -/
noncomputable def mangoldt_shifted_tail_sum (c m : ℕ) (y : ℝ) : ℝ :=
  ∑' q : ℕ, if y ≤ (q : ℝ) then mangoldt_shifted_tail_term c m q else 0

/-- The shifted tail term specialized to the 2-strong argument. -/
noncomputable def mangoldt_two_shifted_tail_term (m q : ℕ) : ℝ :=
  mangoldt_shifted_tail_term 2 m q

lemma mangoldt_two_shifted_tail_term_eq (m q : ℕ) :
    mangoldt_two_shifted_tail_term m q = mangoldt_shifted_tail_term 2 m q :=
  rfl

lemma mangoldt_two_shifted_tail_term_nonneg_of_one_le_of_two_le {m q : ℕ}
    (hm : 1 ≤ m) (hq : 2 ≤ q) :
    0 ≤ mangoldt_two_shifted_tail_term m q := by
  rw [mangoldt_two_shifted_tail_term_eq]
  have hmq_two : 2 ≤ m * q := by
    simpa using Nat.mul_le_mul hm hq
  have hmq : 1 < m * q := lt_of_lt_of_le Nat.one_lt_two hmq_two
  have hcmq : 1 < 2 * m * q := by
    have hfour : 4 ≤ 2 * (m * q) := by
      simpa using Nat.mul_le_mul_left 2 hmq_two
    simpa [Nat.mul_assoc] using lt_of_lt_of_le (by norm_num : 1 < 4) hfour
  exact mangoldt_shifted_tail_term_nonneg hmq hcmq

lemma erdos_two_shift_weight_mul_vonMangoldt_div_log_eq_scaled_shifted_tail
    {m q : ℕ} (hmq : 1 < m * q) :
    erdos_two_shift_weight (m * q) * ArithmeticFunction.vonMangoldt q /
        Real.log (((m * q : ℕ) : ℝ)) =
      (1 / (m : ℝ)) * mangoldt_two_shifted_tail_term m q := by
  rw [erdos_two_shift_weight, erdos_shift_weight, mangoldt_two_shifted_tail_term,
    mangoldt_shifted_tail_term]
  have hm_ne_zero : m ≠ 0 := by
    intro hm
    subst m
    simp at hmq
  have hq_ne_zero : q ≠ 0 := by
    intro hq
    subst q
    simp at hmq
  have hm_real_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm_ne_zero
  have hq_real_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq_ne_zero
  have hmq_real : (1 : ℝ) < ((m * q : ℕ) : ℝ) := by exact_mod_cast hmq
  have hlog_mq_ne : Real.log (((m * q : ℕ) : ℝ)) ≠ 0 :=
    (Real.log_pos hmq_real).ne'
  have htwo_mq : 1 < 2 * m * q := by
    have hmq_two : 2 ≤ m * q := hmq
    have hfour : 4 ≤ 2 * (m * q) := by
      simpa using Nat.mul_le_mul_left 2 hmq_two
    simpa [Nat.mul_assoc] using lt_of_lt_of_le (by norm_num : 1 < 4) hfour
  have htwo_mq_real : (1 : ℝ) < ((2 * m * q : ℕ) : ℝ) := by
    exact_mod_cast htwo_mq
  have hlog_two_mq_ne : Real.log (((2 * m * q : ℕ) : ℝ)) ≠ 0 :=
    (Real.log_pos htwo_mq_real).ne'
  norm_num [Nat.cast_mul]
  field_simp [hm_real_ne, hq_real_ne, hlog_mq_ne, hlog_two_mq_ne]

/-- The shifted tail sum specialized to the 2-strong argument. -/
noncomputable def mangoldt_two_shifted_tail_sum (m : ℕ) (y : ℝ) : ℝ :=
  mangoldt_shifted_tail_sum 2 m y

lemma mangoldt_two_shifted_tail_sum_eq (m : ℕ) (y : ℝ) :
    mangoldt_two_shifted_tail_sum m y = mangoldt_shifted_tail_sum 2 m y :=
  rfl

/-- Preimage of a set under multiplication by a fixed natural. -/
def multiplicative_preimage (c : ℕ) (A : Set ℕ) : Set ℕ :=
  {n : ℕ | c * n ∈ A}

lemma mem_multiplicative_preimage {c n : ℕ} {A : Set ℕ} :
    n ∈ multiplicative_preimage c A ↔ c * n ∈ A :=
  Iff.rfl

lemma multiplicative_preimage_primitive {c : ℕ} (hc : c ≠ 0) {A : Set ℕ}
    (hA : primitive_set A) :
    primitive_set (multiplicative_preimage c A) := by
  intro a ha b hb hne hdvd
  change c * a ∈ A at ha
  change c * b ∈ A at hb
  have hdiv : c * a ∣ c * b := by
    rcases hdvd with ⟨d, rfl⟩
    exact ⟨d, by simp [Nat.mul_assoc]⟩
  have hcab : c * a = c * b := hA.eq ha hb hdiv
  have hab : a = b := Nat.mul_left_cancel (Nat.pos_of_ne_zero hc) hcab
  exact hne hab

lemma multiplicative_preimage_two_primitive {A : Set ℕ} (hA : primitive_set A) :
    primitive_set (multiplicative_preimage 2 A) :=
  multiplicative_preimage_primitive (by norm_num : (2 : ℕ) ≠ 0) hA

lemma IsLeastPrimeFactor.exists_eq_mul {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    ∃ m : ℕ, n = p * m :=
  IsLeastPrimeFactor.dvd h

lemma isLeastPrimeFactor_two_iff {n : ℕ} :
    IsLeastPrimeFactor 2 n ↔ n ≠ 0 ∧ 2 ∣ n := by
  constructor
  · intro h
    exact ⟨IsLeastPrimeFactor.ne_zero h, IsLeastPrimeFactor.dvd h⟩
  · rintro ⟨hn0, h2n⟩
    exact ⟨hn0, Nat.prime_two, h2n, fun q hq _ => hq.two_le⟩

lemma image_mul_multiplicative_preimage_subset (c : ℕ) (A : Set ℕ) :
    (fun n : ℕ => c * n) '' multiplicative_preimage c A ⊆ A := by
  rintro n ⟨m, hm, rfl⟩
  exact hm

lemma subset_image_mul_multiplicative_preimage_of_dvd {c : ℕ} {A : Set ℕ}
    (hdiv : ∀ n : ℕ, n ∈ A -> c ∣ n) :
    A ⊆ (fun n : ℕ => c * n) '' multiplicative_preimage c A := by
  intro n hn
  rcases hdiv n hn with ⟨m, rfl⟩
  exact ⟨m, hn, rfl⟩

lemma image_mul_multiplicative_preimage_eq_of_dvd {c : ℕ} {A : Set ℕ}
    (hdiv : ∀ n : ℕ, n ∈ A -> c ∣ n) :
    (fun n : ℕ => c * n) '' multiplicative_preimage c A = A :=
  Set.Subset.antisymm
    (image_mul_multiplicative_preimage_subset c A)
    (subset_image_mul_multiplicative_preimage_of_dvd hdiv)

lemma image_mul_multiplicative_preimage_eq_of_least_prime_factor {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) :
    (fun n : ℕ => p * n) '' multiplicative_preimage p A = A := by
  apply image_mul_multiplicative_preimage_eq_of_dvd
  intro n hn
  exact IsLeastPrimeFactor.dvd (hlpf n hn)

lemma image_two_mul_multiplicative_preimage_eq_of_least_prime_factor {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) :
    (fun n : ℕ => 2 * n) '' multiplicative_preimage 2 A = A :=
  image_mul_multiplicative_preimage_eq_of_least_prime_factor hlpf

lemma multiplicative_preimage_positive_of_least_prime_factor {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage p A) :
    0 < m := by
  by_contra hmpos
  have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
  have hpm_ne_zero : p * m ≠ 0 := IsLeastPrimeFactor.ne_zero (hlpf (p * m) hm)
  exact hpm_ne_zero (by simp [hmzero])

lemma multiplicative_preimage_two_positive_of_least_prime_factor {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage 2 A) :
    0 < m :=
  multiplicative_preimage_positive_of_least_prime_factor hlpf hm

lemma zero_not_mem_multiplicative_preimage_two_of_least_prime_factor {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) :
    0 ∉ multiplicative_preimage 2 A :=
  fun h0 => Nat.lt_irrefl 0
    (multiplicative_preimage_two_positive_of_least_prime_factor hlpf h0)

lemma erdos_weight_mul_eq_inv_mul_shift_of_mem_preimage {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage p A) :
    erdos_weight (p * m) = (1 / (p : ℝ)) * erdos_shift_weight p m := by
  have hpm_lpf : IsLeastPrimeFactor p (p * m) := hlpf (p * m) hm
  exact erdos_weight_mul_eq_inv_mul_shift
    (IsLeastPrimeFactor.prime hpm_lpf).ne_zero
    (Nat.ne_of_gt (multiplicative_preimage_positive_of_least_prime_factor hlpf hm))
    (IsLeastPrimeFactor.one_lt hpm_lpf)

lemma erdos_weight_two_mul_eq_half_shift_of_mem_preimage {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage 2 A) :
    erdos_weight (2 * m) = (1 / 2 : ℝ) * erdos_two_shift_weight m := by
  simpa [erdos_two_shift_weight] using
    erdos_weight_mul_eq_inv_mul_shift_of_mem_preimage hlpf hm

lemma erdos_weight_indicator_two_mul_eq_half_shift_preimage {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) (n : ℕ) :
    A.indicator erdos_weight (2 * n) =
      (1 / 2 : ℝ) *
        (multiplicative_preimage 2 A).indicator erdos_two_shift_weight n := by
  classical
  by_cases hn : n ∈ multiplicative_preimage 2 A
  · have h2n : 2 * n ∈ A := hn
    rw [Set.indicator_of_mem h2n, Set.indicator_of_mem hn]
    exact erdos_weight_two_mul_eq_half_shift_of_mem_preimage hlpf hn
  · have h2n : 2 * n ∉ A := hn
    rw [Set.indicator_of_notMem h2n, Set.indicator_of_notMem hn]
    ring

lemma erdos_weight_finset_sum_two_mul_eq_half_shift_preimage {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) (F : Finset ℕ) :
    (∑ n ∈ F, A.indicator erdos_weight (2 * n)) =
      (1 / 2 : ℝ) *
        ∑ n ∈ F, (multiplicative_preimage 2 A).indicator erdos_two_shift_weight n := by
  calc
    (∑ n ∈ F, A.indicator erdos_weight (2 * n)) =
        ∑ n ∈ F,
          (1 / 2 : ℝ) *
            (multiplicative_preimage 2 A).indicator erdos_two_shift_weight n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact erdos_weight_indicator_two_mul_eq_half_shift_preimage hlpf n
    _ = (1 / 2 : ℝ) *
        ∑ n ∈ F, (multiplicative_preimage 2 A).indicator erdos_two_shift_weight n := by
      rw [Finset.mul_sum]

lemma erdos_shift_weight_pos_of_mem_preimage {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage p A) :
    0 < erdos_shift_weight p m := by
  have hpm_lpf : IsLeastPrimeFactor p (p * m) := hlpf (p * m) hm
  exact erdos_shift_weight_pos
    (IsLeastPrimeFactor.prime hpm_lpf).one_lt
    (multiplicative_preimage_positive_of_least_prime_factor hlpf hm)

lemma erdos_two_shift_weight_pos_of_mem_preimage {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor 2 n) {m : ℕ}
    (hm : m ∈ multiplicative_preimage 2 A) :
    0 < erdos_two_shift_weight m := by
  simpa [erdos_two_shift_weight] using erdos_shift_weight_pos_of_mem_preimage hlpf hm

/-!
### AKS multiplicative-walk data
-/

/-- A number is `x`-rough if all of its prime divisors are at least `x`. -/
abbrev IsXRough (x : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p -> p ∣ n -> x ≤ (p : ℝ)

lemma IsXRough.mono_left {x y : ℝ} {n : ℕ} (hxy : x ≤ y)
    (hn : IsXRough y n) :
    IsXRough x n := by
  intro p hp hpn
  exact le_trans hxy (hn p hp hpn)

lemma IsLeastPrimeFactor.isXRough {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    IsXRough (p : ℝ) n := by
  intro q hq hqn
  exact_mod_cast IsLeastPrimeFactor.le_of_prime_dvd h hq hqn

lemma IsXRough.of_le_two {x : ℝ} (hx : x ≤ 2) (n : ℕ) :
    IsXRough x n := by
  intro p hp _hpn
  exact hx.trans (by exact_mod_cast hp.two_le)

lemma IsXRough.one (x : ℝ) :
    IsXRough x 1 := by
  intro p hp hp_dvd_one
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hp_dvd_one
  have hp_two : 2 ≤ p := hp.two_le
  omega

lemma isXRough_two (n : ℕ) :
    IsXRough 2 n :=
  IsXRough.of_le_two le_rfl n

lemma IsXRough.not_zero_of_two_lt {x : ℝ} {n : ℕ}
    (hx : 2 < x) (hn : IsXRough x n) :
    n ≠ 0 := by
  intro hn_zero
  have hx_le_two : x ≤ (2 : ℝ) := by
    exact hn 2 Nat.prime_two (by rw [hn_zero]; exact dvd_zero 2)
  linarith

/-- The set of `x`-rough integers used in the AKS and Erdős-strong arguments. -/
def rough_numbers (x : ℝ) : Set ℕ :=
  {n : ℕ | IsXRough x n}

lemma mem_rough_numbers {x : ℝ} {n : ℕ} :
    n ∈ rough_numbers x ↔ IsXRough x n :=
  Iff.rfl

lemma IsLeastPrimeFactor.mem_rough_numbers {p n : ℕ} (h : IsLeastPrimeFactor p n) :
    n ∈ rough_numbers (p : ℝ) :=
  IsLeastPrimeFactor.isXRough h

lemma one_mem_rough_numbers (x : ℝ) :
    1 ∈ rough_numbers x :=
  IsXRough.one x

lemma subset_rough_numbers_of_least_prime_factor {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) :
    A ⊆ rough_numbers (p : ℝ) := by
  intro n hn
  exact IsLeastPrimeFactor.mem_rough_numbers (hlpf n hn)

lemma multiplicative_preimage_subset_rough_numbers_of_least_prime_factor
    {p : ℕ} {A : Set ℕ}
    (hlpf : ∀ n : ℕ, n ∈ A -> IsLeastPrimeFactor p n) :
    multiplicative_preimage p A ⊆ rough_numbers (p : ℝ) := by
  intro m hm q hq hqm
  have hpm_lpf : IsLeastPrimeFactor p (p * m) := hlpf (p * m) hm
  have hm_dvd_pm : m ∣ p * m := ⟨p, by rw [Nat.mul_comm]⟩
  have hq_dvd_pm : q ∣ p * m := dvd_trans hqm hm_dvd_pm
  exact_mod_cast IsLeastPrimeFactor.le_of_prime_dvd hpm_lpf hq hq_dvd_pm

lemma rough_numbers_antitone {x y : ℝ} (hxy : x ≤ y) :
    rough_numbers y ⊆ rough_numbers x := by
  intro n hn
  exact IsXRough.mono_left hxy hn

lemma rough_numbers_two_eq_univ :
    rough_numbers 2 = Set.univ := by
  ext n
  exact ⟨fun _ => Set.mem_univ n, fun _ => isXRough_two n⟩

lemma rough_numbers_subset_nonzero_of_two_lt {x : ℝ} (hx : 2 < x) :
    rough_numbers x ⊆ {n : ℕ | n ≠ 0} := by
  intro _ hn
  exact IsXRough.not_zero_of_two_lt hx hn

lemma rough_mul_small_right_injective {x : ℝ} {n₁ n₂ d₁ d₂ : ℕ}
    (hx : 2 < x) (hn₁ : IsXRough x n₁) (hn₂ : IsXRough x n₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₁x : (d₁ : ℝ) < x)
    (hd₂x : (d₂ : ℝ) < x) (hprod : n₁ * d₁ = n₂ * d₂) :
    d₁ = d₂ := by
  have hn₁0 := IsXRough.not_zero_of_two_lt hx hn₁
  have hn₂0 := IsXRough.not_zero_of_two_lt hx hn₂
  have hfac := congrArg Nat.factorization hprod
  rw [Nat.factorization_mul hn₁0 hd₁.ne',
    Nat.factorization_mul hn₂0 hd₂.ne'] at hfac
  apply Nat.factorization_inj hd₁.ne' hd₂.ne'
  ext p
  by_cases hp : Nat.Prime p
  · by_cases hpd : p ∣ d₁ ∨ p ∣ d₂
    · have hpx : (p : ℝ) < x := by
        rcases hpd with hpd | hpd
        · exact (by exact_mod_cast Nat.le_of_dvd hd₁ hpd : (p : ℝ) ≤ d₁).trans_lt hd₁x
        · exact (by exact_mod_cast Nat.le_of_dvd hd₂ hpd : (p : ℝ) ≤ d₂).trans_lt hd₂x
      have hn₁fac : n₁.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr <| Or.inl fun hpn => not_le_of_gt hpx (hn₁ p hp hpn)
      have hn₂fac : n₂.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr <| Or.inl fun hpn => not_le_of_gt hpx (hn₂ p hp hpn)
      have := Finsupp.ext_iff.mp hfac p
      simpa [hn₁fac, hn₂fac] using this
    · have hpd₁ : ¬p ∣ d₁ := fun h => hpd (Or.inl h)
      have hpd₂ : ¬p ∣ d₂ := fun h => hpd (Or.inr h)
      simp [Nat.factorization_eq_zero_of_not_dvd hpd₁,
        Nat.factorization_eq_zero_of_not_dvd hpd₂]
  · simp [hp]

lemma log_nat_le_reciprocal_sum_Ico (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ≤ ∑ d ∈ Finset.Ico 1 N, 1 / (d : ℝ) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 / t)
      (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro a ha b hb hab
    exact one_div_le_one_div_of_le
      (show 0 < a from lt_of_lt_of_le (by norm_num) ha.1) hab
  have hint := AntitoneOn.integral_le_sum_Ico
    (f := fun t : ℝ => 1 / t) hN hanti
  rw [integral_one_div] at hint
  · simpa using hint
  · rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    exact fun h => (show ¬ (((1 : ℕ) : ℝ) ≤ (0 : ℝ)) by norm_num) h.1

lemma reciprocal_le_inv_rpow {s : ℝ} (hs : s ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ 1 / Real.rpow (n : ℝ) s := by
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) s)
  calc
    Real.rpow (n : ℝ) s ≤ Real.rpow (n : ℝ) 1 :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hs
    _ = n := Real.rpow_one _

lemma inv_rpow_sum_Icc_le {T s : ℝ} (hT : 1 ≤ T)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (∑ n ∈ Finset.Icc 1 ⌊T⌋₊, 1 / Real.rpow (n : ℝ) s) ≤
      Real.rpow T (1 - s) / (1 - s) := by
  let N := ⌊T⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hT)
  have hanti : AntitoneOn (fun t : ℝ => 1 / Real.rpow t s)
      (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro a ha b hb hab
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [ha.1]) s)
      (Real.rpow_le_rpow (by linarith [ha.1]) hab hs0.le)
  have hanti' : AntitoneOn (fun t : ℝ => 1 / Real.rpow t s)
      (Set.Icc 1 ((1 : ℝ) + (N - 1 : ℕ))) := by
    convert hanti using 1
    rw [Nat.cast_sub hN]
    norm_num
  have hint := AntitoneOn.sum_le_integral
    (f := fun t : ℝ => 1 / Real.rpow t s) hanti'
  have hsum : (∑ n ∈ Finset.Icc 1 N, 1 / Real.rpow (n : ℝ) s) =
      1 + ∑ i ∈ Finset.range (N - 1),
        1 / Real.rpow ((1 : ℝ) + (i + 1 : ℕ)) s := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext n; simp,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [show N = (N - 1) + 1 by omega, Finset.sum_range_succ']
    simp [add_comm]
  have hint' : (∑ i ∈ Finset.range (N - 1),
      1 / Real.rpow ((1 : ℝ) + (i + 1 : ℕ)) s) ≤
      ∫ t : ℝ in 1..N, t ^ (-s) := by
    have hend : (1 : ℝ) + (N - 1 : ℕ) = N := by
      rw [Nat.cast_sub hN]
      norm_num
    rw [hend] at hint
    calc
      _ ≤ ∫ t : ℝ in 1..N, 1 / Real.rpow t s := hint
      _ = ∫ t : ℝ in 1..N, t ^ (-s) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by exact_mod_cast hN)] at ht
        simpa [one_div] using
          (Real.rpow_neg (zero_le_one.trans ht.1) s).symm
  rw [integral_rpow (Or.inl (by linarith))] at hint'
  rw [hsum]
  have hNpow : Real.rpow (N : ℝ) (1 - s) ≤ Real.rpow T (1 - s) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N)
      (Nat.floor_le (by linarith : 0 ≤ T)) (by linarith)
  calc
    1 + ∑ i ∈ Finset.range (N - 1),
        1 / Real.rpow ((1 : ℝ) + (i + 1 : ℕ)) s ≤
        1 + ((N : ℝ) ^ (-s + 1) - 1 ^ (-s + 1)) / (-s + 1) :=
      by simpa [add_comm] using add_le_add_left hint' 1
    _ = 1 + (Real.rpow (N : ℝ) (1 - s) - 1) / (1 - s) := by
      have he : -s + 1 = 1 - s := by ring
      rw [he, Real.one_rpow]
      rfl
    _ ≤ Real.rpow (N : ℝ) (1 - s) / (1 - s) := by
      have hsden : 0 < 1 - s := by linarith
      rw [le_div_iff₀ hsden]
      field_simp
      nlinarith
    _ ≤ Real.rpow T (1 - s) / (1 - s) :=
      div_le_div_of_nonneg_right hNpow (by linarith)

/-- Prime powers `p^j` with `p ≤ x` and `j ≥ 1`, used as increments in the
AKS multiplicative random walk. -/
abbrev IsSmallPrimePower (x : ℝ) (q : ℕ) : Prop :=
  ∃ p j : ℕ, Nat.Prime p ∧ 1 ≤ j ∧ (p : ℝ) ≤ x ∧ q = p ^ j

lemma IsSmallPrimePower.mono_left {x y : ℝ} {q : ℕ} (hxy : x ≤ y)
    (hq : IsSmallPrimePower x q) :
    IsSmallPrimePower y q := by
  rcases hq with ⟨p, j, hp, hj, hpx, hqeq⟩
  exact ⟨p, j, hp, hj, hpx.trans hxy, hqeq⟩

lemma IsSmallPrimePower.one_lt {x : ℝ} {q : ℕ} (hq : IsSmallPrimePower x q) :
    1 < q := by
  rcases hq with ⟨p, j, hp, hj, _hpx, rfl⟩
  have hj_pos : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj
  exact Nat.one_lt_pow (Nat.ne_of_gt hj_pos) hp.one_lt

lemma IsSmallPrimePower.pos {x : ℝ} {q : ℕ} (hq : IsSmallPrimePower x q) :
    0 < q :=
  Nat.lt_trans Nat.zero_lt_one (IsSmallPrimePower.one_lt hq)

lemma IsSmallPrimePower.ne_zero {x : ℝ} {q : ℕ} (hq : IsSmallPrimePower x q) :
    q ≠ 0 :=
  Nat.ne_of_gt (IsSmallPrimePower.pos hq)

lemma IsSmallPrimePower.ne_one {x : ℝ} {q : ℕ} (hq : IsSmallPrimePower x q) :
    q ≠ 1 :=
  Nat.ne_of_gt (IsSmallPrimePower.one_lt hq)

/-- The AKS increment support: prime powers generated by primes at most `x`. -/
def small_prime_powers (x : ℝ) : Set ℕ :=
  {q : ℕ | IsSmallPrimePower x q}

lemma mem_small_prime_powers {x : ℝ} {q : ℕ} :
    q ∈ small_prime_powers x ↔ IsSmallPrimePower x q :=
  Iff.rfl

lemma small_prime_powers_of_prime {x : ℝ} {p : ℕ}
    (hp : Nat.Prime p) (hpx : (p : ℝ) ≤ x) :
    p ∈ small_prime_powers x :=
  ⟨p, 1, hp, by norm_num, hpx, by simp⟩

lemma small_prime_powers_mono {x y : ℝ} (hxy : x ≤ y) :
    small_prime_powers x ⊆ small_prime_powers y := by
  intro q hq
  exact IsSmallPrimePower.mono_left hxy hq

lemma small_prime_powers_subset_positive (x : ℝ) :
    small_prime_powers x ⊆ {q : ℕ | 0 < q} := by
  intro _ hq
  exact IsSmallPrimePower.pos hq

lemma small_prime_powers_subset_one_lt (x : ℝ) :
    small_prime_powers x ⊆ {q : ℕ | 1 < q} := by
  intro _ hq
  exact IsSmallPrimePower.one_lt hq

lemma small_prime_powers_subset_ne_one (x : ℝ) :
    small_prime_powers x ⊆ {q : ℕ | q ≠ 1} := by
  intro _ hq
  exact IsSmallPrimePower.ne_one hq

lemma small_prime_powers_subset_nonzero (x : ℝ) :
    small_prime_powers x ⊆ {q : ℕ | q ≠ 0} := by
  intro _ hq
  exact IsSmallPrimePower.ne_zero hq

/-- The exponent `s = 1 - 1 / (10 log x)` used in the AKS argument. -/
noncomputable def aksExponent (x : ℝ) : ℝ :=
  1 - 1 / (10 * Real.log x)

lemma one_sub_aksExponent (x : ℝ) :
    1 - aksExponent x = 1 / (10 * Real.log x) := by
  rw [aksExponent]
  ring

lemma one_sub_aksExponent_pos {x : ℝ} (hx : 1 < x) :
    0 < 1 - aksExponent x := by
  rw [one_sub_aksExponent]
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  exact one_div_pos.mpr (mul_pos (by norm_num) hlog_pos)

lemma aksExponent_lt_one {x : ℝ} (hx : 1 < x) :
    aksExponent x < 1 := by
  have hpos := one_sub_aksExponent_pos hx
  linarith

/-- For the AKS range `x ≥ 3`, the exponent
`s = 1 - 1 / (10 log x)` is strictly positive. -/
lemma aksExponent_pos {x : ℝ} (hx : 3 ≤ x) :
    0 < aksExponent x := by
  have hx_pos : 0 < x := by linarith
  have hlog3_le : Real.log 3 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hden_pos : 0 < 10 * Real.log x := by
    exact mul_pos (by norm_num) (Real.log_pos (by linarith))
  have hden_one : 1 < 10 * Real.log x := by
    linarith [Real.log_three_gt_d9]
  rw [aksExponent]
  have hinv_lt : 1 / (10 * Real.log x) < 1 := by
    rw [div_lt_one hden_pos]
    exact hden_one
  linarith

/-- The AKS exponent lies in `(0, 1)` throughout the theorem's range. -/
lemma aksExponent_mem_Ioo {x : ℝ} (hx : 3 ≤ x) :
    aksExponent x ∈ Set.Ioo 0 1 :=
  ⟨aksExponent_pos hx, aksExponent_lt_one (by linarith)⟩

/-- Exact evaluation behind the uniform comparison on `[y/x,y]`:
`x^(1-s) = exp(1/10)` for the AKS exponent. -/
lemma aks_rpow_one_sub_exponent {x : ℝ} (hx : 1 < x) :
    Real.rpow x (1 - aksExponent x) = Real.exp ((1 : ℝ) / 10) := by
  rw [one_sub_aksExponent]
  change x ^ (1 / (10 * Real.log x)) = _
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 1
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp

lemma one_div_rpow_eq_rpow_one_sub_div {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    1 / Real.rpow (n : ℝ) s =
      Real.rpow (n : ℝ) (1 - s) / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  change 1 / ((n : ℝ) ^ s) = (n : ℝ) ^ (1 - s) / (n : ℝ)
  rw [Real.rpow_sub hn_pos 1 s, Real.rpow_one]
  field_simp

/-- A fixed lower bound for the exponent used in the AKS argument. -/
lemma four_fifths_le_aksExponent {x : ℝ} (hx : 3 ≤ x) :
    (4 : ℝ) / 5 ≤ aksExponent x := by
  have hlog : (9 : ℝ) / 10 < Real.log x :=
    (by linarith [Real.log_three_gt_d9] : (9 : ℝ) / 10 < Real.log 3).trans_le
      (Real.log_le_log (by norm_num) hx)
  have hden : 0 < 10 * Real.log x := by positivity
  rw [aksExponent]
  have hinv : 1 / (10 * Real.log x) ≤ (1 : ℝ) / 5 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith
  linarith

/-- The AKS partition function `Z = ∑_{p≤x}∑_{j≥1} p^{-js}`. -/
noncomputable def aksPartitionFunction (x s : ℝ) : ℝ :=
  by
    classical
    exact ∑' q : ℕ, if IsSmallPrimePower x q then 1 / Real.rpow (q : ℝ) s else 0

lemma aksPartitionFunction_eq_indicator (x s : ℝ) :
    aksPartitionFunction x s =
      ∑' q : ℕ,
        (small_prime_powers x).indicator
          (fun q : ℕ => 1 / Real.rpow (q : ℝ) s) q := by
  classical
  rw [aksPartitionFunction]
  congr with q

lemma aksPartitionFunction_nonneg (x s : ℝ) :
    0 ≤ aksPartitionFunction x s := by
  classical
  rw [aksPartitionFunction]
  apply tsum_nonneg
  intro q
  by_cases hq : IsSmallPrimePower x q
  · rw [if_pos hq]
    exact one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg q) s)
  · rw [if_neg hq]

/-- The partition function in the literal double-sum form used in the TeX:
first over primes `p ≤ x`, then over positive exponents. -/
noncomputable def aksPrimePowerPartitionFunction (x s : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    ∑' j : ℕ, 1 / Real.rpow (((p ^ (j + 1) : ℕ) : ℝ)) s

/-- For a fixed prime and positive exponent `s`, the prime-power contribution
to the AKS partition function is a summable geometric series. -/
lemma aks_prime_power_series_summable {p : ℕ} (hp : Nat.Prime p)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun j : ℕ =>
      1 / Real.rpow (((p ^ (j + 1) : ℕ) : ℝ)) s) := by
  let r : ℝ := 1 / Real.rpow (p : ℝ) s
  have hp_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    dsimp [r]
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
      (Real.one_lt_rpow hp_one hs)
  refine ((summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left r).congr
    fun j => ?_
  dsimp [r]
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p) s (j + 1)]
  simp [one_div, pow_succ]

/-- Geometric evaluation of a prime-power series with arbitrary exponent
shift. -/
lemma aks_prime_power_shifted_series_tsum {p : ℕ} (hp : Nat.Prime p)
    {s : ℝ} (hs : 0 < s) (d : ℕ) :
    (∑' j : ℕ, 1 / Real.rpow (((p ^ (j + d) : ℕ) : ℝ)) s) =
      (1 / Real.rpow (p : ℝ) s) ^ d *
        (1 - 1 / Real.rpow (p : ℝ) s)⁻¹ := by
  let r : ℝ := 1 / Real.rpow (p : ℝ) s
  have hp_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpow : 1 < Real.rpow (p : ℝ) s := Real.one_lt_rpow hp_one hs
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hr_lt_one : r < 1 := by
    dsimp [r]
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpow
  calc
    (∑' j : ℕ, 1 / Real.rpow (((p ^ (j + d) : ℕ) : ℝ)) s) =
        ∑' j : ℕ, r ^ d * r ^ j := by
      apply tsum_congr
      intro j
      dsimp [r]
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p) s (j + d)]
      simp [one_div, pow_add, mul_comm]
    _ = r ^ d * ∑' j : ℕ, r ^ j := tsum_mul_left
    _ = r ^ d * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]

/-- Exact geometric evaluation of one prime's contribution to the AKS
partition function. -/
lemma aks_prime_power_series_tsum {p : ℕ} (hp : Nat.Prime p)
    {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, 1 / Real.rpow (((p ^ (j + 1) : ℕ) : ℝ)) s) =
      1 / (Real.rpow (p : ℝ) s - 1) := by
  rw [aks_prime_power_shifted_series_tsum hp hs 1]
  have hpow : 1 < Real.rpow (p : ℝ) s :=
    Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  field_simp [ne_of_gt hpow]

/-- Exact contribution of the higher prime powers `p^j`, `j ≥ 2`, in the
AKS partition-function estimate. -/
lemma aks_higher_prime_power_series_tsum {p : ℕ} (hp : Nat.Prime p)
    {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, 1 / Real.rpow (((p ^ (j + 2) : ℕ) : ℝ)) s) =
      1 / (Real.rpow (p : ℝ) s * (Real.rpow (p : ℝ) s - 1)) := by
  rw [aks_prime_power_shifted_series_tsum hp hs 2]
  have hpow : 1 < Real.rpow (p : ℝ) s :=
    Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  field_simp [ne_of_gt hpow]

/-- A fixed summable majorant for the higher-prime-power contribution. -/
lemma aks_higher_prime_power_term_le {p : ℕ} (hp : Nat.Prime p)
    {s : ℝ} (hs : (4 : ℝ) / 5 ≤ s) :
    1 / (Real.rpow (p : ℝ) s * (Real.rpow (p : ℝ) s - 1)) ≤
      4 / Real.rpow (p : ℝ) ((8 : ℝ) / 5) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hp_pos : 0 < (p : ℝ) := by positivity
  have hs_half : (1 : ℝ) / 2 ≤ s := by linarith
  have hsqrt43 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrtp : Real.sqrt 2 ≤ Real.sqrt (p : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hp.two_le)
  have hhalf : Real.rpow (p : ℝ) ((1 : ℝ) / 2) ≤ Real.rpow (p : ℝ) s :=
    Real.rpow_le_rpow_of_exponent_le hp_one hs_half
  have ha43 : (4 : ℝ) / 3 ≤ Real.rpow (p : ℝ) s := by
    exact hsqrt43.trans (hsqrtp.trans (by simpa [Real.sqrt_eq_rpow] using hhalf))
  have ha_pos : 0 < Real.rpow (p : ℝ) s := Real.rpow_pos_of_pos hp_pos s
  have hsub : Real.rpow (p : ℝ) s / 4 ≤ Real.rpow (p : ℝ) s - 1 := by
    linarith
  have hden : Real.rpow (p : ℝ) s * Real.rpow (p : ℝ) s / 4 ≤
      Real.rpow (p : ℝ) s * (Real.rpow (p : ℝ) s - 1) := by
    nlinarith
  have hsquare :
      Real.rpow (p : ℝ) s * Real.rpow (p : ℝ) s =
        Real.rpow (p : ℝ) (2 * s) := by
    calc
      _ = Real.rpow (p : ℝ) (s + s) := (Real.rpow_add hp_pos s s).symm
      _ = _ := by congr 1; ring
  have hexp : (8 : ℝ) / 5 ≤ 2 * s := by linarith
  have hpow : Real.rpow (p : ℝ) ((8 : ℝ) / 5) ≤
      Real.rpow (p : ℝ) (2 * s) :=
    Real.rpow_le_rpow_of_exponent_le hp_one hexp
  calc
    1 / (Real.rpow (p : ℝ) s * (Real.rpow (p : ℝ) s - 1)) ≤
        1 / (Real.rpow (p : ℝ) s * Real.rpow (p : ℝ) s / 4) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = 4 / Real.rpow (p : ℝ) (2 * s) := by
      rw [← hsquare]
      field_simp [ha_pos.ne']
    _ ≤ 4 / Real.rpow (p : ℝ) ((8 : ℝ) / 5) := by
      gcongr
      exact Real.rpow_pos_of_pos hp_pos _

/-- The literal AKS partition function is positive in the theorem range. -/
lemma aksPrimePowerPartitionFunction_pos {x s : ℝ}
    (hx : 2 ≤ x) (hs : 0 < s) :
    0 < aksPrimePowerPartitionFunction x s := by
  rw [aksPrimePowerPartitionFunction]
  refine Finset.sum_pos' ?_ ?_
  · intro p _hp
    exact tsum_nonneg fun j => one_div_nonneg.mpr
      (Real.rpow_nonneg (Nat.cast_nonneg (p ^ (j + 1))) s)
  · have htwo : 2 ∈ Nat.primesLE ⌊x⌋₊ := by
      rw [Nat.mem_primesLE]
      exact ⟨Nat.le_floor (by exact_mod_cast hx), Nat.prime_two⟩
    refine ⟨2, htwo, ?_⟩
    have hzero :
        0 < 1 / Real.rpow ((((2 : ℕ) ^ (0 + 1) : ℕ) : ℝ)) s := by
      simpa using one_div_pos.mpr
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s)
    exact (aks_prime_power_series_summable Nat.prime_two hs).tsum_pos
      (fun j => one_div_nonneg.mpr
        (Real.rpow_nonneg (Nat.cast_nonneg (2 ^ (j + 1))) s)) 0 hzero

/-- Unique factorisation identifies the literal `(p,j)` indexing of the AKS
partition function with its prime-power support. -/
noncomputable def aksPrimePowerIndexEquiv (x : ℝ) (hx : 0 ≤ x) :
    (Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ) ≃
      {q : ℕ // IsSmallPrimePower x q} := by
  classical
  let f : (Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ) →
      {q : ℕ // IsSmallPrimePower x q} := fun a =>
    ⟨a.1.1 ^ (a.2 + 1), a.1.1, a.2 + 1,
      Nat.prime_of_mem_primesLE a.1.2, by omega,
      (by
        exact (by exact_mod_cast Nat.le_of_mem_primesLE a.1.2 :
          (a.1.1 : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx)), rfl⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨⟨p, hp⟩, j⟩ ⟨⟨q, hq⟩, k⟩ h
    have hpow : p ^ (j + 1) = q ^ (k + 1) := congrArg Subtype.val h
    have hpq := Nat.Prime.pow_inj' (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hq) (by omega) (by omega) hpow
    obtain ⟨rfl, hjk⟩ := hpq
    have : j = k := by omega
    subst k
    rfl
  · rintro ⟨q, p, j, hp, hj, hpx, rfl⟩
    have hple : p ∈ Nat.primesLE ⌊x⌋₊ := by
      rw [Nat.mem_primesLE]
      exact ⟨Nat.le_floor hpx, hp⟩
    refine ⟨⟨⟨p, hple⟩, j - 1⟩, ?_⟩
    apply Subtype.ext
    simp only [f]
    congr 1
    omega

/-- The random-walk and literal double-sum definitions of the AKS partition
function agree. -/
lemma aksPartitionFunction_eq_primePowerPartitionFunction {x s : ℝ}
    (hx : 0 ≤ x) (hs : 0 < s) :
    aksPartitionFunction x s = aksPrimePowerPartitionFunction x s := by
  classical
  have hsigma : Summable (fun a :
      Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ =>
        1 / Real.rpow (((a.1.1 ^ (a.2 + 1) : ℕ) : ℝ)) s) := by
    refine (summable_sigma_of_nonneg fun _ => one_div_nonneg.mpr
      (Real.rpow_nonneg (Nat.cast_nonneg _) s)).2 ⟨?_, Summable.of_finite⟩
    intro p
    exact aks_prime_power_series_summable
      (Nat.prime_of_mem_primesLE p.2) hs
  rw [aksPartitionFunction_eq_indicator]
  calc
    (∑' q : ℕ, (small_prime_powers x).indicator
        (fun q : ℕ => 1 / Real.rpow (q : ℝ) s) q) =
        ∑' q : {q : ℕ // IsSmallPrimePower x q},
          1 / Real.rpow (q.1 : ℝ) s := by
      simpa [small_prime_powers] using
        (tsum_subtype (small_prime_powers x)
          (fun q : ℕ => 1 / Real.rpow (q : ℝ) s)).symm
    _ = ∑' a : Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ,
          1 / Real.rpow (((a.1.1 ^ (a.2 + 1) : ℕ) : ℝ)) s := by
      simpa [aksPrimePowerIndexEquiv] using
        (Equiv.tsum_eq (aksPrimePowerIndexEquiv x hx)
          (fun q : {q : ℕ // IsSmallPrimePower x q} =>
            1 / Real.rpow (q.1 : ℝ) s)).symm
    _ = ∑' p : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊},
          ∑' j : ℕ, 1 / Real.rpow (((p.1 ^ (j + 1) : ℕ) : ℝ)) s := by
      exact hsigma.tsum_sigma' fun p => aks_prime_power_series_summable
        (Nat.prime_of_mem_primesLE p.2) hs
    _ = aksPrimePowerPartitionFunction x s := by
      rw [aksPrimePowerPartitionFunction]
      exact Finset.tsum_subtype' (Nat.primesLE ⌊x⌋₊)
        (fun p => ∑' j : ℕ,
          1 / Real.rpow (((p ^ (j + 1) : ℕ) : ℝ)) s)

/-- The indexed AKS partition function is positive in the theorem range. -/
lemma aksPartitionFunction_pos {x s : ℝ} (hx : 2 ≤ x) (hs : 0 < s) :
    0 < aksPartitionFunction x s := by
  rw [aksPartitionFunction_eq_primePowerPartitionFunction (by linarith) hs]
  exact aksPrimePowerPartitionFunction_pos hx hs

/-- Finite closed form for the literal AKS partition function. -/
lemma aksPrimePowerPartitionFunction_eq_sum {x s : ℝ} (hs : 0 < s) :
    aksPrimePowerPartitionFunction x s =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (Real.rpow (p : ℝ) s - 1) := by
  rw [aksPrimePowerPartitionFunction]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact aks_prime_power_series_tsum (Nat.prime_of_mem_primesLE hp) hs

/-- In the AKS theorem range the partition function is already larger than
one, witnessed by the full geometric contribution of the prime `2`. -/
lemma one_lt_aksPartitionFunction_aksExponent {x : ℝ} (hx : 3 ≤ x) :
    1 < aksPartitionFunction x (aksExponent x) := by
  have hs := aksExponent_pos hx
  rw [aksPartitionFunction_eq_primePowerPartitionFunction (by linarith) hs,
    aksPrimePowerPartitionFunction_eq_sum hs]
  have htwo : 2 ∈ Nat.primesLE ⌊x⌋₊ := by
    rw [Nat.mem_primesLE]
    exact ⟨Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ x)), Nat.prime_two⟩
  have hterms : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      0 ≤ 1 / (Real.rpow (p : ℝ) (aksExponent x) - 1) := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primesLE hp
    have : 1 < Real.rpow (p : ℝ) (aksExponent x) :=
      Real.one_lt_rpow (by exact_mod_cast hpprime.one_lt) hs
    positivity
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum (fun p hp => hterms p hp) htwo)
  have hpow_pos : 1 < Real.rpow (2 : ℝ) (aksExponent x) :=
    Real.one_lt_rpow (by norm_num) hs
  have hpow_lt : Real.rpow (2 : ℝ) (aksExponent x) < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (aksExponent_lt_one (by linarith))
  simpa using one_div_lt_one_div_of_lt
    (by linarith : 0 < Real.rpow (2 : ℝ) (aksExponent x) - 1)
    (by linarith : Real.rpow (2 : ℝ) (aksExponent x) - 1 < 1)

/-- Exact split of the AKS partition function into its prime and higher-prime-
power contributions, preceding TeX equation `\eqref{qasym}`. -/
lemma aksPrimePowerPartitionFunction_eq_prime_add_higher {x s : ℝ}
    (hs : 0 < s) :
    aksPrimePowerPartitionFunction x s =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / Real.rpow (p : ℝ) s) +
      ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        1 / (Real.rpow (p : ℝ) s * (Real.rpow (p : ℝ) s - 1)) := by
  rw [aksPrimePowerPartitionFunction_eq_sum hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpow : 1 < Real.rpow (p : ℝ) s :=
    Real.one_lt_rpow
      (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt) hs
  have hsub : Real.rpow (p : ℝ) s - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hpow)
  field_simp [hsub, ne_of_gt (zero_lt_one.trans hpow)]
  ring

/-- A universal constant dominating the AKS higher-prime-power correction. -/
noncomputable def aksHigherPrimePowerBound : ℝ :=
  ∑' n : ℕ, 4 / Real.rpow (n : ℝ) ((8 : ℝ) / 5)

lemma aksHigherPrimePowerBound_nonneg : 0 ≤ aksHigherPrimePowerBound :=
  tsum_nonneg fun n => div_nonneg (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The contribution of prime powers of exponent at least two is uniformly
bounded, the `O(1)` estimate used in the proof of TeX equation `\eqref{qasym}`. -/
lemma aks_higher_prime_power_sum_le_bound {x : ℝ} (hx : 3 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊,
      1 / (Real.rpow (p : ℝ) (aksExponent x) *
        (Real.rpow (p : ℝ) (aksExponent x) - 1))) ≤
      aksHigherPrimePowerBound := by
  have hsumm : Summable (fun n : ℕ =>
      4 / Real.rpow (n : ℝ) ((8 : ℝ) / 5)) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_rpow.mpr
        (by norm_num : (1 : ℝ) < 8 / 5)).mul_left 4
  calc
    (∑ p ∈ Nat.primesLE ⌊x⌋₊,
        1 / (Real.rpow (p : ℝ) (aksExponent x) *
          (Real.rpow (p : ℝ) (aksExponent x) - 1))) ≤
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          4 / Real.rpow (p : ℝ) ((8 : ℝ) / 5) := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact aks_higher_prime_power_term_le
        (Nat.prime_of_mem_primesLE hp) (four_fifths_le_aksExponent hx)
    _ ≤ ∑' n : ℕ, 4 / Real.rpow (n : ℝ) ((8 : ℝ) / 5) :=
      hsumm.sum_le_tsum _ fun n _ => div_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = aksHigherPrimePowerBound := rfl

/-- The exponent increment in the AKS prime contribution is uniformly small
for primes `p ≤ x`. -/
lemma aks_prime_rpow_increment_bound {x : ℝ} (hx : 3 ≤ x) {p : ℕ}
    (hp : Nat.Prime p) (hpx : (p : ℝ) ≤ x) :
    |Real.rpow (p : ℝ) (1 - aksExponent x) - 1| ≤
      2 * (1 - aksExponent x) * Real.log (p : ℝ) := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hlog_le : Real.log (p : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hp.pos) hpx
  have hdelta : 0 < 1 - aksExponent x := one_sub_aksExponent_pos (by linarith)
  have hdelta_log : (1 - aksExponent x) * Real.log x = (1 : ℝ) / 10 := by
    rw [one_sub_aksExponent]
    field_simp [hlogx.ne']
  have ht_nonneg : 0 ≤ Real.log (p : ℝ) * (1 - aksExponent x) :=
    mul_nonneg hlogp hdelta.le
  have ht_le : Real.log (p : ℝ) * (1 - aksExponent x) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hlog_le hdelta.le
    rw [mul_comm] at hdelta_log
    nlinarith
  have hexp := Real.abs_exp_sub_one_le
    (show |Real.log (p : ℝ) * (1 - aksExponent x)| ≤ 1 by
      rw [abs_of_nonneg ht_nonneg]
      exact ht_le)
  simpa [Real.rpow_def_of_pos (show 0 < (p : ℝ) by exact_mod_cast hp.pos),
    mul_assoc, mul_comm, mul_left_comm, abs_of_nonneg hlogp,
    abs_of_nonneg hdelta.le] using hexp

/-- Pointwise mean-value estimate for the prime contribution in the AKS
partition function. -/
lemma aks_prime_rpow_reciprocal_sub_le {x : ℝ} (hx : 3 ≤ x) {p : ℕ}
    (hp : Nat.Prime p) (hpx : (p : ℝ) ≤ x) :
    |1 / Real.rpow (p : ℝ) (aksExponent x) - 1 / (p : ℝ)| ≤
      Real.log (p : ℝ) / (5 * (p : ℝ) * Real.log x) := by
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hfactor :
      1 / Real.rpow (p : ℝ) (aksExponent x) - 1 / (p : ℝ) =
        (1 / (p : ℝ)) *
          (Real.rpow (p : ℝ) (1 - aksExponent x) - 1) := by
    rw [show 1 / Real.rpow (p : ℝ) (aksExponent x) =
      Real.rpow (p : ℝ) (-aksExponent x) by
        simpa [one_div] using
          (Real.rpow_neg (le_of_lt hp_pos) (aksExponent x)).symm]
    rw [show 1 / (p : ℝ) = Real.rpow (p : ℝ) (-1 : ℝ) by
      simp [Real.rpow_neg_one]]
    rw [mul_sub, mul_one]
    have hmul : Real.rpow (p : ℝ) (-1 : ℝ) *
        Real.rpow (p : ℝ) (1 - aksExponent x) =
          Real.rpow (p : ℝ) (-aksExponent x) := by
      calc
        _ = Real.rpow (p : ℝ) ((-1 : ℝ) + (1 - aksExponent x)) :=
          (Real.rpow_add hp_pos _ _).symm
        _ = _ := by congr 1; ring
    rw [hmul]
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
  calc
    1 / (p : ℝ) * |Real.rpow (p : ℝ) (1 - aksExponent x) - 1| ≤
        1 / (p : ℝ) *
          (2 * (1 - aksExponent x) * Real.log (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (aks_prime_rpow_increment_bound hx hp hpx) (by positivity)
    _ = Real.log (p : ℝ) / (5 * (p : ℝ) * Real.log x) := by
      rw [one_sub_aksExponent]
      field_simp [hp_pos.ne', hlogx.ne']
      ring

/-- The prime logarithmic reciprocal sum is a sub-sum of the von Mangoldt
partial sum. -/
lemma aks_prime_log_reciprocal_sum_le_mangoldt {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ) / (p : ℝ)) ≤
      mangoldt_reciprocal_partial_sum x := by
  let f : ℕ → ℝ := fun n =>
    if 1 ≤ n ∧ (n : ℝ) ≤ x then
      ArithmeticFunction.vonMangoldt n / (n : ℝ)
    else 0
  have hf : Summable f := by
    apply summable_of_hasFiniteSupport
    refine (Finset.finite_toSet (Finset.range (⌊x⌋₊ + 1))).subset ?_
    intro n hn
    by_contra hnrange
    have hn_gt : ⌊x⌋₊ < n := by
      simpa [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hnrange
    have hnx : x < (n : ℝ) := by
      exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn_gt)
    exact hn (by simp [f, not_le_of_gt hnx])
  calc
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ) / (p : ℝ)) =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Nat.mem_primesLE.mp hp
      have hpx : (p : ℝ) ≤ x :=
        (by exact_mod_cast hp'.1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
          (Nat.floor_le (by linarith))
      simp [f, hp'.2.one_le, hpx, ArithmeticFunction.vonMangoldt_apply_prime hp'.2]
    _ ≤ ∑' n : ℕ, f n := hf.sum_le_tsum _ fun n _ => by
      dsimp [f]
      split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      · exact le_rfl
    _ = mangoldt_reciprocal_partial_sum x := rfl

/-- Uniform error when replacing `p⁻ˢ` by `p⁻¹` in the AKS prime
contribution. -/
lemma aks_prime_rpow_sum_sub_reciprocal_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x ->
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊,
          1 / Real.rpow (p : ℝ) (aksExponent x)) -
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)| ≤ C := by
  obtain ⟨D, hD, hM⟩ := mertens_von_mangoldt_reciprocal
  refine ⟨(1 : ℝ) / 5 + D / (5 * Real.log 3), by positivity, ?_⟩
  intro x hx
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog3x : Real.log (3 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hMangoldt : mangoldt_reciprocal_partial_sum x ≤ Real.log x + D := by
    have h := hM x (by linarith)
    linarith [le_abs_self (mangoldt_reciprocal_partial_sum x - Real.log x)]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (1 / Real.rpow (p : ℝ) (aksExponent x) - 1 / (p : ℝ))| ≤
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          |1 / Real.rpow (p : ℝ) (aksExponent x) - 1 / (p : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          Real.log (p : ℝ) / (5 * (p : ℝ) * Real.log x) := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact aks_prime_rpow_reciprocal_sub_le hx
        (Nat.prime_of_mem_primesLE hp)
        ((by exact_mod_cast Nat.le_of_mem_primesLE hp : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
          (Nat.floor_le (by linarith)))
    _ = (1 / (5 * Real.log x)) *
          ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    _ ≤ (1 / (5 * Real.log x)) * mangoldt_reciprocal_partial_sum x :=
      mul_le_mul_of_nonneg_left
        (aks_prime_log_reciprocal_sum_le_mangoldt (by linarith)) (by positivity)
    _ ≤ (1 / (5 * Real.log x)) * (Real.log x + D) :=
      mul_le_mul_of_nonneg_left hMangoldt (by positivity)
    _ = (1 : ℝ) / 5 + D / (5 * Real.log x) := by
      field_simp [hlogx.ne']
    _ ≤ (1 : ℝ) / 5 + D / (5 * Real.log 3) := by
      gcongr

/-- The finite `primesLE` reciprocal sum is the indicator sum used by the
single-file Mertens theorem. -/
lemma aks_prime_reciprocal_sum_eq_mertens_sum {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      ∑' p : ℕ, (prime_layer ∩ real_initial_segment x).indicator
        (fun p : ℕ => 1 / (p : ℝ)) p := by
  classical
  symm
  rw [tsum_eq_sum (s := Nat.primesLE ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Nat.mem_primesLE.mp hp
    have hpx : (p : ℝ) ≤ x :=
      (by exact_mod_cast hp'.1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
        (Nat.floor_le hx)
    simp [prime_layer, real_initial_segment, hp'.2, hp'.2.one_le, hpx]
  · intro n hn
    by_cases hmem : n ∈ prime_layer ∩ real_initial_segment x
    · have hn_le : n ≤ ⌊x⌋₊ := Nat.le_floor hmem.2.2
      exact False.elim (hn (Nat.mem_primesLE.mpr ⟨hn_le, hmem.1⟩))
    · simp [Set.indicator_of_notMem hmem]

/-- The AKS partition-function asymptotic `Z = log log x + O(1)` from TeX
equation `\eqref{qasym}`, in uniform bounded-error form. -/
lemma aksPrimePowerPartitionFunction_log_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x ->
      |aksPrimePowerPartitionFunction x (aksExponent x) -
        Real.log (Real.log x)| ≤ C := by
  obtain ⟨C₁, hC₁, hprime⟩ := aks_prime_rpow_sum_sub_reciprocal_bound
  obtain ⟨C₂, hC₂, hmertens⟩ := mertens_prime_reciprocal
  refine ⟨C₁ + C₂ + aksHigherPrimePowerBound,
    add_nonneg (add_nonneg hC₁ hC₂) aksHigherPrimePowerBound_nonneg, ?_⟩
  intro x hx
  let P : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    1 / Real.rpow (p : ℝ) (aksExponent x)
  let R : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)
  let E : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    1 / (Real.rpow (p : ℝ) (aksExponent x) *
      (Real.rpow (p : ℝ) (aksExponent x) - 1))
  have hZ : aksPrimePowerPartitionFunction x (aksExponent x) = P + E := by
    simpa [P, E] using
      aksPrimePowerPartitionFunction_eq_prime_add_higher
        (aksExponent_pos hx)
  have hPR : |P - R| ≤ C₁ := by simpa [P, R] using hprime x hx
  have hR : |R - Real.log (Real.log x)| ≤ C₂ := by
    dsimp [R]
    rw [aks_prime_reciprocal_sum_eq_mertens_sum (by linarith : 0 ≤ x)]
    exact hmertens x (by linarith)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    refine Finset.sum_nonneg fun p hp => ?_
    have hpprime := Nat.prime_of_mem_primesLE hp
    have hpow : 1 < Real.rpow (p : ℝ) (aksExponent x) :=
      Real.one_lt_rpow (by exact_mod_cast hpprime.one_lt) (aksExponent_pos hx)
    positivity
  have hE : |E| ≤ aksHigherPrimePowerBound := by
    rw [abs_of_nonneg hE_nonneg]
    exact aks_higher_prime_power_sum_le_bound hx
  rw [hZ]
  calc
    |P + E - Real.log (Real.log x)| =
        |(P - R) + (R - Real.log (Real.log x)) + E| := by congr 1; ring
    _ ≤ |P - R| + |R - Real.log (Real.log x)| + |E| := by
      calc
        _ ≤ |(P - R) + (R - Real.log (Real.log x))| + |E| := abs_add_le _ _
        _ ≤ (|P - R| + |R - Real.log (Real.log x)|) + |E| :=
          by linarith [abs_add_le (P - R) (R - Real.log (Real.log x))]
    _ ≤ C₁ + C₂ + aksHigherPrimePowerBound := by linarith

/-- The partition function used by the random walk satisfies the literal TeX
asymptotic `Z = log log x + O(1)`. -/
lemma aksPartitionFunction_log_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x ->
      |aksPartitionFunction x (aksExponent x) - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := aksPrimePowerPartitionFunction_log_log_bound
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [aksPartitionFunction_eq_primePowerPartitionFunction
    (by linarith) (aksExponent_pos hx)]
  exact hbound x hx

/-- The partition-function factor in the AKS hitting estimate has the final
TeX scale `log x / sqrt(log log x)`, uniformly for `x ≥ 3`. -/
lemma aksPartitionFunction_exp_div_sqrt_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x ->
      Real.exp (aksPartitionFunction x (aksExponent x)) /
          Real.sqrt (aksPartitionFunction x (aksExponent x)) ≤
        C * Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  obtain ⟨D, hD, hZD⟩ := aksPartitionFunction_log_log_bound
  refine ⟨Real.exp D * Real.sqrt (1 + D), by positivity, ?_⟩
  intro x hx
  let Z := aksPartitionFunction x (aksExponent x)
  let L := Real.log (Real.log x)
  have hlogx : 1 < Real.log x := by
    have hlog3 : 1 < Real.log 3 := by linarith [oddzeta_le_log_three]
    exact hlog3.trans_le (Real.log_le_log (by norm_num) hx)
  have hL : 0 < L := Real.log_pos hlogx
  have hZ : 1 ≤ Z := one_lt_aksPartitionFunction_aksExponent hx |>.le
  have hdiff := abs_le.mp (hZD x hx)
  have hZupper : Z ≤ L + D := by linarith
  have hLupper : L ≤ (1 + D) * Z := by nlinarith
  have hexp : Real.exp Z ≤ Real.exp D * Real.log x := by
    calc
      Real.exp Z ≤ Real.exp (L + D) := Real.exp_le_exp.mpr hZupper
      _ = Real.exp D * Real.log x := by
        rw [Real.exp_add, show Real.exp L = Real.log x from
          Real.exp_log (Real.log_pos (by linarith : 1 < x))]
        ring
  have hsqrt : Real.sqrt L ≤ Real.sqrt (1 + D) * Real.sqrt Z := by
    calc
      Real.sqrt L ≤ Real.sqrt ((1 + D) * Z) := Real.sqrt_le_sqrt hLupper
      _ = Real.sqrt (1 + D) * Real.sqrt Z :=
        Real.sqrt_mul (by linarith) Z
  have hsqrtZ : 0 < Real.sqrt Z := Real.sqrt_pos.mpr (by linarith)
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  rw [div_le_div_iff₀ hsqrtZ hsqrtL]
  calc
    Real.exp Z * Real.sqrt L ≤
        (Real.exp D * Real.log x) * Real.sqrt L :=
      mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg L)
    _ ≤ (Real.exp D * Real.log x) *
        (Real.sqrt (1 + D) * Real.sqrt Z) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (Real.exp D * Real.sqrt (1 + D) * Real.log x) *
        Real.sqrt Z := by ring

lemma aksPartitionFunction_exp_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x ->
      Real.exp (aksPartitionFunction x (aksExponent x)) ≤ C * Real.log x := by
  obtain ⟨D, hD, hZD⟩ := aksPartitionFunction_log_log_bound
  refine ⟨Real.exp D, Real.exp_pos D |>.le, ?_⟩
  intro x hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hupper := (abs_le.mp (hZD x hx)).2
  calc
    Real.exp (aksPartitionFunction x (aksExponent x)) ≤
        Real.exp (Real.log (Real.log x) + D) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp D * Real.log x := by
      rw [Real.exp_add, Real.exp_log hlogx]
      ring

/-- The AKS multiplicative random-walk increment weight before proving the
partition-function normalization estimates. -/
noncomputable def aksStepWeight (x s : ℝ) (q : ℕ) : ℝ :=
  by
    classical
    exact
      if IsSmallPrimePower x q then
        1 / Real.rpow (q : ℝ) s / aksPartitionFunction x s
      else 0

lemma aksStepWeight_of_small_prime_power {x s : ℝ} {q : ℕ}
    (hq : IsSmallPrimePower x q) :
    aksStepWeight x s q = 1 / Real.rpow (q : ℝ) s / aksPartitionFunction x s := by
  classical
  simp [aksStepWeight, hq]

lemma aksStepWeight_eq_zero_of_not_small_prime_power {x s : ℝ} {q : ℕ}
    (hq : ¬ IsSmallPrimePower x q) :
    aksStepWeight x s q = 0 := by
  classical
  simp [aksStepWeight, hq]

lemma aksStepWeight_eq_zero_of_not_mem_small_prime_powers {x s : ℝ} {q : ℕ}
    (hq : q ∉ small_prime_powers x) :
    aksStepWeight x s q = 0 :=
  aksStepWeight_eq_zero_of_not_small_prime_power (by
    simpa [small_prime_powers] using hq)

lemma aksStepWeight_nonneg {x s : ℝ}
    (hZ : 0 ≤ aksPartitionFunction x s) (q : ℕ) :
    0 ≤ aksStepWeight x s q := by
  classical
  by_cases hq : IsSmallPrimePower x q
  · rw [aksStepWeight_of_small_prime_power hq]
    exact div_nonneg (one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg q) s)) hZ
  · rw [aksStepWeight_eq_zero_of_not_small_prime_power hq]

lemma aksStepWeight_nonneg_unconditional {x s : ℝ} (q : ℕ) :
    0 ≤ aksStepWeight x s q :=
  aksStepWeight_nonneg (aksPartitionFunction_nonneg x s) q

/-- Once the partition function is nonzero, the AKS increment weights have
total mass one, as required for the multiplicative random walk. -/
lemma aksStepWeight_tsum_eq_one {x s : ℝ}
    (hZ : aksPartitionFunction x s ≠ 0) :
    (∑' q : ℕ, aksStepWeight x s q) = 1 := by
  classical
  calc
    (∑' q : ℕ, aksStepWeight x s q) =
        ∑' q : ℕ,
          (if IsSmallPrimePower x q then
            1 / Real.rpow (q : ℝ) s
          else 0) / aksPartitionFunction x s := by
      apply tsum_congr
      intro q
      by_cases hq : IsSmallPrimePower x q <;> simp [aksStepWeight, hq]
    _ = (∑' q : ℕ,
          if IsSmallPrimePower x q then
            1 / Real.rpow (q : ℝ) s
          else 0) / aksPartitionFunction x s := by
      rw [tsum_div_const (a := aksPartitionFunction x s)]
    _ = aksPartitionFunction x s / aksPartitionFunction x s := by
      rw [aksPartitionFunction]
    _ = 1 := div_self hZ

lemma aksStepWeight_probability_mass {x s : ℝ}
    (hZ : aksPartitionFunction x s ≠ 0) :
    (∀ q : ℕ, 0 ≤ aksStepWeight x s q) ∧
      (∑' q : ℕ, aksStepWeight x s q) = 1 :=
  ⟨fun q => aksStepWeight_nonneg_unconditional (x := x) (s := s) q,
    aksStepWeight_tsum_eq_one hZ⟩

/-- In the AKS theorem range the selected increment weights are
unconditionally a probability mass function. -/
lemma aksStepWeight_probability_mass_aksExponent {x : ℝ} (hx : 3 ≤ x) :
    (∀ q : ℕ, 0 ≤ aksStepWeight x (aksExponent x) q) ∧
      (∑' q : ℕ, aksStepWeight x (aksExponent x) q) = 1 :=
  aksStepWeight_probability_mass
    (aksPartitionFunction_pos (by linarith) (aksExponent_pos hx)).ne'

/-- Unnormalised density of the AKS increment law. -/
noncomputable def aksPartitionNumerator (x s : ℝ) (q : ℕ) : ℝ := by
  classical
  exact if IsSmallPrimePower x q then 1 / Real.rpow (q : ℝ) s else 0

set_option maxHeartbeats 800000 in
-- Transporting summability across the sigma/subtype prime-power equivalence is elaboration-heavy.
lemma aksPartitionNumerator_summable {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    Summable (aksPartitionNumerator x s) := by
  classical
  have hsigma : Summable (fun a :
      Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ =>
        1 / Real.rpow (((a.1.1 ^ (a.2 + 1) : ℕ) : ℝ)) s) := by
    refine (summable_sigma_of_nonneg fun _ => one_div_nonneg.mpr
      (Real.rpow_nonneg (Nat.cast_nonneg _) s)).2 ⟨?_, Summable.of_finite⟩
    intro p
    exact aks_prime_power_series_summable
      (Nat.prime_of_mem_primesLE p.2) hs
  have hsub : Summable (fun q : {q : ℕ // IsSmallPrimePower x q} =>
      1 / Real.rpow (q.1 : ℝ) s) := by
    let g := fun q : {q : ℕ // IsSmallPrimePower x q} =>
      1 / Real.rpow (q.1 : ℝ) s
    have hcomp : (fun a :
        Σ _ : {p : ℕ // p ∈ Nat.primesLE ⌊x⌋₊}, ℕ =>
          1 / Real.rpow (((a.1.1 ^ (a.2 + 1) : ℕ) : ℝ)) s) =
        g ∘ aksPrimePowerIndexEquiv x hx := by
      funext a
      rfl
    rw [hcomp] at hsigma
    exact (Equiv.summable_iff (aksPrimePowerIndexEquiv x hx)).1 hsigma
  let F := aksPartitionNumerator x s
  have hzero : ∀ q ∉ Set.range
      ((↑) : {q : ℕ // IsSmallPrimePower x q} → ℕ), F q = 0 := by
    intro q hq
    dsimp [F, aksPartitionNumerator]
    split_ifs with h
    · exact (hq ⟨⟨q, h⟩, rfl⟩).elim
    · rfl
  have hcomp : F ∘ ((↑) : {q : ℕ // IsSmallPrimePower x q} → ℕ) =
      fun q => 1 / Real.rpow (q.1 : ℝ) s := by
    funext q
    simp [F, aksPartitionNumerator, q.2]
  rw [← hcomp] at hsub
  exact (Function.Injective.summable_iff (f := F)
    (g := ((↑) : {q : ℕ // IsSmallPrimePower x q} → ℕ))
    Subtype.val_injective hzero).1 hsub

lemma aksStepWeight_summable {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    Summable (aksStepWeight x s) := by
  classical
  refine ((aksPartitionNumerator_summable hx hs).div_const
    (aksPartitionFunction x s)).congr fun q => ?_
  by_cases hq : IsSmallPrimePower x q <;>
    simp [aksPartitionNumerator, aksStepWeight, hq]

/-- Upward multiplicative kernel associated with the AKS increment law. -/
noncomputable def aksUpwardKernel (x s : ℝ) :
    Option ℕ → Option ℕ → ℝ
  | some n, some m =>
      if n ∣ m ∧ n < m then aksStepWeight x s (m / n) else 0
  | _, _ => 0

lemma aksUpwardKernel_nonneg (x s : ℝ) (a b : Option ℕ) :
    0 ≤ aksUpwardKernel x s a b := by
  cases a <;> cases b <;> simp only [aksUpwardKernel, le_refl]
  split_ifs
  · exact aksStepWeight_nonneg_unconditional _
  · exact le_rfl

lemma aksUpwardKernel_finite_row {x s : ℝ} (hx : 2 ≤ x) (hs : 0 < s)
    (n : ℕ) (_hn : 1 ≤ n) (S : Finset ℕ) :
    (∑ m ∈ S, if 1 ≤ m then aksUpwardKernel x s (some n) (some m) else 0) ≤ 1 := by
  classical
  let T := S.filter fun m => 1 ≤ m ∧ n ∣ m ∧ n < m
  have hinj : ∀ a ∈ T, ∀ b ∈ T, a / n = b / n -> a = b := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = n * (a / n) := (Nat.mul_div_cancel' ha'.2.1).symm
      _ = n * (b / n) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hb'.2.1
  calc
    (∑ m ∈ S, if 1 ≤ m then aksUpwardKernel x s (some n) (some m) else 0) =
        ∑ m ∈ T, aksStepWeight x s (m / n) := by
      dsimp [T]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m hm => ?_
      by_cases hm1 : 1 ≤ m <;> by_cases hdiv : n ∣ m ∧ n < m <;>
        simp [aksUpwardKernel, hm1, hdiv]
    _ = ∑ q ∈ T.image (fun m => m / n), aksStepWeight x s q := by
      symm
      rw [Finset.sum_image]
      exact fun a ha b hb hab => hinj a ha b hb hab
    _ ≤ ∑' q : ℕ, aksStepWeight x s q :=
      (aksStepWeight_summable (by linarith) hs).sum_le_tsum _ fun q _ =>
        aksStepWeight_nonneg_unconditional q
    _ = 1 := aksStepWeight_tsum_eq_one
      (aksPartitionFunction_pos (by linarith) hs).ne'

lemma aksUpwardKernel_divisor_step {x s : ℝ} {n q : ℕ}
    (hn : n ≠ 0) (hq : 1 < q) (hqn : q ∣ n) :
    aksUpwardKernel x s (some (n / q)) (some n) = aksStepWeight x s q := by
  have hdiv : n / q ∣ n := Nat.div_dvd_of_dvd hqn
  have hlt : n / q < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hq
  simp [aksUpwardKernel, hdiv, hlt, Nat.div_div_self hqn hn]


lemma aksStepWeight_pos_of_small_prime_power {x s : ℝ} {q : ℕ}
    (hZ : 0 < aksPartitionFunction x s) (hq : IsSmallPrimePower x q) :
    0 < aksStepWeight x s q := by
  rw [aksStepWeight_of_small_prime_power hq]
  have : 0 < (q : ℝ) := by exact_mod_cast IsSmallPrimePower.pos hq
  exact div_pos (one_div_pos.mpr (Real.rpow_pos_of_pos this s)) hZ

lemma aksStepWeight_pos_aksExponent_of_small_prime_power {x : ℝ} (hx : 3 ≤ x)
    {q : ℕ} (hq : IsSmallPrimePower x q) :
    0 < aksStepWeight x (aksExponent x) q :=
  aksStepWeight_pos_of_small_prime_power
    (aksPartitionFunction_pos (by linarith) (aksExponent_pos hx)) hq

lemma aksStepWeight_support_subset_small_prime_powers {x s : ℝ} {q : ℕ}
    (hq : aksStepWeight x s q ≠ 0) :
    q ∈ small_prime_powers x := by
  by_contra hnot
  exact hq (aksStepWeight_eq_zero_of_not_mem_small_prime_powers hnot)

lemma aksStepWeight_support_one_lt {x s : ℝ} {q : ℕ}
    (hq : aksStepWeight x s q ≠ 0) :
    1 < q :=
  IsSmallPrimePower.one_lt (by
    simpa [small_prime_powers] using aksStepWeight_support_subset_small_prime_powers hq)

lemma aksStepWeight_support_ne_zero {x s : ℝ} {q : ℕ}
    (hq : aksStepWeight x s q ≠ 0) :
    q ≠ 0 :=
  Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one (aksStepWeight_support_one_lt hq))

lemma aksStepWeight_support_ne_one {x s : ℝ} {q : ℕ}
    (hq : aksStepWeight x s q ≠ 0) :
    q ≠ 1 :=
  Nat.ne_of_gt (aksStepWeight_support_one_lt hq)

lemma aksStepWeight_eq_zero_of_not_one_lt {x s : ℝ} {q : ℕ}
    (hq : ¬ 1 < q) :
    aksStepWeight x s q = 0 := by
  by_contra hne
  exact hq (aksStepWeight_support_one_lt hne)

lemma aksStepWeight_zero (x s : ℝ) :
    aksStepWeight x s 0 = 0 :=
  aksStepWeight_eq_zero_of_not_one_lt (by norm_num)

lemma aksStepWeight_one (x s : ℝ) :
    aksStepWeight x s 1 = 0 :=
  aksStepWeight_eq_zero_of_not_one_lt (by norm_num)

/-- Prime divisors of `n` at most `x`; each contributes one maximal
prime-power block to the AKS factorisation. -/
noncomputable def aksSmallPrimeSupport (x : ℝ) (n : ℕ) : Finset ℕ :=
  n.factorization.support.filter fun p => (p : ℝ) ≤ x

/-- The product of the maximal prime-power blocks with prime at most `x`. -/
noncomputable def aksSmallPart (x : ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ aksSmallPrimeSupport x n, p ^ n.factorization p

/-- The complementary `x`-rough factor in the AKS decomposition. -/
noncomputable def aksRoughPart (x : ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (fun p : ℕ => x < (p : ℝ)),
    p ^ n.factorization p

lemma mem_aksSmallPrimeSupport {x : ℝ} {n p : ℕ} :
    p ∈ aksSmallPrimeSupport x n ↔
      p ∈ n.factorization.support ∧ (p : ℝ) ≤ x := by
  simp [aksSmallPrimeSupport]

lemma aksSmallPrimeSupport_prime {x : ℝ} {n p : ℕ}
    (hp : p ∈ aksSmallPrimeSupport x n) :
    Nat.Prime p := by
  have : p ∈ n.primeFactors := by simpa using (mem_aksSmallPrimeSupport.mp hp).1
  exact (Nat.mem_primeFactors.mp this).1

lemma aksSmallPrimeSupport_factorization_pos {x : ℝ} {n p : ℕ}
    (hp : p ∈ aksSmallPrimeSupport x n) :
    0 < n.factorization p := by
  have := Finsupp.mem_support_iff.mp (mem_aksSmallPrimeSupport.mp hp).1
  omega

/-- Every maximal small-prime block is an increment allowed by the AKS walk. -/
lemma aksSmallPrimeSupport_isSmallPrimePower {x : ℝ} {n p : ℕ}
    (hp : p ∈ aksSmallPrimeSupport x n) :
    IsSmallPrimePower x (p ^ n.factorization p) :=
  ⟨p, n.factorization p, aksSmallPrimeSupport_prime hp,
    aksSmallPrimeSupport_factorization_pos hp,
    (mem_aksSmallPrimeSupport.mp hp).2, rfl⟩

/-- The maximal small-prime blocks in the canonical AKS factorisation are
pairwise coprime, as required in the TeX path-count argument. -/
lemma aksSmallPrimeSupport_blocks_pairwise_coprime (x : ℝ) (n : ℕ) :
    (↑(aksSmallPrimeSupport x n) : Set ℕ).Pairwise fun p q =>
      Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q) := by
  intro p hp q hq hpq
  exact Nat.coprime_pow_primes _ _
    (aksSmallPrimeSupport_prime hp) (aksSmallPrimeSupport_prime hq) hpq

/-- Splitting the canonical prime factorisation at `x` reconstructs `n`. -/
lemma aksSmallPart_mul_roughPart {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    aksSmallPart x n * aksRoughPart x n = n := by
  classical
  calc
    aksSmallPart x n * aksRoughPart x n =
        ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
      rw [aksSmallPart, aksRoughPart, aksSmallPrimeSupport]
      simpa only [not_le] using
        Finset.prod_filter_mul_prod_filter_not n.factorization.support
          (fun p : ℕ => (p : ℝ) ≤ x) (fun p => p ^ n.factorization p)
    _ = n := Nat.prod_factorization_pow_eq_self hn

/-- The complementary factor in the canonical split is genuinely
`x`-rough. -/
lemma aksRoughPart_isXRough (x : ℝ) (n : ℕ) :
    IsXRough x (aksRoughPart x n) := by
  intro r hr hrdvd
  rw [aksRoughPart] at hrdvd
  obtain ⟨p, hp, hrp⟩ := (hr.prime.dvd_finsetProd_iff _).mp hrdvd
  have hp' := Finset.mem_filter.mp hp
  have hpprime : Nat.Prime p := by
    have : p ∈ n.primeFactors := by simpa using hp'.1
    exact (Nat.mem_primeFactors.mp this).1
  have hr_dvd_p : r ∣ p := hr.dvd_of_dvd_pow hrp
  have hr_eq : r = p := (Nat.dvd_prime hpprime).mp hr_dvd_p |>.resolve_left hr.ne_one
  simpa [hr_eq] using le_of_lt hp'.2

lemma aksRoughPart_dvd {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    aksRoughPart x n ∣ n :=
  ⟨aksSmallPart x n,
    by simpa [mul_comm] using (aksSmallPart_mul_roughPart (x := x) hn).symm⟩

lemma aksRoughPart_ne_zero {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    aksRoughPart x n ≠ 0 := by
  intro h
  apply hn
  rw [← aksSmallPart_mul_roughPart hn, h, mul_zero]

lemma aksRoughPart_pos {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    0 < aksRoughPart x n :=
  Nat.pos_of_ne_zero (aksRoughPart_ne_zero hn)

lemma aksRoughPart_le {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    aksRoughPart x n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (aksRoughPart_dvd hn)

/-- Canonical form of the factorisation used in the AKS proof: `n` is its
rough core times one admissible maximal prime-power block for each small prime. -/
lemma aks_canonical_factorization {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    ∃ m : ℕ, m ≤ n ∧ IsXRough x m ∧
      n = m * aksSmallPart x n ∧
      ∀ p ∈ aksSmallPrimeSupport x n,
        IsSmallPrimePower x (p ^ n.factorization p) := by
  refine ⟨aksRoughPart x n, aksRoughPart_le hn, aksRoughPart_isXRough x n,
    ?_, fun _ hp => aksSmallPrimeSupport_isSmallPrimePower hp⟩
  simpa [mul_comm] using (aksSmallPart_mul_roughPart (x := x) hn).symm

/-- The orderings of the distinct maximal small-prime blocks. -/
abbrev aksPrimePowerOrderings (x : ℝ) (n : ℕ) :=
  Equiv.Perm {p : ℕ // p ∈ aksSmallPrimeSupport x n}

/-- If there are `k` maximal small-prime blocks, there are exactly `k!`
orders in which the random walk can take them. -/
lemma card_aksPrimePowerOrderings (x : ℝ) (n : ℕ) :
    Fintype.card (aksPrimePowerOrderings x n) =
      Nat.factorial (aksSmallPrimeSupport x n).card := by
  rw [Fintype.card_perm]
  simp

lemma finset_prod_one_div_natCast_rpow (S : Finset ℕ) (f : ℕ → ℕ) (s : ℝ) :
    (∏ i ∈ S, 1 / Real.rpow (f i : ℝ) s) =
      1 / Real.rpow ((∏ i ∈ S, f i : ℕ) : ℝ) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul]
      calc
        1 / Real.rpow (f a : ℝ) s *
            (1 / Real.rpow ((∏ i ∈ S, f i : ℕ) : ℝ) s) =
            1 / (Real.rpow (f a : ℝ) s *
              Real.rpow ((∏ i ∈ S, f i : ℕ) : ℝ) s) := by ring
        _ = 1 / Real.rpow ((f a : ℝ) * (∏ i ∈ S, f i : ℕ)) s := by
          congr 1
          exact (Real.mul_rpow (Nat.cast_nonneg (f a))
            (Nat.cast_nonneg (∏ i ∈ S, f i))).symm

/-- The product of the unnormalised AKS weights of all maximal small-prime
blocks is the unnormalised weight of their product. -/
lemma aksSmallPrimeSupport_weight_product (x s : ℝ) (n : ℕ) :
    (∏ p ∈ aksSmallPrimeSupport x n,
        1 / Real.rpow ((p ^ n.factorization p : ℕ) : ℝ) s) =
      1 / Real.rpow (aksSmallPart x n : ℝ) s := by
  simpa [aksSmallPart] using
    finset_prod_one_div_natCast_rpow (aksSmallPrimeSupport x n)
      (fun p => p ^ n.factorization p) s

/-- The initial rough weight times all block numerators is exactly `n⁻ˢ`, the
algebraic cancellation in the AKS hitting-probability computation. -/
lemma aksRoughPart_weight_mul_smallPart_weight {x s : ℝ} {n : ℕ}
    (hn : n ≠ 0) :
    (1 / Real.rpow (aksRoughPart x n : ℝ) s) *
        (1 / Real.rpow (aksSmallPart x n : ℝ) s) =
      1 / Real.rpow (n : ℝ) s := by
  have hcast : (n : ℝ) =
      (aksRoughPart x n : ℝ) * (aksSmallPart x n : ℝ) := by
    exact_mod_cast (by simpa [mul_comm] using
      (aksSmallPart_mul_roughPart (x := x) hn).symm)
  rw [hcast]
  calc
    1 / Real.rpow (aksRoughPart x n : ℝ) s *
        (1 / Real.rpow (aksSmallPart x n : ℝ) s) =
        1 / (Real.rpow (aksRoughPart x n : ℝ) s *
          Real.rpow (aksSmallPart x n : ℝ) s) := by ring
    _ = 1 / Real.rpow
        ((aksRoughPart x n : ℝ) * (aksSmallPart x n : ℝ)) s := by
      congr 1
      exact (Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)).symm

/-- The probability weight of one fixed ordering of all maximal small-prime
blocks, excluding the initial rough mass. -/
lemma aksSmallPrimeSupport_stepWeight_product (x s : ℝ) (n : ℕ) :
    (∏ p ∈ aksSmallPrimeSupport x n,
        aksStepWeight x s (p ^ n.factorization p)) =
      (1 / Real.rpow (aksSmallPart x n : ℝ) s) /
        aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card := by
  classical
  calc
    (∏ p ∈ aksSmallPrimeSupport x n,
        aksStepWeight x s (p ^ n.factorization p)) =
        ∏ p ∈ aksSmallPrimeSupport x n,
          (1 / Real.rpow ((p ^ n.factorization p : ℕ) : ℝ) s) /
            aksPartitionFunction x s := by
      refine Finset.prod_congr rfl fun p hp => ?_
      exact aksStepWeight_of_small_prime_power
        (aksSmallPrimeSupport_isSmallPrimePower hp)
    _ = (∏ p ∈ aksSmallPrimeSupport x n,
          1 / Real.rpow ((p ^ n.factorization p : ℕ) : ℝ) s) /
          aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card := by
      rw [Finset.prod_div_distrib]
      simp
    _ = _ := by rw [aksSmallPrimeSupport_weight_product]

/-- The initial mass on `x`-rough numbers up to `y` in the AKS proof. -/
noncomputable def aksInitialMass (x y s : ℝ) (n : ℕ) : ℝ :=
  by
    classical
    exact if (n : ℝ) ≤ y ∧ IsXRough x n then 1 / Real.rpow (n : ℝ) s else 0

/-- The support of the AKS initial mass: rough integers up to `y`. -/
def aksInitialSupport (x y : ℝ) : Set ℕ :=
  {n : ℕ | (n : ℝ) ≤ y ∧ IsXRough x n}

lemma mem_aksInitialSupport {x y : ℝ} {n : ℕ} :
    n ∈ aksInitialSupport x y ↔ (n : ℝ) ≤ y ∧ IsXRough x n :=
  Iff.rfl

lemma aksRoughPart_mem_initialSupport {x y : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y) :
    aksRoughPart x n ∈ aksInitialSupport x y := by
  refine ⟨?_, aksRoughPart_isXRough x n⟩
  exact (by exact_mod_cast aksRoughPart_le (x := x) hn :
    (aksRoughPart x n : ℝ) ≤ (n : ℝ)).trans hny

lemma aksInitialSupport_mono_y {x y z : ℝ} (hyz : y ≤ z) :
    aksInitialSupport x y ⊆ aksInitialSupport x z :=
  fun _ hn => ⟨hn.1.trans hyz, hn.2⟩

lemma aksInitialSupport_antitone_x {x z y : ℝ} (hxz : x ≤ z) :
    aksInitialSupport z y ⊆ aksInitialSupport x y :=
  fun _ hn => ⟨hn.1, IsXRough.mono_left hxz hn.2⟩

lemma aksInitialSupport_subset_rough_numbers (x y : ℝ) :
    aksInitialSupport x y ⊆ rough_numbers x := by
  intro _ hn
  exact hn.2

lemma aksInitialSupport_subset_nonzero_of_two_lt {x y : ℝ} (hx : 2 < x) :
    aksInitialSupport x y ⊆ {n : ℕ | n ≠ 0} := by
  intro _ hn
  exact IsXRough.not_zero_of_two_lt hx hn.2

lemma aksInitialSupport_subset_positive_of_two_lt {x y : ℝ} (hx : 2 < x) :
    aksInitialSupport x y ⊆ {n : ℕ | 0 < n} :=
  fun _ hn => Nat.pos_of_ne_zero (aksInitialSupport_subset_nonzero_of_two_lt hx hn)

lemma aksInitialSupport_subset_real_initial_segment_of_two_lt {x y : ℝ}
    (hx : 2 < x) :
    aksInitialSupport x y ⊆ real_initial_segment y :=
  fun _ hn => ⟨Nat.succ_le_of_lt (aksInitialSupport_subset_positive_of_two_lt hx hn), hn.1⟩

/-- The initial support in the AKS construction is finite. -/
lemma aksInitialSupport_finite (x y : ℝ) :
    (aksInitialSupport x y).Finite := by
  by_cases hy : y < 0
  · have hempty : aksInitialSupport x y = ∅ := by
      ext n
      constructor
      · intro hn
        have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        exact False.elim (not_le_of_gt hy (hn_nonneg.trans hn.1))
      · intro hn
        simp at hn
    rw [hempty]
    exact Set.finite_empty
  · have _hy_nonneg : 0 ≤ y := le_of_not_gt hy
    refine (Finset.finite_toSet (Finset.range (⌊y⌋₊ + 1))).subset ?_
    intro n hn
    have hn_floor : n ≤ ⌊y⌋₊ := Nat.le_floor hn.1
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hn_floor))

lemma aksInitialMass_eq_indicator (x y s : ℝ) :
    aksInitialMass x y s =
      fun n : ℕ =>
        (aksInitialSupport x y).indicator
          (fun n : ℕ => 1 / Real.rpow (n : ℝ) s) n := by
  classical
  funext n
  simp only [aksInitialMass, aksInitialSupport, Set.indicator, Set.mem_setOf_eq]

lemma aksInitialMass_of_le_of_rough {x y s : ℝ} {n : ℕ}
    (hny : (n : ℝ) ≤ y) (hrough : IsXRough x n) :
    aksInitialMass x y s n = 1 / Real.rpow (n : ℝ) s := by
  classical
  change (if (n : ℝ) ≤ y ∧ IsXRough x n then 1 / Real.rpow (n : ℝ) s else 0) = _
  rw [if_pos ⟨hny, hrough⟩]

lemma aksInitialMass_eq_zero_of_gt {x y s : ℝ} {n : ℕ}
    (hny : y < (n : ℝ)) :
    aksInitialMass x y s n = 0 := by
  simp [aksInitialMass, not_le_of_gt hny]

lemma aksInitialMass_eq_zero_of_not_rough {x y s : ℝ} {n : ℕ}
    (hrough : ¬ IsXRough x n) :
    aksInitialMass x y s n = 0 := by
  simp [aksInitialMass, hrough]

lemma aksInitialMass_eq_zero_of_not_mem_initialSupport {x y s : ℝ} {n : ℕ}
    (hn : n ∉ aksInitialSupport x y) :
    aksInitialMass x y s n = 0 := by
  by_cases hny : (n : ℝ) ≤ y
  · by_cases hrough : IsXRough x n
    · exact False.elim (hn ⟨hny, hrough⟩)
    · exact aksInitialMass_eq_zero_of_not_rough hrough
  · simp [aksInitialMass, hny]

lemma aksInitialMass_nonneg (x y s : ℝ) (n : ℕ) :
    0 ≤ aksInitialMass x y s n := by
  rw [aksInitialMass]
  split_ifs
  · exact one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  · norm_num

lemma aksInitialMass_support_subset_initialSupport {x y s : ℝ} {n : ℕ}
    (hn : aksInitialMass x y s n ≠ 0) :
    n ∈ aksInitialSupport x y := by
  by_contra hnot
  exact hn (aksInitialMass_eq_zero_of_not_mem_initialSupport hnot)

/-- The AKS initial mass is summable because it has finite support. -/
lemma aksInitialMass_summable (x y s : ℝ) :
    Summable (aksInitialMass x y s) := by
  apply summable_of_hasFiniteSupport
  refine (aksInitialSupport_finite x y).subset ?_
  intro n hn
  exact aksInitialMass_support_subset_initialSupport hn

/-- The total AKS initial mass is the finite sum over natural numbers at most
`y`; the roughness condition remains inside `aksInitialMass`. -/
lemma aksInitialMass_tsum_eq_sum_range (x y s : ℝ) :
    (∑' n : ℕ, aksInitialMass x y s n) =
      ∑ n ∈ Finset.range (⌊y⌋₊ + 1), aksInitialMass x y s n := by
  classical
  exact tsum_eq_sum (s := Finset.range (⌊y⌋₊ + 1)) fun n hn => by
    apply aksInitialMass_eq_zero_of_gt
    by_contra hny
    have hn_le_y : (n : ℝ) ≤ y := le_of_not_gt hny
    have hn_floor : n ≤ ⌊y⌋₊ := Nat.le_floor hn_le_y
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hn_floor))

lemma aksInitialMass_mul_small_sum_le {x y s : ℝ}
    (hx : 2 < x) (hy : 1 ≤ y) :
    (∑' n : ℕ, aksInitialMass x y s n) *
        (∑ d ∈ Finset.Ico 1 ⌊x⌋₊, 1 / Real.rpow (d : ℝ) s) ≤
      ∑ m ∈ Finset.Icc 1 ⌊y * x⌋₊, 1 / Real.rpow (m : ℝ) s := by
  classical
  let hRfin := aksInitialSupport_finite x y
  let R := hRfin.toFinset
  let D := Finset.Ico 1 ⌊x⌋₊
  let F := R ×ˢ D
  let g : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hR : (∑' n : ℕ, aksInitialMass x y s n) =
      ∑ n ∈ R, 1 / Real.rpow (n : ℝ) s := by
    calc
      (∑' n : ℕ, aksInitialMass x y s n) =
          ∑ n ∈ R, aksInitialMass x y s n := by
        refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
          (f := aksInitialMass x y s) (s := R) ?_
        intro n hn
        exact aksInitialMass_eq_zero_of_not_mem_initialSupport fun h =>
          hn (hRfin.mem_toFinset.mpr h)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact aksInitialMass_of_le_of_rough
          (hRfin.mem_toFinset.mp hn).1 (hRfin.mem_toFinset.mp hn).2
  have hinj : Set.InjOn g F := by
    rintro ⟨n₁, d₁⟩ h₁ ⟨n₂, d₂⟩ h₂ heq
    change (n₁, d₁) ∈ F at h₁
    change (n₂, d₂) ∈ F at h₂
    rcases Finset.mem_product.mp h₁ with ⟨h₁R, h₁D⟩
    rcases Finset.mem_product.mp h₂ with ⟨h₂R, h₂D⟩
    have hn₁ := hRfin.mem_toFinset.mp (by simpa [R] using h₁R)
    have hn₂ := hRfin.mem_toFinset.mp (by simpa [R] using h₂R)
    have hd₁ := Finset.mem_Ico.mp (by simpa [D] using h₁D)
    have hd₂ := Finset.mem_Ico.mp (by simpa [D] using h₂D)
    have hd := rough_mul_small_right_injective hx hn₁.2 hn₂.2
      (by omega) (by omega)
      ((by exact_mod_cast hd₁.2 : (d₁ : ℝ) < ⌊x⌋₊).trans_le
        (Nat.floor_le (by linarith)))
      ((by exact_mod_cast hd₂.2 : (d₂ : ℝ) < ⌊x⌋₊).trans_le
        (Nat.floor_le (by linarith))) heq
    have hn : n₁ = n₂ := by
      subst d₂
      change n₁ * d₁ = n₂ * d₁ at heq
      exact Nat.mul_right_cancel (by omega) heq
    exact Prod.ext hn hd
  have himage : F.image g ⊆ Finset.Icc 1 ⌊y * x⌋₊ := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨⟨n, d⟩, hnd, rfl⟩
    have hn := (hRfin.mem_toFinset.mp
      (Finset.mem_product.mp hnd).1)
    have hd := (Finset.mem_Ico.mp (Finset.mem_product.mp hnd).2)
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos
      (aksInitialSupport_subset_positive_of_two_lt hx hn) (by omega), ?_⟩
    apply Nat.le_floor
    rw [Nat.cast_mul]
    exact mul_le_mul hn.1
      ((by exact_mod_cast hd.2.le : (d : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le (by linarith))) (Nat.cast_nonneg d) (by linarith)
  calc
    (∑' n : ℕ, aksInitialMass x y s n) *
        (∑ d ∈ Finset.Ico 1 ⌊x⌋₊, 1 / Real.rpow (d : ℝ) s) =
        ∑ z ∈ F, 1 / Real.rpow (g z : ℝ) s := by
      rw [hR, Finset.sum_product]
      simp only [R, D, g]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_mul]
      rw [one_div, one_div, one_div]
      change (Real.rpow (n : ℝ) s)⁻¹ * (Real.rpow (d : ℝ) s)⁻¹ =
        (Real.rpow ((n : ℝ) * (d : ℝ)) s)⁻¹
      calc
        _ = (Real.rpow (n : ℝ) s * Real.rpow (d : ℝ) s)⁻¹ :=
          (mul_inv _ _).symm
        _ = _ := congrArg Inv.inv
          (Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg d)).symm
    _ = ∑ m ∈ F.image g, 1 / Real.rpow (m : ℝ) s :=
      (Finset.sum_image (f := fun m : ℕ => 1 / Real.rpow (m : ℝ) s) hinj).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊y * x⌋₊, 1 / Real.rpow (m : ℝ) s :=
      Finset.sum_le_sum_of_subset_of_nonneg himage fun m _ _ =>
        one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg m) s)

lemma half_log_le_log_floor {x : ℝ} (hx : 3 ≤ x) :
    Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt : Real.sqrt x ≤ x - 1 := by
    have hpoly : x ≤ (x - 1) ^ 2 := by
      have := mul_nonneg hx0 (sub_nonneg.mpr hx)
      nlinarith
    have hs0 := Real.sqrt_nonneg x
    have hs2 := Real.sq_sqrt hx0
    nlinarith
  have hfloor : Real.sqrt x ≤ (⌊x⌋₊ : ℝ) :=
    hsqrt.trans (Nat.sub_one_lt_floor x).le
  calc
    Real.log x / 2 = Real.log (Real.sqrt x) :=
      (Real.log_sqrt hx0).symm
    _ ≤ Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) hfloor

lemma aks_small_multiplier_sum_lower {x : ℝ} (hx : 3 ≤ x) :
    Real.log x / 2 ≤
      ∑ d ∈ Finset.Ico 1 ⌊x⌋₊,
        1 / Real.rpow (d : ℝ) (aksExponent x) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor
    (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  calc
    Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := half_log_le_log_floor hx
    _ ≤ ∑ d ∈ Finset.Ico 1 ⌊x⌋₊, 1 / (d : ℝ) :=
      log_nat_le_reciprocal_sum_Ico ⌊x⌋₊ hfloor
    _ ≤ ∑ d ∈ Finset.Ico 1 ⌊x⌋₊,
        1 / Real.rpow (d : ℝ) (aksExponent x) := by
      exact Finset.sum_le_sum fun d hd =>
        reciprocal_le_inv_rpow (aksExponent_mem_Ioo hx).2.le
          (Finset.mem_Ico.mp hd).1

/-- TeX equation `\eqref{p2}`, with an explicit absolute constant.  The proof
uses unique-factorisation packing by all positive multipliers below `x`. -/
lemma aksInitialMass_tsum_le {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    (∑' n : ℕ, aksInitialMass x y (aksExponent x) n) ≤
      (20 * Real.exp ((1 : ℝ) / 10)) *
        Real.rpow y (1 - aksExponent x) := by
  let s := aksExponent x
  let a := 1 - s
  let B := ∑' n : ℕ, aksInitialMass x y s n
  let W := ∑ d ∈ Finset.Ico 1 ⌊x⌋₊, 1 / Real.rpow (d : ℝ) s
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ y := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hs := aksExponent_mem_Ioo hx
  have ha : 0 < a := by
    dsimp [a, s]
    exact sub_pos.mpr hs.2
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpack : B * W ≤
      ∑ m ∈ Finset.Icc 1 ⌊y * x⌋₊, 1 / Real.rpow (m : ℝ) s :=
    aksInitialMass_mul_small_sum_le (by linarith) hy
  have hT : 1 ≤ y * x := (by linarith : (1 : ℝ) ≤ x).trans <| by
    simpa using mul_le_mul_of_nonneg_right hy hx0.le
  have hupper : (∑ m ∈ Finset.Icc 1 ⌊y * x⌋₊,
      1 / Real.rpow (m : ℝ) s) ≤ Real.rpow (y * x) a / a := by
    simpa [a, s] using inv_rpow_sum_Icc_le
      hT hs.1 hs.2
  have hW : Real.log x / 2 ≤ W := aks_small_multiplier_sum_lower hx
  have hB : 0 ≤ B := tsum_nonneg (aksInitialMass_nonneg x y s)
  have hBW : B * (Real.log x / 2) ≤ Real.rpow (y * x) a / a :=
    (mul_le_mul_of_nonneg_left hW hB).trans (hpack.trans hupper)
  have hscaled : a * (B * (Real.log x / 2)) ≤ Real.rpow (y * x) a := by
    calc
      a * (B * (Real.log x / 2)) ≤ a * (Real.rpow (y * x) a / a) :=
        mul_le_mul_of_nonneg_left hBW ha.le
      _ = Real.rpow (y * x) a := by field_simp [ha.ne']
  have hacancel : a * (Real.log x / 2) = 1 / 20 := by
    dsimp [a, s]
    rw [one_sub_aksExponent]
    field_simp [hlog.ne']
    ring
  have hB20 : B ≤ 20 * Real.rpow (y * x) a := by
    have hscaled' : B * (1 / 20) ≤ Real.rpow (y * x) a := by
      calc
        B * (1 / 20) = a * (B * (Real.log x / 2)) := by
          rw [← hacancel]
          ring
        _ ≤ _ := hscaled
    linarith
  calc
    (∑' n : ℕ, aksInitialMass x y (aksExponent x) n) = B := rfl
    _ ≤ 20 * Real.rpow (y * x) a := hB20
    _ = 20 * (Real.rpow y a * Real.rpow x a) :=
      congrArg (fun z : ℝ => 20 * z) (Real.mul_rpow hy0 hx0.le)
    _ = (20 * Real.exp ((1 : ℝ) / 10)) *
        Real.rpow y (1 - aksExponent x) := by
      change 20 * (Real.rpow y (1 - aksExponent x) *
        Real.rpow x (1 - aksExponent x)) = _
      rw [aks_rpow_one_sub_exponent (by linarith)]
      ring

/-- The AKS initial distribution has positive total mass whenever its support
contains `1`. -/
lemma aksInitialMass_tsum_pos {x y s : ℝ} (hy : 1 ≤ y) :
    0 < ∑' n : ℕ, aksInitialMass x y s n := by
  have hone_pos : 0 < aksInitialMass x y s 1 := by
    rw [aksInitialMass_of_le_of_rough (by exact_mod_cast hy) (IsXRough.one x)]
    norm_num
  exact (aksInitialMass_summable x y s).tsum_pos
    (aksInitialMass_nonneg x y s) 1 hone_pos

lemma aksInitialMass_pos_of_mem_initialSupport {x y s : ℝ} {n : ℕ}
    (hx : 2 < x) (hn : n ∈ aksInitialSupport x y) :
    0 < aksInitialMass x y s n := by
  rw [aksInitialMass_of_le_of_rough hn.1 hn.2]
  have hn_ne_zero : n ≠ 0 := IsXRough.not_zero_of_two_lt hx hn.2
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn_ne_zero
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hn_pos s)

lemma aksInitialMass_two_of_le {y s : ℝ} {n : ℕ} (hny : (n : ℝ) ≤ y) :
    aksInitialMass 2 y s n = 1 / Real.rpow (n : ℝ) s :=
  aksInitialMass_of_le_of_rough hny (isXRough_two n)

/-- Total mass reaching `n` in the AKS upward multiplicative random walk. -/
noncomputable def aksHittingMass (x y s : ℝ) (n : ℕ) : ℝ :=
  Nat.strongRec (motive := fun _ => ℝ) (fun n rec =>
    aksInitialMass x y s n +
      ∑ q ∈ Finset.range (n + 1),
        if hq : n ≠ 0 ∧ 1 < q ∧ q ∣ n then
          rec (n / q) (Nat.div_lt_self (Nat.pos_of_ne_zero hq.1) hq.2.1) *
            aksStepWeight x s q
        else 0) n

lemma aksHittingMass_recurrence (x y s : ℝ) (n : ℕ) :
    aksHittingMass x y s n =
      aksInitialMass x y s n +
        ∑ q ∈ Finset.range (n + 1),
          if n ≠ 0 ∧ 1 < q ∧ q ∣ n then
            aksHittingMass x y s (n / q) * aksStepWeight x s q
          else 0 := by
  rw [aksHittingMass, Nat.strongRec_eq]
  congr 1

lemma aksHittingMass_nonneg (x y s : ℝ) (n : ℕ) :
    0 ≤ aksHittingMass x y s n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [aksHittingMass_recurrence]
      exact add_nonneg (aksInitialMass_nonneg x y s n) <|
        Finset.sum_nonneg fun q hq => by
          split_ifs with hcond
          · exact mul_nonneg
              (ih (n / q) (Nat.div_lt_self
                (Nat.pos_of_ne_zero hcond.1) hcond.2.1))
              (aksStepWeight_nonneg_unconditional q)
          · exact le_rfl

lemma aksHittingMass_zero {x y s : ℝ} (hx : 2 < x) :
    aksHittingMass x y s 0 = 0 := by
  rw [aksHittingMass_recurrence]
  have hrough : ¬ IsXRough x 0 := by
    intro h
    exact (IsXRough.not_zero_of_two_lt hx h) rfl
  simp [aksInitialMass_eq_zero_of_not_rough hrough]

lemma aksHittingMass_tsum_recurrence {x y s : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    aksHittingMass x y s n = aksInitialMass x y s n +
      ∑' q : ℕ,
        if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          aksHittingMass x y s (n / q) *
            aksUpwardKernel x s (some (n / q)) (some n)
        else 0 := by
  rw [aksHittingMass_recurrence]
  congr 1
  symm
  calc
    (∑' q : ℕ,
        if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          aksHittingMass x y s (n / q) *
            aksUpwardKernel x s (some (n / q)) (some n)
        else 0) =
        ∑ q ∈ Finset.range (n + 1),
          if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
            aksHittingMass x y s (n / q) *
              aksUpwardKernel x s (some (n / q)) (some n)
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.range (n + 1)) fun q hq => ?_
      have hqgt : n < q := by simpa using hq
      have hnotdvd : ¬q ∣ n := fun hdiv =>
        (not_lt_of_ge (Nat.le_of_dvd (by omega) hdiv)) hqgt
      simp [hnotdvd]
    _ = ∑ q ∈ Finset.range (n + 1),
          if n ≠ 0 ∧ 1 < q ∧ q ∣ n then
            aksHittingMass x y s (n / q) * aksStepWeight x s q
          else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hcond : 1 < q ∧ q ∣ n ∧ 1 ≤ n / q
      · rw [if_pos hcond, if_pos ⟨by omega, hcond.1, hcond.2.1⟩,
          aksUpwardKernel_divisor_step (by omega) hcond.1 hcond.2.1]
      · have hcond' : ¬(n ≠ 0 ∧ 1 < q ∧ q ∣ n) := by
          intro h
          apply hcond
          exact ⟨h.2.1, h.2.2,
            Nat.div_pos (Nat.le_of_dvd (by omega) h.2.2) (by omega)⟩
        rw [if_neg hcond, if_neg hcond']

lemma aksInitialMass_le_hittingMass (x y s : ℝ) (n : ℕ) :
    aksInitialMass x y s n ≤ aksHittingMass x y s n := by
  rw [aksHittingMass_recurrence]
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun q hq => by
    split_ifs with hcond
    · exact mul_nonneg (aksHittingMass_nonneg _ _ _ _)
        (aksStepWeight_nonneg_unconditional _)
    · exact le_rfl

/-- One admissible multiplicative step contributes its predecessor mass times
the increment probability to the hitting mass at the target. -/
lemma aksHittingMass_mul_step_le {x y s : ℝ} {m q : ℕ}
    (hm : 0 < m) (hq : 1 < q) :
    aksHittingMass x y s m * aksStepWeight x s q ≤
      aksHittingMass x y s (m * q) := by
  let f : ℕ → ℝ := fun r =>
    if m * q ≠ 0 ∧ 1 < r ∧ r ∣ m * q then
      aksHittingMass x y s (m * q / r) * aksStepWeight x s r
    else 0
  have hqmem : q ∈ Finset.range (m * q + 1) := by
    exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_mul_of_pos_left q hm
  have hterm : f q = aksHittingMass x y s m * aksStepWeight x s q := by
    rw [show f q = if m * q ≠ 0 ∧ 1 < q ∧ q ∣ m * q then
      aksHittingMass x y s (m * q / q) * aksStepWeight x s q else 0 by rfl,
      if_pos ⟨Nat.mul_ne_zero hm.ne' (by omega), hq, dvd_mul_left q m⟩,
      Nat.mul_div_cancel m (by omega)]
  have hsum : f q ≤ ∑ r ∈ Finset.range (m * q + 1), f r :=
    Finset.single_le_sum (fun r hr => by
      dsimp [f]
      split_ifs
      · exact mul_nonneg (aksHittingMass_nonneg _ _ _ _)
          (aksStepWeight_nonneg_unconditional _)
      · exact le_rfl) hqmem
  calc
    aksHittingMass x y s m * aksStepWeight x s q = f q := hterm.symm
    _ ≤ ∑ r ∈ Finset.range (m * q + 1), f r := hsum
    _ ≤ aksInitialMass x y s (m * q) +
        ∑ r ∈ Finset.range (m * q + 1), f r :=
      le_add_of_nonneg_left (aksInitialMass_nonneg _ _ _ _)
    _ = aksHittingMass x y s (m * q) := by
      rw [aksHittingMass_recurrence]

/-- Any finite collection of admissible final increments contributes at most
the hitting mass at the target. -/
lemma aksHittingMass_divisor_sum_le {x y s : ℝ} {n : ℕ} (hn : 0 < n)
    (S : Finset ℕ) (hS : ∀ q ∈ S, 1 < q ∧ q ∣ n) :
    (∑ q ∈ S, aksHittingMass x y s (n / q) * aksStepWeight x s q) ≤
      aksHittingMass x y s n := by
  calc
    (∑ q ∈ S, aksHittingMass x y s (n / q) * aksStepWeight x s q) =
        ∑ q ∈ S, if n ≠ 0 ∧ 1 < q ∧ q ∣ n then
          aksHittingMass x y s (n / q) * aksStepWeight x s q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos ⟨hn.ne', (hS q hq).1, (hS q hq).2⟩]
    _ ≤ ∑ q ∈ Finset.range (n + 1), if n ≠ 0 ∧ 1 < q ∧ q ∣ n then
          aksHittingMass x y s (n / q) * aksStepWeight x s q else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <|
          Nat.le_of_dvd hn (hS q hq).2
      · intro q _ _
        split_ifs
        · exact mul_nonneg (aksHittingMass_nonneg _ _ _ _)
            (aksStepWeight_nonneg_unconditional _)
        · exact le_rfl
    _ ≤ aksInitialMass x y s n +
        ∑ q ∈ Finset.range (n + 1), if n ≠ 0 ∧ 1 < q ∧ q ∣ n then
          aksHittingMass x y s (n / q) * aksStepWeight x s q else 0 :=
      le_add_of_nonneg_left (aksInitialMass_nonneg _ _ _ _)
    _ = aksHittingMass x y s n := (aksHittingMass_recurrence _ _ _ _).symm

private lemma factorial_mul_finset_prod_eq_sum_erase (S : Finset ℕ)
    (hS : S.Nonempty) (a : ℝ) (w : ℕ → ℝ) :
    (Nat.factorial S.card : ℝ) * (a * ∏ q ∈ S, w q) =
      ∑ q ∈ S, (Nat.factorial (S.erase q).card : ℝ) *
        (a * ∏ r ∈ S.erase q, w r) * w q := by
  classical
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  calc
    (Nat.factorial S.card : ℝ) * (a * ∏ q ∈ S, w q) =
        (S.card : ℝ) * ((Nat.factorial (S.card - 1) : ℝ) *
          (a * ∏ q ∈ S, w q)) := by
      rw [show S.card = S.card - 1 + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    _ = ∑ q ∈ S, (Nat.factorial (S.card - 1) : ℝ) *
          (a * ∏ r ∈ S, w r) := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hprod : (∏ r ∈ S, w r) = (∏ r ∈ S.erase q, w r) * w q :=
        (Finset.prod_erase_mul S w hq).symm
      rw [Finset.card_erase_of_mem hq, hprod]
      ring

/-- The recurrence counts every ordering of a finite set of multiplicative
increments. -/
lemma aksInitialMass_mul_finset_steps_factorial_le_hittingMass
    {x y s : ℝ} {m : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (hS : ∀ q ∈ S, 1 < q) :
    (Nat.factorial S.card : ℝ) *
        (aksInitialMass x y s m * ∏ q ∈ S, aksStepWeight x s q) ≤
      aksHittingMass x y s (m * ∏ q ∈ S, q) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
      by_cases hS0 : S = ∅
      · subst S
        simpa using aksInitialMass_le_hittingMass x y s m
      have htarget : 0 < m * ∏ q ∈ S, q := Nat.mul_pos hm <|
        Finset.prod_pos fun q hq => Nat.zero_lt_of_lt (hS q hq)
      calc
        (Nat.factorial S.card : ℝ) *
            (aksInitialMass x y s m * ∏ q ∈ S, aksStepWeight x s q) =
            ∑ q ∈ S, (Nat.factorial (S.erase q).card : ℝ) *
              (aksInitialMass x y s m *
                ∏ r ∈ S.erase q, aksStepWeight x s r) *
                aksStepWeight x s q :=
          factorial_mul_finset_prod_eq_sum_erase S
            (Finset.nonempty_iff_ne_empty.mpr hS0) _ _
        _ ≤ ∑ q ∈ S, aksHittingMass x y s (m * ∏ r ∈ S.erase q, r) *
              aksStepWeight x s q := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_right
            (ih (S.erase q) (Finset.erase_ssubset hq)
              (fun r hr => hS r (Finset.mem_of_mem_erase hr)))
            (aksStepWeight_nonneg_unconditional q)
        _ = ∑ q ∈ S, aksHittingMass x y s ((m * ∏ r ∈ S, r) / q) *
              aksStepWeight x s q := by
          apply Finset.sum_congr rfl
          intro q hq
          congr 2
          have hqpos : 0 < q := Nat.zero_lt_of_lt (hS q hq)
          have hprod : (∏ r ∈ S, r) = (∏ r ∈ S.erase q, r) * q :=
            (Finset.prod_erase_mul S id hq).symm
          rw [hprod, ← mul_assoc, Nat.mul_div_cancel _ hqpos]
        _ ≤ aksHittingMass x y s (m * ∏ q ∈ S, q) := by
          apply aksHittingMass_divisor_sum_le htarget S
          intro q hq
          refine ⟨hS q hq, ?_⟩
          have hprod : (∏ r ∈ S, r) = (∏ r ∈ S.erase q, r) * q :=
            (Finset.prod_erase_mul S id hq).symm
          rw [hprod, ← mul_assoc]
          exact dvd_mul_left q _

/-- Iterating the one-step inequality along any ordered list of admissible
increments gives a genuine path contribution to the hitting mass. -/
lemma aksHittingMass_mul_list_steps_le {x y s : ℝ} {m : ℕ} (hm : 0 < m)
    (l : List ℕ) (hl : ∀ q ∈ l, 1 < q) :
    aksHittingMass x y s m * (l.map (aksStepWeight x s)).prod ≤
      aksHittingMass x y s (m * l.prod) := by
  induction l generalizing m with
  | nil => simp
  | cons q l ih =>
      have hq := hl q (by simp)
      have hl' : ∀ r ∈ l, 1 < r := fun r hr => hl r (by simp [hr])
      have hprod_nonneg : 0 ≤ (l.map (aksStepWeight x s)).prod :=
        List.prod_nonneg fun _ hr => by
          rcases List.mem_map.mp hr with ⟨r, _hr, rfl⟩
          exact aksStepWeight_nonneg_unconditional r
      calc
        aksHittingMass x y s m * ((q :: l).map (aksStepWeight x s)).prod =
            (aksHittingMass x y s m * aksStepWeight x s q) *
              (l.map (aksStepWeight x s)).prod := by simp [mul_assoc]
        _ ≤ aksHittingMass x y s (m * q) *
              (l.map (aksStepWeight x s)).prod :=
          mul_le_mul_of_nonneg_right (aksHittingMass_mul_step_le hm hq) hprod_nonneg
        _ ≤ aksHittingMass x y s ((m * q) * l.prod) :=
          ih (Nat.mul_pos hm (by omega)) hl'
        _ = aksHittingMass x y s (m * (q :: l).prod) := by
          simp [mul_assoc]

lemma aksInitialMass_mul_list_steps_le_hittingMass {x y s : ℝ} {m : ℕ}
    (hm : 0 < m) (l : List ℕ) (hl : ∀ q ∈ l, 1 < q) :
    aksInitialMass x y s m * (l.map (aksStepWeight x s)).prod ≤
      aksHittingMass x y s (m * l.prod) := by
  exact (mul_le_mul_of_nonneg_right (aksInitialMass_le_hittingMass x y s m)
    (List.prod_nonneg fun _ hq => by
      rcases List.mem_map.mp hq with ⟨q, _hq, rfl⟩
      exact aksStepWeight_nonneg_unconditional q)).trans
      (aksHittingMass_mul_list_steps_le hm l hl)

/-- The canonical maximal-prime-power ordering is an actual path from the
rough core to `n`. -/
lemma aks_canonical_ordering_le_hittingMass {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) :
    aksInitialMass x y s (aksRoughPart x n) *
        (∏ p ∈ aksSmallPrimeSupport x n,
          aksStepWeight x s (p ^ n.factorization p)) ≤
      aksHittingMass x y s n := by
  let l := (aksSmallPrimeSupport x n).toList.map
    (fun p => p ^ n.factorization p)
  have hl : ∀ q ∈ l, 1 < q := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
    exact IsSmallPrimePower.one_lt <|
      aksSmallPrimeSupport_isSmallPrimePower (by simpa using hp)
  have hpath := aksInitialMass_mul_list_steps_le_hittingMass (x := x) (y := y) (s := s)
    (aksRoughPart_pos (x := x) hn) l hl
  have hprod : l.prod = aksSmallPart x n := by
    simp [l, aksSmallPart]
  have hweight : (l.map (aksStepWeight x s)).prod =
      ∏ p ∈ aksSmallPrimeSupport x n,
        aksStepWeight x s (p ^ n.factorization p) := by
    simp [l]
  rw [hprod] at hpath
  have htarget : aksRoughPart x n * aksSmallPart x n = n := by
    simpa [mul_comm] using aksSmallPart_mul_roughPart (x := x) hn
  rw [hweight, htarget] at hpath
  exact hpath

/-- Exact mass of any one canonical ordering of the maximal small-prime
blocks from the rough core to `n`. -/
lemma aks_canonical_ordering_weight {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y) :
    aksInitialMass x y s (aksRoughPart x n) *
        (∏ p ∈ aksSmallPrimeSupport x n,
          aksStepWeight x s (p ^ n.factorization p)) =
      (1 / Real.rpow (n : ℝ) s) /
        aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card := by
  rw [aksInitialMass_of_le_of_rough
      (aksRoughPart_mem_initialSupport hn hny).1
      (aksRoughPart_mem_initialSupport hn hny).2,
    aksSmallPrimeSupport_stepWeight_product]
  calc
    (1 / Real.rpow (aksRoughPart x n : ℝ) s) *
        ((1 / Real.rpow (aksSmallPart x n : ℝ) s) /
          aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card) =
        ((1 / Real.rpow (aksRoughPart x n : ℝ) s) *
          (1 / Real.rpow (aksSmallPart x n : ℝ) s)) /
            aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card := by ring
    _ = _ := by rw [aksRoughPart_weight_mul_smallPart_weight hn]

/-- Exact one-ordering lower bound for the actual AKS hitting mass. -/
lemma aks_canonical_ordering_exact_le_hittingMass {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y) :
    (1 / Real.rpow (n : ℝ) s) /
        aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card ≤
      aksHittingMass x y s n := by
  rw [← aks_canonical_ordering_weight hn hny]
  exact aks_canonical_ordering_le_hittingMass hn

lemma aksSmallPrimeSupport_block_injOn (x : ℝ) (n : ℕ) :
    Set.InjOn (fun p => p ^ n.factorization p) (aksSmallPrimeSupport x n) := by
  intro p hp q hq hpq
  exact ((aksSmallPrimeSupport_prime hp).pow_inj'
    (aksSmallPrimeSupport_prime hq)
    (Nat.ne_of_gt <| aksSmallPrimeSupport_factorization_pos hp)
    (Nat.ne_of_gt <| aksSmallPrimeSupport_factorization_pos hq) hpq).1

/-- All `k!` canonical orderings are disjoint contributions to the actual
AKS hitting mass. -/
lemma aks_canonical_orderings_total_weight_le_hittingMass {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) :
    (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y s (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x s (p ^ n.factorization p)) ≤
      aksHittingMass x y s n := by
  classical
  let f : ℕ → ℕ := fun p => p ^ n.factorization p
  let S := (aksSmallPrimeSupport x n).image f
  have hinj : Set.InjOn f (aksSmallPrimeSupport x n) :=
    aksSmallPrimeSupport_block_injOn x n
  have hsteps : ∀ q ∈ S, 1 < q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact (aksSmallPrimeSupport_isSmallPrimePower hp).one_lt
  have h := aksInitialMass_mul_finset_steps_factorial_le_hittingMass
    (x := x) (y := y) (s := s) (aksRoughPart_pos (x := x) hn) S hsteps
  have hcard : S.card = (aksSmallPrimeSupport x n).card :=
    Finset.card_image_iff.mpr hinj
  have hprod : (∏ q ∈ S, q) = aksSmallPart x n := by
    rw [show S = (aksSmallPrimeSupport x n).image f by rfl,
      Finset.prod_image hinj]
    rfl
  have hweight : (∏ q ∈ S, aksStepWeight x s q) =
      ∏ p ∈ aksSmallPrimeSupport x n,
        aksStepWeight x s (p ^ n.factorization p) := by
    rw [show S = (aksSmallPrimeSupport x n).image f by rfl,
      Finset.prod_image hinj]
  rw [hcard, hprod, hweight,
    show aksRoughPart x n * aksSmallPart x n = n by
      simpa [mul_comm] using aksSmallPart_mul_roughPart (x := x) hn] at h
  exact h

/-- Summing the common weight over the `k!` canonical block orderings gives
the factorial factor in the AKS hitting lower bound. -/
lemma aks_canonical_orderings_total_weight {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y) :
    (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y s (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x s (p ^ n.factorization p)) =
      (1 / Real.rpow (n : ℝ) s) *
        (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) /
          aksPartitionFunction x s ^ (aksSmallPrimeSupport x n).card := by
  rw [aks_canonical_ordering_weight hn hny]
  ring

/-- The reciprocal sum over the interval `[y / x, y]`. -/
noncomputable def reciprocal_dyadic_interval_sum (A : Set ℕ) (x y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (A ∩ {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}).indicator
      (fun n : ℕ => 1 / (n : ℝ)) n

/-- The multiplicative interval `[y / x, y]` appearing in the AKS theorem. -/
def aksInterval (x y : ℝ) : Set ℕ :=
  {n : ℕ | y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y}

lemma mem_aksInterval {x y : ℝ} {n : ℕ} :
    n ∈ aksInterval x y ↔ y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y :=
  Iff.rfl

lemma aksInterval_pos {x y : ℝ} {n : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    (hn : n ∈ aksInterval x y) :
    0 < (n : ℝ) := by
  have : 1 ≤ y / x := by
    rw [le_div_iff₀ hx]
    simpa using hxy
  exact lt_of_lt_of_le zero_lt_one (this.trans hn.1)

/-- Uniform lower comparison from the TeX line following `\eqref{qasym}`:
on `[y/x,y]`, `n⁻ˢ` dominates a fixed multiple of `y^(1-s)/n`. -/
lemma aks_interval_rpow_weight_lower {x y : ℝ} {n : ℕ}
    (hx : 3 ≤ x) (hxy : x ≤ y) (hn : n ∈ aksInterval x y) :
    Real.exp (-(1 : ℝ) / 10) * Real.rpow y (1 - aksExponent x) / (n : ℝ) ≤
      1 / Real.rpow (n : ℝ) (aksExponent x) := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hn_pos := aksInterval_pos hx_pos hxy hn
  have ha : 0 ≤ 1 - aksExponent x :=
    (one_sub_aksExponent_pos (by linarith)).le
  have hmono : Real.rpow (y / x) (1 - aksExponent x) ≤
      Real.rpow (n : ℝ) (1 - aksExponent x) :=
    Real.rpow_le_rpow (div_nonneg hy_pos.le hx_pos.le) hn.1 ha
  have hquot : Real.rpow (y / x) (1 - aksExponent x) =
      Real.exp (-(1 : ℝ) / 10) * Real.rpow y (1 - aksExponent x) := by
    change (y / x) ^ (1 - aksExponent x) = _
    rw [Real.div_rpow hy_pos.le hx_pos.le,
      show x ^ (1 - aksExponent x) = Real.exp ((1 : ℝ) / 10) from
        aks_rpow_one_sub_exponent (by linarith)]
    rw [show (-(1 : ℝ) / 10) = -((1 : ℝ) / 10) by ring, Real.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  rw [one_div_rpow_eq_rpow_one_sub_div
    (Nat.ne_of_gt (by exact_mod_cast hn_pos : 0 < n))]
  gcongr
  exact hquot ▸ hmono

lemma primitive_set_inter_aksInterval {A : Set ℕ} (hA : primitive_set A)
    (x y : ℝ) :
    primitive_set (A ∩ aksInterval x y) :=
  primitive_set_of_subset hA (fun _ hn => hn.1)

lemma aksInterval_subset_real_initial_segment {x y : ℝ} (hxy : 1 ≤ y / x) :
    aksInterval x y ⊆ real_initial_segment y := by
  intro n hn
  change y / x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y at hn
  change 1 ≤ n ∧ (n : ℝ) ≤ y
  have hn_one_real : (1 : ℝ) ≤ (n : ℝ) := le_trans hxy hn.1
  have hn_one : 1 ≤ n := by exact_mod_cast hn_one_real
  exact ⟨hn_one, hn.2⟩

lemma aksInterval_subset_real_initial_segment_of_le {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    aksInterval x y ⊆ real_initial_segment y := by
  apply aksInterval_subset_real_initial_segment
  rw [le_div_iff₀ hx]
  simpa using hxy

lemma reciprocal_dyadic_interval_sum_eq (A : Set ℕ) (x y : ℝ) :
    reciprocal_dyadic_interval_sum A x y =
      ∑' n : ℕ, (A ∩ aksInterval x y).indicator (fun n : ℕ => 1 / (n : ℝ)) n := by
  rfl

lemma reciprocal_dyadic_interval_sum_empty (x y : ℝ) :
    reciprocal_dyadic_interval_sum (∅ : Set ℕ) x y = 0 := by
  simp [reciprocal_dyadic_interval_sum]

/-- The elementary real-valued Poisson mass used in the AKS final counting
step, with a local real form convenient for the later combinatorial estimates. -/
noncomputable def aksPoissonMass (Z : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-Z) * Z ^ k / (Nat.factorial k : ℝ)

lemma aksPoissonMass_nonneg {Z : ℝ} (hZ : 0 ≤ Z) (k : ℕ) :
    0 ≤ aksPoissonMass Z k := by
  rw [aksPoissonMass]
  positivity

lemma aksPoissonMass_pos {Z : ℝ} (hZ : 0 < Z) (k : ℕ) :
    0 < aksPoissonMass Z k := by
  rw [aksPoissonMass]
  positivity

lemma aksPoissonMass_zero (Z : ℝ) :
    aksPoissonMass Z 0 = Real.exp (-Z) := by
  simp [aksPoissonMass]

lemma aksPoissonMass_succ_eq (Z : ℝ) (k : ℕ) :
    aksPoissonMass Z (k + 1) =
      aksPoissonMass Z k * (Z / ((k + 1 : ℕ) : ℝ)) := by
  rw [aksPoissonMass, aksPoissonMass, Nat.factorial_succ]
  have hfac_pos : 0 < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hsucc_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos k
  field_simp [Nat.cast_mul, hfac_pos.ne', hsucc_pos.ne']
  push_cast
  ring

lemma aksPoissonMass_le_succ_of_succ_le_rate {Z : ℝ} {k : ℕ}
    (hZ : 0 ≤ Z) (hk : ((k + 1 : ℕ) : ℝ) ≤ Z) :
    aksPoissonMass Z k ≤ aksPoissonMass Z (k + 1) := by
  have hmass_nonneg : 0 ≤ aksPoissonMass Z k :=
    aksPoissonMass_nonneg hZ k
  have hsucc_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos k
  have hratio : 1 ≤ Z / (((k + 1 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ hsucc_pos]
    simpa using hk
  calc
    aksPoissonMass Z k = aksPoissonMass Z k * 1 := by ring
    _ ≤ aksPoissonMass Z k * (Z / (((k + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hmass_nonneg
    _ = aksPoissonMass Z (k + 1) := by
      rw [aksPoissonMass_succ_eq]

lemma aksPoissonMass_succ_le_of_rate_le_succ {Z : ℝ} {k : ℕ}
    (hZ : 0 ≤ Z) (hk : Z ≤ ((k + 1 : ℕ) : ℝ)) :
    aksPoissonMass Z (k + 1) ≤ aksPoissonMass Z k := by
  have hmass_nonneg : 0 ≤ aksPoissonMass Z k :=
    aksPoissonMass_nonneg hZ k
  have hsucc_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos k
  have hratio : Z / (((k + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ hsucc_pos]
    simpa using hk
  calc
    aksPoissonMass Z (k + 1) =
        aksPoissonMass Z k * (Z / (((k + 1 : ℕ) : ℝ))) := by
      rw [aksPoissonMass_succ_eq]
    _ ≤ aksPoissonMass Z k * 1 :=
      mul_le_mul_of_nonneg_left hratio hmass_nonneg
    _ = aksPoissonMass Z k := by ring

/-- A Poisson mass of nonnegative rate is maximized at the natural floor of
its rate. -/
lemma aksPoissonMass_le_floor {Z : ℝ} (hZ : 0 ≤ Z) (k : ℕ) :
    aksPoissonMass Z k ≤ aksPoissonMass Z ⌊Z⌋₊ := by
  by_cases hk : k ≤ ⌊Z⌋₊
  · exact Nat.le_induction (m := k)
      (P := fun j _ => j ≤ ⌊Z⌋₊ ->
        aksPoissonMass Z k ≤ aksPoissonMass Z j)
      (fun _ => le_rfl)
      (fun j _ ih hj =>
        (ih (Nat.le_trans (Nat.le_succ j) hj)).trans
          (aksPoissonMass_le_succ_of_succ_le_rate hZ (by
            exact (by exact_mod_cast hj : ((j + 1 : ℕ) : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans
              (Nat.floor_le hZ)))) ⌊Z⌋₊ hk le_rfl
  · have hfloor_le : ⌊Z⌋₊ ≤ k := by omega
    exact Nat.le_induction (m := ⌊Z⌋₊)
      (P := fun j _ => aksPoissonMass Z j ≤ aksPoissonMass Z ⌊Z⌋₊)
      le_rfl
      (fun j hj ih =>
        (aksPoissonMass_succ_le_of_rate_le_succ hZ (by
          have hlt : Z < (⌊Z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Z
          have hj' : (⌊Z⌋₊ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          norm_num at hlt ⊢
          linarith)).trans ih) k hfloor_le

lemma one_add_inv_pow_le_exp_one (m : ℕ) (hm : 1 ≤ m) :
    ((1 : ℝ) + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  calc
    ((1 : ℝ) + 1 / (m : ℝ)) ^ m ≤
        (Real.exp (1 / (m : ℝ))) ^ m := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp (1 / (m : ℝ))
    _ = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

/-- Effective Stirling bound for the maximal Poisson atom, first expressed
in terms of the integer mode. -/
lemma aksPoissonMass_floor_le_exp_div_sqrt {Z : ℝ} (hZ : 1 ≤ Z) :
    aksPoissonMass Z ⌊Z⌋₊ ≤ Real.exp 1 / Real.sqrt (⌊Z⌋₊ : ℝ) := by
  let m := ⌊Z⌋₊
  have hm : 1 ≤ m := (Nat.one_le_floor_iff Z).mpr hZ
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmZ : (m : ℝ) ≤ Z := Nat.floor_le (by linarith)
  have hZm : Z < (m : ℝ) + 1 := by simpa [m] using Nat.lt_floor_add_one Z
  have hratio : (Z / (m : ℝ)) ^ m ≤ Real.exp 1 := by
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ m) (one_add_inv_pow_le_exp_one m hm)
    rw [div_le_iff₀ hm_pos]
    field_simp
    linarith
  have hpow : Z ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    calc
      Z ^ m = (Z / (m : ℝ)) ^ m * (m : ℝ) ^ m := by
        rw [div_pow]
        field_simp
      _ ≤ Real.exp 1 * (m : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
  have hexp : Real.exp (-Z) ≤ Real.exp (-(m : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hmZ)
  have hnum : Real.exp (-Z) * Z ^ m ≤
      Real.exp 1 * ((m : ℝ) / Real.exp 1) ^ m := by
    calc
      Real.exp (-Z) * Z ^ m ≤ Real.exp (-(m : ℝ)) *
          (Real.exp 1 * (m : ℝ) ^ m) :=
        mul_le_mul hexp hpow (by positivity) (by positivity)
      _ = Real.exp 1 * ((m : ℝ) / Real.exp 1) ^ m := by
        rw [div_pow, ← Real.exp_nat_mul]
        rw [Real.exp_neg]
        field_simp
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    apply Real.sqrt_le_sqrt
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hstirling : Real.sqrt (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m ≤
      (Nat.factorial m : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hsqrt (by positivity)).trans
      (Stirling.le_factorial_stirling m)
  have hbase_pos : 0 < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_pos
  change Real.exp (-Z) * Z ^ m / (Nat.factorial m : ℝ) ≤ _
  calc
    Real.exp (-Z) * Z ^ m / (Nat.factorial m : ℝ) ≤
        (Real.exp (-Z) * Z ^ m) /
          (Real.sqrt (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos hsqrt_pos hbase_pos) hstirling
    _ ≤ (Real.exp 1 * ((m : ℝ) / Real.exp 1) ^ m) /
          (Real.sqrt (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = Real.exp 1 / Real.sqrt (m : ℝ) := by
      field_simp

/-- Uniform local Poisson estimate, with an explicit absolute constant:
`sup_k P(X = k) ≤ e√2 / √Z` for rate `Z ≥ 1`. -/
lemma aksPoissonMass_le_exp_mul_sqrt_two_div_sqrt {Z : ℝ}
    (hZ : 1 ≤ Z) (k : ℕ) :
    aksPoissonMass Z k ≤ Real.exp 1 * Real.sqrt 2 / Real.sqrt Z := by
  let m := ⌊Z⌋₊
  have hm : 1 ≤ m := (Nat.one_le_floor_iff Z).mpr hZ
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hZ_pos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ_le : Z ≤ 2 * (m : ℝ) := by
    have hlt : Z < (m : ℝ) + 1 := by simpa [m] using Nat.lt_floor_add_one Z
    have hm_one : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hsqrt : Real.sqrt Z ≤ Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    calc
      Real.sqrt Z ≤ Real.sqrt (2 * (m : ℝ)) := Real.sqrt_le_sqrt hZ_le
      _ = Real.sqrt 2 * Real.sqrt (m : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    aksPoissonMass Z k ≤ aksPoissonMass Z m :=
      aksPoissonMass_le_floor (by linarith) k
    _ ≤ Real.exp 1 / Real.sqrt (m : ℝ) := by
      simpa [m] using aksPoissonMass_floor_le_exp_div_sqrt hZ
    _ ≤ Real.exp 1 * Real.sqrt 2 / Real.sqrt Z := by
      rw [le_div_iff₀ (Real.sqrt_pos.2 hZ_pos), div_mul_eq_mul_div,
        div_le_iff₀ (Real.sqrt_pos.2 hm_pos)]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos 1).le

/-- Reciprocal form of the local Poisson estimate, matching the factor in the
AKS hitting lower bound. -/
lemma aksPoissonMass_reciprocal_lower_bound {Z : ℝ} (hZ : 1 ≤ Z) (k : ℕ) :
    Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)) ≤
      1 / (Real.exp Z * aksPoissonMass Z k) := by
  have hmass_pos : 0 < aksPoissonMass Z k :=
    aksPoissonMass_pos (lt_of_lt_of_le zero_lt_one hZ) k
  have hsqrt_pos : 0 < Real.sqrt Z := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hZ)
  have hden : Real.exp Z * aksPoissonMass Z k ≤
      Real.exp Z * (Real.exp 1 * Real.sqrt 2 / Real.sqrt Z) :=
    mul_le_mul_of_nonneg_left
      (aksPoissonMass_le_exp_mul_sqrt_two_div_sqrt hZ k) (Real.exp_pos Z).le
  calc
    Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)) =
        1 / (Real.exp Z * (Real.exp 1 * Real.sqrt 2 / Real.sqrt Z)) := by
      field_simp
    _ ≤ 1 / (Real.exp Z * aksPoissonMass Z k) :=
      one_div_le_one_div_of_le (mul_pos (Real.exp_pos Z) hmass_pos) hden

lemma aksPoissonMass_eq_poissonMeasure_real_singleton {Z : ℝ} (hZ : 0 ≤ Z)
    (k : ℕ) :
    aksPoissonMass Z k =
      (ProbabilityTheory.poissonMeasure (NNReal.mk Z hZ)).real ({k} : Set ℕ) := by
  rw [ProbabilityTheory.poissonMeasure_real_singleton, aksPoissonMass]
  simp

lemma aksPoissonMass_hasSum_one {Z : ℝ} (hZ : 0 ≤ Z) :
    HasSum (fun k : ℕ => aksPoissonMass Z k) 1 := by
  simpa [aksPoissonMass] using
    (ProbabilityTheory.hasSum_one_poissonMeasure (NNReal.mk Z hZ))

lemma aksPoissonMass_tsum_eq_one {Z : ℝ} (hZ : 0 ≤ Z) :
    (∑' k : ℕ, aksPoissonMass Z k) = 1 :=
  (aksPoissonMass_hasSum_one hZ).tsum_eq

lemma aksPoissonMass_probability_mass {Z : ℝ} (hZ : 0 ≤ Z) :
    (∀ k : ℕ, 0 ≤ aksPoissonMass Z k) ∧
      (∑' k : ℕ, aksPoissonMass Z k) = 1 :=
  ⟨aksPoissonMass_nonneg hZ, aksPoissonMass_tsum_eq_one hZ⟩

lemma exp_mul_aksPoissonMass (Z : ℝ) (k : ℕ) :
    Real.exp Z * aksPoissonMass Z k = Z ^ k / (Nat.factorial k : ℝ) := by
  rw [aksPoissonMass, ← mul_div_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul]

lemma aksPoissonMass_reciprocal_factor {Z : ℝ} (hZ : Z ≠ 0) (k : ℕ) :
    (Nat.factorial k : ℝ) / Z ^ k =
      1 / (Real.exp Z * aksPoissonMass Z k) := by
  have hfac : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [exp_mul_aksPoissonMass]
  field_simp [pow_ne_zero k hZ, hfac]

lemma aksPoissonMass_hitting_factor {Z : ℝ} (hZ : Z ≠ 0) (s : ℝ) (n k : ℕ) :
    (1 / Real.rpow (n : ℝ) s) * (Nat.factorial k : ℝ) / Z ^ k =
      (1 / Real.rpow (n : ℝ) s) / (Real.exp Z * aksPoissonMass Z k) := by
  calc
    (1 / Real.rpow (n : ℝ) s) * (Nat.factorial k : ℝ) / Z ^ k =
        (1 / Real.rpow (n : ℝ) s) * ((Nat.factorial k : ℝ) / Z ^ k) := by
      ring
    _ = (1 / Real.rpow (n : ℝ) s) / (Real.exp Z * aksPoissonMass Z k) := by
      rw [aksPoissonMass_reciprocal_factor hZ k]
      ring

/-- The factorial aggregate of the canonical AKS paths is exactly the Poisson
denominator appearing in the paper. -/
lemma aks_canonical_orderings_total_weight_eq_poisson {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y)
    (hZ : aksPartitionFunction x s ≠ 0) :
    (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y s (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x s (p ^ n.factorization p)) =
      (1 / Real.rpow (n : ℝ) s) /
        (Real.exp (aksPartitionFunction x s) *
          aksPoissonMass (aksPartitionFunction x s)
            (aksSmallPrimeSupport x n).card) := by
  rw [aks_canonical_orderings_total_weight hn hny]
  exact aksPoissonMass_hitting_factor (Z := aksPartitionFunction x s) hZ s n
    (aksSmallPrimeSupport x n).card

/-- Quantitative lower bound for the canonical path aggregate, obtained from
the uniform local Poisson estimate. -/
lemma aks_canonical_orderings_total_weight_lower_bound {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y)
    (hZ : 1 ≤ aksPartitionFunction x s) :
    (1 / Real.rpow (n : ℝ) s) *
        (Real.sqrt (aksPartitionFunction x s) /
          (Real.exp (aksPartitionFunction x s) *
            (Real.exp 1 * Real.sqrt 2))) ≤
      (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y s (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x s (p ^ n.factorization p)) := by
  rw [aks_canonical_orderings_total_weight_eq_poisson hn hny (by linarith)]
  apply mul_le_mul_of_nonneg_left _
    (one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s))
  simpa [one_div] using
    aksPoissonMass_reciprocal_lower_bound hZ
      (aksSmallPrimeSupport x n).card

lemma aks_hittingMass_lower_bound {x y s : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hny : (n : ℝ) ≤ y)
    (hZ : 1 ≤ aksPartitionFunction x s) :
    (1 / Real.rpow (n : ℝ) s) *
        (Real.sqrt (aksPartitionFunction x s) /
          (Real.exp (aksPartitionFunction x s) *
            (Real.exp 1 * Real.sqrt 2))) ≤
      aksHittingMass x y s n :=
  (aks_canonical_orderings_total_weight_lower_bound hn hny hZ).trans
    (aks_canonical_orderings_total_weight_le_hittingMass hn)

/-- Unconditional theorem-range form of the AKS canonical-path lower bound. -/
lemma aks_canonical_orderings_total_weight_lower_bound_aksExponent
    {x y : ℝ} {n : ℕ} (hx : 3 ≤ x) (hn : n ≠ 0) (hny : (n : ℝ) ≤ y) :
    (1 / Real.rpow (n : ℝ) (aksExponent x)) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2))) ≤
      (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y (aksExponent x) (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x (aksExponent x) (p ^ n.factorization p)) :=
  aks_canonical_orderings_total_weight_lower_bound hn hny
    (one_lt_aksPartitionFunction_aksExponent hx).le

/-- Pointwise canonical-path estimate in the final TeX scale
`y^(1-s)/n`, valid uniformly on `[y/x,y]`. -/
lemma aks_canonical_orderings_interval_lower_bound
    {x y : ℝ} {n : ℕ} (hx : 3 ≤ x) (hxy : x ≤ y)
    (hn : n ∈ aksInterval x y) :
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) / (n : ℝ)) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2))) ≤
      (Nat.factorial (aksSmallPrimeSupport x n).card : ℝ) *
        (aksInitialMass x y (aksExponent x) (aksRoughPart x n) *
          ∏ p ∈ aksSmallPrimeSupport x n,
            aksStepWeight x (aksExponent x) (p ^ n.factorization p)) := by
  have hn_pos := aksInterval_pos (by linarith : 0 < x) hxy hn
  exact (mul_le_mul_of_nonneg_right (aks_interval_rpow_weight_lower hx hxy hn)
    (by positivity)).trans
      (aks_canonical_orderings_total_weight_lower_bound_aksExponent hx
        (Nat.ne_of_gt (by exact_mod_cast hn_pos : 0 < n)) hn.2)

/-- Pointwise AKS lower bound for the actual hitting mass on `[y/x,y]`. -/
lemma aks_hittingMass_interval_lower_bound
    {x y : ℝ} {n : ℕ} (hx : 3 ≤ x) (hxy : x ≤ y)
    (hn : n ∈ aksInterval x y) :
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) / (n : ℝ)) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2))) ≤
      aksHittingMass x y (aksExponent x) n := by
  have hn_pos := aksInterval_pos (by linarith : 0 < x) hxy hn
  exact (aks_canonical_orderings_interval_lower_bound hx hxy hn).trans
    (aks_canonical_orderings_total_weight_le_hittingMass
      (Nat.ne_of_gt (by exact_mod_cast hn_pos : 0 < n)))

/-- The number `ω_{≤x}(n)` from the AKS LYM remark: prime factors of `n`
counted without multiplicity and restricted to primes at most `x`. -/
noncomputable def aksSmallPrimeFactorCount (x : ℝ) (n : ℕ) : ℕ :=
  (aksSmallPrimeSupport x n).card

lemma aksSmallPrimeFactorCount_eq_card (x : ℝ) (n : ℕ) :
    aksSmallPrimeFactorCount x n = (aksSmallPrimeSupport x n).card :=
  rfl

lemma aksSmallPrimeFactorCount_zero (x : ℝ) :
    aksSmallPrimeFactorCount x 0 = 0 := by
  simp [aksSmallPrimeFactorCount, aksSmallPrimeSupport, Nat.factorization_zero]

lemma aksSmallPrimeFactorCount_one (x : ℝ) :
    aksSmallPrimeFactorCount x 1 = 0 := by
  simp [aksSmallPrimeFactorCount, aksSmallPrimeSupport, Nat.factorization_one]

lemma aksSmallPrimeFactorCount_mono {x y : ℝ} (hxy : x ≤ y) (n : ℕ) :
    aksSmallPrimeFactorCount x n ≤ aksSmallPrimeFactorCount y n := by
  classical
  apply Finset.card_le_card
  intro p hp
  exact mem_aksSmallPrimeSupport.mpr
    ⟨(mem_aksSmallPrimeSupport.mp hp).1,
      (mem_aksSmallPrimeSupport.mp hp).2.trans hxy⟩

lemma aksSmallPrimeFactorCount_le_cardFactors (x : ℝ) (n : ℕ) :
    aksSmallPrimeFactorCount x n ≤ ArithmeticFunction.cardFactors n := by
  classical
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [aksSmallPrimeFactorCount, Finset.card_eq_sum_ones]
  calc
    (∑ p ∈ aksSmallPrimeSupport x n, 1) ≤
        ∑ p ∈ aksSmallPrimeSupport x n, n.factorization p := by
      exact Finset.sum_le_sum fun p hp => by
        have := Finsupp.mem_support_iff.mp
          (mem_aksSmallPrimeSupport.mp hp).1
        omega
    _ ≤ ∑ p ∈ n.factorization.support, n.factorization p :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma aksSmallPrimeFactorCount_eq_support_card_of_forall_le {x : ℝ} {n : ℕ}
    (hsmall : ∀ p : ℕ, p ∈ n.factorization.support -> (p : ℝ) ≤ x) :
    aksSmallPrimeFactorCount x n = n.factorization.support.card := by
  classical
  rw [aksSmallPrimeFactorCount, aksSmallPrimeSupport]
  rw [Finset.filter_eq_self.mpr hsmall]

lemma aksSmallPrimeFactorCount_eq_zero_of_forall_lt {x : ℝ} {n : ℕ}
    (hlarge : ∀ p : ℕ, p ∈ n.factorization.support -> x < (p : ℝ)) :
    aksSmallPrimeFactorCount x n = 0 := by
  classical
  rw [aksSmallPrimeFactorCount, Finset.card_eq_zero, aksSmallPrimeSupport,
    Finset.filter_eq_empty_iff]
  exact fun p hp => not_le_of_gt (hlarge p hp)

/-- The LYM summand in Remark `lym-rem`, with `Z` left as the Poisson rate. -/
noncomputable def aksLYMWeight (x Z : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * aksPoissonMass Z (aksSmallPrimeFactorCount x n))

lemma aksLYMWeight_nonneg {Z : ℝ} (hZ : 0 ≤ Z) (x : ℝ) (n : ℕ) :
    0 ≤ aksLYMWeight x Z n := by
  rw [aksLYMWeight]
  exact one_div_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg n)
      (aksPoissonMass_nonneg hZ (aksSmallPrimeFactorCount x n)))

lemma aksLYMWeight_pos {Z : ℝ} (hZ : 0 < Z) (x : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < aksLYMWeight x Z n := by
  rw [aksLYMWeight]
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  exact one_div_pos.mpr
    (mul_pos hn_pos (aksPoissonMass_pos hZ (aksSmallPrimeFactorCount x n)))

lemma aksLYMWeight_eq_poissonMeasure {x Z : ℝ} (hZ : 0 ≤ Z) (n : ℕ) :
    aksLYMWeight x Z n =
      1 / ((n : ℝ) *
        (ProbabilityTheory.poissonMeasure (NNReal.mk Z hZ)).real
          ({aksSmallPrimeFactorCount x n} : Set ℕ)) := by
  rw [aksLYMWeight, aksPoissonMass_eq_poissonMeasure_real_singleton hZ]

/-- The interval-restricted LYM sum from the AKS remark. -/
noncomputable def aksLYMSum (A : Set ℕ) (x y Z : ℝ) : ℝ :=
  ∑' n : ℕ, (A ∩ aksInterval x y).indicator (aksLYMWeight x Z) n

lemma aksLYMSum_empty (x y Z : ℝ) :
    aksLYMSum (∅ : Set ℕ) x y Z = 0 := by
  simp [aksLYMSum]

/-!
## The shifted von Mangoldt tail estimate

TeX Lemma `lem:mangoldt-tail-and-B`(iii), equation `\eqref{sharp-2}`:
`∑_q Λ(q) / (q log(mq) log(2mq)) ≤ 1 / log(2m)` for all `m ≥ 1`.
-/

/-- The Laplace representation `∫₀^∞ a^{-t} dt = 1/log a` for `a > 1`
(TeX equation `\eqref{log-1}`). -/
lemma laplace_reciprocal_log {a : ℝ} (ha : 1 < a) :
    ∫ t : ℝ in Set.Ioi 0, Real.rpow a (-t) = 1 / Real.log a := by
  convert integral_exp_neg_mul_rpow zero_lt_one (Real.log_pos ha) using 1 <;>
    norm_num [Real.rpow_def_of_pos (zero_lt_one.trans ha)]
  rw [Real.rpow_neg_one]

/-- Integrability of `a^{-t}` on `(0, ∞)` for `a > 1`. -/
lemma laplace_reciprocal_log_integrable {a : ℝ} (ha : 1 < a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.rpow a (-t)) (Set.Ioi 0) := by
  norm_num [Real.rpow_def_of_pos (zero_lt_one.trans ha)]
  convert (exp_neg_integrableOn_Ioi 0 (Real.log_pos ha)) using 1
  ext
  ring_nf

set_option maxHeartbeats 800000 in
-- The finite Fubini expansion and pointwise integral comparison need additional elaboration time.
/-- The finite-range shifted von Mangoldt tail bound for `n ≥ 2`:
`∑_{q < N, q ≥ 2} Λ(q)/(q log(nq) log(2nq)) ≤ 1/log(2n)`. -/
lemma mangoldt_shifted_tail_range_bound (n N : ℕ) (hn : 2 ≤ n) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 n q else 0) ≤
      1 / Real.log (((2 * n : ℕ) : ℝ)) := by
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini :
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 n q else 0) =
        ∫ t in Set.Ioi 0,
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))
            else 0) / Real.log (2 : ℝ) := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_finsetSum]
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro q hq
      split_ifs with hq_ge
      · have hq_nat : 2 ≤ q := by exact_mod_cast hq_ge
        have hn_ne : n ≠ 0 := by omega
        have hq_ne : q ≠ 0 := by omega
        have hnq_nat : 1 < n * q := by
          exact (show 1 < n by omega).trans_le
            (Nat.le_mul_of_pos_right n (by omega))
        have h2nq_nat : 1 < 2 * n * q := by
          calc
            1 < n * q := hnq_nat
            _ ≤ 2 * n * q := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using
                Nat.le_mul_of_pos_right (n * q) (by norm_num : 0 < 2)
        simp only [Real.rpow_eq_pow]
      -- Evaluate the integral $\int_{0}^{\infty} (nq)^{-t} (1 - 2^{-t}) \, dt$.
        have h_integral :
            ∫ t in Set.Ioi 0,
                (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) =
              1 / Real.log (n * q) - 1 / Real.log (2 * n * q) := by
          have h_integral :
              ∫ t in Set.Ioi 0,
                  (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) =
                (∫ t in Set.Ioi 0, Real.rpow (n * q) (-t)) -
                  ∫ t in Set.Ioi 0, Real.rpow (2 * n * q) (-t) := by
            rw [← MeasureTheory.integral_sub]
            · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro t _ht
              norm_num [Real.rpow_neg, Real.mul_rpow, hn_ne, hq_ne]
              ring_nf
            · have hbase : 1 < (n * q : ℝ) := by
                exact_mod_cast hnq_nat
              exact laplace_reciprocal_log_integrable hbase
            · exact laplace_reciprocal_log_integrable
                (by exact_mod_cast h2nq_nat)
          rw [h_integral, laplace_reciprocal_log (by exact_mod_cast hnq_nat),
            laplace_reciprocal_log (by exact_mod_cast h2nq_nat)]
        have h_scaled :
            ∫ t in Set.Ioi 0,
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) =
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                (1 / Real.log (n * q) - 1 / Real.log (2 * n * q)) := by
          calc
            (∫ t in Set.Ioi 0,
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))) =
                ∫ t in Set.Ioi 0,
                  (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                    ((n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro t _
              ring
            _ = (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                ∫ t in Set.Ioi 0,
                  (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) := by
              rw [MeasureTheory.integral_const_mul]
            _ = _ := by rw [h_integral]
        have h_scaled_pow :
            ∫ t : ℝ in Set.Ioi 0,
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (n * q : ℝ) ^ (-t) * (1 - (2 : ℝ) ^ (-t)) =
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                (1 / Real.log (n * q) - 1 / Real.log (2 * n * q)) := by
          simpa only [Real.rpow_eq_pow] using h_scaled
        rw [h_scaled_pow, mangoldt_shifted_tail_term]
        norm_num [Nat.cast_mul]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        have hlogn : 0 < Real.log (n : ℝ) :=
          Real.log_pos (by norm_cast)
        have hlogq : 0 < Real.log (q : ℝ) :=
          Real.log_pos (by norm_cast)
        have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
        field_simp [hlogn.ne', hlogq.ne', hlog2.ne',
          (add_pos hlogn hlogq).ne',
          (add_pos hlog2 (add_pos hlogn hlogq)).ne']
        ring_nf
      · norm_num
    · intro i hi
      split_ifs
      · norm_num
        refine MeasureTheory.Integrable.mono'
          (g := fun t =>
            (ArithmeticFunction.vonMangoldt i / i) * (n * i : ℝ) ^ (-t) * 1)
          ?_ ?_ ?_
        · norm_num [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ) * i)]
          have h_exp := exp_neg_integrableOn_Ioi 0
            (show 0 < Real.log (n * i) by
              exact Real.log_pos (by norm_cast at *; nlinarith))
          simpa only [neg_mul] using h_exp.const_mul _
        · exact Measurable.aestronglyMeasurable (by
            exact Measurable.mul
              (Measurable.mul measurable_const
                (Measurable.pow measurable_const measurable_id'.neg))
              (Measurable.sub measurable_const
                (Measurable.pow measurable_const measurable_id'.neg)))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
          have hterm_nonneg :
              0 ≤ (ArithmeticFunction.vonMangoldt i / (i : ℝ)) *
                (n * i : ℝ) ^ (-t) := by
            exact mul_nonneg
              (div_nonneg (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
                (Nat.cast_nonneg _))
              (Real.rpow_nonneg (by positivity) _)
          have hfactor_nonneg : 0 ≤ 1 - Real.rpow 2 (-t) := by
            exact sub_nonneg.2 <| le_trans
              (Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (neg_nonpos.2 ht.out.le))
              (by norm_num)
          calc
            ‖(ArithmeticFunction.vonMangoldt i / (i : ℝ)) *
                (n * i : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))‖ =
                (ArithmeticFunction.vonMangoldt i / (i : ℝ)) *
                  (n * i : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) :=
              Real.norm_of_nonneg (mul_nonneg hterm_nonneg hfactor_nonneg)
            _ ≤ (ArithmeticFunction.vonMangoldt i / (i : ℝ)) *
                (n * i : ℝ) ^ (-t) * 1 :=
              mul_le_mul_of_nonneg_left
                (sub_le_self _ (Real.rpow_nonneg (by norm_num) _))
                hterm_nonneg
      · norm_num
  -- By the geometric bound, we have:
  have h_geometric_bound :
      ∀ t > 0,
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))
          else 0) ≤
          (Real.log 2 / (Real.rpow 2 t - 1)) *
            (n : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) := by
    intros t ht
    have h_geometric_bound :
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) * (q : ℝ) ^ (-t)
          else 0) ≤ Real.log 2 / (Real.rpow 2 t - 1) := by
      calc
        (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) * (q : ℝ) ^ (-t)
            else 0) =
            ∑ q ∈ Finset.range N,
              if (2 : ℝ) ≤ (q : ℝ) then
                ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
              else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs with hq
          · have hq_pos : 0 < (q : ℝ) := by linarith
            change ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                Real.rpow (q : ℝ) (-t) =
              ArithmeticFunction.vonMangoldt q /
                Real.rpow (q : ℝ) (1 + t)
            simp only [Real.rpow_eq_pow]
            have hpow :
                (q : ℝ) ^ (1 + t) =
                  (q : ℝ) * (q : ℝ) ^ t := by
              simpa only [Real.rpow_one] using
                Real.rpow_add hq_pos 1 t
            have hneg :
                (q : ℝ) ^ (-t) = ((q : ℝ) ^ t)⁻¹ :=
              Real.rpow_neg hq_pos.le t
            rw [hpow, hneg]
            simp only [div_eq_mul_inv, mul_inv, mul_assoc]
          · rfl
        _ ≤ Real.log 2 / (Real.rpow 2 t - 1) :=
          mangoldt_dirichlet_series_finite_threshold_geometric_bound_local t ht N
    have hfactor :
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))
          else 0) =
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) * (q : ℝ) ^ (-t)
            else 0) *
            (n : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t)) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : (2 : ℝ) ≤ (q : ℝ)
      · rw [if_pos hq, if_pos hq, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg q)]
        ring_nf
      · rw [if_neg hq, if_neg hq, zero_mul, zero_mul]
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h_geometric_bound
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-t)))
      (sub_nonneg.mpr
        (by simpa using
          Real.rpow_le_rpow_of_exponent_le one_le_two (neg_nonpos.mpr ht.le)))
  -- By combining the results from Fubini's theorem and the geometric bound, we get:
  have h_combined :
      (∫ t in Set.Ioi 0,
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (n * q : ℝ) ^ (-t) * (1 - Real.rpow 2 (-t))
          else 0) / Real.log (2 : ℝ)) ≤
        ∫ t in Set.Ioi 0, (n : ℝ) ^ (-t) * Real.rpow 2 (-t) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      refine div_nonneg (Finset.sum_nonneg fun q hq => ?_)
        (Real.log_nonneg one_le_two)
      split_ifs
      · exact mul_nonneg
          (mul_nonneg
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
            (Real.rpow_nonneg (by positivity) _))
          (sub_nonneg.2 (by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (neg_nonpos.2 ht.out.le)))
      · norm_num
    · have h_integrable :
          MeasureTheory.IntegrableOn
            (fun t : ℝ => (n * 2 : ℝ) ^ (-t)) (Set.Ioi 0) := by
        exact laplace_reciprocal_log_integrable
          (show 1 < (n * 2 : ℝ) by norm_cast; linarith)
      refine h_integrable.congr_fun ?_ measurableSet_Ioi
      intro t _ht
      change Real.rpow ((n : ℝ) * 2) (-t) =
        Real.rpow (n : ℝ) (-t) * Real.rpow 2 (-t)
      exact Real.mul_rpow (Nat.cast_nonneg n) zero_le_two
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      refine (h_geometric_bound t ht).trans_eq ?_
      have hpow : 1 < Real.rpow 2 t := by
        simpa using Real.rpow_lt_rpow_of_exponent_lt one_lt_two ht.out
      have hrpow_ne : Real.rpow 2 t ≠ 0 :=
        (Real.rpow_pos_of_pos zero_lt_two t).ne'
      have hcancel :
          1 - (Real.rpow 2 t)⁻¹ =
            (Real.rpow 2 t)⁻¹ * (Real.rpow 2 t - 1) := by
        field_simp [hrpow_ne]
      have hneg : Real.rpow 2 (-t) = (Real.rpow 2 t)⁻¹ :=
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) t
      rw [hneg, hcancel]
      field_simp [sub_ne_zero.mpr hpow.ne']
      exact div_self (sub_ne_zero.mpr hpow.ne')
  -- Evaluate the remaining integral.
  have h_remaining_integral :
      ∫ t in Set.Ioi 0, (n : ℝ) ^ (-t) * Real.rpow 2 (-t) =
        1 / Real.log (2 * n) := by
    simpa [Nat.cast_mul, mul_comm, Real.mul_rpow (Nat.cast_nonneg n) zero_le_two] using
      (laplace_reciprocal_log (show 1 < (2 * n : ℝ) by norm_cast; linarith))
  grind +revert

set_option maxHeartbeats 800000 in
-- The endpoint case expands a finite sum of improper integrals.
/-- The finite-range shifted von Mangoldt tail bound for `m = 1`:
`∑_{q < N, q ≥ 2} Λ(q)/(q log q log(2q)) ≤ 1/log 2` for `N ≥ 2`. -/
lemma mangoldt_shifted_tail_range_bound_one (N : ℕ) (_hN : 2 ≤ N) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 1 q else 0) ≤
      1 / Real.log 2 := by
  have h_integral_bound :
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 1 q else 0) ≤
        (1 / Real.log 2) *
          ∫ t in Set.Ioi 0,
            (∑ q ∈ Finset.range N,
              if (2 : ℝ) ≤ (q : ℝ) then
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  Real.rpow (q : ℝ) (-t)
              else 0) * (1 - Real.rpow 2 (-t)) := by
    have h_integral_bound :
        ∀ q ∈ Finset.range N,
          (if (2 : ℝ) ≤ (q : ℝ) then
            mangoldt_shifted_tail_term 2 1 q
          else 0) ≤
            (1 / Real.log 2) *
              ∫ t in Set.Ioi 0,
                (if (2 : ℝ) ≤ (q : ℝ) then
                  ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                    Real.rpow (q : ℝ) (-t)
                else 0) * (1 - Real.rpow 2 (-t)) := by
      intro q hq
      by_cases hq_ge_2 : (2 : ℝ) ≤ (q : ℝ)
      · have hq_nat : 2 ≤ q := by exact_mod_cast hq_ge_2
        have hq_ne : q ≠ 0 := by omega
        have hq_base : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
        have h2q_nat : 1 < 2 * q := by omega
        have h_integral_bound :
            ∫ t in Set.Ioi 0,
                Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t)) =
              1 / Real.log (q : ℝ) - 1 / Real.log ((2 * q : ℕ) : ℝ) := by
          have hsub :
              ∫ t in Set.Ioi 0,
                  Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t)) =
                (∫ t in Set.Ioi 0, Real.rpow (q : ℝ) (-t)) -
                  ∫ t in Set.Ioi 0, Real.rpow (2 * q : ℝ) (-t) := by
            rw [← MeasureTheory.integral_sub]
            · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro t _
              norm_num [Real.mul_rpow, Real.rpow_neg, hq_ne]
              ring_nf
            · exact laplace_reciprocal_log_integrable hq_base
            · exact laplace_reciprocal_log_integrable
                (by exact_mod_cast h2q_nat)
          rw [hsub, laplace_reciprocal_log hq_base,
            laplace_reciprocal_log (by exact_mod_cast h2q_nat)]
          norm_num [Nat.cast_mul]
        have h_scaled :
            ∫ t in Set.Ioi 0,
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t)) =
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                (1 / Real.log (q : ℝ) -
                  1 / Real.log ((2 * q : ℕ) : ℝ)) := by
          calc
            (∫ t in Set.Ioi 0,
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t))) =
                ∫ t in Set.Ioi 0,
                  (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                    (Real.rpow (q : ℝ) (-t) *
                      (1 - Real.rpow 2 (-t))) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro t _
              ring
            _ = (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                ∫ t in Set.Ioi 0,
                  Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t)) := by
              rw [MeasureTheory.integral_const_mul]
            _ = _ := by rw [h_integral_bound]
        simp only [if_pos hq_ge_2]
        rw [h_scaled, mangoldt_shifted_tail_term]
        norm_num [Nat.cast_mul]
        rw [Real.log_mul (by positivity) (by positivity)]
        have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq_base
        have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
        field_simp [hq_ne, hlogq.ne', hlog2.ne',
          (add_pos hlog2 hlogq).ne']
        ring_nf
        exact le_rfl
      · norm_num [hq_ge_2]
    refine le_trans (Finset.sum_le_sum h_integral_bound) ?_
    rw [← Finset.mul_sum, ← MeasureTheory.integral_finsetSum]
    · norm_num [Finset.sum_mul]
    · intro q hq
      split_ifs with hq_ge_2
      · norm_num
        refine MeasureTheory.Integrable.mono'
          (g := fun t => ArithmeticFunction.vonMangoldt q / q * q ^ (-t))
          ?_ ?_ ?_
        · norm_num [Real.rpow_def_of_pos (by positivity : 0 < (q : ℝ))]
          have h_exp := exp_neg_integrableOn_Ioi 0
            (show 0 < Real.log q by
              exact Real.log_pos (by norm_cast at *))
          simpa only [neg_mul] using h_exp.const_mul _
        · fun_prop
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
          have hterm_nonneg :
              0 ≤ ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                Real.rpow (q : ℝ) (-t) := by
            exact mul_nonneg
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          have hfactor_nonneg : 0 ≤ 1 - Real.rpow 2 (-t) := by
            exact sub_nonneg.2 <| le_trans
              (Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (neg_nonpos.2 ht.out.le))
              (by norm_num)
          calc
            ‖ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t))‖ =
                ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                  Real.rpow (q : ℝ) (-t) * (1 - Real.rpow 2 (-t)) :=
              Real.norm_of_nonneg (mul_nonneg hterm_nonneg hfactor_nonneg)
            _ ≤ ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                Real.rpow (q : ℝ) (-t) :=
              mul_le_of_le_one_right hterm_nonneg
                (sub_le_self _ (Real.rpow_nonneg (by norm_num) _))
      · norm_num
  -- Apply the geometric Dirichlet bound to the integrand.
  have h_geometric_bound :
      ∀ t > 0,
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              Real.rpow (q : ℝ) (-t)
          else 0) * (1 - Real.rpow 2 (-t)) ≤
            Real.log 2 * Real.rpow 2 (-t) := by
    intro t ht
    have h_geometric_bound :
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              Real.rpow (q : ℝ) (-t)
          else 0) ≤ Real.log 2 / (Real.rpow 2 t - 1) := by
      calc
        (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                Real.rpow (q : ℝ) (-t)
            else 0) =
            ∑ q ∈ Finset.range N,
              if (2 : ℝ) ≤ (q : ℝ) then
                ArithmeticFunction.vonMangoldt q /
                  Real.rpow (q : ℝ) (1 + t)
              else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs with hq
          · have hq_pos : 0 < (q : ℝ) := by linarith
            change ArithmeticFunction.vonMangoldt q / (q : ℝ) *
                Real.rpow (q : ℝ) (-t) =
              ArithmeticFunction.vonMangoldt q /
                Real.rpow (q : ℝ) (1 + t)
            simp only [Real.rpow_eq_pow]
            have hpow :
                (q : ℝ) ^ (1 + t) = (q : ℝ) * (q : ℝ) ^ t := by
              simpa only [Real.rpow_one] using
                Real.rpow_add hq_pos 1 t
            have hneg :
                (q : ℝ) ^ (-t) = ((q : ℝ) ^ t)⁻¹ :=
              Real.rpow_neg hq_pos.le t
            rw [hpow, hneg]
            simp only [div_eq_mul_inv, mul_inv, mul_assoc]
          · rfl
        _ ≤ Real.log 2 / (Real.rpow 2 t - 1) :=
          mangoldt_dirichlet_series_finite_threshold_geometric_bound_local t ht N
    refine le_trans
      (mul_le_mul_of_nonneg_right h_geometric_bound (sub_nonneg.mpr ?_)) ?_
    · exact le_trans
        (Real.rpow_le_rpow_of_exponent_le one_le_two (neg_nonpos.mpr ht.le))
        (by norm_num)
    · norm_num [Real.rpow_neg] at *
      field_simp
      exact div_self_le_one _
  -- Apply the geometric bound to the integral.
  have h_integral_bound' :
      (∫ t in Set.Ioi 0,
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              Real.rpow (q : ℝ) (-t)
          else 0) * (1 - Real.rpow 2 (-t))) ≤
        ∫ t in Set.Ioi 0, Real.log 2 * Real.rpow 2 (-t) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      refine mul_nonneg ?_ ?_
      · exact Finset.sum_nonneg fun q hq => by
          split_ifs
          · exact mul_nonneg
              (div_nonneg
                (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
                (Nat.cast_nonneg _))
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          · positivity
      · exact sub_nonneg.2 <| le_trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (neg_nonpos.mpr ht.out.le))
          (by norm_num)
    · norm_num [Real.rpow_def_of_pos]
      have h_integrable :=
        (exp_neg_integrableOn_Ioi 0 (Real.log_pos one_lt_two)).integrable
      simpa [mul_comm] using h_integrable.const_mul (Real.log 2)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact h_geometric_bound t ht
  -- Evaluate the integral $\int_{0}^{\infty} 2^{-t} \, dt$.
  have h_integral_eval :
      ∫ t in Set.Ioi 0, Real.rpow 2 (-t) = 1 / Real.log 2 :=
    laplace_reciprocal_log one_lt_two
  calc
    _ ≤ (1 / Real.log 2) *
        ∫ t in Set.Ioi 0,
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                Real.rpow (q : ℝ) (-t)
            else 0) * (1 - Real.rpow 2 (-t)) :=
      h_integral_bound
    _ ≤ (1 / Real.log 2) *
        ∫ t in Set.Ioi 0, Real.log 2 * Real.rpow 2 (-t) :=
      mul_le_mul_of_nonneg_left h_integral_bound' (by positivity)
    _ = 1 / Real.log 2 := by
      rw [MeasureTheory.integral_const_mul, h_integral_eval]
      field_simp [ne_of_gt (Real.log_pos one_lt_two)]

/-- The summands of the shifted tail are nonnegative. -/
lemma mangoldt_shifted_tail_if_nonneg {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    0 ≤ if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0 := by
  split_ifs with h
  · exact mangoldt_two_shifted_tail_term_nonneg_of_one_le_of_two_le hm (by exact_mod_cast h)
  · exact le_rfl

/-- The finite-range shifted tail bound for `m = 1`, with the smallness
hypothesis on the range removed. -/
lemma mangoldt_shifted_tail_range_bound_one' (N : ℕ) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 1 q else 0) ≤
      1 / Real.log 2 := by
  rcases le_or_gt 2 N with hN | hN
  · exact mangoldt_shifted_tail_range_bound_one N hN
  · calc
      (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 1 q else 0) ≤
          ∑ q ∈ Finset.range 2,
            if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 1 q else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN.le)
          (fun q _ _ => mangoldt_shifted_tail_if_nonneg le_rfl q)
      _ ≤ 1 / Real.log 2 := mangoldt_shifted_tail_range_bound_one 2 le_rfl

/-- The unified finite-range shifted tail bound, for all `m ≥ 1`. -/
lemma mangoldt_shifted_tail_range_bound_all (m N : ℕ) (hm : 1 ≤ m) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0) ≤
      1 / Real.log (((2 * m : ℕ) : ℝ)) := by
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · rw [← hm1]
    simpa using mangoldt_shifted_tail_range_bound_one' N
  · exact mangoldt_shifted_tail_range_bound m N hm2

/-- The shifted tail series is summable for every `m ≥ 1`. -/
lemma mangoldt_two_shifted_tail_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0) :=
  summable_of_sum_range_le (mangoldt_shifted_tail_if_nonneg hm)
    (fun N => mangoldt_shifted_tail_range_bound_all m N hm)

/-- TeX Lemma `lem:mangoldt-tail-and-B`(iii), equation `\eqref{sharp-2}`:
the full shifted von Mangoldt tail bound for `m ≥ 1`. -/
lemma mangoldt_shifted_tail_tsum_bound (m : ℕ) (hm : 1 ≤ m) :
    (∑' q : ℕ,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0) ≤
      1 / Real.log (((2 * m : ℕ) : ℝ)) :=
  (mangoldt_two_shifted_tail_summable m hm).tsum_le_of_sum_range_le
    (fun N => mangoldt_shifted_tail_range_bound_all m N hm)

/-- Paper equation `\eqref{sharp-2}` phrased with the shifted tail-sum
vocabulary. -/
lemma lemma_mangoldt_tail_shifted_sharp (m : ℕ) (hm : 1 ≤ m) :
    mangoldt_two_shifted_tail_sum m 2 ≤ 1 / Real.log (((2 * m : ℕ) : ℝ)) :=
  mangoldt_shifted_tail_tsum_bound m hm

/-!
## Sub-invariance of the rescaled weight `ν₂`

TeX Section `2-strong-sec`: the weight `ν₂(n) = 1/(n log(2n))` is sub-invariant
for the von Mangoldt downward chain, by Lemma `lem:mangoldt-tail-and-B`(iii).
-/

/-- Sub-invariance of `ν₂` for the von Mangoldt downward chain
(real-threshold form): `∑_{q ≥ 2} ν₂(mq) Λ(q) / log(mq) ≤ ν₂(m)`. -/
lemma erdos_two_shift_subinvariant (m : ℕ) (hm : 1 ≤ m) :
    (∑' q : ℕ, if (2 : ℝ) ≤ (q : ℝ) then
      erdos_two_shift_weight (m * q) * ArithmeticFunction.vonMangoldt q /
        Real.log (((m * q : ℕ) : ℝ)) else 0) ≤
      erdos_two_shift_weight m := by
  calc
    (∑' q : ℕ, if (2 : ℝ) ≤ (q : ℝ) then
        erdos_two_shift_weight (m * q) * ArithmeticFunction.vonMangoldt q /
          Real.log (((m * q : ℕ) : ℝ)) else 0)
        = ∑' q : ℕ, (1 / (m : ℝ)) *
            (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0) := by
          refine tsum_congr fun q => ?_
          by_cases hq : (2 : ℝ) ≤ (q : ℝ)
          · rw [if_pos hq, if_pos hq]
            exact erdos_two_shift_weight_mul_vonMangoldt_div_log_eq_scaled_shifted_tail
              (lt_of_lt_of_le one_lt_two
                (le_trans (by exact_mod_cast hq) (Nat.le_mul_of_pos_left q hm)))
          · rw [if_neg hq, if_neg hq, mul_zero]
    _ = (1 / (m : ℝ)) * ∑' q : ℕ,
          (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_shifted_tail_term 2 m q else 0) :=
        tsum_mul_left
    _ ≤ (1 / (m : ℝ)) * (1 / Real.log (((2 * m : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mangoldt_shifted_tail_tsum_bound m hm)
          (by positivity)
    _ = erdos_two_shift_weight m := by
        rw [erdos_two_shift_weight, erdos_shift_weight, div_mul_div_comm, one_mul]

/-- The summands in the `ν₂` sub-invariance sum are nonnegative. -/
lemma nu2_subinvariant_term_nonneg (n : ℕ) (hn : 1 ≤ n) (q : ℕ) :
    0 ≤ (if 1 < q then
      erdos_two_shift_weight (n * q) * ArithmeticFunction.vonMangoldt q /
        Real.log (((n * q : ℕ) : ℝ)) else 0) := by
  split_ifs with hq
  · refine div_nonneg (mul_nonneg (erdos_two_shift_weight_nonneg_of_pos
      (Nat.mul_pos hn (by omega))) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.log_nonneg ?_)
    exact_mod_cast Nat.mul_pos hn (by omega : 0 < q)
  · exact le_rfl

/-- The `ν₂` sub-invariance series is summable. -/
lemma nu2_subinvariant_summable (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => if 1 < q then
      erdos_two_shift_weight (n * q) * ArithmeticFunction.vonMangoldt q /
        Real.log (((n * q : ℕ) : ℝ)) else 0) := by
  refine ((mangoldt_two_shifted_tail_summable n hn).mul_left (1 / (n : ℝ))).congr
    fun q => ?_
  by_cases hq : 1 < q
  · rw [if_pos hq, if_pos (by exact_mod_cast (by omega : 2 ≤ q) : (2 : ℝ) ≤ (q : ℝ))]
    exact (erdos_two_shift_weight_mul_vonMangoldt_div_log_eq_scaled_shifted_tail
      (lt_of_lt_of_le one_lt_two
        (le_trans (by omega) (Nat.le_mul_of_pos_left q hn)))).symm
  · rw [if_neg hq, if_neg (by push Not; exact_mod_cast (by omega : q < 2)), mul_zero]

/-- Sub-invariance of `ν₂` for the von Mangoldt downward chain
(natural-threshold form), TeX inequality `\eqref{sub}` for the weight `ν₂`. -/
lemma nu2_subinvariant_tsum (n : ℕ) (hn : 1 ≤ n) :
    (∑' q : ℕ, if 1 < q then
      erdos_two_shift_weight (n * q) * ArithmeticFunction.vonMangoldt q /
        Real.log (((n * q : ℕ) : ℝ)) else 0) ≤
      erdos_two_shift_weight n := by
  refine le_trans (le_of_eq (tsum_congr fun q => ?_)) (erdos_two_shift_subinvariant n hn)
  refine if_congr ?_ rfl rfl
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.cast_le]
  omega

/-!
## An abstract weighted-antichain inequality for adjoint (upward) Markov chains

This isolates the purely combinatorial core of the adjoint-chain argument used
to bound Erdős sums of primitive sets: TeX inequality `\eqref{psum-weight-upper}`
combined with the recursion `\eqref{h-recurse-upper}`, abstracting the absorbing
layer `L`, the weight `w`, the hitting mass `h` and the floor `lo` of the state
space.
-/

/-- Adjoint-kernel package: a nonnegative kernel `U` on `Option ℕ` whose rows over
states `≥ lo` are sub-stochastic. -/
structure GenAdjPkg (U : Option ℕ → Option ℕ → ℝ) (lo : ℕ) : Prop where
  nonneg : ∀ a b : Option ℕ, 0 ≤ U a b
  finite_row : ∀ n : ℕ, lo ≤ n → ∀ s : Finset ℕ,
    (∑ m ∈ s, if lo ≤ m then U (some n) (some m) else 0) ≤ 1

/-- Hitting-mass package: a nonnegative weight `h` equal to `w`, vanishing below the
floor `lo`, satisfying the upward recurrence (TeX `\eqref{h-recurse-upper}` and
`\eqref{nu-recurse}`) with boundary on the absorbing layer `L`, and summable on `L`. -/
structure GenHitting (U : Option ℕ → Option ℕ → ℝ) (h w : ℕ → ℝ)
    (L : Set ℕ) (lo : ℕ) : Prop where
  nonneg : ∀ n : ℕ, 0 ≤ h n
  recurrence : ∀ n : ℕ, lo ≤ n ->
    h n =
      L.indicator h n +
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0)
  equals_w : ∀ n : ℕ, h n = w n
  small_zero : ∀ n : ℕ, ¬ lo ≤ n -> h n = 0
  L_summable : Summable (fun n : ℕ => L.indicator h n)

/-- Source-term version of `GenHitting`, appropriate for upward walks begun
from a general summable initial mass `b`. -/
structure GenSourceHitting (U : Option ℕ → Option ℕ → ℝ)
    (h b : ℕ → ℝ) (lo : ℕ) : Prop where
  nonneg : ∀ n : ℕ, 0 ≤ h n
  recurrence : ∀ n : ℕ, lo ≤ n ->
    h n = b n +
      ∑' q : ℕ,
        if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
          h (n / q) * U (some (n / q)) (some n)
        else 0
  small_zero : ∀ n : ℕ, ¬ lo ≤ n -> h n = 0
  source_nonneg : ∀ n : ℕ, 0 ≤ b n
  source_summable : Summable b

set_option maxHeartbeats 1600000 in
-- The finite divisor closure argument generates a large elaboration term.
/-- The abstract weighted-antichain inequality, TeX `\eqref{psum-weight-upper}`:
if `U` is the adjoint kernel of a downward chain with sub-stochastic rows and `h`
is a hitting mass with boundary data on `L`, then `∑_{n ∈ A} h n ≤ ∑_{n ∈ L} h n`
for every primitive set `A`. -/
lemma gen_adjoint_antichain_bound {U : Option ℕ → Option ℕ → ℝ}
    {h w : ℕ → ℝ} {L : Set ℕ} {lo : ℕ} (hlo : 1 ≤ lo)
    (hU : GenAdjPkg U lo) (hh : GenHitting U h w L lo) :
    ∀ A : Set ℕ, primitive_set A ->
      (∀ s : Finset ℕ,
        (∑ n ∈ s, A.indicator h n) ≤
          ∑' n : ℕ, L.indicator h n) ∧
      Summable (fun n : ℕ => A.indicator h n) ∧
        (∑' n : ℕ, A.indicator h n) ≤
          ∑' n : ℕ, L.indicator h n := by
  classical
  have hfinite : ∀ A : Set ℕ, primitive_set A -> ∀ s : Finset ℕ,
      (∑ n ∈ s, A.indicator h n) ≤
        ∑' n : ℕ, L.indicator h n := by
    intro A hA s
    obtain ⟨hU_nonneg, hU_row_fin⟩ := hU
    obtain ⟨hh_nonneg, hh_rec, hh_eq, hh_small, hh_Lsumm⟩ := hh
    let T : Finset ℕ := s.filter (fun n => n ∈ A ∧ lo ≤ n)
    let D : Finset ℕ := T.biUnion (fun a => a.divisors.filter (fun d => lo ≤ d))
    let N : Finset ℕ := D.filter (fun n => n ∉ T)
    have hD_lo : ∀ n : ℕ, n ∈ D -> lo ≤ n := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      exact (Finset.mem_filter.mp hn).2
    have hT_subset_D : T ⊆ D := by
      intro n hnT
      have hnT' : n ∈ s ∧ n ∈ A ∧ lo ≤ n := by
        simpa [T] using hnT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨n, hnT, ?_⟩
      have hn_ne : n ≠ 0 := by
        have := hnT'.2.2; omega
      simp [hnT'.2.2, hn_ne]
    have hD_dvd_active : ∀ n : ℕ, n ∈ D -> ∃ a : ℕ, a ∈ T ∧ n ∣ a := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      have hn' := Finset.mem_filter.mp hn
      exact ⟨a, haT, (Nat.mem_divisors.mp hn'.1).1⟩
    have hD_pred : ∀ {n p : ℕ}, n ∈ D -> p ∣ n -> lo ≤ p -> p ∈ D := by
      intro n p hnD hpn hp_lo
      rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
      have hpa : p ∣ a := dvd_trans hpn hna
      have haT' : a ∈ s ∧ a ∈ A ∧ lo ≤ a := by
        simpa [T] using haT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨a, haT, ?_⟩
      have ha_ne : a ≠ 0 := by
        have := haT'.2.2; omega
      simp [hp_lo, Nat.mem_divisors.mpr ⟨hpa, ha_ne⟩]
    have hleft_eq : (∑ n ∈ s, A.indicator h n) = ∑ n ∈ T, h n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnA : n ∈ A
      · by_cases hn_lo : lo ≤ n
        · simp [hnA, hn_lo]
        · simp [hnA, hn_lo, hh_small n hn_lo]
      · simp [hnA]
    have hsum_D_split : (∑ n ∈ D, h n) = (∑ n ∈ T, h n) + ∑ n ∈ N, h n := by
      have hfilter_T : D.filter (fun n => n ∈ T) = T := by
        ext n
        by_cases hnT : n ∈ T
        · simp [hnT, hT_subset_D hnT]
        · simp [hnT]
      have hpartition := Finset.sum_filter_add_sum_filter_not
        (s := D) (p := fun n => n ∈ T) (f := fun n => h n)
      rw [hfilter_T] at hpartition
      simpa [N, add_comm] using hpartition.symm
    have hincoming_le_N : ∀ n : ℕ, n ∈ D ->
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
      intro n hnD
      let f : ℕ → ℝ := fun q =>
        if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
          h (n / q) * U (some (n / q)) (some n)
        else 0
      let Q : Finset ℕ := n.divisors.filter (fun q => 1 < q ∧ q ∣ n ∧ lo ≤ n / q)
      have hn_ne : n ≠ 0 := by
        have := hD_lo n hnD; omega
      have htsum_eq : (∑' q : ℕ, f q) = ∑ q ∈ n.divisors, f q := by
        exact tsum_eq_sum (s := n.divisors) (fun q hq => by
          dsimp [f]
          by_cases hcond : 1 < q ∧ q ∣ n ∧ lo ≤ n / q
          · exfalso
            exact hq (Nat.mem_divisors.mpr ⟨hcond.2.1, hn_ne⟩)
          · simp [hcond])
      have hsum_filter : (∑ q ∈ n.divisors, f q) =
          ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
        dsimp [Q, f]
        exact (Finset.sum_filter (s := n.divisors)
          (p := fun q => 1 < q ∧ q ∣ n ∧ lo ≤ n / q)
          (f := fun q => h (n / q) * U (some (n / q)) (some n))).symm
      have hinj : ∀ q ∈ Q, ∀ r ∈ Q, n / q = n / r -> q = r := by
        intro q hq r hr hqr
        have hq' : 1 < q ∧ q ∣ n ∧ lo ≤ n / q := (Finset.mem_filter.mp hq).2
        have hr' : 1 < r ∧ r ∣ n ∧ lo ≤ n / r := (Finset.mem_filter.mp hr).2
        have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
        have hrmul : n / r * r = n := Nat.div_mul_cancel hr'.2.1
        have hqpos : 0 < n / q := by
          have := hq'.2.2; omega
        apply Nat.mul_left_cancel hqpos
        calc
          n / q * q = n := hqmul
          _ = n / r * r := hrmul.symm
          _ = n / q * r := by rw [hqr]
      have hsum_image : (∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n)) =
          ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := by
        symm
        rw [Finset.sum_image]
        intro q hq r hr hqr
        exact hinj q hq r hr hqr
      have himage_subset : Q.image (fun q => n / q) ⊆ N := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨q, hqQ, rfl⟩
        have hq' : 1 < q ∧ q ∣ n ∧ lo ≤ n / q := (Finset.mem_filter.mp hqQ).2
        have hpred_dvd : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hq'.2.1).symm⟩
        have hpredD : n / q ∈ D := hD_pred hnD hpred_dvd hq'.2.2
        have hpred_not_T : n / q ∉ T := by
          intro hpT
          rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
          have hpT' : n / q ∈ s ∧ n / q ∈ A ∧ lo ≤ n / q := by
            simpa [T] using hpT
          have haT' : a ∈ s ∧ a ∈ A ∧ lo ≤ a := by
            simpa [T] using haT
          have hp_dvd_a : n / q ∣ a := dvd_trans hpred_dvd hna
          have hpa_eq : n / q = a := hA.eq hpT'.2.1 haT'.2.1 hp_dvd_a
          subst a
          have hpred_lt_n : n / q < n := by
            have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
            have hpos : 0 < n / q := by
              have := hq'.2.2; omega
            calc
              n / q < n / q * q :=
                (Nat.lt_mul_iff_one_lt_right (a := n / q) (b := q) hpos).mpr hq'.1
              _ = n := hqmul
          have hn_le_pred : n ≤ n / q := Nat.le_of_dvd (by omega) hna
          omega
        simp [N, hpredD, hpred_not_T]
      calc
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) = ∑' q : ℕ, f q := rfl
        _ = ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
          rw [htsum_eq, hsum_filter]
        _ = ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := hsum_image
        _ ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro p hpN hpnot
            exact mul_nonneg (hh_nonneg p) (hU_nonneg (some p) (some n))
    have hbalance : (∑ n ∈ D, h n) ≤
        (∑ n ∈ D, L.indicator h n) +
          ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
      calc
        (∑ n ∈ D, h n) =
            ∑ n ∈ D,
              (L.indicator h n +
                ∑' q : ℕ,
                  if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
                    h (n / q) * U (some (n / q)) (some n)
                  else 0) := by
              apply Finset.sum_congr rfl
              intro n hnD
              exact hh_rec n (hD_lo n hnD)
        _ ≤ ∑ n ∈ D,
              (L.indicator h n +
                ∑ p ∈ N, h p * U (some p) (some n)) := by
              apply Finset.sum_le_sum
              intro n hnD
              exact add_le_add le_rfl (hincoming_le_N n hnD)
        _ = (∑ n ∈ D, L.indicator h n) +
              ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.sum_comm]
    have hout_le : (∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n)) ≤
        ∑ p ∈ N, h p := by
      apply Finset.sum_le_sum
      intro p hpN
      have hpD : p ∈ D := (Finset.mem_filter.mp hpN).1
      have hp_lo : lo ≤ p := hD_lo p hpD
      have hrow : (∑ n ∈ D, U (some p) (some n)) ≤ 1 := by
        have hrow' := hU_row_fin p hp_lo D
        convert hrow' using 1
        apply Finset.sum_congr rfl
        intro n hnD
        simp [hD_lo n hnD]
      calc
        (∑ n ∈ D, h p * U (some p) (some n)) =
            h p * ∑ n ∈ D, U (some p) (some n) := by
              rw [Finset.mul_sum]
        _ ≤ h p * 1 := mul_le_mul_of_nonneg_left hrow (hh_nonneg p)
        _ = h p := by ring
    have hinit_le : (∑ n ∈ D, L.indicator h n) ≤
        ∑' n : ℕ, L.indicator h n := by
      exact hh_Lsumm.sum_le_tsum D (fun n hn => by
        by_cases hnL : n ∈ L
        · rw [Set.indicator_of_mem hnL]
          exact hh_nonneg n
        · rw [Set.indicator_of_notMem hnL])
    have hactive_le_init : (∑ n ∈ T, h n) ≤
        ∑ n ∈ D, L.indicator h n := by
      have hsplit := hsum_D_split
      have hb := hbalance
      have ho := hout_le
      linarith
    rw [hleft_eq]
    exact le_trans hactive_le_init hinit_le
  intro A hA
  have hnonneg : ∀ n : ℕ, 0 ≤ A.indicator h n := by
    intro n
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn]
      exact hh.nonneg n
    · rw [Set.indicator_of_notMem hn]
  have hsumm : Summable (fun n : ℕ => A.indicator h n) :=
    summable_of_sum_range_le hnonneg (fun N => hfinite A hA (Finset.range N))
  exact ⟨hfinite A hA, hsumm, hsumm.tsum_le_of_sum_range_le
    (fun N => hfinite A hA (Finset.range N))⟩

/-- Source-term weighted-antichain inequality for upward divisibility walks.
This is TeX inequality `\eqref{psum-weight-upper}` for a general initial mass. -/
lemma gen_source_antichain_bound {U : Option ℕ → Option ℕ → ℝ}
    {h b : ℕ → ℝ} {lo : ℕ} (hlo : 1 ≤ lo)
    (hU : GenAdjPkg U lo) (hh : GenSourceHitting U h b lo) :
    ∀ A : Set ℕ, primitive_set A ->
      (∀ s : Finset ℕ,
        (∑ n ∈ s, A.indicator h n) ≤
          ∑' n : ℕ, b n) ∧
      Summable (fun n : ℕ => A.indicator h n) ∧
        (∑' n : ℕ, A.indicator h n) ≤
          ∑' n : ℕ, b n := by
  classical
  have hfinite : ∀ A : Set ℕ, primitive_set A -> ∀ s : Finset ℕ,
      (∑ n ∈ s, A.indicator h n) ≤
        ∑' n : ℕ, b n := by
    intro A hA s
    obtain ⟨hU_nonneg, hU_row_fin⟩ := hU
    obtain ⟨hh_nonneg, hh_rec, hh_small, hb_nonneg, hb_summ⟩ := hh
    let T : Finset ℕ := s.filter (fun n => n ∈ A ∧ lo ≤ n)
    let D : Finset ℕ := T.biUnion (fun a => a.divisors.filter (fun d => lo ≤ d))
    let N : Finset ℕ := D.filter (fun n => n ∉ T)
    have hD_lo : ∀ n : ℕ, n ∈ D -> lo ≤ n := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      exact (Finset.mem_filter.mp hn).2
    have hT_subset_D : T ⊆ D := by
      intro n hnT
      have hnT' : n ∈ s ∧ n ∈ A ∧ lo ≤ n := by
        simpa [T] using hnT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨n, hnT, ?_⟩
      have hn_ne : n ≠ 0 := by
        have := hnT'.2.2; omega
      simp [hnT'.2.2, hn_ne]
    have hD_dvd_active : ∀ n : ℕ, n ∈ D -> ∃ a : ℕ, a ∈ T ∧ n ∣ a := by
      intro n hn
      dsimp [D] at hn
      rcases Finset.mem_biUnion.mp hn with ⟨a, haT, hn⟩
      have hn' := Finset.mem_filter.mp hn
      exact ⟨a, haT, (Nat.mem_divisors.mp hn'.1).1⟩
    have hD_pred : ∀ {n p : ℕ}, n ∈ D -> p ∣ n -> lo ≤ p -> p ∈ D := by
      intro n p hnD hpn hp_lo
      rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
      have hpa : p ∣ a := dvd_trans hpn hna
      have haT' : a ∈ s ∧ a ∈ A ∧ lo ≤ a := by
        simpa [T] using haT
      dsimp [D]
      refine Finset.mem_biUnion.mpr ⟨a, haT, ?_⟩
      have ha_ne : a ≠ 0 := by
        have := haT'.2.2; omega
      simp [hp_lo, Nat.mem_divisors.mpr ⟨hpa, ha_ne⟩]
    have hleft_eq : (∑ n ∈ s, A.indicator h n) = ∑ n ∈ T, h n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnA : n ∈ A
      · by_cases hn_lo : lo ≤ n
        · simp [hnA, hn_lo]
        · simp [hnA, hn_lo, hh_small n hn_lo]
      · simp [hnA]
    have hsum_D_split : (∑ n ∈ D, h n) = (∑ n ∈ T, h n) + ∑ n ∈ N, h n := by
      have hfilter_T : D.filter (fun n => n ∈ T) = T := by
        ext n
        by_cases hnT : n ∈ T
        · simp [hnT, hT_subset_D hnT]
        · simp [hnT]
      have hpartition := Finset.sum_filter_add_sum_filter_not
        (s := D) (p := fun n => n ∈ T) (f := fun n => h n)
      rw [hfilter_T] at hpartition
      simpa [N, add_comm] using hpartition.symm
    have hincoming_le_N : ∀ n : ℕ, n ∈ D ->
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
      intro n hnD
      let f : ℕ → ℝ := fun q =>
        if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
          h (n / q) * U (some (n / q)) (some n)
        else 0
      let Q : Finset ℕ := n.divisors.filter (fun q => 1 < q ∧ q ∣ n ∧ lo ≤ n / q)
      have hn_ne : n ≠ 0 := by
        have := hD_lo n hnD; omega
      have htsum_eq : (∑' q : ℕ, f q) = ∑ q ∈ n.divisors, f q := by
        exact tsum_eq_sum (s := n.divisors) (fun q hq => by
          dsimp [f]
          by_cases hcond : 1 < q ∧ q ∣ n ∧ lo ≤ n / q
          · exfalso
            exact hq (Nat.mem_divisors.mpr ⟨hcond.2.1, hn_ne⟩)
          · simp [hcond])
      have hsum_filter : (∑ q ∈ n.divisors, f q) =
          ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
        dsimp [Q, f]
        exact (Finset.sum_filter (s := n.divisors)
          (p := fun q => 1 < q ∧ q ∣ n ∧ lo ≤ n / q)
          (f := fun q => h (n / q) * U (some (n / q)) (some n))).symm
      have hinj : ∀ q ∈ Q, ∀ r ∈ Q, n / q = n / r -> q = r := by
        intro q hq r hr hqr
        have hq' : 1 < q ∧ q ∣ n ∧ lo ≤ n / q := (Finset.mem_filter.mp hq).2
        have hr' : 1 < r ∧ r ∣ n ∧ lo ≤ n / r := (Finset.mem_filter.mp hr).2
        have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
        have hrmul : n / r * r = n := Nat.div_mul_cancel hr'.2.1
        have hqpos : 0 < n / q := by
          have := hq'.2.2; omega
        apply Nat.mul_left_cancel hqpos
        calc
          n / q * q = n := hqmul
          _ = n / r * r := hrmul.symm
          _ = n / q * r := by rw [hqr]
      have hsum_image : (∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n)) =
          ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := by
        symm
        rw [Finset.sum_image]
        intro q hq r hr hqr
        exact hinj q hq r hr hqr
      have himage_subset : Q.image (fun q => n / q) ⊆ N := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨q, hqQ, rfl⟩
        have hq' : 1 < q ∧ q ∣ n ∧ lo ≤ n / q := (Finset.mem_filter.mp hqQ).2
        have hpred_dvd : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hq'.2.1).symm⟩
        have hpredD : n / q ∈ D := hD_pred hnD hpred_dvd hq'.2.2
        have hpred_not_T : n / q ∉ T := by
          intro hpT
          rcases hD_dvd_active n hnD with ⟨a, haT, hna⟩
          have hpT' : n / q ∈ s ∧ n / q ∈ A ∧ lo ≤ n / q := by
            simpa [T] using hpT
          have haT' : a ∈ s ∧ a ∈ A ∧ lo ≤ a := by
            simpa [T] using haT
          have hp_dvd_a : n / q ∣ a := dvd_trans hpred_dvd hna
          have hpa_eq : n / q = a := hA.eq hpT'.2.1 haT'.2.1 hp_dvd_a
          subst a
          have hpred_lt_n : n / q < n := by
            have hqmul : n / q * q = n := Nat.div_mul_cancel hq'.2.1
            have hpos : 0 < n / q := by
              have := hq'.2.2; omega
            calc
              n / q < n / q * q :=
                (Nat.lt_mul_iff_one_lt_right (a := n / q) (b := q) hpos).mpr hq'.1
              _ = n := hqmul
          have hn_le_pred : n ≤ n / q := Nat.le_of_dvd (by omega) hna
          omega
        simp [N, hpredD, hpred_not_T]
      calc
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
            h (n / q) * U (some (n / q)) (some n)
          else 0) = ∑' q : ℕ, f q := rfl
        _ = ∑ q ∈ Q, h (n / q) * U (some (n / q)) (some n) := by
          rw [htsum_eq, hsum_filter]
        _ = ∑ p ∈ Q.image (fun q => n / q), h p * U (some p) (some n) := hsum_image
        _ ≤ ∑ p ∈ N, h p * U (some p) (some n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro p hpN hpnot
            exact mul_nonneg (hh_nonneg p) (hU_nonneg (some p) (some n))
    have hbalance : (∑ n ∈ D, h n) ≤
        (∑ n ∈ D, b n) +
          ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
      calc
        (∑ n ∈ D, h n) =
            ∑ n ∈ D,
              (b n +
                ∑' q : ℕ,
                  if 1 < q ∧ q ∣ n ∧ lo ≤ n / q then
                    h (n / q) * U (some (n / q)) (some n)
                  else 0) := by
              apply Finset.sum_congr rfl
              intro n hnD
              exact hh_rec n (hD_lo n hnD)
        _ ≤ ∑ n ∈ D,
              (b n +
                ∑ p ∈ N, h p * U (some p) (some n)) := by
              apply Finset.sum_le_sum
              intro n hnD
              exact add_le_add le_rfl (hincoming_le_N n hnD)
        _ = (∑ n ∈ D, b n) +
              ∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n) := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.sum_comm]
    have hout_le : (∑ p ∈ N, ∑ n ∈ D, h p * U (some p) (some n)) ≤
        ∑ p ∈ N, h p := by
      apply Finset.sum_le_sum
      intro p hpN
      have hpD : p ∈ D := (Finset.mem_filter.mp hpN).1
      have hp_lo : lo ≤ p := hD_lo p hpD
      have hrow : (∑ n ∈ D, U (some p) (some n)) ≤ 1 := by
        have hrow' := hU_row_fin p hp_lo D
        convert hrow' using 1
        apply Finset.sum_congr rfl
        intro n hnD
        simp [hD_lo n hnD]
      calc
        (∑ n ∈ D, h p * U (some p) (some n)) =
            h p * ∑ n ∈ D, U (some p) (some n) := by
              rw [Finset.mul_sum]
        _ ≤ h p * 1 := mul_le_mul_of_nonneg_left hrow (hh_nonneg p)
        _ = h p := by ring
    have hinit_le : (∑ n ∈ D, b n) ≤
        ∑' n : ℕ, b n :=
      hb_summ.sum_le_tsum D (fun n _ => hb_nonneg n)
    have hactive_le_init : (∑ n ∈ T, h n) ≤
        ∑ n ∈ D, b n := by
      have hsplit := hsum_D_split
      have hb := hbalance
      have ho := hout_le
      linarith
    rw [hleft_eq]
    exact le_trans hactive_le_init hinit_le
  intro A hA
  have hnonneg : ∀ n : ℕ, 0 ≤ A.indicator h n := by
    intro n
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn]
      exact hh.nonneg n
    · rw [Set.indicator_of_notMem hn]
  have hsumm : Summable (fun n : ℕ => A.indicator h n) :=
    summable_of_sum_range_le hnonneg (fun N => hfinite A hA (Finset.range N))
  exact ⟨hfinite A hA, hsumm, hsumm.tsum_le_of_sum_range_le
    (fun N => hfinite A hA (Finset.range N))⟩

/-!
### Flow-network cut capacity

This is TeX Remark `gpt-rem-5`.  The source term below is the mass crossing
from `S` to its complement in a downward kernel `P`.  `GenSourceHitting`
packages the corresponding flow-conservation identity and the convergence
hypotheses suppressed in the paper's informal statement.
-/

noncomputable def genCutSource (P : ℕ → ℕ → ℝ) (ν : ℕ → ℝ)
    (S : Set ℕ) (lo n : ℕ) : ℝ := by
  classical
  exact S.indicator (fun n => ν n * ∑' m : ℕ,
    if lo ≤ m ∧ m ∣ n ∧ m ∉ S then P n m else 0) n

noncomputable def genCutCapacity (P : ℕ → ℕ → ℝ) (ν : ℕ → ℝ)
    (S : Set ℕ) (lo : ℕ) : ℝ :=
  ∑' n : ℕ, genCutSource P ν S lo n

lemma gen_cut_capacity_inequality {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ} {ν : ℕ → ℝ} {S A : Set ℕ} {lo : ℕ}
    (hlo : 1 ≤ lo) (hU : GenAdjPkg U lo)
    (hcut : GenSourceHitting U (S.indicator ν)
      (genCutSource P ν S lo) lo) (hA : primitive_set A) :
    Summable (fun n : ℕ => (A ∩ S).indicator ν n) ∧
      (∑' n : ℕ, (A ∩ S).indicator ν n) ≤ genCutCapacity P ν S lo := by
  obtain ⟨_, hsumm, hle⟩ := gen_source_antichain_bound hlo hU hcut A hA
  have hind : A.indicator (S.indicator ν) = (A ∩ S).indicator ν := by
    funext n
    by_cases hnA : n ∈ A <;> by_cases hnS : n ∈ S <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hnA, hnS]
  rw [hind] at hsumm hle
  exact ⟨hsumm, by simpa [genCutCapacity] using hle⟩

/-- Public alias for TeX Remark `gpt-rem-5`. -/
theorem remark_gpt_rem_5 {P : ℕ → ℕ → ℝ}
    {U : Option ℕ → Option ℕ → ℝ} {ν : ℕ → ℝ} {S A : Set ℕ} {lo : ℕ}
    (hlo : 1 ≤ lo) (hU : GenAdjPkg U lo)
    (hcut : GenSourceHitting U (S.indicator ν)
      (genCutSource P ν S lo) lo) (hA : primitive_set A) :
    (∑' n : ℕ, (A ∩ S).indicator ν n) ≤ genCutCapacity P ν S lo :=
  (gen_cut_capacity_inequality hlo hU hcut hA).2

lemma oddBM_GenAdjPkg {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) :
    GenAdjPkg (oddBM_upward_kernel k Q) 1 :=
  ⟨oddBM_upward_kernel_nonneg hk hQ,
    oddBM_upward_kernel_finite_row hk hQ⟩

lemma oddBM_GenHitting {k : ℕ} {Q : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) :
    GenHitting (oddBM_upward_kernel k Q) (oddBM_hittingWeight k Q)
      (oddBM_hittingWeight k Q) (oddBM_terminal k Q) 1 := by
  refine ⟨oddBM_hittingWeight_nonneg hk hQ,
    oddBM_hittingWeight_recurrence hk hQ, fun _ => rfl, ?_, ?_⟩
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    rw [oddBM_hittingWeight, Set.indicator_of_notMem]
    intro h
    exact (oddBM_state_positive_of_odd_primes hQ h).ne' rfl
  · have hsumm := (oddBM_terminal_erdos_bound k hQ).1
    convert hsumm using 1
    funext n
    by_cases hn : n ∈ oddBM_terminal k Q
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn,
        oddBM_hittingWeight, Set.indicator_of_mem
          (oddBM_terminal_subset_state k Q hn)]
    · simp [Set.indicator_of_notMem hn]

/-- Odd Banks--Martin for a primitive set already restricted to its allowed
odd primes: `f(A) ≤ f(N_k(Q))`. -/
theorem odd_banks_martin_restricted {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hA : primitive_set A)
    (hAQ : A ⊆ oddBM_state k Q) :
    Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
      erdos_sum A ≤ erdos_sum (oddBM_terminal k Q) := by
  obtain ⟨_, hsumm, hle⟩ := gen_adjoint_antichain_bound le_rfl
    (oddBM_GenAdjPkg hk hQ) (oddBM_GenHitting hk hQ) A hA
  have hAeq : A.indicator (oddBM_hittingWeight k Q) =
      A.indicator erdos_weight := by
    funext n
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn,
        oddBM_hittingWeight, Set.indicator_of_mem (hAQ hn)]
    · simp [Set.indicator_of_notMem hn]
  have hLeq : (oddBM_terminal k Q).indicator (oddBM_hittingWeight k Q) =
      (oddBM_terminal k Q).indicator erdos_weight := by
    funext n
    by_cases hn : n ∈ oddBM_terminal k Q
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn,
        oddBM_hittingWeight, Set.indicator_of_mem
          (oddBM_terminal_subset_state k Q hn)]
    · simp [Set.indicator_of_notMem hn]
  rw [hAeq] at hsumm hle
  rw [hLeq] at hle
  exact ⟨hsumm, hle⟩

/-- Odd Banks--Martin in the paper's original form. -/
theorem odd_banks_martin {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hA : primitive_set A)
    (hAk : A ⊆ omega_ge_layer k) :
    Summable (fun n : ℕ => (restrict_to_primes A Q).indicator erdos_weight n) ∧
      erdos_sum (restrict_to_primes A Q) ≤ erdos_sum (oddBM_terminal k Q) := by
  apply odd_banks_martin_restricted hk hQ (restrict_to_primes_primitive hA)
  intro n hn
  exact ⟨restrict_to_primes_subset_omega_ge hAk hn, hn.2⟩

theorem theorem_odd_banks_martin {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : IsSetOfOddPrimes Q) (hA : primitive_set A)
    (hAk : A ⊆ omega_ge_layer k) :
    erdos_sum (restrict_to_primes A Q) ≤ erdos_sum (oddBM_terminal k Q) :=
  (odd_banks_martin hk hQ hA hAk).2

/-- The AKS multiplicative kernel is a nonnegative sub-stochastic upward
kernel in the theorem range. -/
lemma aks_GenAdjPkg {x s : ℝ} (hx : 2 ≤ x) (hs : 0 < s) :
    GenAdjPkg (aksUpwardKernel x s) 1 :=
  ⟨aksUpwardKernel_nonneg x s, aksUpwardKernel_finite_row hx hs⟩

/-- The recursively defined AKS hitting mass satisfies the source-term
recurrence with initial mass `aksInitialMass`. -/
lemma aks_GenSourceHitting {x y s : ℝ} (hx : 2 < x) :
    GenSourceHitting (aksUpwardKernel x s)
      (aksHittingMass x y s) (aksInitialMass x y s) 1 :=
  ⟨aksHittingMass_nonneg x y s,
    fun n hn => aksHittingMass_tsum_recurrence hn,
    fun n hn => by
      have : n = 0 := by omega
      simpa [this] using aksHittingMass_zero (y := y) (s := s) hx,
    aksInitialMass_nonneg x y s,
    aksInitialMass_summable x y s⟩

/-- TeX equation `\eqref{p1}` for the AKS walk: the hitting mass collected by
a primitive set is at most the total initial mass on rough numbers. -/
lemma aks_primitive_hitting_mass_bound {x y s : ℝ}
    (hx : 2 < x) (hs : 0 < s) {A : Set ℕ} (hA : primitive_set A) :
    Summable (fun n : ℕ => A.indicator (aksHittingMass x y s) n) ∧
      (∑' n : ℕ, A.indicator (aksHittingMass x y s) n) ≤
        ∑' n : ℕ, aksInitialMass x y s n := by
  obtain ⟨_, hsum, hle⟩ := gen_source_antichain_bound le_rfl
    (aks_GenAdjPkg hx.le (by linarith)) (aks_GenSourceHitting hx) A hA
  exact ⟨hsum, hle⟩

lemma aks_primitive_hitting_mass_bound_aksExponent {x y : ℝ}
    (hx : 3 ≤ x) {A : Set ℕ} (hA : primitive_set A) :
    Summable (fun n : ℕ =>
      A.indicator (aksHittingMass x y (aksExponent x)) n) ∧
      (∑' n : ℕ, A.indicator (aksHittingMass x y (aksExponent x)) n) ≤
        ∑' n : ℕ, aksInitialMass x y (aksExponent x) n :=
  aks_primitive_hitting_mass_bound (by linarith) (aksExponent_pos hx) hA

/-- The pointwise AKS estimate summed over a primitive set in `[y/x,y]`.
Together with the rough-number estimate `\eqref{p2}`, this is the final
probabilistic inequality used in the AKS theorem. -/
lemma aks_interval_weighted_sum_le_initialMass {x y : ℝ}
    (hx : 3 ≤ x) (hxy : x ≤ y) {A : Set ℕ} (hA : primitive_set A) :
    (∑' n : ℕ, (A ∩ aksInterval x y).indicator (fun n : ℕ =>
      (Real.exp (-(1 : ℝ) / 10) *
          Real.rpow y (1 - aksExponent x) / (n : ℝ)) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2)))) n) ≤
      ∑' n : ℕ, aksInitialMass x y (aksExponent x) n := by
  classical
  let B := A ∩ aksInterval x y
  let f : ℕ → ℝ := fun n => B.indicator (fun n : ℕ =>
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) / (n : ℝ)) *
      (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
        (Real.exp (aksPartitionFunction x (aksExponent x)) *
          (Real.exp 1 * Real.sqrt 2)))) n
  let g : ℕ → ℝ := B.indicator (aksHittingMass x y (aksExponent x))
  have hB : primitive_set B := primitive_set_inter_aksInterval hA x y
  obtain ⟨hg, hgle⟩ := aks_primitive_hitting_mass_bound_aksExponent
    (y := y) hx hB
  have hBfinite : B.Finite := by
    refine ((Set.finite_le_nat ⌊y⌋₊).subset ?_).inter_of_right A
    intro n hn
    exact Nat.le_floor hn.2
  have hf : Summable f := by
    refine summable_of_ne_finset_zero (s := hBfinite.toFinset) ?_
    intro n hn
    have hnB : n ∉ B := fun hmem => hn (hBfinite.mem_toFinset.mpr hmem)
    simp [f, Set.indicator_of_notMem hnB]
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hn : n ∈ B
    · simp only [f, g, Set.indicator_of_mem hn]
      exact aks_hittingMass_interval_lower_bound hx hxy hn.2
    · simp [f, g, Set.indicator_of_notMem hn]
  exact (Summable.tsum_le_tsum hfg hf hg).trans hgle

lemma aks_LYM_interval_sum_le_initialMass {x y : ℝ}
    (hx : 3 ≤ x) (hxy : x ≤ y) {A : Set ℕ} (hA : primitive_set A) :
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) /
          Real.exp (aksPartitionFunction x (aksExponent x))) *
      aksLYMSum A x y (aksPartitionFunction x (aksExponent x)) ≤
        ∑' n : ℕ, aksInitialMass x y (aksExponent x) n := by
  classical
  let Z := aksPartitionFunction x (aksExponent x)
  let B := A ∩ aksInterval x y
  let f : ℕ → ℝ := fun n => B.indicator (fun n : ℕ =>
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) / Real.exp Z) *
      aksLYMWeight x Z n) n
  let g : ℕ → ℝ := B.indicator (aksHittingMass x y (aksExponent x))
  have hB : primitive_set B := primitive_set_inter_aksInterval hA x y
  obtain ⟨hg, hgle⟩ := aks_primitive_hitting_mass_bound_aksExponent hx hB
  have hBfinite : B.Finite := by
    refine ((Set.finite_le_nat ⌊y⌋₊).subset ?_).inter_of_right A
    intro n hn
    exact Nat.le_floor hn.2
  have hf : Summable f := summable_of_ne_finset_zero
    (s := hBfinite.toFinset) fun n hn => by
      simp [f, Set.indicator_of_notMem fun h => hn (hBfinite.mem_toFinset.mpr h)]
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hn : n ∈ B
    · simp only [f, g, Set.indicator_of_mem hn]
      have hnpos := aksInterval_pos (by linarith : 0 < x) hxy hn.2
      have hpath := aks_canonical_orderings_total_weight_eq_poisson
        (x := x) (y := y) (s := aksExponent x)
        (Nat.ne_of_gt (by exact_mod_cast hnpos : 0 < n)) hn.2.2
        (aksPartitionFunction_pos (by linarith) (aksExponent_pos hx)).ne'
      have hweight :
          (Real.exp (-(1 : ℝ) / 10) *
              Real.rpow y (1 - aksExponent x) / Real.exp Z) *
            aksLYMWeight x Z n ≤
          (1 / Real.rpow (n : ℝ) (aksExponent x)) /
            (Real.exp Z * aksPoissonMass Z (aksSmallPrimeSupport x n).card) := by
        rw [aksLYMWeight, aksSmallPrimeFactorCount_eq_card]
        have hinterval := aks_interval_rpow_weight_lower hx hxy hn.2
        let P := aksPoissonMass (aksPartitionFunction x (aksExponent x))
          (aksSmallPrimeSupport x n).card
        have hP : 0 < P := aksPoissonMass_pos
          (aksPartitionFunction_pos (by linarith : 2 ≤ x) (aksExponent_pos hx))
          (aksSmallPrimeSupport x n).card
        have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
        dsimp [Z]
        calc
          Real.exp (-(1 : ℝ) / 10) *
                Real.rpow y (1 - aksExponent x) /
                Real.exp (aksPartitionFunction x (aksExponent x)) *
              (1 / ((n : ℝ) * aksPoissonMass
                (aksPartitionFunction x (aksExponent x))
                (aksSmallPrimeSupport x n).card)) =
              (Real.exp (-(1 : ℝ) / 10) *
                  Real.rpow y (1 - aksExponent x) / (n : ℝ)) /
                (Real.exp (aksPartitionFunction x (aksExponent x)) * P) := by
            change _ * (1 / ((n : ℝ) * P)) = _
            field_simp [hnreal.ne', hP.ne', Real.exp_ne_zero]
          _ ≤ (1 / Real.rpow (n : ℝ) (aksExponent x)) /
                (Real.exp (aksPartitionFunction x (aksExponent x)) * P) :=
            div_le_div_of_nonneg_right hinterval
              (mul_pos (Real.exp_pos _) hP).le
      exact hweight.trans <| hpath.symm.le.trans
        (aks_canonical_orderings_total_weight_le_hittingMass
          (Nat.ne_of_gt (by exact_mod_cast hnpos : 0 < n)))
    · simp [f, g, Set.indicator_of_notMem hn]
  have hle := (Summable.tsum_le_tsum hfg hf hg).trans hgle
  calc
    (Real.exp (-(1 : ℝ) / 10) *
        Real.rpow y (1 - aksExponent x) / Real.exp Z) *
        aksLYMSum A x y Z = ∑' n : ℕ, f n := by
      rw [aksLYMSum, ← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : n ∈ B
      · simp [f, B, Set.indicator_of_mem hn]
      · simp [f, B, Set.indicator_of_notMem hn]
    _ ≤ _ := hle

lemma aks_interval_weighted_sum_eq_factor {x y : ℝ} (A : Set ℕ) :
    (∑' n : ℕ, (A ∩ aksInterval x y).indicator (fun n : ℕ =>
      (Real.exp (-(1 : ℝ) / 10) *
          Real.rpow y (1 - aksExponent x) / (n : ℝ)) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2)))) n) =
      (Real.exp (-(1 : ℝ) / 10) *
          Real.rpow y (1 - aksExponent x) *
        (Real.sqrt (aksPartitionFunction x (aksExponent x)) /
          (Real.exp (aksPartitionFunction x (aksExponent x)) *
            (Real.exp 1 * Real.sqrt 2)))) *
        reciprocal_dyadic_interval_sum A x y := by
  rw [reciprocal_dyadic_interval_sum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ A ∩ aksInterval x y
  · simp only [Set.indicator_of_mem hn]
    ring
  · simp [Set.indicator_of_notMem hn]

/-- The complete AKS deduction after equation `\eqref{p2}`: any uniform
initial-mass constant gives the desired reciprocal interval estimate. -/
lemma aks_reciprocal_interval_sum_le_of_initialMass_bound
    {C x y : ℝ} (hC : 0 ≤ C) (hx : 3 ≤ x) (hxy : x ≤ y)
    {A : Set ℕ} (hA : primitive_set A)
    (hinit : (∑' n : ℕ, aksInitialMass x y (aksExponent x) n) ≤
      C * Real.rpow y (1 - aksExponent x)) :
    reciprocal_dyadic_interval_sum A x y ≤
      C * Real.exp ((1 : ℝ) / 10) * (Real.exp 1 * Real.sqrt 2) *
        (Real.exp (aksPartitionFunction x (aksExponent x)) /
          Real.sqrt (aksPartitionFunction x (aksExponent x))) := by
  let Z := aksPartitionFunction x (aksExponent x)
  let Y := Real.rpow y (1 - aksExponent x)
  let S := reciprocal_dyadic_interval_sum A x y
  have hy : 0 < y := lt_of_lt_of_le (by linarith : 0 < x) hxy
  have hY : 0 < Y := Real.rpow_pos_of_pos hy _
  have hZ : 0 < Z := one_lt_aksPartitionFunction_aksExponent hx |>.trans' zero_lt_one
  have hsqrtZ : 0 < Real.sqrt Z := Real.sqrt_pos.mpr hZ
  have hden : 0 < Real.exp Z * (Real.exp 1 * Real.sqrt 2) := by positivity
  have hcoef : 0 < Real.exp (-(1 : ℝ) / 10) * Y *
      (Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2))) := by
    positivity
  have hweighted := aks_interval_weighted_sum_le_initialMass hx hxy hA
  rw [aks_interval_weighted_sum_eq_factor] at hweighted
  change (Real.exp (-(1 : ℝ) / 10) * Y *
      (Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)))) * S ≤ _
    at hweighted
  have hle : (Real.exp (-(1 : ℝ) / 10) * Y *
      (Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)))) * S ≤ C * Y :=
    hweighted.trans hinit
  have hle' : S ≤ C * Y /
      (Real.exp (-(1 : ℝ) / 10) * Y *
        (Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)))) := by
    rw [le_div_iff₀ hcoef]
    simpa [mul_comm] using hle
  calc
    S ≤ C * Y /
        (Real.exp (-(1 : ℝ) / 10) * Y *
          (Real.sqrt Z / (Real.exp Z * (Real.exp 1 * Real.sqrt 2)))) := hle'
    _ = C * Real.exp ((1 : ℝ) / 10) * (Real.exp 1 * Real.sqrt 2) *
        (Real.exp Z / Real.sqrt Z) := by
      have hexp : Real.exp (-(1 : ℝ) / 10) * Real.exp ((1 : ℝ) / 10) = 1 := by
        rw [← Real.exp_add]
        norm_num
      field_simp [hY.ne', hsqrtZ.ne', Real.exp_ne_zero]
      nlinarith

/-- Ahlswede--Khachatrian--Sárközy: uniformly for primitive `A` and
`3 ≤ x ≤ y`, the reciprocal mass on `[y/x,y]` is
`O(log x / sqrt(log log x))`. -/
theorem ahlswede_khachatrian_sarkozy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        reciprocal_dyadic_interval_sum A x y ≤
          C * Real.log x / Real.sqrt (Real.log (Real.log x)) := by
  obtain ⟨D, hD, hpart⟩ := aksPartitionFunction_exp_div_sqrt_bound
  let C₀ := 20 * Real.exp ((1 : ℝ) / 10)
  let K := C₀ * Real.exp ((1 : ℝ) / 10) *
    (Real.exp 1 * Real.sqrt 2)
  refine ⟨K * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y A hx hxy hA
  have hpost := aks_reciprocal_interval_sum_le_of_initialMass_bound
    (C := C₀) (by positivity) hx hxy hA (aksInitialMass_tsum_le hx hxy)
  exact hpost.trans <| by
    dsimp [K]
    calc
      C₀ * Real.exp ((1 : ℝ) / 10) * (Real.exp 1 * Real.sqrt 2) *
          (Real.exp (aksPartitionFunction x (aksExponent x)) /
            Real.sqrt (aksPartitionFunction x (aksExponent x))) ≤
          C₀ * Real.exp ((1 : ℝ) / 10) * (Real.exp 1 * Real.sqrt 2) *
            (D * Real.log x / Real.sqrt (Real.log (Real.log x))) :=
        mul_le_mul_of_nonneg_left (hpart x hx) (by positivity)
      _ = K * D * Real.log x / Real.sqrt (Real.log (Real.log x)) := by
        dsimp [K]
        ring

theorem theorem_AKS :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        reciprocal_dyadic_interval_sum A x y ≤
          C * Real.log x / Real.sqrt (Real.log (Real.log x)) :=
  ahlswede_khachatrian_sarkozy

/-- The LYM refinement from TeX Remark `lym-rem`. -/
theorem aks_LYM_refinement :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> primitive_set A ->
        aksLYMSum A x y (aksPartitionFunction x (aksExponent x)) ≤
          C * Real.log x := by
  obtain ⟨D, hD, hpart⟩ := aksPartitionFunction_exp_bound
  let C₀ := 20 * Real.exp ((1 : ℝ) / 10)
  let K := C₀ * Real.exp ((1 : ℝ) / 10)
  refine ⟨K * D, mul_nonneg (by positivity) hD, ?_⟩
  intro x y A hx hxy hA
  let Z := aksPartitionFunction x (aksExponent x)
  let Y := Real.rpow y (1 - aksExponent x)
  let S := aksLYMSum A x y Z
  have hy : 0 < y := lt_of_lt_of_le (by linarith : 0 < x) hxy
  have hY : 0 < Y := Real.rpow_pos_of_pos hy _
  have hcoef : 0 < Real.exp (-(1 : ℝ) / 10) * Y / Real.exp Z := by positivity
  have hwalk := aks_LYM_interval_sum_le_initialMass hx hxy hA
  have hmass := aksInitialMass_tsum_le hx hxy
  change (Real.exp (-(1 : ℝ) / 10) * Y / Real.exp Z) * S ≤ _ at hwalk
  change _ ≤ C₀ * Y at hmass
  have hle : S ≤ C₀ * Y /
      (Real.exp (-(1 : ℝ) / 10) * Y / Real.exp Z) := by
    rw [le_div_iff₀ hcoef]
    simpa [mul_comm] using hwalk.trans hmass
  have hcancel : C₀ * Y /
      (Real.exp (-(1 : ℝ) / 10) * Y / Real.exp Z) = K * Real.exp Z := by
    dsimp [K]
    have hexp : Real.exp (-(1 : ℝ) / 10) * Real.exp ((1 : ℝ) / 10) = 1 := by
      rw [← Real.exp_add]
      norm_num
    field_simp [hY.ne', Real.exp_ne_zero]
    convert congrArg (fun z : ℝ => C₀ * z) hexp.symm using 1 <;> ring_nf
  calc
    S ≤ K * Real.exp Z := hle.trans_eq hcancel
    _ ≤ K * (D * Real.log x) :=
      mul_le_mul_of_nonneg_left (hpart x hx) (by positivity)
    _ = K * D * Real.log x := by ring

/-!
## `2` is Erdős-strong

TeX Theorem `2-strong` (Section `2-strong-sec`): for every primitive set `A`
of even numbers, `f(A) ≤ f({2}) = ν₀(2)`.  The proof rescales by `2`, forms the
adjoint of the von Mangoldt downward chain against the sub-invariant weight
`ν₂(n) = 1/(n log(2n))`, and applies the antichain inequality
`\eqref{psum-weight-upper}` with boundary mass `b(1) = ν₂(1) = 1/log 2`.
-/

/-- The adjoint upward kernel of the von Mangoldt downward chain with respect to
the sub-invariant weight `ν₂` (TeX `\eqref{adjoint-def}`): it carries mass from a
divisor `n` up to a proper multiple `m` with weight `ν₂(m) Λ(m/n) / (ν₂(n) log m)`. -/
noncomputable def U2 : Option ℕ → Option ℕ → ℝ
  | some n, some m =>
      if n ∣ m ∧ n < m then
        erdos_two_shift_weight m * ArithmeticFunction.vonMangoldt (m / n) /
          (erdos_two_shift_weight n * Real.log (m : ℝ))
      else 0
  | _, _ => 0

lemma U2_some_some (n m : ℕ) :
    U2 (some n) (some m) =
      if n ∣ m ∧ n < m then
        erdos_two_shift_weight m * ArithmeticFunction.vonMangoldt (m / n) /
          (erdos_two_shift_weight n * Real.log (m : ℝ))
      else 0 :=
  rfl

/-- Nonnegativity of the adjoint kernel `U2`. -/
lemma U2_nonneg : ∀ a b : Option ℕ, 0 ≤ U2 a b := by
  intro a b
  rcases a with _ | n <;> rcases b with _ | m
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · rw [U2_some_some]
    by_cases hcond : n ∣ m ∧ n < m
    · rw [if_pos hcond]
      have hm_pos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hcond.2
      have hn_pos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hp
        · exact absurd (Nat.eq_zero_of_zero_dvd hcond.1) (by omega)
        · exact hp
      exact div_nonneg
        (mul_nonneg (erdos_two_shift_weight_nonneg_of_pos hm_pos)
          ArithmeticFunction.vonMangoldt_nonneg)
        (mul_nonneg (erdos_two_shift_weight_nonneg_of_pos hn_pos)
          (Real.log_nonneg (by exact_mod_cast hm_pos)))
    · rw [if_neg hcond]

/-- The rows of `U2` over states `≥ 1` are sub-stochastic; this is the adjoint
form of the sub-invariance inequality `\eqref{sub}` for `ν₂`. -/
lemma U2_finite_row : ∀ n : ℕ, 1 ≤ n → ∀ s : Finset ℕ,
    (∑ m ∈ s, if 1 ≤ m then U2 (some n) (some m) else 0) ≤ 1 := by
  intro n hn s
  classical
  have hν_pos : 0 < erdos_two_shift_weight n := erdos_two_shift_weight_pos hn
  calc
    (∑ m ∈ s, if 1 ≤ m then U2 (some n) (some m) else 0)
        = ∑ m ∈ s.filter (fun m => n ∣ m ∧ n < m), U2 (some n) (some m) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun m _ => ?_
          by_cases hcond : n ∣ m ∧ n < m
          · rw [if_pos (hn.trans hcond.2.le), if_pos hcond]
          · rw [if_neg hcond]
            by_cases h1m : 1 ≤ m
            · rw [if_pos h1m, U2_some_some, if_neg hcond]
            · rw [if_neg h1m]
    _ = ∑ m ∈ s.filter (fun m => n ∣ m ∧ n < m),
          (if 1 < m / n then
            erdos_two_shift_weight (n * (m / n)) *
              ArithmeticFunction.vonMangoldt (m / n) /
              Real.log (((n * (m / n) : ℕ) : ℝ))
          else 0) / erdos_two_shift_weight n := by
          refine Finset.sum_congr rfl fun m hm => ?_
          obtain ⟨hdvd, hlt⟩ := (Finset.mem_filter.mp hm).2
          have hmn : n * (m / n) = m := Nat.mul_div_cancel' hdvd
          have hq1 : 1 < m / n := by
            by_contra hcon
            push Not at hcon
            have hle : m ≤ n := by
              calc
                m = n * (m / n) := hmn.symm
                _ ≤ n * 1 := Nat.mul_le_mul_left n hcon
                _ = n := Nat.mul_one n
            omega
          rw [U2_some_some, if_pos ⟨hdvd, hlt⟩, if_pos hq1, hmn]
          ring
    _ = (∑ m ∈ s.filter (fun m => n ∣ m ∧ n < m),
          if 1 < m / n then
            erdos_two_shift_weight (n * (m / n)) *
              ArithmeticFunction.vonMangoldt (m / n) /
              Real.log (((n * (m / n) : ℕ) : ℝ))
          else 0) / erdos_two_shift_weight n := (Finset.sum_div _ _ _).symm
    _ = (∑ q ∈ (s.filter (fun m => n ∣ m ∧ n < m)).image (fun m => m / n),
          if 1 < q then
            erdos_two_shift_weight (n * q) * ArithmeticFunction.vonMangoldt q /
              Real.log (((n * q : ℕ) : ℝ))
          else 0) / erdos_two_shift_weight n := by
          congr 1
          symm
          rw [Finset.sum_image]
          intro a ha b hb hab
          calc
            a = n * (a / n) := (Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2.1).symm
            _ = n * (b / n) := congrArg (fun q => n * q) hab
            _ = b := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.1
    _ ≤ (∑' q : ℕ,
          if 1 < q then
            erdos_two_shift_weight (n * q) * ArithmeticFunction.vonMangoldt q /
              Real.log (((n * q : ℕ) : ℝ))
          else 0) / erdos_two_shift_weight n := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            ((nu2_subinvariant_summable n hn).sum_le_tsum _
              fun q _ => nu2_subinvariant_term_nonneg n hn q)
            (inv_nonneg.mpr hν_pos.le)
    _ ≤ erdos_two_shift_weight n / erdos_two_shift_weight n := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (nu2_subinvariant_tsum n hn)
            (inv_nonneg.mpr hν_pos.le)
    _ = 1 := div_self hν_pos.ne'

/-- The upward recurrence (TeX `\eqref{nu-recurse}`) satisfied by the hitting
mass `ν₂` with boundary `{1}`. -/
lemma nu2_recurrence : ∀ n : ℕ, 1 ≤ n →
    erdos_two_shift_weight n =
      ({1} : Set ℕ).indicator erdos_two_shift_weight n +
        (∑' q : ℕ,
          if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
            erdos_two_shift_weight (n / q) * U2 (some (n / q)) (some n)
          else 0) := by
  intro n hn
  by_cases hn1 : n = 1
  · subst hn1
    have hzero : ∀ q : ℕ,
        (if 1 < q ∧ q ∣ 1 ∧ 1 ≤ 1 / q then
          erdos_two_shift_weight (1 / q) * U2 (some (1 / q)) (some 1)
        else 0) = 0 := by
      intro q
      rw [if_neg]
      rintro ⟨h1q, hdvd, -⟩
      exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)
    rw [tsum_congr hzero, tsum_zero, add_zero,
      Set.indicator_of_mem (Set.mem_singleton 1)]
  · have hn2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlog_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn2).ne'
    have htsum_eq : (∑' q : ℕ,
        if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          erdos_two_shift_weight (n / q) * U2 (some (n / q)) (some n)
        else 0) =
        ∑ q ∈ n.divisors,
          if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
            erdos_two_shift_weight (n / q) * U2 (some (n / q)) (some n)
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := n.divisors) ?_
      intro q hq
      have hcond : ¬ (1 < q ∧ q ∣ n ∧ 1 ≤ n / q) :=
        fun hcon => hq (Nat.mem_divisors.mpr ⟨hcon.2.1, by omega⟩)
      rw [if_neg hcond]
    have hterm : ∀ q ∈ n.divisors,
        (if 1 < q ∧ q ∣ n ∧ 1 ≤ n / q then
          erdos_two_shift_weight (n / q) * U2 (some (n / q)) (some n)
        else 0) =
        (if 1 < q then
          erdos_two_shift_weight n * ArithmeticFunction.vonMangoldt q
        else 0) / Real.log (n : ℝ) := by
      intro q hq
      obtain ⟨hqdvd, hn0⟩ := Nat.mem_divisors.mp hq
      by_cases h1q : 1 < q
      · have hdiv_pos : 0 < n / q :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) (by omega)
        have hd : n / q ∣ n := Nat.div_dvd_of_dvd hqdvd
        have hlt : n / q < n := Nat.div_lt_self (by omega) h1q
        have hν_pos : (0 : ℝ) < erdos_two_shift_weight (n / q) :=
          erdos_two_shift_weight_pos hdiv_pos
        rw [if_pos ⟨h1q, hqdvd, hdiv_pos⟩, if_pos h1q, U2_some_some,
          if_pos ⟨hd, hlt⟩, Nat.div_div_self hqdvd hn0]
        field_simp
        try ring
      · rw [if_neg (fun hcon => h1q hcon.1), if_neg h1q, zero_div]
    have hdrop : ∀ q ∈ n.divisors,
        ((if 1 < q then
          erdos_two_shift_weight n * ArithmeticFunction.vonMangoldt q
        else 0) / Real.log (n : ℝ)) =
        erdos_two_shift_weight n * ArithmeticFunction.vonMangoldt q /
          Real.log (n : ℝ) := by
      intro q hq
      have hq_pos := Nat.pos_of_mem_divisors hq
      rcases Nat.lt_or_ge q 2 with h1 | h1
      · have hq1 : q = 1 := by omega
        subst hq1
        simp [ArithmeticFunction.vonMangoldt_apply_one]
      · rw [if_pos (by omega : 1 < q)]
    rw [Set.indicator_of_notMem (by simpa using hn1), zero_add, htsum_eq,
      Finset.sum_congr rfl (fun q hq => (hterm q hq).trans (hdrop q hq)),
      ← Finset.sum_div, ← Finset.mul_sum, von_mangoldt_divisor_sum,
      mul_div_assoc, div_self hlog_ne, mul_one]

/-- The adjoint-kernel package for the `2`-strong chain. -/
lemma two_strong_GenAdjPkg : GenAdjPkg U2 1 :=
  ⟨U2_nonneg, U2_finite_row⟩

/-- The hitting-mass package for the `2`-strong chain. -/
lemma two_strong_GenHitting :
    GenHitting U2 erdos_two_shift_weight erdos_two_shift_weight ({1} : Set ℕ) 1 :=
  { nonneg := fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp [erdos_two_shift_weight, erdos_shift_weight]
      · exact erdos_two_shift_weight_nonneg_of_pos h
    recurrence := nu2_recurrence
    equals_w := fun _ => rfl
    small_zero := fun n hn => by
      obtain rfl : n = 0 := by omega
      simp [erdos_two_shift_weight, erdos_shift_weight]
    L_summable := summable_of_hasFiniteSupport
      ((Set.finite_singleton 1).subset Set.support_indicator_subset) }

/-- The total boundary mass on `{1}` equals `ν₂(1) = 1/log 2`. -/
lemma tsum_singleton_indicator_nu2 :
    (∑' n : ℕ, ({1} : Set ℕ).indicator erdos_two_shift_weight n) =
      erdos_two_shift_weight 1 := by
  rw [tsum_eq_single 1 fun b hb => Set.indicator_of_notMem (by simpa using hb) _,
    Set.indicator_of_mem (Set.mem_singleton 1)]

/-- The weighted-antichain inequality `\eqref{n2}` for `ν₂`: for every primitive
set `A'`, `∑_{n ∈ A'} ν₂(n) ≤ ν₂(1)`. -/
theorem two_strong_antichain (A : Set ℕ) (hA : primitive_set A) :
    Summable (fun n : ℕ => A.indicator erdos_two_shift_weight n) ∧
      (∑' n : ℕ, A.indicator erdos_two_shift_weight n) ≤
        erdos_two_shift_weight 1 := by
  obtain ⟨-, hsumm, hle⟩ :=
    gen_adjoint_antichain_bound le_rfl two_strong_GenAdjPkg two_strong_GenHitting A hA
  exact ⟨hsumm, hle.trans_eq tsum_singleton_indicator_nu2⟩

/-- **`2` is Erdős-strong** (TeX Theorem `2-strong`). -/
theorem two_is_erdos_strong : erdos_strong 2 := by
  refine ⟨Nat.prime_two, fun A hA hlpf => ?_⟩
  obtain ⟨hsumm', hle'⟩ :=
    two_strong_antichain (multiplicative_preimage 2 A)
      (multiplicative_preimage_two_primitive hA)
  have hsupp : Function.support (A.indicator erdos_weight) ⊆
      Set.range (fun m : ℕ => 2 * m) := by
    intro n hn
    have hnA : n ∈ A := by
      by_contra hnA
      exact hn (Set.indicator_of_notMem hnA _)
    obtain ⟨m, rfl⟩ := IsLeastPrimeFactor.dvd (hlpf n hnA)
    exact ⟨m, rfl⟩
  have hinj : Function.Injective (fun m : ℕ => 2 * m) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hcomp : ∀ m : ℕ, A.indicator erdos_weight (2 * m) =
      (1 / 2 : ℝ) * (multiplicative_preimage 2 A).indicator erdos_two_shift_weight m :=
    erdos_weight_indicator_two_mul_eq_half_shift_preimage hlpf
  have hzero : ∀ x ∉ Set.range (fun m : ℕ => 2 * m),
      A.indicator erdos_weight x = 0 := by
    intro x hx
    by_contra hcon
    exact hx (hsupp hcon)
  have hsummf : Summable (A.indicator erdos_weight) :=
    (hinj.summable_iff hzero).mp
      ((hsumm'.mul_left (1 / 2 : ℝ)).congr fun m => (hcomp m).symm)
  refine ⟨hsummf, ?_⟩
  calc
    erdos_sum A = ∑' m : ℕ, A.indicator erdos_weight (2 * m) :=
      (hinj.tsum_eq hsupp).symm
    _ = (1 / 2 : ℝ) * ∑' m : ℕ,
          (multiplicative_preimage 2 A).indicator erdos_two_shift_weight m := by
        rw [← tsum_mul_left]
        exact tsum_congr hcomp
    _ ≤ (1 / 2 : ℝ) * erdos_two_shift_weight 1 :=
        mul_le_mul_of_nonneg_left hle' (by norm_num)
    _ = erdos_weight 2 := by
        rw [erdos_two_shift_weight_one, erdos_weight, div_mul_div_comm, one_mul]
        norm_num

/-- Public paper statement: TeX Theorem `2-strong`. -/
theorem theorem_2_strong : erdos_strong 2 :=
  two_is_erdos_strong

end MangoldtArxiv
