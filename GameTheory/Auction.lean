import Mathlib

open Nat

/-
This lemma establishes that for any non-zero natural number n, if its minimal factor
is not equal to itself (meaning n is composite), then the square of its minimal
factor is less than or equal to n. This corresponds to the observation in the informal
proof that "there must be a factor of m less than √m".
-/
lemma minFac_sq_le {n: ℕ} (hnezero : n≠ 0) (hn : minFac n ≠ n): (minFac n)^2 ≤  n := by
  -- We use pattern matching on n to handle all possible cases
  match n with
  -- Case 0: Contradicts our assumption that n≠0
  | 0 => contradiction
  -- Case 1: Simplifies the expression as 1 has no proper factors
  | 1 => simp
  -- Case n+2: Handles all numbers ≥ 2
  | n+2 =>
    -- Get the fact that minFac divides n+2
    obtain ⟨r,hr⟩ := Nat.minFac_dvd (n+2)
    -- Pattern match on r to handle different cases of the quotient
    match r with
    -- Case r=0: Impossible as minFac divides n+2
    | 0 => linarith
    -- Case r=1: Would mean minFac = n+2, contradicting our hypothesis
    | 1 => nth_rw 2 [hr] at hn; simp at hn
    -- Case r≥2: Main case for composite numbers
    | r+2 =>
      -- Establish that r+2 divides n+2
      have hh : (r+2) ∣  (n+2) := ⟨minFac (n+2), (by nth_rw 1 [hr,mul_comm])⟩
      -- Show that minFac is less than or equal to r+2
      have hr' : minFac (n+2) ≤ (r+2) := Nat.minFac_le_of_dvd (by linarith) hh
      -- Final calculation showing (minFac n)² ≤ n
      calc
      _ =  (minFac (n+2)) * minFac (n+2) := by ring_nf
      _ ≤ minFac (n+2) * (r+2) := Nat.mul_le_mul_left _ hr'
      _ = _ := hr.symm

/-
This lemma formalizes the first observation in the informal proof: if a number n
is coprime to all numbers m where m² ≤ n (except 0), then n is prime. This essentially
proves that if m is relatively prime to numbers less than √n, then n must be prime.
-/
lemma prime_of_coprime_below_sqrt (n : ℕ) (h1 : 1 < n)
  (h2: ∀ m:ℕ, m^2  ≤  n →  m ≠ 0 → n.Coprime m) : Nat.Prime n :=  by
  -- Convert the goal to use the minFac definition of primality
  rw [Nat.prime_def_minFac]
  -- Proof by contradiction: assume n is not prime
  by_contra H; push_neg at H
  -- If n is not prime, then minFac n ≠ n
  replace H := H (by linarith)
  -- Let m be the minimal factor of n
  let m := minFac n
  -- Establish that n ≠ 1 from h1
  have nneone : n ≠ 1 := by linarith
  -- minFac is always positive
  have mpos := Nat.minFac_pos n
  -- Apply h2 to m (minimal factor)
  -- We know m² ≤ n from minFac_sq_le and m ≠ 0
  replace h2 := h2 (m) (minFac_sq_le (by linarith) H) (by linarith)
  -- Show contradiction: n should not be coprime to its minimal factor
  apply Nat.Prime.not_coprime_iff_dvd.2 ?_ h2
  -- Prove that minFac n divides n
  use (minFac n)
  simp [Nat.minFac_prime nneone,Nat.minFac_dvd]
  -- Complete the proof by showing minFac n divides itself
  exact Nat.dvd_refl n.minFac

/-
This lemma proves the existence of a dyadic interval containing a given ratio b/k.
Specifically, for given natural numbers k and b where 1 ≤ k ≤ b, there exists some i
where b < 2^i * k ≤ 2b. This helps establish dyadic approximations useful in
number theory and algorithms.
-/
lemma exists_dyadic_multiple_in_range {k b : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ b) : ∃ i, b < 2^i * k ∧ 2^i *k ≤ 2* b := by
  -- First prove that b/k is not zero
  have hbk :  b/k ≠ 0 := by
    -- Use the division characterization theorem
    apply Nat.div_ne_zero_iff.2
    constructor
    · -- Prove k ≠ 0 by contradiction
      by_contra h
      rw [h] at h1
      linarith
    · exact h2
  -- Choose i to be log2(b/k) + 1
  use Nat.log2 (b/k) + 1
  constructor
  -- Prove the lower bound: b < 2^i * k
  · have h2bk: (b/k).log2 < (b/k).log2 + 1 := Nat.lt_succ_self _
    replace h2bk := (Nat.log2_lt hbk).1 h2bk
    replace h2bk := succ_le_of_lt h2bk
    calc
    _ < b/k * k + k := lt_div_mul_add (by linarith)
    _ = (b/k+1) *k := by ring
    _ ≤  2 ^((b/k).log2 +1) * k := Nat.mul_le_mul_right k h2bk
  -- Prove the upper bound: 2^i * k ≤ 2b
  · -- First rewrite 2^(log2(b/k) + 1) as 2 * 2^log2(b/k)
    have h2 : 2 ^((b/k).log2 +1)  = 2 * 2^( (b/k).log2 ):=
      by rw [pow_succ _ _,mul_comm]
    rw [h2]
    -- Use the property that 2^log2(x) ≤ x
    have h3 : 2^((b/k).log2) ≤ b/k := Nat.log2_self_le hbk
    rw [mul_assoc]
    apply Nat.mul_le_mul_left 2
    calc
    _ ≤  (b/k) * k := Nat.mul_le_mul_right k h3
    _ ≤ b := by rw [mul_comm]; apply mul_div_le

/-
This lemma extends coprimality from numbers greater than b to all numbers greater than 1.
It uses dyadic intervals to show that if m is coprime to all numbers k where b < k ≤ 2b,
then m is coprime to all numbers k where 1 < k ≤ 2b.
The key insight is using dyadic scaling to relate smaller numbers to larger ones.
-/
lemma coprime_range_extend_down  {m b: ℕ }
  (h: ∀ k, b < k → k ≤ 2*b → Coprime m k) :
   ∀ k, 1 < k →  k ≤ 2 * b → Coprime m k  := by
   -- Take any k satisfying the conditions
   intro k hk1 hk2
   -- Case split on whether k is greater than b
   by_cases hk0 : b < k
   · -- If k > b, directly apply hypothesis h
     exact h k hk0 hk2
   · -- If k ≤ b, need to use dyadic scaling
     push_neg at hk0
     -- Get dyadic interval containing k
     obtain ⟨i, hi1, hi2⟩  :=  exists_dyadic_multiple_in_range (le_of_lt hk1) hk0
     -- Apply hypothesis h to 2^i * k
     have hc := h (2^i *k) hi1 hi2
     -- Use fact that if m is coprime to 2^i * k, then m is coprime to k
     exact Nat.coprime_mul_iff_right.1 hc |>.2

/-
This lemma proves that if m is coprime to all numbers k where b < k ≤ 2b and
m < (2b+1)², then m is prime. It combines the previous coprime_range_extend_down with prime_of_coprime_below_sqrt
to establish primality by showing m is coprime to all numbers up to its square root.
-/
lemma prime_of_coprime_range_sq  {m b: ℕ } (h1 : 1 < m)
  (h: ∀ k,  b < k → k ≤ 2*b → Coprime m k) (h2 : m < (2*b+1)^2):
   Nat.Prime m   := by
    -- Apply coprime_range_extend_down to extend coprimality to all k > 1
    replace h := coprime_range_extend_down h
    -- Use prime_of_coprime_below_sqrt to prove primality
    apply prime_of_coprime_below_sqrt m h1
    -- Need to show m is coprime to all k where k² ≤ m
    intro k hk1 hk2
    -- Handle the case k = 1 separately
    by_cases hk0 : k=1
    · simp [hk0]
    -- For k > 1, use the extended coprimality from coprime_range_extend_down
    push_neg at hk0
    refine h k ?_ ?_
    -- Prove k > 1 using case analysis
    · match k with
      | 0 => exfalso; exact hk2 rfl
      | 1 => exfalso; exact hk0 rfl
      | n+2 => linarith

    -- Show k ≤ 2*b using the bound m < (2b+1)²
    · replace h2 := lt_of_le_of_lt hk1 h2
      rw [pow_two,pow_two] at h2
      replace h2 := Nat.mul_self_lt_mul_self_iff.1 h2
      linarith

/-
This lemma proves that if a ≤ b, b divides c, and c < 2a, then b must equal c.
The proof works by considering the possible quotients when b divides c and showing
that the only possibility satisfying all conditions is when the quotient is 1.
-/
lemma eq_of_dvd_bound_above (a b c : ℕ ) (h : c≠ 0):
  a ≤ b → b ∣ c → c < 2*a → b =c := by
  -- Assume the hypotheses
  intro h1 h2 h3
  -- Get the quotient k where c = b*k
  obtain ⟨k,hk⟩ := h2
  -- Case analysis on k
  match k with
  -- If k = 0, then c = 0, contradicting h
  | 0 => simp at hk; exfalso; exact h hk
  -- If k = 1, then c = b, which is what we want to prove
  | 1 => simp [hk]
  -- If k ≥ 2, derive a contradiction using the bounds
  | k+2 =>
    -- Show that c = b*(k+2) ≥ 2*a
    have hh : 2 * a ≤  c  := by
      calc
      2 * a ≤ 2 * b := by linarith
      _ ≤ 2*b + k * b := by simp
      _ = b *(k+2) := by ring_nf
      _ = c := hk.symm
    -- This contradicts c < 2*a
    linarith

/-
This lemma proves that if b is nonzero and a ≤ a-b, then a must be 0.
The key insight is that for positive a, a-b is always strictly less than a when b≠0,
so a ≤ a-b can only hold when a=0.
-/
lemma eq_zero_of_le_self_sub {a b : ℕ}  : b≠ 0 → a ≤ a-b → a = 0 := by
  -- Take the hypotheses
  intro h1 h2
  -- Case analysis on a
  match a with
  -- If a = 0, we're done
  | 0 => rfl
  -- If a = k+1, derive a contradiction
  | a +1 =>
    -- Show that (a+1)-b < a+1
    have : a+1-b < a+1 := by
      calc
      -- Rewrite using properties of subtraction
      _ =  a - (b-1) := by
        rw [<-Nat.succ_pred h1,Nat.succ_eq_add_one,add_comm b.pred,Nat.sub_add_eq]
        norm_num
      -- Use basic inequalities
      _ ≤ a := by simp
      -- Complete the proof
      _ < _  := by linarith
    -- This contradicts the assumption a ≤ a-b
    linarith

/-
This lemma proves that if b ≤ a and b ≠ 0, then a-b < a.
The proof works by expressing b ≤ a as a = b + c for some c,
then using properties of subtraction and addition.
-/
lemma sub_lt_self_of_pos {a b:ℕ} : b ≤ a → b≠0 → a-b < a := by
  -- Take the hypotheses
  intro h1 h2
  -- Express b ≤ a as a = b + c for some c
  obtain ⟨c,hc⟩ := le_iff_exists_add.1 h1
  -- Rewrite using commutativity and simplify using b ≠ 0
  rw [hc,add_comm]
  simp [Nat.zero_lt_of_ne_zero h2]

/-
This lemma establishes that comparing natural numbers as real numbers
is equivalent to comparing them directly as natural numbers.
It uses the more general result about coercion of ordered types.
-/
lemma Real.coe_lt_coe {a b :ℕ } : (a :ℝ ) < (b: ℝ) ↔ a < b := by
  -- Simplify using the general coercion lemma for ordered types
  simp [WithZero.coe_lt_coe]

/-
This is a solution to IMO 1987 Problem 6. The proof shows that if f(x) = x² + x + p
and f(k) is prime for all k ≤ √(p/3), then f(i) is prime for all i ≤ p-2.

The key strategy is to prove by contradiction that any number in the range
can't be composite by showing it would lead to impossible divisibility conditions.
-/
theorem imo_1987_p6
  (p : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ x, f x = x^2 + x + p)
  (h₁ : ∀ k : ℕ, k ≤ Nat.floor (Real.sqrt (p / 3)) → Nat.Prime (f k)) :
  ∀ i ≤ p - 2, Nat.Prime (f i) := by
  -- Define r as the floor of sqrt(p/3)
  let r := Nat.floor (Real.sqrt (p/3))
  -- Proceed by strong induction on k
  intro k
  apply Nat.case_strong_induction_on k
  · intro; exact h₁ 0 (Nat.zero_le _)
  intro k IH hk
  -- If k+1 ≤ r, use h₁ directly
  by_cases h : k+1 ≤ r
  · exact h₁ (k+1) h
  -- Otherwise, we need to prove it for larger values
  · push_neg at h
    let kk := k+1
    let s := kk - r
    let N := f kk
    -- Express kk in terms of s and r
    have hksr : kk =  s + r := Nat.eq_add_of_sub_eq (le_of_lt h) (by rfl)
    -- Establish key inequalities
    have hs : 1 ≤ s := by
      dsimp [s,kk]; exact Nat.le_sub_of_add_le' h
    -- Series of intermediate inequalities needed
    have ieq1 : s+2 < 4*s+1 := by linarith
    have ieq2 : s^2 ≤ s^2 *4 := by nlinarith
    have ieq3 : 3*r ≤ 6*r*s  := by nlinarith
    have ieq4 : p ≤ 3*r^2 + 6*r + 2 := by
      have ieq5: √ (p/3) < r+1 := Nat.lt_floor_add_one _
      replace ieq5 := Real.lt_sq_of_sqrt_lt ieq5 |> (div_lt_iff₀ (by linarith)).1
      replace ieq5: (p) < (3*r^2 + 6*r +3) := Real.coe_lt_coe.1 <| by
        have casteq: ((r:ℝ)+1)^2 * 3 = ((3*r^2+6*r+3:ℕ):ℝ) := by simp;ring_nf
        rw [<-casteq]
        exact ieq5
      linarith
    -- Establish properties of N (the value we're proving is prime)
    have hN0 : N =  kk^2+kk+p := h₀ kk
    have hN1 : N < (2 * (s + r) +1)^2  := by
      calc
      _ = _:= hN0
      _ ≤  3*r^2 + 6*r + 2 + (r+s)*(r+s+1) := by nlinarith
      _ = 4*r^2 + 2* r*s + s^2 + 7*r+s+2 := by ring_nf
      _ < 4*r^2 +4*s^2 +8*r*s+4*r+4*s+1 := by nlinarith
      _ = _ := by ring
    rw [<-hksr] at hN1
    -- Prove coprimality with all potential factors
    have hP : ∀ i , kk < i → i ≤ 2*(kk) → Coprime N i := by
      by_contra H
      push_neg at H
      obtain ⟨j, hj1,hj2,hj3⟩ := H
      have hj1' : s+r +1 ≤ j := by rw [<-hksr]; apply succ_le_of_lt hj1
      let  ss :=  j-(s+r+1)
      have hss0 : j =  ss + (s+r+1) := Nat.eq_add_of_sub_eq hj1' (by rfl)
      -- Show p ≥ 2
      have hp: 2 ≤ p := Nat.lt_of_sub_ne_zero (by linarith: p-2 ≠ 0) |> le_of_lt
      -- Use induction hypothesis to show f(ss) is prime
      have hss1 : ss ≤ k := by
        apply Nat.le_of_add_le_add_right (b :=s+r+1)
        rw [<-hss0,<-hksr]
        calc
        _ ≤ _ := hj2
        _ = _ := by ring_nf
      replace hss1 : Nat.Prime (f ss) := IH ss hss1 (by linarith)
      -- Express N in terms of f(ss)
      have hfss: N = f ss + (2*kk - j+1) *j := by
        rw [hN0,h₀ ss]
        zify
        rw [Int.natCast_sub hj2,hss0,<-hksr]
        push_cast
        ring_nf
      -- Derive contradiction from divisibility properties
      rw [hfss,Nat.coprime_add_mul_right_left] at hj3
      have hss2 : f ss ∣ j := Nat.Prime.dvd_iff_not_coprime hss1 |>.2 hj3
      have hfss1: p ≤ f ss := by rw [h₀ ss];linarith [sq_nonneg ss]
      have hp1 : p-2 < p := sub_lt_self_of_pos hp (by linarith)
      have hfss2: j < 2*p := by
        calc
        _ ≤ 2*kk := hj2
        _ ≤ 2*(p-2) := by apply Nat.mul_le_mul_left 2; exact hk
        _ < 2*p := by linarith [hp1]
      -- Final contradiction
      have hj : j≠ 0 := by linarith
      have hfss3: f ss = j := eq_of_dvd_bound_above _ _ _ hj hfss1 hss2 hfss2
      rw [h₀ ss,hss0,add_comm _ ss,add_assoc] at hfss3
      replace hfss3 := add_left_cancel hfss3
      have hc1 : p ≤ k + 2 := by
        calc
          p ≤ ss^2 + p := by linarith [pow_two_nonneg ss]
          _ = _ := hfss3
          _ = _ := by rw [<-hksr]
      have hc2: p ≤ p-1 := by
        calc
        _ ≤ _ := hc1
        _ = (k+1) + 1 := by ring_nf
        _ ≤ (p-2)+1 := by linarith
        _ = p-1 := by
          obtain ⟨cc,hcc⟩ := le_iff_exists_add.1 hp
          rw [hcc,add_comm 2 cc];norm_num
            -- Final steps showing contradiction
      have : p = 0 := eq_zero_of_le_self_sub (by simp) hc2
      linarith
    -- Show f(kk) > 1
    have hfk : 1 < f kk := by
      rw [h₀,hksr]
      calc
      _ < 1 + 1 := by decide
      _ ≤ s^2 + s  := by nlinarith [hs]
      _ ≤ s^2 + 2 * r *s + r^2 + s + r + p := by linarith
      _ = _ := by ring
    -- Apply key lemma to conclude f(kk) is prime
    exact prime_of_coprime_range_sq (hfk) hP hN1
