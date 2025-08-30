import Mathlib

section

-- gcd

example (a b c : ℤ) (hdvd : c ∣ a * b) (h_coprime : gcd c a = 1) : c ∣ b := by
  refine Int.dvd_of_dvd_mul_right_of_gcd_one hdvd ?_
  exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h_coprime)))

example {a b c : ℕ} (hdvd : c ∣ a * b) (h_coprime : gcd c a = 1) : c ∣ b := by
  exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime hdvd

/- Lemma, if $a$ and $b$ are coprime, then $a$ divides $x a + y b$. -/
example (a b x y : ℤ) : (gcd a b) ∣  x * a + y * b := by
  refine Dvd.dvd.linear_comb ?_ ?_ x y
  . exact gcd_dvd_left a b
  . exact gcd_dvd_right a b

/- Lemma, if $a$ and $b$ are coprime, then $a$ divides $x a + y b$ if and only if $a$ divides $1$. -/
example (a b x y : ℤ) (h : x * a + y * b = 1) : gcd a b = 1 := by
  have : (gcd a b) ∣ 1 := by
    rw [← h]
    refine Dvd.dvd.linear_comb ?_ ?_ x y
    . exact gcd_dvd_left a b
    . exact gcd_dvd_right a b
  refine Int.eq_one_of_dvd_one ?_ this
  exact Int.zero_le_ofNat (a.gcd b)


example (S : Finset ℕ) (n : ℕ) (h : ∏ x ∈ S, (x : ZMod n) = 1) :
    ∏ x ∈ S, x ≡ 1 [MOD n] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_prod, Nat.cast_one]
  exact h


end


section
-- mod

example (a p : ℤ) (h : a * (-1) ≡ 1 [ZMOD p]) : a ≡ -1 [ZMOD p] := by
  rw [show a * (-1) = -a by ring] at h
  exact Int.neg_modEq_neg.mp h

example (a p n : ℤ) (h : p ∣ n) : a % n % p = a % p := by
  exact Int.emod_emod_of_dvd a h

example (b c : ℕ) (h : b % c = 0) : c * (b / c) = b := by
  refine Nat.mul_div_cancel' ?_
  exact Nat.dvd_of_mod_eq_zero h

example (a b c : ℤ) (h : c ∣ a - b) : a ≡ b [ZMOD c] := by
  rw [Int.modEq_iff_dvd]
  exact dvd_sub_comm.mp h

example (a b c : ℤ) (h : c ∣ b - a) : a ≡ b [ZMOD c] := by
  exact Int.modEq_iff_dvd.mpr h

example (a b c : ℤ) : (a + b) % c = (a % c + b % c) % c := by
  exact Int.add_emod a b c

example (a b : ℤ) : a * b % b = 0 := by
  exact Int.mul_emod_left a b



example (x n : ℕ) (hn_pos : 0 < n) (h : x.gcd n = 1) : ∃ y, x * y % n = 1 % n := by
  by_cases hn : n = 1
  . use 1
    simp_all [Nat.mod_one x]
  obtain ⟨y, hy⟩ := Nat.exists_mul_emod_eq_gcd (show x.gcd n < n by omega)
  use y % n
  have hy_ne_zero : y % n ≠ 0 := by
    by_contra! h_contra
    have : x * y % n = 0 := by
      refine Nat.mod_eq_zero_of_dvd ?_
      suffices : n ∣ y
      . exact Dvd.dvd.mul_left this x
      exact Nat.dvd_of_mod_eq_zero h_contra
    omega
  rw [show 1 % n = 1 by exact Nat.one_mod_eq_one.mpr hn, ← h, ← hy]
  exact Nat.mul_mod_mod x y n


lemma lemma_exist_inverse (x n : ℕ) (hn_pos : 0 < n) (h : x.gcd n = 1) : ∃ y, y ∈ Finset.Icc 1 n ∧ x * y % n = 1 % n := by
  by_cases hn : n = 1
  . use 1
    simp_all [Nat.mod_one x]
  obtain ⟨y, hy⟩ := Nat.exists_mul_emod_eq_gcd (show x.gcd n < n by omega)
  use y % n
  have hy_ne_zero : y % n ≠ 0 := by
    by_contra! h_contra
    have : x * y % n = 0 := by
      refine Nat.mod_eq_zero_of_dvd ?_
      suffices : n ∣ y
      . exact Dvd.dvd.mul_left this x
      exact Nat.dvd_of_mod_eq_zero h_contra
    omega
  constructor
  . simp
    constructor
    . omega
    . apply le_of_lt
      exact Nat.mod_lt y hn_pos
  . rw [show 1 % n = 1 by exact Nat.one_mod_eq_one.mpr hn, ← h, ← hy]
    exact Nat.mul_mod_mod x y n

lemma lemma_dvd_of_mul_and_coprime {a b c : ℤ} (hdvd : c ∣ a * b) (h_coprime : gcd c a = 1) : c ∣ b := by
  refine Int.dvd_of_dvd_mul_right_of_gcd_one hdvd ?_
  exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h_coprime)))


lemma lemma_exist_unique_inverse_in_range
    (x n : ℕ)
    (hn_pos : 0 < n)
    (h : x.gcd n = 1) :
    ∃! y, (y ∈ Finset.Icc 1 n ∧ x * y % n = 1 % n) := by

  by_cases hn : n = 1
  . use 1
    simp [hn]
    exact Nat.mod_one x

  obtain ⟨y, hy⟩ := lemma_exist_inverse x n hn_pos h
  use y
  simp [hy]
  intro z hz_ge hz_le hz_mod
  by_contra! h_contra

  have h1 : (x : ℤ) * (y : ℤ) ≡ 1 [ZMOD n] := by
    obtain ⟨_, hy⟩ := hy
    zify at hy
    exact hy

  have h2 : (x : ℤ) * (z : ℤ) ≡ 1 [ZMOD n] := by
    zify at hz_mod
    exact hz_mod

  have h3 : (x : ℤ) * (y - z) ≡ 0 [ZMOD n] := by
    rw [mul_sub, show (0 : ℤ) = 1 - 1 by ring]
    exact Int.ModEq.symm (Int.ModEq.sub (id (Int.ModEq.symm h1)) (id (Int.ModEq.symm h2)))

  replace h3 : (n : ℤ) ∣ x * ((y : ℤ) - (z : ℤ)) := by
    exact Int.dvd_of_emod_eq_zero h3

  have h4 : (n : ℤ) ∣ (y : ℤ) - (z : ℤ) := by
    have : gcd (x : ℤ) (n : ℤ) = 1 := by
      zify at h
      rw [← h]
      rfl
    replace this : gcd (n : ℤ) (x : ℤ) = 1 := by
      rw [← this]
      exact gcd_comm (n : ℤ) (x : ℤ)
    exact lemma_dvd_of_mul_and_coprime h3 this

  replace h4 : (y : ℤ) ≡ (z : ℤ) [ZMOD n] := by
    rw [Int.modEq_iff_dvd]
    exact dvd_sub_comm.mp h4

  replace h4 : y % n = z % n := by
    exact Int.ofNat_inj.mp h4

  by_cases hy_eq_n : y = n
  . simp [hy_eq_n] at h4
    have ⟨k, hk⟩ : n ∣ z := by exact Nat.dvd_of_mod_eq_zero (id (Eq.symm h4))
    have : k = 1 := by nlinarith
    simp [hk, this, hy_eq_n] at h_contra

  simp at hy
  obtain ⟨⟨hy_ge, hy_le⟩, _⟩ := hy

  have hz_ne_n : z ≠ n := by
    by_contra! hz_eq_n
    simp [hz_eq_n] at h4
    have ⟨k, hk⟩ : n ∣ y := by exact Nat.dvd_of_mod_eq_zero h4
    have : k = 1 := by nlinarith
    simp [hk, this, hz_eq_n] at h_contra

  have hy_eq : y % n = y := by
    have hy_lt_n : y < n := by omega
    exact Nat.mod_eq_of_lt hy_lt_n

  have hz_eq : z % n = z := by
    have hz_lt_n : z < n := by
      omega
    exact Nat.mod_eq_of_lt hz_lt_n

  apply h_contra
  omega

end



section
-- dvd


example (a b : ℕ) (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  apply (Nat.pow_dvd_pow_iff (by norm_num)).mp at h
  exact h


example (a b : ℕ) (h : a ∣ b) : a ^ 2 ∣ b ^ 2 := by
  exact pow_dvd_pow_of_dvd h 2

-- 若一个整数在两个连续整数的平方之间，则他不是完全平方数
example (a x : ℕ) (h1 : a ^ 2 < x) (h2 : x < (a + 1) ^ 2) : ¬ IsSquare x := by
  intro h
  rcases h with ⟨k, hk⟩
  have h3 : a ^ 2 < k ^ 2 := by
    nlinarith [hk]
  have h4 : k ^ 2 < (a + 1) ^ 2 := by
    nlinarith [hk, h2]
  have h5 : a < k := by
    by_contra h
    push_neg at h
    have h6 : k ≤ a := by linarith
    have h7 : k ^ 2 ≤ a ^ 2 := by
      apply Nat.pow_le_pow_left
      all_goals linarith
    nlinarith
  have h8 : k < a + 1 := by
    by_contra h
    push_neg at h
    have h9 : a + 1 ≤ k := by linarith
    have h10 : (a + 1 : ℕ) ^ 2 ≤ k ^ 2 := by
      apply Nat.pow_le_pow_left
      all_goals linarith
    nlinarith
  -- Now we have a < k and k < a + 1, which is a contradiction for natural numbers
  have h11 : k ≤ a := by
    omega
  all_goals omega


-- 若 a | b，且 b 在 x * a 和 (x + 2) * a 之间，则 b = (x + 1) * a
example (a b x : ℕ) (h1 : a ∣ b) (h2 : x * a < b) (h3 : b < (x + 2) * a) : b = (x + 1) * a := by
  rcases h1 with ⟨k, hk⟩
  have h4 : x < k := by
    by_contra h
    push_neg at h
    have h5 : x ≥ k := by omega
    have h6 : x * a ≥ k * a := by
      nlinarith
    have h7 : x * a ≥ k * a := h6
    have h8 : k * a ≤ x * a := by linarith
    have h9 : k * a > x * a := by
      nlinarith [h2, hk]
    linarith
  have h7 : k < x + 2 := by
    by_contra h
    push_neg at h
    have h8 : k ≥ x + 2 := by omega
    have h9 : k * a ≥ (x + 2) * a := by
      nlinarith
    have h10 : k * a ≥ (x + 2) * a := h9
    have h11 : k * a < (x + 2) * a := by
      nlinarith [h3, hk]
    linarith
  have h10 : k = x + 1 := by
    omega
  rw [h10] at hk
  linarith

example (a b c : ℝ) (h : a * b = c * b) (hb : b ≠ 0) : a = c := by
  apply_fun (fun x => x / b) at h
  rw [mul_div_cancel_right₀ _ hb, mul_div_cancel_right₀ _ hb] at h
  exact h


end


section
-- mod

theorem mod_sub_eq {a b : ℕ} {m : ℕ}
    (hm : m > 0) (h1 : a ≥ b) (h2 : a % m ≥ b % m) :
    a % m - b % m = (a - b) % m := by
  trans (a % m - b % m) % m
  . refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact tsub_lt_of_lt (Nat.mod_lt a hm)
  zify
  rw [Nat.cast_sub h2, Nat.cast_sub h1, Int.natCast_emod, Int.natCast_emod]
  exact Eq.symm (Int.sub_emod a b m)

end


section
-- multiset

lemma Multiset_erase_add_singleton {α : Type} [DecidableEq α] (s : Multiset α)
    {a : α} (ha : a ∈ s) :
    (s.erase a) + {a} = s := by
  exact Multiset.add_singleton_eq_iff.mpr ⟨ha, rfl⟩

lemma Multiset_map_erase_add_singleton {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Multiset α) (x : α) (hx : x ∈ s)
    (hf : Function.Injective f) :
    Multiset.map f s = (Multiset.map f (s.erase x)) + {f x} := by
  rw [Multiset.map_erase_of_mem f s hx]
  rw [Multiset_erase_add_singleton]
  exact (Multiset.mem_map_of_injective hf).mpr hx

lemma lemma_finset_card
    (n : ℕ)
    (t k : ℕ)
    (h : k < n) :
    Finset.card {x : Fin n | t ≤ x ∧ x < n - k} = n - k - t := by
  refine Finset.card_eq_of_equiv_fin ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let toFun : { x : Fin n // t ≤ x ∧ x < n - k} → Fin (n - k - t) := by
    intro ⟨x, hx⟩
    use x.val - t
    omega
  apply Equiv.ofBijective toFun ?_
  refine (Function.bijective_iff_existsUnique toFun).mpr ?_
  intro b
  refine Function.Injective.existsUnique_of_mem_range ?_ ?_
  . refine injective_of_lt_imp_ne ?_
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have : x ≠ y := by
      exact Fin.ne_of_lt hxy
    simp [toFun]
    omega
  simp only [Set.mem_range, Subtype.exists, toFun]
  use ⟨b + t, by omega⟩
  simp only [add_tsub_cancel_right, Fin.eta, le_add_iff_nonneg_left, zero_le, true_and, exists_prop,
    and_true]
  omega

lemma Multiset_Icc_erase_left (a b : ℕ) :
    (Multiset.Icc a b).erase a = Multiset.Icc (a + 1) b := by
  have t1 : (Finset.Icc a b).erase a = Finset.Icc (a + 1) b := by
    rw [Finset.Icc_erase_left]
    exact Eq.symm (Finset.Icc_succ_left_eq_Ioc a b)

  have t2 : (Finset.Icc (a + 1) b).val = Multiset.Icc (a + 1) b := by
    exact rfl
  have t3 : ((Finset.Icc a b).erase a).val = (Multiset.Icc a b).erase a := by
    exact rfl
  rw [← t2, ← t3]
  exact congrArg Finset.val t1

lemma Multiset_Icc_erase_right (a b : ℕ) (hb : 0 < b) :
    (Multiset.Icc a b).erase b = Multiset.Icc a (b - 1) := by
  have t1 : (Finset.Icc a b).erase b = Finset.Icc a (b - 1) := by
    rw [Finset.Icc_erase_right]
    exact Eq.symm (Nat.Icc_pred_right a hb)

  have t2 : (Finset.Icc a (b - 1)).val = Multiset.Icc a (b - 1) := by
    exact rfl
  have t3 : ((Finset.Icc a b).erase b).val = (Multiset.Icc a b).erase b := by
    exact rfl
  rw [← t2, ← t3]
  exact congrArg Finset.val t1

lemma Multiset_map_Icc_sub {n : ℕ} {a b : ℕ}
    (hc : b < n)
    (ha : b ≤ a) :
    Multiset.map (fun k ↦ a - k.val) (Multiset.Icc (⟨0, by omega⟩ : Fin n) ⟨b, by omega⟩) =
      Multiset.Icc (a - b) a := by
  refine Eq.symm ((fun {α} {s t} a a_1 ↦ (Multiset.Nodup.ext a a_1).mpr) ?_ ?_ ?_)
  . exact Multiset.nodup_Icc
  . refine Multiset.Nodup.map_on ?_ ?_
    . intro ⟨x, hxlt⟩ hx ⟨y, hylt⟩ hy hxy
      simp at hx hy hxy ⊢
      omega
    . exact Multiset.nodup_Icc
  intro x
  simp
  constructor
  . intro ⟨h1, h2⟩
    use ⟨a - x, by omega⟩
    simp
    omega
  . simp
    intro ⟨y, hy⟩ h1 h2 h3
    simp at h1 h2 h3
    omega

example (s : Multiset ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ s, f x = g x) :
    Multiset.map f s = Multiset.map g s := by
  exact Multiset.map_congr rfl h

example
    (n : ℕ)
    (f : (Fin n) → Prop)
    [DecidablePred f] :
    Fintype.card {i : Fin n // f i} = Finset.card {i : Fin n | f i} := by
  exact Fintype.card_subtype f

example (a b : Multiset ℕ) (x : ℕ) (hx : x ∈ b) :
    (a + b).erase x = a + b.erase x := by
  exact Multiset.erase_add_right_pos a hx

example (a b : Multiset ℕ) (x : ℕ) (hx : x ∈ a) :
    (a + b).erase x = a.erase x + b := by
  exact Multiset.erase_add_left_pos b hx

example (a b c : ℕ) : a + b + c = a + c + b := by
  exact Nat.add_right_comm a b c

end


section
-- logic

example (a b : Prop): ¬a → b ↔ b ∨ a := by
  exact Iff.symm or_iff_not_imp_right

end

example (s : Finset ℕ) (h : ∀ (x : ℕ), x ∉ s) : s.card = 0 := by
  aesop

example (s : Finset ℕ) : 0 < s.card → s.Nonempty := by
  intro h
  exact Finset.card_pos.mp h

example (s : Finset ℕ) (hs : s.card = 0) : s = ∅ := by
  exact Finset.card_eq_zero.mp hs

example (s : Finset ℕ) (hs_card : 2 ≤ s.card) :
    ∃ u ∈ s, ∃ v ∈ s, u ≠ v := by

  have ⟨u, hu_mem⟩ : ∃ u, u ∈ s := by refine Finset.Nonempty.exists_mem (Finset.card_pos.mp (by omega))
  let s' := s.erase u
  have _ : s'.card = s.card - 1 := by exact Finset.card_erase_of_mem hu_mem
  have ⟨v, hv_mem⟩ : ∃ v, v ∈ s' := by refine Finset.Nonempty.exists_mem (Finset.card_pos.mp (by omega))
  use u, hu_mem, v
  aesop

section
-- Partition

example (a b : ℕ) (s : Multiset ℕ) (hlt : a < b) :
    (s.filter (fun x => x < a)).card ≤ (s.filter (fun x => x < b)).card := by
  refine Multiset.card_le_card ?_
  apply Multiset.monotone_filter_right
  omega


end


section
-- Partition

open Finset Nat Std List

open Multiset
open BigOperators Partition Nat List
open Function YoungDiagram

example {α : Type} (s : Finset α) : s.attach.toSet = Set.univ := by
  exact Finset.coe_attach s


-- 辅助结论1
lemma utils_1
    {i j a b z : ℕ}
    (hiz : 2 ^ i * a = z)
    (hjz : 2 ^ j * b = z)
    (h_a_odd : Odd a)
    (h_b_odd : Odd b) :
    a = b := by
  have h1 : 2 ^ i * a = 2 ^ j * b := by
    linarith
  by_cases h2 : i ≤ j
  · -- Assume i ≤ j
    have h3 : i ≤ j := h2
    have h4 : 2 ^ i * a = 2 ^ j * b := h1
    have h5 : 2 ^ j * b = 2 ^ i * (2 ^ (j - i) * b) := by
      have h10 : i + (j - i) = j := by omega
      calc
        2 ^ j * b = 2 ^ (i + (j - i)) * b := by rw [show i + (j - i) = j by omega]
        _ = (2 ^ i * 2 ^ (j - i)) * b := by ring
        _ = 2 ^ i * (2 ^ (j - i) * b) := by ring
    rw [h5] at h4
    have h11 : a = 2 ^ (j - i) * b := by
      have h12 : 2 ^ i > 0 := by positivity
      have h13 : 2 ^ i * a = 2 ^ i * (2 ^ (j - i) * b) := by linarith
      have : a = 2 ^ (j - i) * b := by
        apply (mul_left_inj' (show 2 ^ i ≠ 0 by positivity)).mp
        linarith
      assumption
    by_cases h14 : j - i > 0
    · -- Assume j - i > 0
      have h15 : ¬ Odd a := by
        have h16 : (a : ℕ) % 2 = 0 := by
          have h17 : (2 ^ (j - i) : ℕ) % 2 = 0 := by
            have h18 : j - i > 0 := h14
            have h19 : j - i ≥ 1 := by omega
            have h21 : ∀ k : ℕ, 2 ^ (k + 1) % 2 = 0 := by
              intro k
              induction k with
              | zero => norm_num
              | succ k ih =>
                simp [pow_add] at ih ⊢
            have h22 : ∃ k : ℕ, j - i = k + 1 := by
              refine ⟨j - i - 1, by omega⟩
            rcases h22 with ⟨k, hk⟩
            rw [show j - i = k + 1 by omega]
            apply h21 k
          have h16 : (a : ℕ) % 2 = 0 := by
            rw [show a = 2 ^ (j - i) * b by linarith [h11]]
            have h17 : (2 ^ (j - i) * b : ℕ) % 2 = 0 := by
              simp [Nat.mul_mod, h17]
            omega
          omega
        have h18 : a % 2 = 1 := by
          rcases h_a_odd with ⟨m, hm⟩
          omega
        omega
      tauto
    · -- Assume j - i ≤ 0
      have h19 : j - i = 0 := by omega
      have h20 : i = j := by omega
      have h21 : a = b := by
        have h4 : 2 ^ i * a = 2 ^ j * b := h1
        rw [show j = i by omega] at h4
        have h22 : 2 ^ i > 0 := by positivity
        have h23 : 2 ^ i * a = 2 ^ i * b := by linarith
        have : a = b := by
          apply (mul_left_inj' (show 2 ^ i ≠ 0 by positivity)).mp
          linarith
        assumption
      exact h21
  · -- Assume i > j
    have h3 : i > j := by omega
    have h4 : 2 ^ i * a = 2 ^ j * b := h1
    have h5 : 2 ^ i * a = 2 ^ j * (2 ^ (i - j) * a) := by
      have h6 : i - j + j = i := by omega
      calc
        2 ^ i * a = 2 ^ (i - j + j) * a := by rw [show i - j + j = i by omega]
        _ = (2 ^ (i - j) * 2 ^ j) * a := by ring
        _ = 2 ^ j * (2 ^ (i - j) * a) := by ring
    rw [h5] at h4
    have h7 : 2 ^ (i - j) * a = b := by
      have h8 : 2 ^ j > 0 := by positivity
      have h9 : 2 ^ j * (2 ^ (i - j) * a) = 2 ^ j * b := by linarith
      have : 2 ^ (i - j) * a = b := by
        apply (mul_left_inj' (show 2 ^ j ≠ 0 by positivity)).mp
        linarith
      assumption
    have h10 : i - j > 0 := by omega
    have h11 : (b : ℕ) % 2 = 0 := by
      have h12 : (2 ^ (i - j) * a : ℕ) % 2 = 0 := by
        have h13 : (2 ^ (i - j) : ℕ) % 2 = 0 := by
          have h14 : i - j > 0 := h10
          have h15 : i - j ≥ 1 := by omega
          have h21 : ∀ k : ℕ, 2 ^ (k + 1) % 2 = 0 := by
            intro k
            induction k with
            | zero => norm_num
            | succ k ih =>
              simp [pow_add] at ih ⊢
          have h22 : ∃ k : ℕ, i - j = k + 1 := by
            refine ⟨i - j - 1, by omega⟩
          rcases h22 with ⟨k, hk⟩
          rw [show i - j = k + 1 by omega]
          apply h21 k
        have h14 : (2 ^ (i - j) * a : ℕ) % 2 = 0 := by
          simp [Nat.mul_mod, h13]
        assumption
      have h13 : (b : ℕ) = (2 ^ (i - j) * a : ℕ) := by
        linarith [h7]
      rw [h13]
      omega
    have h12 : b % 2 = 1 := by
      rcases h_b_odd with ⟨m, hm⟩
      omega
    omega


-- 构造映射（odds 映射到一个新的 Multiset，其实就是 distincts）
def glaisher_odd_to_distinct_parts {p_parts : Multiset ℕ} (h_part_pos : ∀ {x}, x ∈ p_parts → 0 < x) : Multiset ℕ :=
  p_parts.toFinset.attach.biUnion (
    fun ⟨x, hx⟩ => (
      let m := p_parts.count x
      let f : ℕ → ℕ := fun i => 2 ^ i * x
      have f_inj : Function.Injective f := by
        unfold f
        intro i j h_eq
        have hx_pos : 0 < x := h_part_pos (mem_toFinset.mp hx)
        simp at h_eq
        omega
      m.bitIndices.toFinset.map ⟨f, f_inj⟩
    )
  ) |>.val


-- 证明和相等
lemma glaisher_odd_to_distinct_parts_sum {n : ℕ} {p : Partition n} (h_odd : ∀ i ∈ p.parts, Odd i) :
    (glaisher_odd_to_distinct_parts p.parts_pos).sum = n := by
  conv_rhs => rw [p.parts_sum.symm]
  unfold glaisher_odd_to_distinct_parts
  rw [sum_val, sum_biUnion]
  . simp only [id_eq, sum_map, Embedding.coeFn_mk]
    simp_rw [← sum_mul, twoPowSum_toFinset_bitIndices]
    rw [Finset.sum_attach p.parts.toFinset (fun x => (Multiset.count x p.parts) * x)]
    exact (sum_multiset_count p.parts).symm
  . rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
    have h_ne : a ≠ b := by
      simp_all only [Finset.coe_attach, Set.mem_univ, ne_eq, Subtype.mk.injEq, not_false_eq_true]
    apply Finset.disjoint_left.mpr
    rintro z hza hzb
    simp only [Finset.mem_map, List.mem_toFinset, Embedding.coeFn_mk] at hza hzb
    obtain ⟨i, hi, hiz⟩ := hza
    obtain ⟨j, hj, hjz⟩ := hzb
    have h_a_odd : Odd a := h_odd a (mem_toFinset.mp ha)
    have h_b_odd : Odd b := h_odd b (mem_toFinset.mp hb)
    have hz_pos : 0 < z := by
      rw [← hiz]
      apply mul_pos (Nat.two_pow_pos i) (Odd.pos h_a_odd)
    have : a = b := by
      exact utils_1 hiz hjz h_a_odd h_b_odd
    exact h_ne this

-- 证明映射后仍然都是正数
lemma glaisher_odd_to_distinct_parts_pos {n : ℕ} {p : Partition n} :
    ∀ {x}, x ∈ (glaisher_odd_to_distinct_parts p.parts_pos) → 0 < x := by
  unfold glaisher_odd_to_distinct_parts
  intro x hx
  simp at hx
  obtain ⟨part, ⟨h_part_mem, _⟩, ⟨_, _, hx⟩⟩ := hx
  have h_part_pos : 0 < part := p.parts_pos h_part_mem
  rw [← hx]
  positivity


end



section
-- series

example
    (n : ℕ) (hn : 1 < n)
    (x : ℕ → ℝ)
    (h_x_zero : ∃ i < n, x i ≠ 0)
    (h_sumx_eq_zero : ∑ i ∈ Finset.range n, x i = 0) :
    (∃ (c : ℝ), ∀ i ∈ Finset.range (n - 1), x (i + 1) - x i = c) ↔
      ∃ (r : ℝ), r ≠ 0 ∧ ∀ i ∈ Finset.range n, x i = r * (2 * i - n + 1) := by

  constructor
  . intro ⟨c, hc⟩

    have h_x_i : ∀ i ∈ Finset.range n, x i = (c / 2) * (2 * i - (n - 1)) := by
      have h_x_i_of_x0 : ∀ i ∈ Finset.range n, x i = x 0 + c * i := by
        intro i hi
        induction i with
        | zero =>
          norm_num
        | succ i ih =>
          simp only [Finset.mem_range] at hi
          specialize hc i (by simp only [Finset.mem_range]; omega)
          specialize ih (by simp only [Finset.mem_range]; omega)
          simp only [Nat.cast_add, Nat.cast_one]
          linarith only [hc, ih]
      intro i hi
      have h1 : x i = x 0 + c * ↑i := by
        apply h_x_i_of_x0
        simpa using hi
      have eq1 : ∀ (i : ℕ), i < n → x i = x 0 + c * (↑i : ℝ) := by
        intro i hi
        specialize h_x_i_of_x0 i (by simp; omega)
        simpa using h_x_i_of_x0
      have h3 : ∑ i ∈ Finset.range n, x i = (n : ℝ) * x 0 + c * (∑ i ∈ Finset.range n, (i : ℝ)) := by
        calc
          ∑ i ∈ Finset.range n, x i = ∑ i ∈ Finset.range n, (x 0 + c * (↑i : ℝ)) := by
            apply Finset.sum_congr
            · rfl
            · intro i hi
              specialize eq1 i (by simp at hi; omega)
              linarith
          _ = (n : ℝ) * x 0 + c * (∑ i ∈ Finset.range n, (i : ℝ)) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      have h4 : ∑ i ∈ Finset.range n, (i : ℝ) = (↑n * (↑n - 1) / 2 : ℝ) := by
        have h5 : ∀ (k : ℕ), ∑ i ∈ Finset.range k, (i : ℝ) = (↑k * (↑k - 1) / 2 : ℝ) := by
          intro k
          induction k with
          | zero =>
            simp
          | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            field_simp at *
            ring_nf
        specialize h5 n
        simpa using h5
      rw [h3] at h_sumx_eq_zero
      rw [h4] at h_sumx_eq_zero
      have eq3 : x 0 = -c * ((↑n - 1) / 2 : ℝ) := by
        have hn_nz : (n : ℝ) ≠ 0 := by
          positivity
        have h7 : x 0 + c * ((↑n - 1) / 2 : ℝ) = (0 : ℝ) := by
          apply (mul_left_inj' hn_nz).mp
          linarith
        linarith only [h7]
      rw [h1]
      rw [eq3]
      ring_nf

    have h_c_ne_zero : c ≠ 0 := by
      by_contra! h_contra
      rw [h_contra] at hc
      have : ∀ i ∈ Finset.range n, x i = x 0 := by
        intro i
        induction i with
        | zero =>
          simp
        | succ i ih =>
          intro hi
          simp at hi
          specialize ih (by rw [Finset.mem_range]; omega)
          specialize hc i (by rw [Finset.mem_range]; omega)
          linarith only [ih, hc]
      have hx0 : x 0 = 0 := by
        have : ∑ i ∈ Finset.range n, x i = ∑ i ∈ Finset.range n, x 0 :=
          Finset.sum_congr rfl this
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        rw [this] at h_sumx_eq_zero
        have : (n : ℝ) ≠ 0 := by
          norm_cast
          omega
        exact eq_zero_of_ne_zero_of_mul_left_eq_zero this h_sumx_eq_zero
      obtain ⟨k, ⟨hklt, hxkzero⟩⟩ := h_x_zero
      specialize this k (by rw [Finset.mem_range]; omega)
      rw [this] at hxkzero
      contradiction

    use c / 2
    constructor
    . -- c / 2 ≠ 0
      positivity
    . -- ∀ i ∈ Finset.range n, x i = c / 2 * (2 * ↑i - ↑n + 1)
      convert h_x_i using 1
      ring_nf

  . intro ⟨d, ⟨h_d_ne_zero, hd⟩⟩
    use 2 * d
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hd _ (by simp; omega), hd _ (by simp; omega), Nat.cast_add, Nat.cast_one]
    ring

end


section
-- rational

#check Rat.div_int_inj

example {a b c d : ℤ}
    (hb : 0 < b)
    (hd : 0 < d)
    (h1 : a.gcd b = 1)
    (h2 : c.gcd d = 1)
    (heq : (a / b : ℚ) = (c / d : ℚ)) :
    a = c ∧ b = d := by
  exact Rat.div_int_inj hb hd h1 h2 heq

example {m n : ℤ} (hpos : 0 < m ∧ 0 < n) (hcoprime : IsCoprime m n)
    (hfraction : (m / n : ℚ) = 13 / 4) :
    m = 13 ∧ n = 4 := by
  replace hcoprime : m.natAbs.gcd n.natAbs = 1 := by
    exact Int.isCoprime_iff_gcd_eq_one.mp hcoprime
  exact Rat.div_int_inj hpos.2 zero_lt_four hcoprime (by norm_num) hfraction

end

section
-- digits

#eval Nat.ofDigits 2 [0, 1]
#eval Nat.digits 2 3
#eval Nat.digits 2 6

-- digits_base_mul
example {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
    b.digits (b * m) = 0 :: b.digits m := by
  rw [Nat.digits_def' hb (by positivity)]
  simp [Nat.mul_div_right m (by positivity)]

-- ofDigits_reverse_cons
example {b : ℕ} (l : List ℕ) (d : ℕ) :
    Nat.ofDigits b (d :: l).reverse = Nat.ofDigits b l.reverse + b^l.length * d := by
  simp only [List.reverse_cons]
  rw [Nat.ofDigits_append]
  simp

example (k : ℕ) :
    Nat.ofDigits 2 (Nat.digits 2 (k * 2)).reverse =
    Nat.ofDigits 2 (Nat.digits 2 k).reverse := by

  have l_digits_base_mul {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
      b.digits (b * m) = 0 :: b.digits m := by
    rw [Nat.digits_def' hb (by positivity)]
    simp [Nat.mul_div_right m (by positivity)]

  have l_ofDigits_reverse_cons {b : ℕ} (l : List ℕ) (d : ℕ) :
      Nat.ofDigits b (d :: l).reverse = Nat.ofDigits b l.reverse + b^l.length * d := by
    simp only [List.reverse_cons]
    rw [Nat.ofDigits_append]
    simp

  rcases Nat.eq_zero_or_pos k with hk | hk
  . norm_num [hk]
  rw [mul_comm k 2, l_digits_base_mul one_lt_two hk]
  rw [l_ofDigits_reverse_cons]
  rw [mul_zero, add_zero]


example (k : ℕ) (hk : 0 < k) :
    Nat.ofDigits 2 (Nat.digits 2 (4 * k + 1)).reverse =
    2 * Nat.ofDigits 2 (Nat.digits 2 (2 * k + 1)).reverse - Nat.ofDigits 2 (Nat.digits 2 k).reverse := by

  have l_digits_base_mul {b m : ℕ} (hb : 1 < b) (hm : 0 < m) :
      b.digits (b * m) = 0 :: b.digits m := by
    rw [Nat.digits_def' hb (by positivity)]
    convert Nat.mul_div_right m (Nat.zero_lt_of_lt hb)
    simp

  have l_ofDigits_reverse_cons {b : ℕ} (l : List ℕ) (d : ℕ) :
      Nat.ofDigits b (d :: l).reverse = Nat.ofDigits b l.reverse + b^l.length * d := by
    simp only [List.reverse_cons]
    rw [Nat.ofDigits_append]
    simp

  have h1 : Nat.digits 2 (4 * k + 1) = 1 :: Nat.digits 2 (2 * k) := by
    convert Nat.digits_add 2 one_lt_two 1 (2 * k) one_lt_two (by omega) using 2
    ring

  have h1' : Nat.digits 2 (2 * k) = 0 :: Nat.digits 2 k := by
    refine l_digits_base_mul one_lt_two hk

  have h2 : Nat.digits 2 (2 * k + 1) = 1 :: Nat.digits 2 k := by
    convert Nat.digits_add 2 one_lt_two 1 k one_lt_two (by omega) using 2
    ring

  conv =>
    lhs
    rw [h1, h1']
    rw [l_ofDigits_reverse_cons, l_ofDigits_reverse_cons]
    rw [mul_zero, add_zero, mul_one]

  conv =>
    rhs
    rw [h2, l_ofDigits_reverse_cons, mul_one]

  have : (0 :: Nat.digits 2 k).length = (Nat.digits 2 k).length + 1 := by
    exact rfl
  rw [this, Nat.pow_add_one]
  omega


end

section

def k : ℕ := 12312321

-- def ff (k : ℕ) : Prop := Nat.ofDigits 2 (Nat.digits 2 (4 * k + 3)).reverse = 3 * Nat.ofDigits 2 (Nat.digits 2 (2 * k + 1)).reverse - 2 * Nat.ofDigits 2 (Nat.digits 2 k).reverse

#eval Nat.ofDigits 2 (Nat.digits 2 (4 * k + 1)).reverse
#eval 2 * Nat.ofDigits 2 (Nat.digits 2 (2 * k + 1)).reverse - Nat.ofDigits 2 (Nat.digits 2 k).reverse

#eval Nat.ofDigits 2 (Nat.digits 2 (4 * k + 3)).reverse


#eval Nat.ofDigits 2 (Nat.digits 2 (4 * k + 1)).reverse = 2 * Nat.ofDigits 2 (Nat.digits 2 (2 * k + 1)).reverse - Nat.ofDigits 2 (Nat.digits 2 k).reverse
#eval Nat.ofDigits 2 (Nat.digits 2 (4 * k + 3)).reverse = 3 * Nat.ofDigits 2 (Nat.digits 2 (2 * k + 1)).reverse - 2 * Nat.ofDigits 2 (Nat.digits 2 k).reverse

end


section
-- sum

-- sum i
example (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
  exact Finset.sum_range_id n

-- sum i (real)
example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  have h1 : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      all_goals ring_nf
  specialize h1 n
  simpa using h1

-- sum sq
example {n : ℕ} : ∑ i ∈ Finset.range n, (2 * i - n + 1 : ℝ) ^ 2 = n * (n + 1) * (n - 1) / 3 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    calc
      _ = ∑ x ∈ Finset.range n, (2 * x - n + 1 - 1 : ℝ) ^ 2 + n ^ 2 := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        congr 1
        . apply Finset.sum_congr rfl
          intro x hi
          ring
        . ring
      _ = _ := by
        simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ih]
        simp only [mul_one, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_pow, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right]
        have : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
          have h1 : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              field_simp at *
              all_goals ring_nf
          specialize h1 n
          simpa using h1
        rw [this]
        ring_nf

example (h : Fin 3 → ℝ) : ∑ i ∈ .univ, h i = h 0 + h 1 + h 2 := by
  exact Fin.sum_univ_three h

example
    {n : ℕ} (hn : n ≠ 0)
    {x : ℕ → ℝ} :
    ∑ i ∈ Finset.range n, (x i - (∑ i ∈ Finset.range n, x i) / n) = 0 := by
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ (by norm_cast)]
  rw [sub_self]

example {f : ℕ → ℝ} {k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.range (2 * k), f i =
      (∑ i ∈ Finset.range k, f i) + (∑ i ∈ Finset.Ico k (2 * k), f i) := by
  refine Eq.symm (Finset.sum_range_add_sum_Ico f (by omega))

example (f : ℕ → ℝ) (a b c : ℕ) :
    ∑ x ∈ Finset.Ico a b, f (c + x) = ∑ x ∈ Finset.Ico (a + c) (b + c), f x := by
  exact Finset.sum_Ico_add f a b c

end


section
-- number theory

#check Rat

example {x : ℝ} (hx : ¬ Irrational x) : ∃ y : ℚ, y = x := by
  unfold Irrational at hx
  tauto

example {x : ℚ} : x = x.num / x.den := by
  exact Eq.symm (Rat.num_div_den x)

example {a : ℤ} {b : ℕ} (h : a.natAbs.Coprime b) : IsCoprime a b := by
  exact Int.isCoprime_iff_gcd_eq_one.mpr h

example {x : ℝ} (hx : ¬ Irrational x) : ∃ p q : ℤ, x = p / q ∧ IsCoprime p q := by
  have ⟨y, hy⟩ : ∃ y : ℚ, y = x := by
    unfold Irrational at hx
    tauto
  use y.num, y.den
  split_ands
  . rw [← hy, ← Rat.num_div_den y]
    norm_cast
    simp only [Rat.divInt_ofNat, Rat.mkRat_num_den']
  . exact Int.isCoprime_iff_gcd_eq_one.mpr y.reduced

end


section
-- mod

example (n : ℕ) (hn : 1 < n) : 1 % n = 1 := by
  exact Nat.mod_eq_of_lt hn

example (a b : ℕ) (hb : b ≠ 0) : ⌊(a / b : ℝ)⌋ = (a - a % b) / b := by

  sorry


lemma l_period (a n : ℕ) (ha : 0 < a) (hn : 1 < n)
    (hcop : a.Coprime n) :
    (fun (x : ℕ) => ((a ^ x) % n)).Periodic n.totient := by

  have h0 : 1 ≤ a ^ n.totient := by exact Nat.pow_pos ha

  have h1 (k : ℕ) : a ^ n.totient % n = 1 := by
    have ⟨t, ht⟩ : n ∣ a ^ n.totient - 1 := by
      apply (Nat.modEq_iff_dvd' ?_).mp
      . exact (Nat.ModEq.pow_totient hcop).symm
      . exact h0
    replace ht : a ^ n.totient = n * t + 1 := by omega
    rw [ht]
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
    exact Nat.mod_eq_of_lt hn

  dsimp [Function.Periodic]
  intro x
  rw [pow_add, Nat.mul_mod, h1 n, mul_one, Nat.mod_mod_of_dvd _ (Nat.dvd_refl n)]


end


section

lemma l_odd_pow_injective {n : ℕ} (hn : Odd n) : Function.Injective (· ^ n : ℤ → ℤ) :=
  hn.strictMono_pow.injective

example (k : ℕ) : (2 * k + 1) / 2 = k := by
  omega

example (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 (n + 1), f i = (∑ i ∈ Finset.Icc 1 n, f i) + f (n + 1) := by
  refine Finset.sum_Icc_succ_top ?_ f
  omega

end


section
-- image

#check Function.Bijective
#check Set.InjOn
#check Function.Injective


example
    (f : ℕ → ℕ)
    (hfinj : f.Injective)
    (s : Finset ℕ) :
    (Finset.image f s).card = s.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact hfinj hxy


example (f g : ℕ → ℕ)
    (hf : f.Injective)
    (hg : g.Injective) :
    (f ∘ g).Injective := by
  exact Function.Injective.comp hf hg

example (f g : ℕ → ℕ) :
    f ∘ g = (fun x => f (g x)) := by
  rfl

example :
    (fun (j : ℕ) => (12 * j) ^ 2).Injective := by

  have h1 : (fun (x : ℕ) => x ^ 2).Injective := by
    exact Nat.pow_left_injective two_ne_zero

  have h2 : (fun j => 12 * j).Injective := by
    exact mul_right_injective₀ (show 12 ≠ 0 by norm_num)

  exact Function.Injective.comp h1 h2

example : (Finset.image (fun j => (12 * j) ^ 2) (Finset.Icc 1 83)).card = 83 := by

  have h_inj : (fun (j : ℕ) => (12 * j) ^ 2).Injective := by
    have h1 : (fun (x : ℕ) => x ^ 2).Injective := by
      exact Nat.pow_left_injective two_ne_zero

    have h2 : (fun j => 12 * j).Injective := by
      exact mul_right_injective₀ (show 12 ≠ 0 by norm_num)

    exact Function.Injective.comp h1 h2


  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact h_inj hxy

example (a b : ℕ) : (Finset.Icc a b).card = b + 1 - a := by
  rw [Nat.card_Icc]

example (n : ℕ) : (Finset.Icc 1 n).card = n  := by
  rw [Nat.card_Icc]
  rw [Nat.add_sub_cancel]

end


section
-- totient

#check Nat.totient

#check Nat.ModEq.pow_totient

end


section
-- tan

open Real

lemma l_eq_of_strictMonoOn_eq {l r a b: ℝ} {f : ℝ → ℝ}
    (hfsmono : StrictMonoOn f (Set.Ioo l r))
    (ha : a ∈ Set.Ioo l r) (hb : b ∈ Set.Ioo l r) (hab : f a = f b) :
    a = b := by
  rcases eq_or_ne a b with h | h
  . exact h
  . rcases lt_or_gt_of_ne h with h | h
    . apply hfsmono ha hb at h
      linarith only [h, hab]
    . apply hfsmono hb ha at h
      linarith only [h, hab]

example (x : ℝ) (hx_tan : tan x = -1)
    (h_bounds : 0 < x ∧ x < 3 * π / 2) :
    x = 3 * π / 4 := by

  have : 0 < x ∧ x < π := by
    by_contra h_contra
    rw [not_and_or] at h_contra
    rcases h_contra with h_contra | h_contra
    . tauto
    . rw [not_lt] at h_contra
      obtain ⟨h_pos, h_lt⟩ := h_bounds
      have : 0 ≤ tan x := by
        suffices : 0 ≤ tan (x - π)
        . rwa [tan_sub_pi] at this
        . apply tan_nonneg_of_nonneg_of_le_pi_div_two
          <;> linarith
      norm_num [hx_tan] at this

  have hy_tan : tan (x - π / 2) = 1 := by
    rw [show x - π / 2 = -(π / 2 - x) by ring, tan_neg,
        tan_pi_div_two_sub,
        hx_tan]
    norm_num

  rw [← tan_pi_div_four] at hy_tan

  have h_y_bounds : x - π / 2 ∈ Set.Ioo (- (π / 2)) (π / 2) := by
    constructor <;> linarith

  suffices : x - π / 2 = π / 4
  . linarith only [this]
  . refine l_eq_of_strictMonoOn_eq strictMonoOn_tan h_y_bounds ?_ hy_tan
    rw [Set.mem_Ioo]
    constructor <;> linarith


end


section
-- rpow (confused)

#check Real.rpow
#check HPow.hPow


open Real

example (a b : ℝ) : a ^ 3 = b ^ 3 → a = b := by
  intro h
  rcases pow_eq_pow_iff_cases.mp h with h | h | h
  . contradiction
  . exact h
  . simp [Nat.not_even_iff.mpr] at h

example (a : ℝ) : a ^ (3 : ℝ) = a ^ 3 := by
  exact rpow_ofNat a 3

example (r : ℝ) : log r = log (-r) := by
  exact (log_neg_eq_log r).symm

example : rexp 0 = 1 := by
  exact exp_zero

example : (-1 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by
  rw [rpow_def_of_neg (by norm_num)]
  rw [show 1 / 3 * π = π / 3 by ring_nf, cos_pi_div_three]
  rw [log_neg_eq_log, log_one, zero_mul, exp_zero]
  rw [one_mul]


example : (-8 : ℝ) ^ (1 / 3 : ℝ) = 1 := by
  rw [rpow_def_of_neg (by norm_num)]
  rw [show 1 / 3 * π = π / 3 by ring_nf, cos_pi_div_three]
  rw [log_neg_eq_log, show (8 : ℝ) = 2 ^ 3 by ring, log_pow]
  conv => lhs; norm_cast
  ring_nf
  rw [exp_log (by norm_num)]
  ring

#check rexp

example (r : ℝ) (hr : r < 0)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3) : r ^ 3 + 1 / r ^ 3 = 5778 := by
  set x : ℝ := r ^ (1 / 3 : ℝ) with hx

  have l_eq_of_cube_eq_cube (a b : ℝ) (h : a ^ 3 = b ^ 3) : a = b := by
    rcases pow_eq_pow_iff_cases.mp h with h | h | h
    . contradiction
    . exact h
    . simp [Nat.not_even_iff.mpr] at h

  have h_xne0 : x < 0 := by
    rw [hx]
    have : r ^ (1 / 3 : ℝ) = - (-r) ^ (1 / 3 : ℝ) := by
      rw [rpow_def_of_neg hr, rpow_def_of_pos (by linarith only [hr])]
      rw [show 1 / 3 * π = π / 3 by ring_nf, cos_pi_div_three]
      rw [show log r = log (-r) by rw [log_neg_eq_log]]


      #check cos_pi_div_three
      apply l_eq_of_cube_eq_cube

      #check Real.rpow_inv_natCast_pow
      conv => lhs; rw [show r = -1 * (-r) by ring]


      sorry
    #check mul_rpow
    sorry

  replace h₀ : x ^ 2 - 3 * x + 1 = 0 := by
    apply_fun (· * x) at h₀
    field_simp at h₀

    sorry


  sorry

end


section
-- prime

example (p : ℕ) : p.Prime → 0 < p := by
  intro h
  exact Nat.Prime.pos h

example (p k : ℕ) : p.Prime → 0 < p ^ k := by
  intro h
  refine Nat.pow_pos ?_
  exact Nat.Prime.pos h

example (n : ℕ) : (∃ p r : ℕ, p.Prime ∧ 2 ≤ r ∧ n = p ^ r) → ¬ n.Prime := by
  intro ⟨p, r, hpp, hr, h⟩
  rw [h]
  exact Nat.Prime.not_prime_pow hr

end


section
-- mean inequality

example (n : ℕ) (hn : n > 0) (a : Fin n → ℝ) (h : ∀ i, 0 ≤ a i) :
    (∏ i, a i) ^ ((1 : ℝ) / n) ≤ (∑ i, a i) / n := by
  let s : Finset (Fin n) := .univ
  let w : Fin n → ℝ := fun x => (1 : ℝ) / n

  have hw_sum : ∑ i ∈ s, w i = 1 := by
    rw [Finset.sum_const]
    suffices : s.card = n
    . rw [this]
      field_simp
    exact Finset.card_fin n

  convert Real.geom_mean_le_arith_mean_weighted s w a (by simp [w]) hw_sum (by simp [h])
  . rw [Real.finset_prod_rpow]
    simp [h]
  . simp_rw [w, div_eq_mul_inv, one_mul, mul_comm, Finset.sum_mul, s]


end

section
-- multiset

lemma l_in_product {α β : Type*}
    {a : α} {b : β}
    {s1 : Finset α} {s2 : Finset β}
    (ha : a ∈ s1) (hb : b ∈ s2) :
    (a, b) ∈ s1.product s2 := by
  simp only [Finset.product, Finset.mem_mk]
  have : {(a, b)} = (Finset.product {a} {b}).val := by rfl
  apply Multiset.singleton_subset.mp
  rw [this]
  apply Finset.product_subset_product
  <;> simp only [Finset.singleton_subset_iff, ha, hb]

end


section
-- poly

open Polynomial


lemma cubic_factor {a b c : ℝ} {u v w : ℝ}
    (hroots : (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w}) :
    X ^ 3 + C a * X ^ 2 + C b * X + C c = (X - C u) * (X - C v) * (X - C w) := by
  let p : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c
  have h1 : p.natDegree = 3 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have h2 : Multiset.card p.roots = p.natDegree := by
    simp [p, hroots, h1]
  convert (C_leadingCoeff_mul_prod_multiset_X_sub_C h2).symm using 1
  rw [leadingCoeff, h1]
  simpa [p, hroots] using by ring


lemma cubic_vieta
    {a b c : ℝ} (u v w : ℝ)
    (hroots : (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w}) :
      a = -(u + v + w) ∧
      b = (u * v + v * w + w * u) ∧
      c = -(u * v * w) := by

  have h_expand : (X - C u) * (X - C v) * (X - C w) = X ^ 3 + C (-(u + v + w)) * X ^ 2 + C (u * v + v * w + w * u) * X + C (-(u * v * w)) := by
    simpa only [C_neg, C_add, C_mul] using by ring

  have h_factor := cubic_factor hroots
  rw [h_expand] at h_factor

  split_ands
  <;> [apply_fun (·.coeff 2) at h_factor;
        apply_fun (·.coeff 1) at h_factor;
        apply_fun (·.coeff 0) at h_factor]
  all_goals
    convert h_factor
    all_goals
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num


lemma cubic_roots_nodup_multiset
    (a b c : ℝ) (u v w : ℝ) (f : ℝ → ℝ)
    (hf : f = fun (x : ℝ) => x ^ 3 + a * x ^ 2 + b * x + c)
    (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (hu : f u = 0)
    (hv : f v = 0)
    (hw : f w = 0) :
    (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w} := by

  simp only [hf] at hu hv hw

  let p : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c

  have h_pdegree : p.natDegree = 3 := by simp only [p]; compute_degree!

  have h_pnezero : p ≠ 0 := by
    simp [p]
    refine leadingCoeff_ne_zero.mp ?_
    simp [p, leadingCoeff, h_pdegree]

  have h_card : p.roots.card ≤ 3 := by
    convert card_roots' p
    simp [h_pdegree]

  refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ h_card)
  refine (Multiset.le_iff_subset ?_).mpr ?_
  . simp
    tauto
  . simp [h_pnezero, p, hu, hv, hw]

end


section
-- comm

example (a b c : ℝ) : a + b = c → a = c - b := by
  intro h
  exact eq_sub_of_add_eq h

-- asb community
example (a b : ℝ) : |a - b| = |b - a| := by
  exact abs_sub_comm a b

end

section
-- sum_range

open Finset

example {n : ℕ} : (2 * n) - (∑ i ∈ range (2 * n - 1), (-1 : ℝ) ^ i * ((2 * n - 1) - i) / (i + 2)) =
    (2 * n + 1) * (∑ i ∈ range (2 * n), (-1 : ℝ) ^ i * 1 / (i + 1)) := by
  rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
  . simp [hn_zero]

  have l_1 (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, f (i + 1) = (∑ i ∈ range (n + 1), f i) - f 0 := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ _ (n + 1)]
      ring

  have l_2 (n : ℕ) : 0 = ∑ i ∈ range (2 * n), (-1 : ℝ) ^ i := by
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [mul_add, mul_one, sum_range_succ, sum_range_succ, ← ih, pow_add]
      ring

  specialize l_1 (fun i => (-1 : ℝ) ^ (i + 1) * ((2 * n - 1) - (i - 1)) / (i + 1)) (2 * n - 1)
  have t1 : ∀ (x : ℝ), x + 1 + 1 = x + 2 := by
    intro x
    ring
  have t2 : ∀ x, (-1 : ℝ) ^ (x + 1 + 1) = (-1 : ℝ) ^ x := by
    intro x
    rw [add_assoc, pow_add, neg_one_pow_two, mul_one]
  simp_rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, t1, t2] at l_1
  rw [l_1, Nat.sub_add_cancel (by omega),
      sub_eq_iff_eq_add,
      mul_sum, ← add_sub_assoc, ← sum_add_distrib]
  apply eq_sub_of_add_eq

  convert l_2 n
  . ring
  . field_simp
    ring


example (n : ℕ) (hn : 0 < n) : (2 * n) - (∑ i ∈ range n, (2 * i + 1 : ℝ) / (n + 1 + i)) =
    (2 * n + 1) * (∑ i ∈ range n, (1 : ℝ) / (n + 1 + i)) := by
  rw [sub_eq_iff_eq_add]
  rw [mul_sum, ← sum_add_distrib]
  trans ∑ i ∈ range n, 2
  . rw [sum_const, card_range]
    ring
  . rw [Finset.sum_congr rfl]
    intro i hi
    field_simp
    ring


example (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, f (i + 1) = (∑ i ∈ range (n + 1), f i) - f 0 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ _ (n + 1)]
    ring

example (n : ℕ) : ∑ i ∈ range (2 * n), (-1 : ℝ) ^ i * 1 / (i + 1) =
    ∑ i ∈ range n, (1 : ℝ) / (n + 1 + i) := by
  have l_1 (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, f (i + 1) = (∑ i ∈ range (n + 1), f i) - f 0 := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ _ (n + 1)]
      ring
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    conv => lhs; rw [mul_add, sum_range_succ, sum_range_succ, ih]
    symm
    calc
      _ = (∑ i ∈ range (n + 2), (1 : ℝ) / (n + 1 + i)) - (1 : ℝ) / (n + 1) := by
        specialize l_1 (fun t => (1 : ℝ) / (n + 1 + t)) (n + 1)
        convert l_1 using 3
        . norm_cast
          ring
        . norm_num
      _ = (∑ i ∈ range n, (1 : ℝ) / (n + 1 + i)) + (1 : ℝ) / (2 * n + 1) + (1 : ℝ) / (2 * n + 2) - (1 : ℝ) / (n + 1) := by
        rw [sum_range_succ, sum_range_succ]
        congr 3
        . congr 1
          ring
        . norm_cast
          ring
      _ = _ := by
        rw [add_sub_assoc]
        congr
        . simp
        . norm_cast
        . simp [pow_add, pow_mul]
          field_simp
          ring

end


section
-- injective

example : Function.Injective fun (t : ℝ) => t / 2 := by
  refine mul_left_injective₀ ?_
  norm_num

example : Function.Injective fun (t : ℝ) => (2 - t) / 2 := by
  apply Function.injective_iff_hasLeftInverse.mpr
  unfold Function.HasLeftInverse Function.LeftInverse
  use fun (t : ℝ) => -(t * 2) + 2
  simp

end

section
-- dvd

open Nat

example (a b c : ℕ) (hb : b ≠ 0) (h : b ∣ a) : a / b * c = (a * c) / b := by
  obtain ⟨k, hk⟩ := h
  rw [hk, mul_div_cancel_left₀ _ hb, mul_assoc, mul_div_cancel_left₀ _ hb]

example (n : ℕ) : 2 ^ n * n ! ∣ (2 * n)! := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have t1 : 2 ^ (n + 1) * (n + 1)! = 2 ^ n * n ! * (2 * n + 2) := by
      rw [factorial_succ]
      ring
    have t2 : (2 * (n + 1)) ! = (2 * n) ! * (2 * n + 1) * (2 * n + 2) := by
      rw [mul_add, factorial_succ, factorial_succ]
      ring
    rw [t1, t2]
    apply (mul_dvd_mul_iff_right (by positivity)).mpr
    exact Dvd.dvd.mul_right ih (2 * n + 1)




end


section

#eval padicValNat 2 10
#check factorization
#check factorization_mul
#check Nat.factorization
#check Nat.factorization_mul

#check Nat.pow_left_injective
#check Nat.pow_right_injective

example (a b c : ℕ) (hc : 0 < c) : a ^ c = b ^ c → a = b := by
  intro h
  apply Nat.pow_left_injective (by linarith) h

example (n a b: ℕ) (ha:0<a) (h: n^a=60^b) :
    ∃ k, n = 60^k := by
  have h_fact_3 : (60 ^ b).factorization 3 = b := by
    simp [Nat.factorization_pow, show Nat.factorization 60 3 = 1 by native_decide]
  simp [← h, Nat.factorization_pow] at h_fact_3
  obtain ⟨k, hk⟩ : a ∣ b := Dvd.intro _ h_fact_3
  rw [hk, mul_comm, pow_mul] at h
  use k
  apply Nat.pow_left_injective (by linarith) h

example {n a b : ℕ} (ha : 0 < a)
    (h : n ^ a = 60 ^ b) (hk : b = a * k) :
    ∃ t, n = 60 ^ t := by
  use k
  rw [hk] at h
  have h1 : n ^ a = (60 ^ k) ^ a := by
    rw [h]
    ring_nf
  have cancelexp : n = (60 ^ k) := by
    --apply Nat.pow_right_injective (by linarith) h1
    apply Nat.pow_left_injective (by linarith) h1
  exact cancelexp

end


section

open Polynomial


example (p : ℝ[X]) (hp : p = X^2 + C 3 * X + C 1) (a b : ℝ)
    (hroots : p.roots = {a, b}) : a + b = -3 := by

  have hp_natDegree : p.natDegree = 2 := by
    rw [hp]
    compute_degree!

  have hp_roots_card : p.roots.card = p.natDegree := by
    rw [hp_natDegree, hroots, Multiset.card_pair]

  have t1 : p.coeff 1 = 3 := by
    simp_rw [hp, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
    norm_num

  have t2 : p.leadingCoeff = 1 := by
    rw [leadingCoeff, hp_natDegree]
    simp_rw [hp, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num

  have := coeff_eq_esymm_roots_of_card hp_roots_card (k := 1) (by norm_num [hp_natDegree])
  norm_num [t1, t2, hp_natDegree] at this
  rw [this, hroots, Multiset.esymm, add_comm]
  simp [show Multiset.powersetCard 1 {b} = {{b}} by rfl]


end


section

example {p : ℕ} (hp : p.primeFactors = {5}) (hp_pos : 0 < p) :
    ∃ t : ℕ, p = 5 ^ t := by
  sorry

end

section

example (x : ℤ)
    (h1 : 3+x ≡ 2^2 [ZMOD 3^3])
    (h2 : 5+x ≡ 3^2 [ZMOD 5^3])
    (h3 : 7+x ≡ 5^2 [ZMOD 7^3]) :
    x ≡ 4 [ZMOD 105] := by
  -- deduce x=4 mod 3 from h1
  have h1' : x ≡ 4 [ZMOD 3] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h1
    omega
  -- deduce x=4 mod 5 from h2
  have h2' : x ≡ 4 [ZMOD 5] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h2
    omega
  -- deduce x=4 mod 7 from h3
  have h3' : x ≡ 4 [ZMOD 7] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h3
    omega
  -- combine above results, get x=4 mod 105
  have : x ≡ 4 [ZMOD 3*5] := by
    rw [← Int.modEq_and_modEq_iff_modEq_mul (by norm_num)]
    exact ⟨h1', h2'⟩
  rw [show (105 : ℤ) = 3*5*7 by norm_num]
  rw [← Int.modEq_and_modEq_iff_modEq_mul (by norm_num)]
  exact ⟨this, h3'⟩


end


section

open Real

/- Calculate the sum of the geometric series $1+\left(\frac{1}{5}\right)+\left(\frac{1}{5}\right)^2 + \left(\frac{1}{5}\right)^3 + \dots$. Express your answer as a common fraction. -/
theorem algebra_15301 : ∑' n : ℕ, (1 / 5 : ℝ)^n = 5 / 4 := by
  rw [tsum_geometric_of_lt_one]
  <;> linarith

theorem algebra_15301' : ∑' n : ℕ, (1 / 5 : ℚ)^n = 5 / 4 := by
  rw [tsum_geometric_of_norm_lt_one]
  . norm_num
  . simp
    have : ‖(5 : ℚ)‖ = 5 := by
      refine mem_sphere_zero_iff_norm.mp ?_
      refine Metric.mem_sphere.mpr ?_
      rw [← Rat.dist_cast 5 0]
      simp
    norm_num [this]

theorem algebra_15301'' : ∑' n : ℕ, (1 / 5 : ℚ)^n = 5 / 4 := by
  rw [tsum_geometric_of_norm_lt_one]
  . norm_num
  . simp
    have : ‖(5 : ℚ)‖ = 5 := by
      rw [← sub_zero 5, ← dist_eq_norm, ← Rat.dist_cast]
      simp
    norm_num [this]

example {n : ℕ} {x : ℕ → ℝ}
    (h_x_mono : Monotone x) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, |x i - x j| =
    2 * (∑ i ∈ Finset.range n, ((2 * i - n + 1) * x i)) := by

  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have t1 : ∑ j ∈ Finset.range n, |x n - x j| = (n * x n) - ∑ j ∈ Finset.range n, x j := by
      have : ∀ i ∈ Finset.range n, x i ≤ x n := by
        intro i hi
        rw [Finset.mem_range] at hi
        exact h_x_mono (Nat.le_of_succ_le hi)
      calc
        _ = ∑ j ∈ Finset.range n, (x n - x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [abs_eq_self, sub_nonneg, this i hi]
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib, ih,
      sub_self, abs_zero, add_zero, abs_sub_comm _ (x n),
      add_assoc, ← two_mul, t1, ← mul_add,
      Nat.cast_add, Nat.cast_one]
    rw [← add_comm_sub, ← Finset.sum_sub_distrib]
    congr 2
    . apply Finset.sum_congr rfl
      intro i hi
      ring
    . ring

end


section
-- linear_combination

example {x y : ℝ} (h₀ : x + y = 9) (h₁ : x * y = 10) :
    x ^ 3 + y ^ 3 = 459 := by
  linear_combination (x ^ 2 - 1 * x * y + y ^ 2 + 9 * x + 9 * y + 81) * h₀ - 27 * h₁


end


section
-- finset

open Finset

example (a b : Finset ℤ) :
    #(a ∪ b) = #a + #b - #(a ∩ b) := by
  exact card_union a b

example (s : Finset ℤ) (f g : ℤ → Prop) [DecidablePred f] [DecidablePred g] :
    {x ∈ s | f x ∨ g x} = {x ∈ s | f x} ∪ {x ∈ s | g x} := by
  exact filter_or f g s

example (s : Finset ℤ) (f g : ℤ → Prop) [DecidablePred f] [DecidablePred g] :
    {x ∈ s | f x ∧ g x} = {x ∈ s | f x} ∩ {x ∈ s | g x} := by
  exact filter_and f g s

example (x y : ℤ) (a b : Finset ℤ) (hx : x ∈ a) (hy : y ∈ b) :
    (x, y) ∈ a.product b := by
  apply mem_product.mpr ⟨hx, hy⟩

end

section

open Finset

lemma helper2 (n k: ℕ) (hk : k ≠ 0): #({x ∈ range (n + 1) | k ∣ x}) = n / k + 1 := by
  trans #((range (n / k + 1)).image (k * ·))
  · congr; ext x; simp [dvd_def]
    constructor
    · rintro ⟨h1, ⟨l, rfl⟩⟩
      refine ⟨l, ?_, rfl⟩
      rw [Nat.lt_add_one_iff]
      rw [Nat.le_div_iff_mul_le, mul_comm]
      . exact Nat.le_of_lt_succ h1
      . apply hk.bot_lt
    · rintro ⟨l, hl, rfl⟩
      refine ⟨?_, ⟨_, rfl⟩⟩
      rw [Nat.lt_add_one_iff] at hl
      rw [Nat.le_div_iff_mul_le, mul_comm] at hl
      . exact Order.lt_add_one_iff.mpr hl
      . apply hk.bot_lt
  · rw [Finset.card_image_of_injOn]
    · simp
    · intro x hx y hy hxy
      simpa [hk] using hxy


end


section
-- algebra

example (a b : ℚ) (c : ℕ) : a + √ 10 = b + √ c → a = b := by
  intro h
  by_contra! h_contra
  have heq : √ c = a - b + √ 10 := by
    linarith only [h]

  apply_fun (·) ^ 2 at heq
  simp [add_sq, Real.sq_sqrt] at heq
  have hr : Irrational ((a - b) ^ 2 + 2 * (a - b) * √ 10 + 10) := by
    norm_cast
    apply irrational_add_intCast_iff.mpr
    apply irrational_ratCast_add_iff.mpr
    apply irrational_ratCast_mul_iff.mpr
    constructor
    . refine mul_ne_zero (two_ne_zero) (sub_ne_zero_of_ne h_contra)
    . native_decide

  simp only [← heq, Nat.not_irrational] at hr


end


section
-- inequalities

-- 三角不等式（用 Minkowski 不等式证）
example (a b c d x y : ℝ) : √((a - c) ^ 2 + (b - d) ^ 2) ≤ √((x - a) ^ 2 + (y - b) ^ 2) + √ ((x - c) ^ 2 + (y - d) ^ 2) := by
  convert Real.Lp_add_le (.univ) ![x - a, y - b] ![c - x, d - y] one_le_two using 1
  all_goals
    simp [Real.sqrt_eq_rpow]
    ring_nf


end


section

#eval 1 + 1
#check StrictAntiOn

example {f : ℝ → ℝ} {m : ℤ}
    (hf : f = fun x => x ^ m)
    (hdesc : StrictAntiOn f (Set.Ioi 0)) :
    ∀ x > 0, deriv f x < 0 := by
  intro x hx

  sorry

end


section
-- number_theory

-- 若质数 p 整除 n 的阶乘，那么 $p \le n$
example (p n : ℕ) (hdvd : p ∣ n.factorial) : p.Prime → p ≤ n := by
  intro hpp
  exact (Nat.Prime.dvd_factorial hpp).mp hdvd

-- 对于质数 p，p 不整除 (p-1)!
example (p : ℕ) (hpp : p.Prime) : ¬ p ∣ (p - 1).factorial := by
  by_contra!
  have := (Nat.Prime.dvd_factorial hpp).mp this
  have : 2 ≤ p := by exact Nat.Prime.two_le hpp
  omega

example (a : ℕ) : (a + 1) * a.factorial = (a + 1).factorial := by
  exact rfl

-- 小于 c 的两个不同的数之积，整除 c 的阶乘
example (a b c : ℕ) : 0 < a → a < b → b ≤ c → a * b ∣ c.factorial := by
  rintro h1 h2 h3
  have : a * b ∣ b.factorial := by
    rw [mul_comm, ← Nat.mul_factorial_pred (by omega)]
    apply Nat.mul_dvd_mul_left b
    exact Nat.dvd_factorial h1 (by omega)
  apply this.trans
  exact Nat.factorial_dvd_factorial h3
end


section

example (a b : ℝ) : 1 / (a * b) = (1 / a) * (1 / b) := by
  exact div_mul_eq_div_mul_one_div 1 a b

example (a : ℝ) (n : ℕ) : 1 / (a ^ n) = (1 / a) ^ n := by
  exact Eq.symm (one_div_pow a n)

example : ∑' i, ((1 / 2 : ℝ) ^ i) = 2 := by
  exact tsum_geometric_two

example : ∑' i, ((1 / 2017 : ℝ) ^ i) = 2017 / 2016 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

example (a b c : ℝ) (hc : c ≠ 0) : a / b = (a * c) / (b * c) := by
  exact Eq.symm (mul_div_mul_right a b hc)

end


section
-- mod

example (a b c : ℕ) : (a * b) % c = (a % c * b % c) % c := by
  simp only [Nat.mod_mul_mod, dvd_refl, Nat.mod_mod_of_dvd]

example (a b : ℕ) (hb : 0 < b) : a % b < b := by
  exact Nat.mod_lt a hb

end

section

example (a b c : ℝ) : c ≠ 0 → a * c = b * c → a = b := by
  intro hc h
  exact (mul_left_inj' hc).mp h

example (a b : ℝ) : 0 < a → a ^ b * a ^ (-b) = 1 := by
  intro ha
  calc
    _ = a ^ (b + -b) := by
      refine Eq.symm (Real.rpow_add ha b (-b))
    _ = a ^ (0 : ℝ) := by
      rw [add_neg_cancel]
    _ = 1 := by
      exact Real.rpow_zero a

end


section
-- inequalities

example (a b : ℝ) : 2 * a ≤ 2 * b → a ≤ b := by
  intro h
  linarith

example (a b c : ℝ) (hc : 0 < c) : a ≤ b → a / c ≤ b / c := by
  intro h
  exact (div_le_div_iff_of_pos_right hc).mpr h

example (a b c : ℝ) (hb : 0 < b) : a < c * b → a / b < c := by
  intro h
  exact (div_lt_iff₀ hb).mpr h

example (a b c : ℝ) (hc : 0 < c) : a < b → a * c < b * c := by
  intro h
  exact (mul_lt_mul_iff_of_pos_right hc).mpr h

-- 小于等于推出根号小于等于
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ b → √ a ≤ √ b := by
  intro h
  exact (Real.sqrt_le_sqrt_iff hb).mpr h

-- 小于推出根号小于
example (a b : ℝ) (ha : 0 ≤ a) : a < b → √ a < √ b := by
  intro h
  exact Real.sqrt_lt_sqrt ha h

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 → a = b := by
  intro h
  apply_fun (√ ·) at h
  convert h
  <;> field_simp

end



section

-- lemma tmplemma {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by
--   aesop

#check Nat.factorization
#eval Nat.factorization 60 5

example : True := by
  have l_1 {x : ℕ} : x ≤ x + 1 := by omega
  have l_2 : ∀ ⦃x : ℕ⦄, x ≤ x + 1 := by omega
  -- specialize l_2 x
  -- 这里我想得到 2 ≤ 2 + 1，由于前面 l_2 的参数 x 是隐式的，所以无法 `specialize l_2 x`，不得不手写一个 have statement。
  -- 手写 have statement 比较繁琐，这在自己写或是自动化证明过程中都想避免
  -- 有没有办法使用元编程实现隐参数传递
  -- 可以的话，我希望能给当前环境中所有形如 ∀ ⦃x : α⦄, f x 的 statement 都 apply 一下 x
  have : 2 ≤ 2 + 1 := by
    apply l_2
  trivial

example {a : ℕ} : True := by
  have l_1 : ∀ ⦃x : ℕ⦄, x ≤ x + 1 := by simp
  have hidden_apply {f : ℕ → Prop} (x : ℕ) : (∀ ⦃t : ℕ⦄, f t) → f x := by aesop

  apply hidden_apply a at l_1

  -- 可以写一个这样的引理来实现
  -- 但问题在 apply_all 的时候，类似 True 这样的东西会被循环而出问题
  -- 可不可以写成像 specialize 那样先判断 statement 形式再决定是否 apply
  apply hidden_apply a
  apply hidden_apply a
  apply hidden_apply a
  apply hidden_apply a
  simp only [implies_true]

end


section
-- analysis

-- On the other hand, $k$ can be arbitrarily close to $1 + \sqrt{2}$
example (ε : ℝ) (h_eps_pos : 0 < ε) :
    ∃ a b : ℕ, 0 < b ∧ b < a ∧
    |(a : ℝ) / b - (1 + √ 2)| < ε := by

  sorry

-- For any ε > 0 and A > 0, there exists d > 0 such that if |x - √A| < d, then x + A/x < 2√A + ε. This shows x + A/x approaches 2√A as x approaches √A.
example (ε A : ℝ) (h_eps_pos : 0 < ε) :
    ∃ d, 0 < d ∧ ∀ x,
    |x - √ A| < d →
    x + A / x < 2 * √ A + ε := by
  sorry

end



section
-- set

open Nat Finset


#check card_le_card_biUnion
#check Set.PairwiseDisjoint

example (n : ℕ) (a : Fin n → Finset ℕ)
    (A : Finset ℕ) (hA : A = Icc 1 15)
    (M : Finset ℕ) (h_subset : M ⊆ A)
    (h_disj : ∀ i j, i ≠ j → a i ∩ a j = ∅)
    (h_sub : ∀ i, a i ⊆ A)
    (h_nsub : ∀ i, ¬ a i ⊆ M) :
    #M ≤ 15 - n := by
  let B := A \ M
  let b : Fin n → Finset ℕ := fun i => a i ∩ B
  let C := Finset.univ.biUnion b

  have r1 : ∀ i, b i ≠ ∅ := by
    intro i
    specialize h_sub i
    specialize h_nsub i
    dsimp [b, B]
    -- tauto_set
    sorry

  have r2 : ∀ i j, i ≠ j → b i ∩ b j = ∅ := by
    intro i j hij
    specialize h_disj i j hij
    dsimp [b, B]
    -- tauto_set
    sorry

  have r3 : #(Finset.univ : Finset (Fin n)) ≤ #C := by
    dsimp [C, b]
    apply card_le_card_biUnion
    . unfold Set.PairwiseDisjoint Set.Pairwise
      intro x hx y hy hxy
      exact disjoint_iff_inter_eq_empty.mpr (r2 x y hxy)
    . intro i hi
      exact nonempty_iff_ne_empty.mpr (r1 i)
  simp only [Finset.card_univ, Fintype.card_fin] at r3

  have t0 : #M ≤ #A := by
    exact card_le_card h_subset
  have : C ⊆ B := by
    -- tauto_set
    sorry
  have t1 : #C ≤ #B := by
    exact card_le_card this
  have t2 : #B = #A - #M := by
    exact card_sdiff h_subset
  have t3 : #A = 15 := by
    simp only [hA, card_Icc, reduceAdd, Nat.add_one_sub_one]
  rw [t3] at t0
  rw [t2, t3] at t1
  have : n ≤ 15 - #M := by
    calc
      _ ≤ #C := r3
      _ ≤ 15 - #M := t1
  omega

end


section
-- number_theory

-- lemma, if $x, y \in [1, q]$, and $x mod q = y mod q$ then $x = y$.
lemma l_unique (q x y : ℕ) : (1 ≤ x ∧ x ≤ q ∧ 1 ≤ y ∧ y ≤ q) → x % q = y % q → x = y := by
  rintro ⟨hx1, hx2, hy1, hy2⟩ hmod
  rcases Nat.eq_or_lt_of_le hx2 with hx | hx
  <;> rcases Nat.eq_or_lt_of_le hy2 with hy | hy
  . rw [hx, hy]
  . rw [Nat.mod_eq_of_lt hy, hx, Nat.mod_self q] at hmod
    omega
  . rw [Nat.mod_eq_of_lt hx, hy, Nat.mod_self q] at hmod
    omega
  . convert hmod
    <;> simp only [Nat.mod_eq_of_lt, hx, hy]

lemma l_notdvd_sub_one (x p : ℕ) (hp : 1 < p) (hx : 1 ≤ x) : p ∣ x → ¬ p ∣ (x - 1) := by
  intro h
  by_contra!
  have : p ∣ x - (x - 1) := by exact Nat.dvd_sub h this
  rw [Nat.sub_sub_self hx] at this
  apply Nat.eq_one_of_dvd_one at this
  omega

lemma l_notdvd_add_one (x p : ℕ) (hp : 1 < p) : p ∣ x → ¬ p ∣ (x + 1) := by
  intro h
  by_contra!
  have : p ∣ x + 1 - x := by exact Nat.dvd_sub this h
  rw [Nat.add_sub_cancel_left] at this
  apply Nat.eq_one_of_dvd_one at this
  omega

lemma l_padicValNat_factor_pos (n p : ℕ) (hn : n > 1) (hp : p ∈ n.primeFactors) : 1 ≤ padicValNat p n := by
  have : Fact p.Prime := by
    refine fact_iff.mpr ?_
    exact Nat.prime_of_mem_primeFactors hp
  apply one_le_padicValNat_of_dvd (by linarith)
  exact Nat.dvd_of_mem_primeFactors hp

lemma l_notdvd_pow (x p d : ℕ) (hd : 1 ≤ d) : ¬ p ∣ x → ¬ p ^ d ∣ x := by
  intro h
  by_contra!
  apply h
  exact Nat.dvd_of_pow_dvd hd this

lemma l_dvd_pow_of_dvd_mul_coprime {p d a b : ℕ} (ha : a ≠ 0)  (hp : p.Prime) : (¬ p ∣ b) → p ^ d ∣ a * b → p ^ d ∣ a := by
  intro h1 h2
  have : Fact p.Prime := by exact { out := hp }
  have hb : b ≠ 0 := by
    by_contra!
    simp only [this, dvd_zero, not_true_eq_false] at h1
  have : d ≤ padicValNat p (a * b) := by
    refine (padicValNat_dvd_iff_le ?_).mp h2
    exact mul_ne_zero ha hb
  rw [padicValNat.mul ha hb,
      padicValNat.eq_zero_of_not_dvd h1,
      add_zero] at this
  exact (padicValNat_dvd_iff_le ha).mpr this

lemma prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : ∏ p ∈ n.primeFactors, p ^ padicValNat p n = n := by
  convert Nat.factorization_prod_pow_eq_self hn
  apply Finset.prod_congr
  . exact Nat.support_factorization n
  intro p hp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  simpa using by congr; rw [Nat.factorization_def _ hp.1]

example (a b c : ℕ) : a ≡ b [MOD c] → a % c = b % c := by exact fun a => a

open Function in
example (a s : ℕ → ℕ) (l : List ℕ) :
    List.Pairwise (Nat.Coprime on s) l → { k // ∀ i ∈ l, k ≡ a i [MOD s i] } := by
  exact fun a_1 => Nat.chineseRemainderOfList a s l a_1

open Function in
example (a s : ℕ → ℕ) (l : List ℕ)
    (co : List.Pairwise (Nat.Coprime on s) l) {z : ℕ} (hz : ∀ i ∈ l, z ≡ a i [MOD s i]) :
    z ≡ ↑(Nat.chineseRemainderOfList a s l co) [MOD (List.map s l).prod] := by
  exact Nat.chineseRemainderOfList_modEq_unique a s l co hz

open Function in
example (a s : ℕ → ℕ) (t : Finset ℕ) (hs : ∀ i ∈ t, s i ≠ 0)
    (pp : (t : Set ℕ).Pairwise (Nat.Coprime on s)) : { k // ∀ i ∈ t, k ≡ a i [MOD s i] } := by
  exact Nat.chineseRemainderOfFinset a s t hs pp

open Function in
example (a s : ℕ → ℕ) (t : Finset ℕ) (hs : ∀ i ∈ t, s i ≠ 0)
    (co : (t : Set ℕ).Pairwise (Nat.Coprime on s))
    {z : ℕ} (hz : ∀ i ∈ t, z ≡ a i [MOD s i]) :
    z ≡ ↑(Nat.chineseRemainderOfFinset a s t hs co) [MOD ∏ i ∈ t, s i] := by
  sorry

open Function in
example (a s : ℕ → ℕ) (t : Finset ℕ) (hs : ∀ i ∈ t, s i ≠ 0) (co : (t : Set ℕ).Pairwise (Nat.Coprime on s)) {z : ℕ} (hz : ∀ i ∈ t, z ≡ a i [MOD s i]) : z ≡ ↑(Nat.chineseRemainderOfFinset a s t hs co) [MOD ∏ i ∈ t, s i] := by
  have h₁ : ∀ i ∈ t, z ≡ a i [MOD s i] := hz
  have h₂ : (t : Set ℕ).Pairwise (Nat.Coprime on s) := co
  have h₃ : ∀ i ∈ t, s i ≠ 0 := hs
  -- Use the Chinese Remainder Theorem for Finsets to find a solution modulo the product of the moduli.
  have h₄ : z ≡ ↑(Nat.chineseRemainderOfFinset a s t hs co) [MOD ∏ i ∈ t, s i] := by
    -- Use the properties of modular arithmetic and the Chinese Remainder Theorem to establish the congruence.
    sorry
  exact h₄

#check Nat.chineseRemainder
#check Nat.chineseRemainderOfFinset
#check Nat.chineseRemainderOfList
#check Nat.chineseRemainder_modEq_unique
#check Nat.chineseRemainderOfList_modEq_unique
--#check Nat.chineseRemainderOfFinset_modEq_unique

#check Nat.factorization

#check Nat.chineseRemainder
#check Nat.chineseRemainderOfFinset

#check Fin.val_eq_val

example (x p d : ℕ) (hd : 1 ≤ d) : p ^ d ∣ x → p ∣ x := by
  intro h
  exact Nat.dvd_of_pow_dvd hd h

example (x p d : ℕ) (hd : 1 ≤ d) : ¬ p ∣ x → ¬ p ^ d ∣ x := by
  intro h
  by_contra!
  apply h
  exact Nat.dvd_of_pow_dvd hd this


example (n p : ℕ) (hn : n > 1) (hp : p ∈ n.primeFactors) (Fact : Nat.Prime p) : 1 ≤ padicValNat p n := by
  sorry

-- 双射
#check Function.Bijective

-- 单射
#check Function.Injective

-- 满射
#check Function.Surjective

#check Nat.bijective_iff_surjective_and_card


section
-- set

example (a b c : ℝ) : a + b + c = a + c + b := by
  exact add_right_comm a b c

example (n : ℕ) (hn : 3 < n) : Finset.range n = Finset.range 3 ∪ Finset.Ico 3 n := by
  rw [Finset.range_eq_Ico]
  refine Eq.symm (Finset.Ico_union_Ico_eq_Ico ?_ ?_)
  <;> omega

example (a b : Finset ℕ) : (a ∪ b) \ {3} = (a \ {3}) ∪ (b \ {3}) := by
  exact Finset.union_sdiff_distrib a b {3}

example (a b : Finset ℕ) : Disjoint a b → Disjoint a (b \ {3}) := by
  intro h
  exact Disjoint.disjoint_sdiff_right h

example {n : ℕ} : Finset.Ico 3 n \ {3} = (Finset.Ico 3 n).erase 3 := by
  exact Finset.sdiff_singleton_eq_erase 3 (Finset.Ico 3 n)

example (n : ℕ) : Finset.Ico 3 n \ {3} = Finset.Ico 4 n := by
  rw [Finset.sdiff_singleton_eq_erase 3 (Finset.Ico 3 n)]
  exact Eq.symm Nat.Ico_succ_left_eq_erase_Ico

end



section
-- triangle

open Real

example (x : ℝ) : cos x ^ 2 + sin x ^ 2 = 1 := by
  exact cos_sq_add_sin_sq x

end


section
-- inequality (simple)

example (a b : ℝ) : a - b ≥ 0 → a ≥ b := by
  intro h
  exact sub_nonneg.mp h

example (a b : ℝ) : 0 ≤ a → a + b ≥ b := by
  intro h
  exact le_add_of_nonneg_left h

example (a b : ℝ) : |a * b| ≤ |a| * |b| := by
  apply abs_le_of_sq_le_sq
  . simp only [mul_pow, sq_abs, le_refl]
  . positivity

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  exact abs_sub_abs_le_abs_sub a b


end


section
-- finset

example (alphabet : Set Char) (ha : alphabet = {'A', 'B', 'C'}) :
    (Set.univ : Set (alphabet × alphabet × alphabet)).ncard = 27 := by
  -- Make a tree-diagram for all three-letter code words starting with $A$.
  -- Each path from the top to the bottom contains 3 letters,
  -- which is one of the code words beginning with $A$.
  -- There are 9 such code words.
  -- Clearly, there are 9 code words starting with $B$ and 9 starting with $C$.
  -- In all, there are $\boxed{27}$ code words.
  have : alphabet.Finite := by simp [ha]
  have : Fintype alphabet := this.fintype
  have alphabet_card : Fintype.card alphabet = 3 := by simp [ha]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_univ, Finset.card_univ,
    Fintype.card_prod, Fintype.card_prod, alphabet_card]

end


section
-- inequality

-- the minimum is at most the geometric mean.
example (a b c d : ℝ) (hd : 0 < d) :
    a * b * c ≤ d ^ 3 → min (min a b) c ≤ d := by
  intro h
  by_contra! h_contra
  have : d < a ∧ d < b ∧ d < c := by simp_all only [lt_inf_iff, and_self]
  have : d ^ 3 < a * b * c := by
    rw [pow_three, ← mul_assoc]
    gcongr <;> simp_all only
  linarith only [this, h]

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a ^ 2 ≤ b ^ 2 → a ≤ b := by
  intro h
  convert sq_le_sq.mp h
  <;> simp only [abs_of_pos, ha, hb]


example (a b : ℝ) (hb : 0 < b) : a ^ 2 ≤ b ^ 2 → a ≤ b := by
  intro h
  apply sq_le_sq.mp at h
  trans |a|
  . exact le_abs_self a
  rw [abs_of_pos hb] at h
  exact h

-- 平方小于等于推出小于等于（要求大的那个数非负）
#check le_of_sq_le_sq
example (a b : ℝ) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 → a ≤ b := by
  intro h
  exact le_of_sq_le_sq h hb

-- 平方小于推出小于（要求大的那个数非负）
example (a b : ℝ) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 → a < b := by
  intro h
  have : |a| < b := abs_lt_of_sq_lt_sq h hb
  have : a ≤ |a| := le_abs_self a
  linarith

example (a b : ℕ) : a ^ 2 < b ^ 2 → a < b := by
  intro h
  exact lt_of_pow_lt_pow_left' 2 h

-- 非负数，小于推出平方小于
example (a b : ℝ) (ha : 0 ≤ a) : a < b → a ^ 2 < b ^ 2 := by
  intro h
  have : |a| < |b| := by
    convert h <;> apply abs_of_nonneg (by linarith)
  exact sq_lt_sq.mpr this

example (a b : ℕ) : a < b → a ^ 2 < b ^ 2 := by
  intro h
  refine Nat.pow_lt_pow_left h two_ne_zero

example (a b : ℝ) : a ≤ 0 → b ≤ 0 → 0 ≤ a * b := by
  intro ha hb
  exact mul_nonneg_of_nonpos_of_nonpos ha hb

example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ d) : a ≤ b → c ≤ d → a * c ≤ b * d := by
  intro h1 h2
  apply mul_le_mul_of_nonneg h1 h2 ha hc


-- Cauchy-Schwarz Inequality
#check Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
#check Finset.sum_mul_sq_le_sq_mul_sq
#check norm_inner_eq_norm_iff

example (x1 x2 x3 y1 y2 y3 : ℝ) (hpos : 0 ≤ x1 ∧ 0 ≤ x2 ∧ 0 ≤ x3 ∧ 0 ≤ x3 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3) :
    (√ (x1 * y1) + √ (x2 * y2) + √ (x3 * y3)) ^ 2 ≤ (x1 + x2 + x3) * (y1 + y2 + y3) := by
  let s : Finset (Fin 3) := .univ
  let f : (Fin 3) → ℝ := ![√ x1, √ x2, √ x3]
  let g : (Fin 3) → ℝ := ![√ y1, √ y2, √ y3]
  convert Finset.sum_mul_sq_le_sq_mul_sq s f g using 2
  <;> simp [s, f, g, Fin.sum_univ_three]
  . repeat rw [Real.sqrt_mul (by tauto)]
  . repeat rw [Real.sq_sqrt (by tauto)]
  . repeat rw [Real.sq_sqrt (by tauto)]

example
    (n : ℕ)
    (f g : (Fin n) → ℝ)
    (hf : ∃ i , f i ≠ 0)
    (hg : ∃ i , g i ≠ 0) :
    (∑ i , f i * g i) ^ 2 = (∑ i , f i ^ 2) * ∑ i , g i ^ 2 ↔
      ∃ (r : ℝ), r ≠ 0 ∧ ∀ i, g i = r * f i := by
  -- let x : EuclideanSpace ℝ (Fin n) := fun i => f i
  -- let y : EuclideanSpace ℝ (Fin n) := fun i => g i

  -- have x_ne_zero : x ≠ 0 := by
  --   rcases hf with ⟨i, hi⟩
  --   intro h
  --   exact hi (congrFun h i)

  -- have y_ne_zero : y ≠ 0 := by
  --   rcases hg with ⟨i, hi⟩
  --   intro h
  --   exact hi (congrFun h i)

  -- have h_inner : inner ℝ x y = ∑ i, f i * g i := by
  --   simp [x, y, mul_comm]

  -- have h_norm_x : ‖x‖^2 = ∑ i, f i ^ 2 := by
  --   simp [norm_eq_sqrt_real_inner, x, Real.sq_sqrt (Finset.sum_nonneg (fun i a ↦ mul_self_nonneg (f i)))]
  --   ring_nf

  -- have h_norm_y : ‖y‖^2 = ∑ i, g i ^ 2 := by
  --   simp [norm_eq_sqrt_real_inner, y, Real.sq_sqrt (Finset.sum_nonneg (fun i a ↦ mul_self_nonneg (g i)))]
  --   ring_nf

  -- have h1 : ‖inner ℝ x y‖ = ‖x‖ * ‖y‖ ↔ ‖inner ℝ x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  --   constructor
  --   . intro h
  --     rw [h]
  --     exact mul_pow ‖x‖ ‖y‖ 2
  --   . intro h
  --     rw [← mul_pow] at h
  --     convert (sq_eq_sq_iff_abs_eq_abs _ _ ).mp h using 1
  --     . exact Eq.symm (abs_norm (inner ℝ x y))
  --     . simp only [abs_mul, abs_norm]

  -- have h2 : ‖inner ℝ x y‖ = ‖x‖ * ‖y‖ ↔ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x :=
  --   norm_inner_eq_norm_iff x_ne_zero y_ne_zero

  -- rw [h1] at h2
  -- convert h2 using 1

  -- . simp [h_inner, h_norm_x, h_norm_y]
  -- . simp [PiLp.ext_iff, x, y]
  sorry

end




section
-- eq

example (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) : (1 / b + 1 / c) * (2 * a * b * c) = 2 * a * c + 2 * a * b := by
  obtain ⟨ha, hb, hc⟩ := h
  field_simp
  ring

example (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) : 1 / 2 * (2 * a / (b * c) + b / (c * a) + c / (a * b)) * (2 * a * b * c) = 2 * a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := h
  field_simp
  ring

end


section
--prod

open Finset

-- prod ge one
example (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact one_le_mul_of_one_le_of_one_le ih (hf n)



end


section
--div

example (a b c d : ℝ) : a / b * (c / d) = (a * c) / (b * d) := by
  exact div_mul_div_comm a b c d

end



section
--inequalities

theorem am_gm_two_vars (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have h₁ : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  nlinarith [Real.sq_sqrt (mul_nonneg ha.le hb.le), sq_nonneg (a - b)]


example (a b : ℝ) : a ≤ b ↔ 0 ≤ b - a := by
  constructor
  . intro h
    exact sub_nonneg_of_le h
  . intro h
    exact sub_nonneg.mp h

example (a b c d : ℝ) (h : 0 < b ∧ 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  obtain ⟨hb, hd⟩ := h
  exact div_le_div_iff₀ hb hd

-- amgm
#check Real.geom_mean_le_arith_mean_weighted

#check Real.geom_mean_le_arith_mean2_weighted

#check Real.geom_mean_le_arith_mean3_weighted

-- amgm_3
example {a b c : ℝ} : 0 ≤ a → 0 ≤ b → 0 ≤ c → 3 * (a * b * c) ^ (1 / 3 : ℝ) ≤ a + b + c := by
  intro ha hb hc
  have t1 : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have := Real.geom_mean_le_arith_mean3_weighted t1 t1 t1 ha hb hc (by norm_num)
  rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (by positivity) hc,
      ← mul_add, ← mul_add] at this
  replace := mul_le_mul_of_nonneg_left this zero_le_three
  rw [one_div, mul_inv_cancel_left₀ three_ne_zero, ← one_div] at this
  exact this

-- amgm_2
example {a b : ℝ} : 0 ≤ a → 0 ≤ b → 2 * √ (a * b) ≤ a + b := by
  intro ha hb
  have t1 : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have := Real.geom_mean_le_arith_mean2_weighted t1 t1 ha hb (by norm_num)
  rw [← Real.mul_rpow ha hb, ← mul_add,
      Real.rpow_div_two_eq_sqrt 1 (by positivity), Real.rpow_one] at this
  linarith

example (a b c : ℝ) (hc : c ≠ 0) : a = b / c → a * c = b := by
  intro h
  exact (eq_mul_inv_iff_mul_eq₀ hc).mp h

example (a b c : ℝ) (hc : c ≠ 0) : a = c⁻¹ * b → c * a = b := by
  intro h
  exact ((inv_mul_eq_iff_eq_mul₀ hc).mp h.symm).symm

example (a b c : ℝ) (hc : 0 ≤ c) : a ≤ b → a * c ≤ b * c := by
  intro h
  exact mul_le_mul_of_nonneg_right h hc

example (a b c : ℝ) (hc : 0 < c) : a * c ≤ b * c → a ≤ b := by
  intro h
  exact le_of_mul_le_mul_right h hc

example (a b c : ℝ) (hc : 0 < c) : a ≤ c⁻¹ * b → c * a ≤ b := by
  intro h
  exact (le_inv_mul_iff₀' hc).mp h


end


section
--mod

example (a b c : ℤ) : (a + b) % c = (a % c + b % c) % c := by
  exact Int.add_emod a b c

example (c : ℕ) : (2021 : ℤ) ^ c % 4 = 1 := by
  norm_cast
  rw [Nat.pow_mod]
  norm_num

example (c : ℕ) : (2021 ^ c - (1 : ℤ)) % 4 = 0 := by
  rw [Int.sub_emod, show (1 : ℤ) % 4 = 1 by norm_num,
      show (2021 : ℤ) ^ c % 4 = 1 by norm_cast; norm_num [Nat.pow_mod],
      sub_self]
  norm_num

end

section
-- dvd

example (a b : ℕ) (hpos : 0 < a) : a.gcd b ∣ a.lcm b := by
  have ⟨⟨ka, hka⟩, ⟨kb, hkb⟩⟩ := Nat.gcd_dvd a b
  have : a.lcm b = ka * kb * a.gcd b := by
    rw [Nat.lcm]
    set g := a.gcd b
    rw [hka, hkb, mul_assoc, Nat.mul_div_cancel_left _ ?_]
    . ring
    exact Nat.gcd_pos_of_pos_left b hpos
  rw [this]
  exact Nat.dvd_mul_left ?_ ?_


example (a b c : ℕ) (hap : a.Prime) (hdvd : a ∣ b ^ c) : a ∣ b := by
  exact Nat.Prime.dvd_of_dvd_pow hap hdvd

example (a b : ℕ) (hbp : b.Prime) (hdvd : a ∣ b) : a = 1 ∨ a.Prime := by
  have : a = 1 ∨ a = b := by exact (Nat.dvd_prime hbp).mp hdvd
  rcases this with h | h
  . simp only [h, true_or]
  . simp only [h, hbp, or_true]

end

section
-- int

example {a b : ℕ} : ((a : ℤ) - b).natAbs = ((b : ℤ) - a).natAbs := by
  refine Int.natAbs_eq_iff_mul_self_eq.mpr (by ring)

end

section
--tmp

example
    (a b : NNReal)
    (h0 : 0 < a ∧ 0 < b)
    (h1 : a ^ 2 = 6 * b)
    (h2 : a ^ 2 = 54 / b) :
    6 * b ^ 2 = 54 := by
  rw [pow_two, ← mul_assoc, ← h1, h2, div_mul_cancel₀ _ ?_]
  exact ne_of_gt h0.2

end

section
--dvd

example (a b c : ℕ) (hcop : a.Coprime b) : a ∣ c → b ∣ c → a * b ∣ c := by
  intro h1 h2
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2

example (a b c : ℕ) (hcop : a.gcd b = 1) : a ∣ c → b ∣ c → a * b ∣ c := by
  intro h1 h2
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2

example (n : ℕ) : 2 ∣ n * (n + 1) := by
  refine (Nat.Prime.dvd_mul Nat.prime_two).mpr ?_
  rcases n.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  . simp [hk, ← two_mul]
  . simp [hk]

example (n : ℕ) : 2 ∣ (n - 1) * n * (n + 1) := by
  rw [mul_assoc]
  apply dvd_mul_of_dvd_right
  refine (Nat.Prime.dvd_mul Nat.prime_two).mpr ?_
  rcases n.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  . simp [hk, ← two_mul]
  . simp [hk]

example (n : ℕ) : 2 ∣ (n - 1) * n * (n + 1) := by
  apply Nat.dvd_of_mod_eq_zero
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with (h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt]

example (n : ℕ) : 3 ∣ n * (n + 1) * (n + 2) := by
  have : n % 3 < 3 := by refine Nat.mod_lt n zero_lt_three
  set m := n % 3 with hm
  interval_cases m
  <;> [suffices : 3 ∣ n; suffices : 3 ∣ (n + 2); suffices : 3 ∣ (n + 1)]
  any_goals simp [mul_assoc, dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, this]
  all_goals
    apply Nat.dvd_of_mod_eq_zero
    norm_num [Nat.add_mod, ← hm]

example (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  trans n % 6 * (n % 6 + 1) % 6 * (n % 6 + 2) % 6
  . simp [Nat.mul_mod]
  have : n % 6 < 6 := Nat.mod_lt n (by linarith only)
  interval_cases n % 6 <;> norm_num

end


section
-- inequation

example (a b : ℝ) : 0 ≤ a → 0 ≤ b → a + b ≥ 2 * √ (a * b) := by
  intro ha hb
  refine two_mul_le_add_of_sq_eq_mul ha hb ?_
  apply Real.sq_sqrt
  positivity

example (a b c : ℝ) : 0 < c → a < b → a * c < b * c := by
  intro hc h
  exact (mul_lt_mul_iff_of_pos_right hc).mpr h

example (a b : ℝ) : 0 < a → a < b → 1 < b / a := by
  intro ha h
  apply (div_lt_div_iff_of_pos_right ha).mpr at h
  convert h
  symm
  apply div_self (by linarith only [ha])

end


section

example (a b : ℕ) : a ^ 3 ∣ b → a ^ 2 ∣ b := by
  intro h
  exact dvd_of_mul_right_dvd h


example (a b : ℕ) : a ^ 6 ∣ b → a ^ 2 ∣ b := by
  intro h
  refine Nat.pow_dvd_of_le_of_pow_dvd (show 2 ≤ 6 by norm_num) h

example (a b c : ℕ) : a ∣ b → a ∣ c → a ∣ b + c := by
  intro h1 h2
  exact (Nat.dvd_add_iff_right h1).mp h2

#check add_sub_cancel_left
#check Nat.dvd_sub'

example (a b c : ℕ) : a ∣ b → ¬ a ∣ c → ¬ a ∣ b + c := by
  intro h1 h2
  by_contra!
  apply Nat.dvd_sub this at h1
  rw [Nat.add_sub_cancel_left] at h1
  contradiction

end


section

open Finset


example (a : ℤ) : -1 + a + 1 = a := by
  exact neg_add_cancel_comm 1 a

example (a b c : ℕ) (hc : c ≠ 0) : a * c ∣ b * c → a ∣ b := by
  intro h
  exact (mul_dvd_mul_iff_right hc).mp h

example (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℕ) : ∑ i ∈ range n, f i = f 0 + f 1 + ∑ i ∈ Ico 2 n, f i := by
  rw [range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot (by linarith) f]
  rw [sum_eq_sum_Ico_succ_bot (by linarith) f]
  ring

example (a b : ℕ) : a ^ 3 ∣ b → a ^ 2 ∣ b := by
  intro h
  exact dvd_of_mul_right_dvd h


example (a b : ℕ) : a ^ 6 ∣ b → a ^ 2 ∣ b := by
  intro h
  refine Nat.pow_dvd_of_le_of_pow_dvd (show 2 ≤ 6 by norm_num) h

example (a b c : ℕ) : a ∣ b → a ∣ c → a ∣ b + c := by
  intro h1 h2
  exact (Nat.dvd_add_iff_right h1).mp h2

example (a b c : ℕ) : a ∣ b → ¬ a ∣ c → ¬ a ∣ b + c := by
  intro h1 h2
  by_contra!
  apply Nat.dvd_sub this at h1
  rw [Nat.add_sub_cancel_left] at h1
  contradiction


end

section

-- 二项式取模

lemma l_sum_extract_three_bot {R : Type} {n : ℕ} (hn : 3 ≤ n) [CommSemiring R] {f : ℕ → R} : ∑ i ∈ Finset.range n, f i = f 0 + f 1 + f 2 + ∑ i ∈ Finset.Ico 3 n, f i := by
  rw [Finset.range_eq_Ico]
  repeat rw [Finset.sum_eq_sum_Ico_succ_bot (by linarith) f]
  ring

lemma l_sum_extract_two_bot {R : Type} {n : ℕ} (hn : 2 ≤ n) [CommSemiring R] {f : ℕ → R} : ∑ i ∈ Finset.range n, f i = f 0 + f 1 + ∑ i ∈ Finset.Ico 2 n, f i := by
  rw [Finset.range_eq_Ico]
  repeat rw [Finset.sum_eq_sum_Ico_succ_bot (by linarith) f]
  ring

example (a b : ℤ) : a ≡ a [ZMOD b] := by
  simp only [Int.ModEq.refl]

example (a b c : ℤ) : c ≡ 0 [ZMOD b] → a + c ≡ a [ZMOD b] := by
  intro h
  conv => lhs; rw [add_comm]
  conv => rhs; rw [← zero_add a]
  apply h.add
  rfl

example (a b : ℤ) : a % b = 0 → a ≡ 0 [ZMOD b] := by
  exact fun a => a

example (f : ℕ → ℤ) (n : ℤ) : (∀ i ∈ Finset.Ico 2 6, n ∣ f i) → n ∣ ∑ i ∈ Finset.Ico 2 6, f i := by
  intro h
  exact Finset.dvd_sum h

example (a b c : ℕ) : a * b * c = c * b * a := by
  rw [mul_comm, mul_comm a, ← mul_assoc]

example (k n : ℕ) (hn : 2 ≤ n) : (k - 1) ^ n ≡ n.choose 0 * (-1) ^ n + n.choose 1 * (-1) ^ (n - 1) * k [ZMOD k ^ 2] := by

  have l_sum_extract_two_bot {R : Type} {n : ℕ} (hn : 2 ≤ n) [CommSemiring R] {f : ℕ → R} : ∑ i ∈ Finset.range n, f i = f 0 + f 1 + ∑ i ∈ Finset.Ico 2 n, f i := by
    rw [Finset.range_eq_Ico]
    repeat rw [Finset.sum_eq_sum_Ico_succ_bot (by linarith) f]
    ring

  have tmplemma {a b c : ℤ} : c ≡ 0 [ZMOD b] → a + c ≡ a [ZMOD b] := by
    intro h
    conv => lhs; rw [add_comm]
    conv => rhs; rw [← zero_add a]
    apply h.add
    rfl

  rw [show (k : ℤ) - 1 = k + (-1) by ring,
      add_pow, l_sum_extract_two_bot (by linarith only [hn]),
      mul_comm _ (n.choose 1 : ℤ), mul_comm ((k : ℤ) ^ 1), ← mul_assoc]
  simp

  apply tmplemma

  suffices : (k : ℤ) ^ 2 ∣ (∑ i ∈ Finset.Ico 2 (n + 1), k ^ i * (-1 : ℤ) ^ (n - i) * (n.choose i))
  . exact Dvd.dvd.modEq_zero_int this
  apply Finset.dvd_sum
  intro i hi
  rw [show (k : ℤ) ^ i = k ^ 2 * k ^ (i - 2) by rw [← pow_add, Nat.add_sub_cancel']; exact (Finset.mem_Ico.mp hi).1,
      mul_assoc ((k : ℤ) ^ 2), mul_assoc]
  apply dvd_mul_right


end



section

-- PythagoreanTriple

#check PythagoreanTriple

#check PythagoreanTriple.IsClassified

#check PythagoreanTriple.classified

example (x y z : ℤ) (h : PythagoreanTriple x y z) :
    ∃ k m n : ℤ,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1 := by
  exact h.classified

example {x y z : ℤ} (hpos : 0 < x ∧ 0 < y ∧ 0 < z) (h : PythagoreanTriple x y z) :
    ∃ k m n : ℤ,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      (0 < k ∧ 0 < m ∧ 0 < n) := by
  obtain ⟨k, m, n, ⟨h, _⟩⟩ := h.classified

  have : 0 < k ∧ 0 < m * n ∨ k < 0 ∧ m * n < 0 := by
    apply pos_and_pos_or_neg_and_neg_of_mul_pos
    suffices : 0 < k * (2 * m * n)
    . rw [mul_assoc 2, mul_left_comm] at this
      exact pos_of_mul_pos_right this zero_le_two
    omega

  rcases this with ⟨hk, hmn⟩ | ⟨hk, hmn⟩
  . apply pos_and_pos_or_neg_and_neg_of_mul_pos at hmn
    have hmn' : 2 * |m| * |n| = 2 * m * n := by
      rcases hmn with ⟨hm, hn⟩ | ⟨hm, hn⟩
      <;> simp [abs_of_pos, abs_of_neg, hm, hn]
    use k, |m|, |n|
    constructor
    . convert h using 4
      any_goals simp [sq_abs]
    . simp [hk]
      omega
  . apply mul_neg_iff.mp at hmn
    have hmn' : k * (m ^ 2 - n ^ 2) = -k * (|n| ^ 2 - |m| ^ 2) ∧ k * (2 * m * n) = -k * (2 * |n| * |m|) := by
      simp only [sq_abs]
      ring_nf
      rw [true_and]
      rcases hmn with ⟨hm, hn⟩ | ⟨hm, hn⟩
      <;> simp [abs_of_pos, abs_of_neg, hm, hn, mul_right_comm]
    rw [hmn'.1, hmn'.2] at h
    use -k, |n|, |m|
    constructor
    . exact h
    . simp [hk]
      omega

end


section

example (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  exact (sq_eq_sq₀ ha hb).mp h

#check pos_and_pos_or_neg_and_neg_of_mul_pos

example (a b : ℤ) (hab : 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  exact pos_and_pos_or_neg_and_neg_of_mul_pos hab

example (a b c : ℝ) (h : a ≠ 0) : (a * b) / (a * c) = b / c := by
  exact mul_div_mul_left b c h

example (a b c : ℝ) (h : c ≠ 0) : a / b = (a / c) / (b / c) := by
  exact Eq.symm (div_div_div_cancel_right₀ h a b)

example (a b c : ℝ) (h : c ≠ 0) : a * c = b * c → a = b := by
  intro h1
  apply_fun fun t => t * c⁻¹ at h1
  simp_rw [mul_inv_cancel_right₀ h] at h1
  exact h1

end
