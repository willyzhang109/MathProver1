open Multiset
                   

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
                     
  let IsGood (B : Board) : Prop := B.card = 2026 ∧ ∀ x ∈ B, 1 ≤ x
  let board_measure (B : Board) : ℕ := 2027 * B.prod + (B.filter (fun a => 1 < a)).card
  
  have prod_pos_of_pos : ∀ (B : Board), (∀ x ∈ B, 0 < x) → 0 < B.prod := by
    intro B h
    induction B using Multiset.induction with
    | empty => simp
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 0 < x := h x (mem_cons_self x s)
      have hs : ∀ y ∈ s, 0 < y := fun y hy => h y (mem_cons_of_mem hy)
      have ih_s := ih hs
      exact Nat.mul_pos hx ih_s

  have prod_pos_of_isGood : ∀ (B : Board), IsGood B → 0 < B.prod := by
    intro B hG
    exact prod_pos_of_pos B (fun x hx => by have := hG.2 x hx; omega)

  have isGood_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → IsGood B' := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_card : (m ::ₘ n ::ₘ s).card = 2026 := hG.1
    simp only [card_cons] at h_card
    have h_card' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card = 2026 := by
      simp only [card_cons]
      omega
    refine ⟨h_card', ?_⟩
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · have hgcd : Nat.gcd m n ≠ 0 := by
        intro h
        have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
        rw [h] at h_dvd
        rcases h_dvd with ⟨c, hc⟩
        simp only [zero_mul] at hc
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        exact hm0 hc
      omega
    · have hlcm : Nat.lcm m n ≠ 0 := by
        intro h
        have h_mul : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
        rw [h, zero_mul] at h_mul
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        have hn0 : n ≠ 0 := by
          intro h_zero
          rw [h_zero] at hn
          contradiction
        have h_mn : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
        exact h_mn h_mul.symm
      have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
        exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
      have h_pos : 1 ≤ Nat.lcm m n / Nat.gcd m n := by
        have h_gcd_le : Nat.gcd m n ≤ Nat.lcm m n := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          have hn0 : n ≠ 0 := by
            intro h_zero
            rw [h_zero] at hn
            contradiction
          exact Nat.lcm_ne_zero hm0 hn0)) hgcd_dvd
        have h_gcd_pos : 0 < Nat.gcd m n := by
          have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
          by_contra h_zero
          have : Nat.gcd m n = 0 := by omega
          rw [this] at h_dvd
          rcases h_dvd with ⟨c, hc⟩
          simp only [zero_mul] at hc
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          exact hm0 hc
        exact Nat.div_pos h_gcd_le h_gcd_pos
      omega
    · have h_in : x ∈ m ::ₘ n ::ₘ s := by simp [hx]
      exact hG.2 x h_in

  have measure_decreasing : ∀ {B B' : Board}, IsGood B → Move B B' → board_measure B' < board_measure B := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_g_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
      exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have h_lg : (Nat.lcm m n / Nat.gcd m n) * Nat.gcd m n = Nat.lcm m n := Nat.div_mul_cancel h_g_dvd
    have h_lcm_gcd : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
    
    have h_prod_eq : (m ::ₘ n ::ₘ s).prod = (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * Nat.gcd m n := by
      simp only [prod_cons]
      have h1 : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) * Nat.gcd m n =
                ((Nat.lcm m n / Nat.gcd m n) * Nat.gcd m n) * Nat.gcd m n * s.prod := by ring
      rw [h1, h_lg]
      rw [h_lcm_gcd]
      ring
    
    have hG' : IsGood (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) := isGood_of_move hG (by
      refine ⟨m, n, s, hm, hn, rfl, rfl⟩)
    have h_prod'_pos : 0 < (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := prod_pos_of_isGood _ hG'
    
    by_cases hg1 : Nat.gcd m n = 1
    · have h_prod_eq2 : (m ::ₘ n ::ₘ s).prod = (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := by
        rw [h_prod_eq, hg1, mul_one]
      have h_filter_B : ((m ::ₘ n ::ₘ s).filter (fun a => 1 < a)).card = 2 + ((s.filter (fun a => 1 < a)).card) := by
        simp [hm, hn]
        omega
      have h_filter_B' : (((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card) = 1 + ((s.filter (fun a => 1 < a)).card) := by
        simp only [filter_cons]
        have hg_not : ¬ (1 < Nat.gcd m n) := by rw [hg1]; omega
        simp [hg_not]
        have hl : 1 < Nat.lcm m n / Nat.gcd m n := by
          have h_l_eq : Nat.lcm m n / Nat.gcd m n = m * n := by
            have h_l_lcm : Nat.lcm m n / Nat.gcd m n = Nat.lcm m n := by rw [hg1, Nat.div_one]
            rw [h_l_lcm]
            have h_lcm_1 : Nat.lcm m n * 1 = m * n := by rw [← h_lcm_gcd, hg1]
            rw [mul_one] at h_lcm_1
            exact h_lcm_1
          rw [h_l_eq]
          nlinarith
        simp [hl]
      simp only [board_measure]
      rw [h_prod_eq2, h_filter_B, h_filter_B']
      omega
    · have hg_gt : 1 < Nat.gcd m n := by
        have : 1 ≤ Nat.gcd m n := by
          have hx : Nat.gcd m n ∈ Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s := mem_cons_self _ _
          exact hG'.2 _ hx
        omega
      have h_prod_gt : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod < (m ::ₘ n ::ₘ s).prod := by
        rw [h_prod_eq]
        have : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * 2 ≤ (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * Nat.gcd m n :=
          Nat.mul_le_mul_left _ hg_gt
        omega
      have h_filter_le : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card ≤ 2026 := by
        have h_sub : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a) ≤ Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s :=
          Multiset.filter_le _ _
        have h_card_le := Multiset.card_le_card h_sub
        rw [hG'.1] at h_card_le
        exact h_card_le
      simp only [board_measure]
      omega

  intro ⟨f, hf0, hf_move⟩
  have h_good_f : ∀ k, IsGood (f k) := by
    intro k
    induction k with
    | zero =>
      rw [hf0]
      refine ⟨hB₀.1, ?_⟩
      intro x hx
      have := hB₀.2 x hx
      omega
    | succ k ih =>
      exact isGood_of_move ih (hf_move k)

  have h_dec : ∀ k, board_measure (f (k + 1)) < board_measure (f k) := by
    intro k
    exact measure_decreasing (h_good_f k) (hf_move k)

  have h_le : ∀ k, board_measure (f k) + k ≤ board_measure (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h_step := h_dec k
      omega

  let N := board_measure (f 0) + 1
  have h_contra := h_le N
  omega
                   

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
                     
  let IsGood (B : Board) : Prop := B.card = 2026 ∧ ∀ x ∈ B, 1 ≤ x
  
  have prod_pos_of_pos : ∀ (B : Board), (∀ x ∈ B, 0 < x) → 0 < B.prod := by
    intro B h
    induction B using Multiset.induction with
    | empty => simp
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 0 < x := h x (mem_cons_self x s)
      have hs : ∀ y ∈ s, 0 < y := fun y hy => h y (mem_cons_of_mem hy)
      have ih_s := ih hs
      exact Nat.mul_pos hx ih_s

  have prod_pos_of_isGood : ∀ (B : Board), IsGood B → 0 < B.prod := by
    intro B hG
    exact prod_pos_of_pos B (fun x hx => by have := hG.2 x hx; omega)

  have isGood_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → IsGood B' := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_card : (m ::ₘ n ::ₘ s).card = 2026 := hG.1
    simp only [card_cons] at h_card
    have h_card' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card = 2026 := by
      simp only [card_cons]
      omega
    refine ⟨h_card', ?_⟩
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · have hgcd : Nat.gcd m n ≠ 0 := by
        intro h
        have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
        rw [h] at h_dvd
        rcases h_dvd with ⟨c, hc⟩
        simp only [zero_mul] at hc
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        exact hm0 hc
      omega
    · have hlcm : Nat.lcm m n ≠ 0 := by
        intro h
        have h_mul : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
        rw [h, zero_mul] at h_mul
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        have hn0 : n ≠ 0 := by
          intro h_zero
          rw [h_zero] at hn
          contradiction
        have h_mn : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
        exact h_mn h_mul.symm
      have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
        exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
      have h_pos : 1 ≤ Nat.lcm m n / Nat.gcd m n := by
        have h_gcd_le : Nat.gcd m n ≤ Nat.lcm m n := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          have hn0 : n ≠ 0 := by
            intro h_zero
            rw [h_zero] at hn
            contradiction
          exact Nat.lcm_ne_zero hm0 hn0)) hgcd_dvd
        have h_gcd_pos : 0 < Nat.gcd m n := by
          have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
          by_contra h_zero
          have : Nat.gcd m n = 0 := by omega
          rw [this] at h_dvd
          rcases h_dvd with ⟨c, hc⟩
          simp only [zero_mul] at hc
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          exact hm0 hc
        exact Nat.div_pos h_gcd_le h_gcd_pos
      omega
    · have h_in : x ∈ m ::ₘ n ::ₘ s := by simp [hx]
      exact hG.2 x h_in

  have prod_gt_one_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → 1 < B.prod → 1 < B'.prod := by
    intro B B' hG hM hP
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    by_contra h_le
    have hG' : IsGood (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) := isGood_of_move hG (by
      refine ⟨m, n, s, hm, hn, rfl, rfl⟩)
    have h_pos : 0 < (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := prod_pos_of_isGood _ hG'
    have h_eq1 : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod = 1 := by omega
    simp only [prod_cons] at h_eq1
    rw [mul_eq_one] at h_eq1
    have hg := h_eq1.1
    have h_eq2 := h_eq1.2
    rw [mul_eq_one] at h_eq2
    have hl := h_eq2.1
    have hlcm : Nat.lcm m n = 1 := by
      rw [hg, Nat.div_one] at hl
      exact hl
    have h_dvd : m ∣ Nat.lcm m n := Nat.dvd_lcm_left m n
    rw [hlcm] at h_dvd
    have : m = 1 := Nat.eq_one_of_dvd_one h_dvd
    omega

  have prod_ge_one : ∀ (s : Board), (∀ y ∈ s, 1 ≤ y) → 1 ≤ s.prod := by
    intro s hs
    induction s using Multiset.induction with
    | empty => simp
    | cons y t ih =>
      simp only [prod_cons]
      have hy : 1 ≤ y := hs y (mem_cons_self y t)
      have ht : 1 ≤ t.prod := ih (fun z hz => hs z (mem_cons_of_mem hz))
      nlinarith

  have prod_gt_one_of_mem_gt_one : ∀ {B : Board}, B.card ≥ 1 → (∀ x ∈ B, 1 < x) → 1 < B.prod := by
    intro B h_card h_gt
    induction B using Multiset.induction with
    | empty => simp at h_card
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 1 < x := h_gt x (mem_cons_self x s)
      have hs_all : ∀ y ∈ s, 1 ≤ y := by
        intro y hy
        have := h_gt y (mem_cons_of_mem hy)
        omega
      have hs_prod : 1 ≤ s.prod := prod_ge_one s hs_all
      nlinarith

  have good_and_prod_gt_one_of_reachable : ∀ {B' : Board}, Reachable B₀ B' → IsGood B' ∧ 1 < B'.prod := by
    intro B' hreach
    induction hreach with
    | refl =>
      have hG0 : IsGood B₀ := by
        refine ⟨hB₀.1, ?_⟩
        intro x hx
        have := hB₀.2 x hx
        omega
      have hP0 : 1 < B₀.prod := by
        have h_card : B₀.card ≥ 1 := by omega
        exact prod_gt_one_of_mem_gt_one h_card hB₀.2
      exact ⟨hG0, hP0⟩
    | tail h hM ih =>
      exact ⟨isGood_of_move ih.1 hM, prod_gt_one_of_move ih.1 hM ih.2⟩

  have h_good_and_prod := good_and_prod_gt_one_of_reachable hreach
  have hG' := h_good_and_prod.1
  have hP' := h_good_and_prod.2

  have filter_card_ge_one : 1 ≤ (B'.filter (fun a => 1 < a)).card := by
    by_contra h_card
    have h_card0 : (B'.filter (fun a => 1 < a)).card = 0 := by omega
    have h_filter_empty : B'.filter (fun a => 1 < a) = ∅ := card_eq_zero.mp h_card0
    have h_all_one : ∀ x ∈ B', x = 1 := by
      intro x hx
      have h_le : 1 ≤ x := hG'.2 x hx
      have h_not_gt : ¬ (1 < x) := by
        intro h_gt
        have h_mem : x ∈ B'.filter (fun a => 1 < a) := by
          simp [hx, h_gt]
        rw [h_filter_empty] at h_mem
        simp at h_mem
      omega
    have prod_eq_one_of_all_one : ∀ (s : Board), (∀ x ∈ s, x = 1) → s.prod = 1 := by
      intro s hs
      induction s using Multiset.induction with
      | empty => simp
      | cons y t ih =>
        simp only [prod_cons]
        have hy : y = 1 := hs y (mem_cons_self y t)
        have ht : t.prod = 1 := ih (fun z hz => hs z (mem_cons_of_mem hz))
        rw [hy, ht, one_mul]
    have h_prod_one : B'.prod = 1 := prod_eq_one_of_all_one B' h_all_one
    omega

  have h_term_unfold : (B'.filter (fun a => 1 < a)).card ≤ 1 := hterm
  unfold HasUniqueLarge
  omega
                   

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
-- EVOLVE-BLOCK-START
  let IsGood (B : Board) : Prop := B.card = 2026 ∧ ∀ x ∈ B, 1 ≤ x
  let board_measure (B : Board) : ℕ := 2027 * B.prod + (B.filter (fun a => 1 < a)).card
  
  have prod_pos_of_pos : ∀ (B : Board), (∀ x ∈ B, 0 < x) → 0 < B.prod := by
    intro B h
    induction B using Multiset.induction with
    | empty => simp
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 0 < x := h x (mem_cons_self x s)
      have hs : ∀ y ∈ s, 0 < y := fun y hy => h y (mem_cons_of_mem hy)
      have ih_s := ih hs
      exact Nat.mul_pos hx ih_s

  have prod_pos_of_isGood : ∀ (B : Board), IsGood B → 0 < B.prod := by
    intro B hG
    exact prod_pos_of_pos B (fun x hx => by have := hG.2 x hx; omega)

  have isGood_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → IsGood B' := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_card : (m ::ₘ n ::ₘ s).card = 2026 := hG.1
    simp only [card_cons] at h_card
    have h_card' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card = 2026 := by
      simp only [card_cons]
      omega
    refine ⟨h_card', ?_⟩
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · have hgcd : Nat.gcd m n ≠ 0 := by
        intro h
        have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
        rw [h] at h_dvd
        rcases h_dvd with ⟨c, hc⟩
        simp only [zero_mul] at hc
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        exact hm0 hc
      omega
    · have hlcm : Nat.lcm m n ≠ 0 := by
        intro h
        have h_mul : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
        rw [h, zero_mul] at h_mul
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        have hn0 : n ≠ 0 := by
          intro h_zero
          rw [h_zero] at hn
          contradiction
        have h_mn : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
        exact h_mn h_mul.symm
      have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
        exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
      have h_pos : 1 ≤ Nat.lcm m n / Nat.gcd m n := by
        have h_gcd_le : Nat.gcd m n ≤ Nat.lcm m n := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          have hn0 : n ≠ 0 := by
            intro h_zero
            rw [h_zero] at hn
            contradiction
          exact Nat.lcm_ne_zero hm0 hn0)) hgcd_dvd
        have h_gcd_pos : 0 < Nat.gcd m n := by
          have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
          by_contra h_zero
          have : Nat.gcd m n = 0 := by omega
          rw [this] at h_dvd
          rcases h_dvd with ⟨c, hc⟩
          simp only [zero_mul] at hc
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          exact hm0 hc
        exact Nat.div_pos h_gcd_le h_gcd_pos
      omega
    · have h_in : x ∈ m ::ₘ n ::ₘ s := by simp [hx]
      exact hG.2 x h_in

  have measure_decreasing : ∀ {B B' : Board}, IsGood B → Move B B' → board_measure B' < board_measure B := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_g_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
      exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have h_lg : (Nat.lcm m n / Nat.gcd m n) * Nat.gcd m n = Nat.lcm m n := Nat.div_mul_cancel h_g_dvd
    have h_lcm_gcd : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
    
    have h_prod_eq : (m ::ₘ n ::ₘ s).prod = (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * Nat.gcd m n := by
      simp only [prod_cons]
      have h1 : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) * Nat.gcd m n =
                ((Nat.lcm m n / Nat.gcd m n) * Nat.gcd m n) * Nat.gcd m n * s.prod := by ring
      rw [h1, h_lg]
      rw [h_lcm_gcd]
      ring
    
    have hG' : IsGood (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) := isGood_of_move hG (by
      refine ⟨m, n, s, hm, hn, rfl, rfl⟩)
    have h_prod'_pos : 0 < (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := prod_pos_of_isGood _ hG'
    
    by_cases hg1 : Nat.gcd m n = 1
    · have h_prod_eq2 : (m ::ₘ n ::ₘ s).prod = (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := by
        rw [h_prod_eq, hg1, mul_one]
      have h_filter_B : ((m ::ₘ n ::ₘ s).filter (fun a => 1 < a)).card = 2 + ((s.filter (fun a => 1 < a)).card) := by
        simp [hm, hn]
        omega
      have h_filter_B' : (((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card) = 1 + ((s.filter (fun a => 1 < a)).card) := by
        simp only [filter_cons]
        have hg_not : ¬ (1 < Nat.gcd m n) := by rw [hg1]; omega
        simp [hg_not]
        have hl : 1 < Nat.lcm m n / Nat.gcd m n := by
          have h_l_eq : Nat.lcm m n / Nat.gcd m n = m * n := by
            have h_l_lcm : Nat.lcm m n / Nat.gcd m n = Nat.lcm m n := by rw [hg1, Nat.div_one]
            rw [h_l_lcm]
            have h_lcm_1 : Nat.lcm m n * 1 = m * n := by rw [← h_lcm_gcd, hg1]
            rw [mul_one] at h_lcm_1
            exact h_lcm_1
          rw [h_l_eq]
          nlinarith
        simp [hl]
      simp only [board_measure]
      rw [h_prod_eq2, h_filter_B, h_filter_B']
      omega
    · have hg_gt : 1 < Nat.gcd m n := by
        have : 1 ≤ Nat.gcd m n := by
          have hx : Nat.gcd m n ∈ Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s := mem_cons_self _ _
          exact hG'.2 _ hx
        omega
      have h_prod_gt : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod < (m ::ₘ n ::ₘ s).prod := by
        rw [h_prod_eq]
        have : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * 2 ≤ (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod * Nat.gcd m n :=
          Nat.mul_le_mul_left _ hg_gt
        omega
      have h_filter_le : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)).card ≤ 2026 := by
        have h_sub : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a) ≤ Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s :=
          Multiset.filter_le _ _
        have h_card_le := Multiset.card_le_card h_sub
        rw [hG'.1] at h_card_le
        exact h_card_le
      simp only [board_measure]
      omega

  intro ⟨f, hf0, hf_move⟩
  have h_good_f : ∀ k, IsGood (f k) := by
    intro k
    induction k with
    | zero =>
      rw [hf0]
      refine ⟨hB₀.1, ?_⟩
      intro x hx
      have := hB₀.2 x hx
      omega
    | succ k ih =>
      exact isGood_of_move ih (hf_move k)

  have h_dec : ∀ k, board_measure (f (k + 1)) < board_measure (f k) := by
    intro k
    exact measure_decreasing (h_good_f k) (hf_move k)

  have h_le : ∀ k, board_measure (f k) + k ≤ board_measure (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h_step := h_dec k
      omega

  let N := board_measure (f 0) + 1
  have h_contra := h_le N
  omega
-- EVOLVE-BLOCK-END

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
-- EVOLVE-BLOCK-START
  let IsGood (B : Board) : Prop := B.card = 2026 ∧ ∀ x ∈ B, 1 ≤ x
  
  have prod_pos_of_pos : ∀ (B : Board), (∀ x ∈ B, 0 < x) → 0 < B.prod := by
    intro B h
    induction B using Multiset.induction with
    | empty => simp
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 0 < x := h x (mem_cons_self x s)
      have hs : ∀ y ∈ s, 0 < y := fun y hy => h y (mem_cons_of_mem hy)
      have ih_s := ih hs
      exact Nat.mul_pos hx ih_s

  have prod_pos_of_isGood : ∀ (B : Board), IsGood B → 0 < B.prod := by
    intro B hG
    exact prod_pos_of_pos B (fun x hx => by have := hG.2 x hx; omega)

  have isGood_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → IsGood B' := by
    intro B B' hG hM
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have h_card : (m ::ₘ n ::ₘ s).card = 2026 := hG.1
    simp only [card_cons] at h_card
    have h_card' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card = 2026 := by
      simp only [card_cons]
      omega
    refine ⟨h_card', ?_⟩
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · have hgcd : Nat.gcd m n ≠ 0 := by
        intro h
        have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
        rw [h] at h_dvd
        rcases h_dvd with ⟨c, hc⟩
        simp only [zero_mul] at hc
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        exact hm0 hc
      omega
    · have hlcm : Nat.lcm m n ≠ 0 := by
        intro h
        have h_mul : Nat.lcm m n * Nat.gcd m n = m * n := Nat.lcm_mul_gcd m n
        rw [h, zero_mul] at h_mul
        have hm0 : m ≠ 0 := by
          intro h_zero
          rw [h_zero] at hm
          contradiction
        have hn0 : n ≠ 0 := by
          intro h_zero
          rw [h_zero] at hn
          contradiction
        have h_mn : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
        exact h_mn h_mul.symm
      have hgcd_dvd : Nat.gcd m n ∣ Nat.lcm m n := by
        exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
      have h_pos : 1 ≤ Nat.lcm m n / Nat.gcd m n := by
        have h_gcd_le : Nat.gcd m n ≤ Nat.lcm m n := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          have hn0 : n ≠ 0 := by
            intro h_zero
            rw [h_zero] at hn
            contradiction
          exact Nat.lcm_ne_zero hm0 hn0)) hgcd_dvd
        have h_gcd_pos : 0 < Nat.gcd m n := by
          have h_dvd : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
          by_contra h_zero
          have : Nat.gcd m n = 0 := by omega
          rw [this] at h_dvd
          rcases h_dvd with ⟨c, hc⟩
          simp only [zero_mul] at hc
          have hm0 : m ≠ 0 := by
            intro h_zero
            rw [h_zero] at hm
            contradiction
          exact hm0 hc
        exact Nat.div_pos h_gcd_le h_gcd_pos
      omega
    · have h_in : x ∈ m ::ₘ n ::ₘ s := by simp [hx]
      exact hG.2 x h_in

  have prod_gt_one_of_move : ∀ {B B' : Board}, IsGood B → Move B B' → 1 < B.prod → 1 < B'.prod := by
    intro B B' hG hM hP
    rcases hM with ⟨m, n, s, hm, hn, rfl, rfl⟩
    by_contra h_le
    have hG' : IsGood (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) := isGood_of_move hG (by
      refine ⟨m, n, s, hm, hn, rfl, rfl⟩)
    have h_pos : 0 < (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod := prod_pos_of_isGood _ hG'
    have h_eq1 : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod = 1 := by omega
    simp only [prod_cons] at h_eq1
    rw [mul_eq_one] at h_eq1
    have hg := h_eq1.1
    have h_eq2 := h_eq1.2
    rw [mul_eq_one] at h_eq2
    have hl := h_eq2.1
    have hlcm : Nat.lcm m n = 1 := by
      rw [hg, Nat.div_one] at hl
      exact hl
    have h_dvd : m ∣ Nat.lcm m n := Nat.dvd_lcm_left m n
    rw [hlcm] at h_dvd
    have : m = 1 := Nat.eq_one_of_dvd_one h_dvd
    omega

  have prod_ge_one : ∀ (s : Board), (∀ y ∈ s, 1 ≤ y) → 1 ≤ s.prod := by
    intro s hs
    induction s using Multiset.induction with
    | empty => simp
    | cons y t ih =>
      simp only [prod_cons]
      have hy : 1 ≤ y := hs y (mem_cons_self y t)
      have ht : 1 ≤ t.prod := ih (fun z hz => hs z (mem_cons_of_mem hz))
      nlinarith

  have prod_gt_one_of_mem_gt_one : ∀ {B : Board}, B.card ≥ 1 → (∀ x ∈ B, 1 < x) → 1 < B.prod := by
    intro B h_card h_gt
    induction B using Multiset.induction with
    | empty => simp at h_card
    | cons x s ih =>
      simp only [prod_cons]
      have hx : 1 < x := h_gt x (mem_cons_self x s)
      have hs_all : ∀ y ∈ s, 1 ≤ y := by
        intro y hy
        have := h_gt y (mem_cons_of_mem hy)
        omega
      have hs_prod : 1 ≤ s.prod := prod_ge_one s hs_all
      nlinarith

  have good_and_prod_gt_one_of_reachable : ∀ {B' : Board}, Reachable B₀ B' → IsGood B' ∧ 1 < B'.prod := by
    intro B' hreach
    induction hreach with
    | refl =>
      have hG0 : IsGood B₀ := by
        refine ⟨hB₀.1, ?_⟩
        intro x hx
        have := hB₀.2 x hx
        omega
      have hP0 : 1 < B₀.prod := by
        have h_card : B₀.card ≥ 1 := by omega
        exact prod_gt_one_of_mem_gt_one h_card hB₀.2
      exact ⟨hG0, hP0⟩
    | tail h hM ih =>
      exact ⟨isGood_of_move ih.1 hM, prod_gt_one_of_move ih.1 hM ih.2⟩

  have h_good_and_prod := good_and_prod_gt_one_of_reachable hreach
  have hG' := h_good_and_prod.1
  have hP' := h_good_and_prod.2

  have filter_card_ge_one : 1 ≤ (B'.filter (fun a => 1 < a)).card := by
    by_contra h_card
    have h_card0 : (B'.filter (fun a => 1 < a)).card = 0 := by omega
    have h_filter_empty : B'.filter (fun a => 1 < a) = ∅ := card_eq_zero.mp h_card0
    have h_all_one : ∀ x ∈ B', x = 1 := by
      intro x hx
      have h_le : 1 ≤ x := hG'.2 x hx
      have h_not_gt : ¬ (1 < x) := by
        intro h_gt
        have h_mem : x ∈ B'.filter (fun a => 1 < a) := by
          simp [hx, h_gt]
        rw [h_filter_empty] at h_mem
        simp at h_mem
      omega
    have prod_eq_one_of_all_one : ∀ (s : Board), (∀ x ∈ s, x = 1) → s.prod = 1 := by
      intro s hs
      induction s using Multiset.induction with
      | empty => simp
      | cons y t ih =>
        simp only [prod_cons]
        have hy : y = 1 := hs y (mem_cons_self y t)
        have ht : t.prod = 1 := ih (fun z hz => hs z (mem_cons_of_mem hz))
        rw [hy, ht, one_mul]
    have h_prod_one : B'.prod = 1 := prod_eq_one_of_all_one B' h_all_one
    omega

  have h_term_unfold : (B'.filter (fun a => 1 < a)).card ≤ 1 := hterm
  unfold HasUniqueLarge
  omega
-- EVOLVE-BLOCK-END

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
-- EVOLVE-BLOCK-START
  intro M
  constructor
  · intro h
    have hM_eq : M = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₁ h₁ t₁ M h.1 h.2
    have hU₂ : HasUniqueLarge B₂ := statement_a_unique_large B₀ hB₀ B₂ h₂ t₂
    have h_ne : B₂.filter (fun a => 1 < a) ≠ ∅ := by
      intro hc
      unfold HasUniqueLarge at hU₂
      rw [hc] at hU₂
      simp at hU₂
    rcases Multiset.exists_mem_of_ne_zero h_ne with ⟨M₂, hM₂⟩
    rw [mem_filter] at hM₂
    have hM₂_eq : M₂ = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₂ h₂ t₂ M₂ hM₂.2 hM₂.1
    have h_eq : M = M₂ := by rw [hM_eq, hM₂_eq]
    rw [h_eq]
    exact ⟨hM₂.2, hM₂.1⟩
  · intro h
    have hM_eq : M = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₂ h₂ t₂ M h.1 h.2
    have hU₁ : HasUniqueLarge B₁ := statement_a_unique_large B₀ hB₀ B₁ h₁ t₁
    have h_ne : B₁.filter (fun a => 1 < a) ≠ ∅ := by
      intro hc
      unfold HasUniqueLarge at hU₁
      rw [hc] at hU₁
      simp at hU₁
    rcases Multiset.exists_mem_of_ne_zero h_ne with ⟨M₁, hM₁⟩
    rw [mem_filter] at hM₁
    have hM₁_eq : M₁ = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B₁ h₁ t₁ M₁ hM₁.2 hM₁.1
    have h_eq : M = M₁ := by rw [hM_eq, hM₁_eq]
    rw [h_eq]
    exact ⟨hM₁.2, hM₁.1⟩
-- EVOLVE-BLOCK-END