# Automatic Math Theorem Prover

By William Zhang

This repository contains an automatic theorem prover that I designed and implemented as a personal project. I have been very interested in Automated Theorem Proving (ATP) for a while, but it's not until very recently, particularly within the past year, that AI through Large Language Models (LLMs) could prove nontrivial theorems with frequent successes. Now with LLMs highly capable of advanced math reasoning such as ChatGPT, Claude, and Gemini readily available through API access, combined with the auto-verification feature of Lean 4, such an automatic tool is finally feasible and accessible. This project was an attempt in bringing such a tool to a wider audience. Coincidentally, a couple of weeks after this project concluded, OpenAI announced that they solved the Navier-Stokes Millennium Prize Problem with their in-house LLM ([Finite Time Blowup for Navier–Stokes](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)). This was in addition to other recent solutions to some decade-old open mathematics, physics, and computer science problems published by frontier AI labs including Anthropic, Google DeepMind, and OpenAI. It is such an exciting time for ATP, to say the least! 

The server can be accessed at [Math Prover](https://htmlpreview.github.io/?https://github.com/willyzhang109/MathProver1/blob/main/web/index.html).   Please note that the service may be unavailable due to spending limit reached.

## The Structure

- **The Interface:** The user interacts with the system through a web browser by entering the math theorem to be proved in either Lean 4 form or in natural language plus Lean 4 form. The request is then sent to the proof-synthesizing agent server. To facilitate users without much experience in Lean interacting with the system, an interface is also provided to convert a natural language problem statement to Lean 4 form. (Users can also use their favorite LLMs directly to convert to and/or verify the problem's Lean 4 form.) After a request is submitted, the user can monitor the progress of the proof-searching agent.
Lean 4 is required in both cases because it's the only automatic/programmatic way of verifying the LLM's proposed proof. While the Lean 4-only form provides a much more concise interface to the LLM, particularly for LLMs with a small context window size, the natural language statement option provides the LLM with more context for proof technique searching. 

- **The Core:** At the core is a Ralph loop that iteratively queries/prompts an LLM to complete the proof and automatically verifies the LLM’s responses using the Lean 4 compiler, feeding any errors back to the LLM, until either a complete proof is found or resource limit (token or LLM API budget) has been reached.

- **The Server:** A containerized RESTful server is implemented to take each user request from the frontend and fork a Ralph loop to handle it.

## The Benefit

- It guarantees the correctness of a proof through Lean 4.
- It saves manual human interactions with the LLM by automatically verifying the LLM's responses and feeding any errors back to the LLM.
- It does not stop working until a correct proof is found (or resource limit is reached).

## The Example

I fed the system the first problem from IMO 2026 in Lean 4-only form. With Gemini 3.6 Flash (knowledge cutoff date: 02/2026--so no leakage) as the LLM, it gave me a complete proof after about $10 of API spending. The original problem with a natural language solution can be found [here](https://artofproblemsolving.com/wiki/index.php?title=2026_IMO_Problems/Problem_1).

The problem in Lean 4 (The EVOLVE-BLOCK-START/END markers are for instructing the LLM where it can make changes):

```lean
import Mathlib
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
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
-- EVOLVE-BLOCK-START
  sorry
-- EVOLVE-BLOCK-END
```

The complete and verified proof returned by the agent after 6 loops (with no "sorry" lemmas or new axioms introduced), which can be fed to any Lean 4 compiler for verification:
```lean
import Mathlib
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
                     
  have board_card_move : ∀ {B B' : Board}, Move B B' → B'.card = B.card := by
    intro B B' h
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    simp only [Multiset.card_cons]

  have board_card_reachable : ∀ {B₀ B' : Board}, Reachable B₀ B' → B'.card = B₀.card := by
    intro B₀ B' h
    induction h with
    | refl => rfl
    | tail _ hstep ih => rw [board_card_move hstep, ih]

  have filter_card_le_card : ∀ (B : Board), (B.filter (fun a => 1 < a)).card ≤ B.card := by
    intro B
    exact Multiset.card_le_card (Multiset.filter_le (fun a => 1 < a) B)

  have board_ge_one_of_move : ∀ {B B' : Board}, Move B B' → (∀ x ∈ B, 1 ≤ x) → ∀ x ∈ B', 1 ≤ x := by
    intro B B' h hB
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have hgcd_pos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ (by omega)
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hgcd_pos
    · rw [Nat.one_le_div_iff hgcd_pos]
      exact Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) hdvd
    · exact hB x (by simp [hx])

  have board_ge_one_of_reachable : ∀ {B₀ B' : Board}, IsInitial B₀ → Reachable B₀ B' → ∀ x ∈ B', 1 ≤ x := by
    intro B₀ B' hB₀ hreach
    induction hreach with
    | refl => intro x hx; exact (hB₀.2 x hx).le
    | tail _ hstep ih => exact board_ge_one_of_move hstep ih

  let measure (B : Board) : ℕ := B.prod * 2027 + (B.filter (fun a => 1 < a)).card

  have measure_move : ∀ {B B' : Board}, Move B B' → (∀ x ∈ B, 1 ≤ x) → B.card ≤ 2026 → measure B' < measure B := by
    intro B B' h hge hcard
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    dsimp [measure]
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hgcd_pos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgcd_ge1 : 1 ≤ Nat.gcd m n := hgcd_pos
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have h_prod_B : (m ::ₘ n ::ₘ s).prod = m * n * s.prod := by simp [mul_assoc]
    have h_prod_B' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod = Nat.lcm m n * s.prod := by
      simp only [prod_cons]
      rw [← mul_assoc, Nat.mul_div_cancel' hdvd]
    have h_sprod_pos : 0 < s.prod := by
      apply Multiset.prod_pos
      intro x hx
      have := hge x (by simp [hx])
      omega
    have h_card_B' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card ≤ 2026 := by
      have : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).card = (m ::ₘ n ::ₘ s).card := by simp
      omega
    have h_filter_le' : (filter (fun a => 1 < a) (m.gcd n ::ₘ (m.lcm n / m.gcd n) ::ₘ s)).card ≤ 2026 := by
      exact Nat.le_trans (filter_card_le_card _) h_card_B'

    rcases Nat.eq_or_lt_of_le hgcd_ge1 with hgcd1 | hgcd_gt1
    · -- Case 1: gcd m n = 1
      have hlcm_mn : m.lcm n = m * n := by
        rw [Nat.lcm, hgcd1.symm, Nat.div_one]
      have hmn : 1 < m * n := by nlinarith
      rw [h_prod_B', h_prod_B, hgcd1.symm, hlcm_mn, Nat.div_one]
      simp [hm, hn, hmn]
    · -- Case 2: gcd m n > 1
      have h_mul_gcd : m.gcd n * m.lcm n = m * n := Nat.gcd_mul_lcm m n
      have h_lcm_pos : 0 < m.lcm n := Nat.lcm_pos (by omega) (by omega)
      have h_lcm_le : m.lcm n * 2 ≤ m * n := by
        calc m.lcm n * 2 ≤ m.lcm n * m.gcd n := Nat.mul_le_mul_left _ hgcd_gt1
        _ = m.gcd n * m.lcm n := by ring
        _ = m * n := h_mul_gcd
      have h_lcm_strict : m.lcm n < m * n := by omega
      have h_lcm_le' : m.lcm n + 1 ≤ m * n := by omega
      have h_prod_sub : m.lcm n * prod s + prod s ≤ m * n * prod s := by
        calc m.lcm n * prod s + prod s ≤ m.lcm n * prod s + m.lcm n * prod s := by
               have : prod s ≤ m.lcm n * prod s := Nat.le_mul_of_pos_left _ h_lcm_pos
               omega
        _ = (m.lcm n * 2) * prod s := by ring
        _ ≤ (m * n) * prod s := Nat.mul_le_mul_right (prod s) h_lcm_le
        _ = m * n * prod s := by ring
      have h_prod_sub' : m.lcm n * prod s + 1 ≤ m * n * prod s := by omega
      have h_filter_B : (filter (fun a => 1 < a) (m ::ₘ n ::ₘ s)).card = (filter (fun a => 1 < a) s).card + 2 := by
        simp [hm, hn]
      have h_step1 : m.lcm n * prod s * 2027 + 2026 < (m.lcm n * prod s + 1) * 2027 := by
        rw [Nat.add_one_mul]
        exact Nat.add_lt_add_left (Nat.lt_succ_self 2026) _
      have h_step2 : (m.lcm n * prod s + 1) * 2027 ≤ (m * n * prod s) * 2027 :=
        Nat.mul_le_mul_right 2027 h_prod_sub'
      have h_step0 : m.lcm n * prod s * 2027 + (filter (fun a => 1 < a) (m.gcd n ::ₘ (m.lcm n / m.gcd n) ::ₘ s)).card ≤ m.lcm n * prod s * 2027 + 2026 :=
        Nat.add_le_add_left h_filter_le' (m.lcm n * prod s * 2027)
      have h_step3 : m * n * prod s * 2027 ≤ m * n * prod s * 2027 + ((filter (fun a => 1 < a) s).card + 2) :=
        Nat.le_add_right (m * n * prod s * 2027) ((filter (fun a => 1 < a) s).card + 2)
      have h_step12 : m.lcm n * prod s * 2027 + 2026 < m * n * prod s * 2027 := lt_of_lt_of_le h_step1 h_step2
      have h_step123 : m.lcm n * prod s * 2027 + 2026 < m * n * prod s * 2027 + ((filter (fun a => 1 < a) s).card + 2) := lt_of_lt_of_le h_step12 h_step3
      rw [h_prod_B', h_prod_B, h_filter_B]
      exact Nat.lt_of_le_of_lt h_step0 h_step123

  intro ⟨f, hf0, hf_step⟩
  have hreach_f : ∀ k, Reachable B₀ (f k) := by
    intro k
    induction k with
    | zero => rw [hf0]; exact Relation.ReflTransGen.refl
    | succ k ih => exact Relation.ReflTransGen.tail ih (hf_step k)
  have hcard_f : ∀ k, (f k).card = 2026 := by
    intro k
    rw [board_card_reachable (hreach_f k), hB₀.1]
  have hge_f : ∀ k, ∀ x ∈ f k, 1 ≤ x := by
    intro k
    exact board_ge_one_of_reachable hB₀ (hreach_f k)
  have hdec : ∀ k, measure (f (k + 1)) < measure (f k) := by
    intro k
    exact measure_move (hf_step k) (hge_f k) (by rw [hcard_f k])
  have h_le : ∀ k, measure (f k) + k ≤ measure B₀ := by
    intro k
    induction k with
    | zero => rw [hf0]; omega
    | succ k ih =>
      have := hdec k
      omega
  have := h_le (measure B₀ + 1)
  omega
                   

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
                     
  have board_ge_one_of_move : ∀ {B B' : Board}, Move B B' → (∀ x ∈ B, 1 ≤ x) → ∀ x ∈ B', 1 ≤ x := by
    intro B B' h hB
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have hgcd_pos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ (by omega)
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hgcd_pos
    · rw [Nat.one_le_div_iff hgcd_pos]
      exact Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) hdvd
    · exact hB x (by simp [hx])
  have board_ge_one_of_reachable : ∀ {B₀ B' : Board}, IsInitial B₀ → Reachable B₀ B' → ∀ x ∈ B', 1 ≤ x := by
    intro B₀ B' hB₀ hreach
    induction hreach with
    | refl => intro x hx; exact (hB₀.2 x hx).le
    | tail _ hstep ih => exact board_ge_one_of_move hstep ih

  have padicValNat_gcd_eq : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    apply Nat.le_antisymm
    · rw [le_min_iff]
      constructor
      · rw [← padicValNat_dvd_iff_le ha]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_left a b)
      · rw [← padicValNat_dvd_iff_le hb]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_right a b)
    · rw [← padicValNat_dvd_iff_le hgcd]
      rw [Nat.dvd_gcd_iff]
      exact ⟨(padicValNat_dvd_iff_le ha).mpr (Nat.min_le_left _ _),
             (padicValNat_dvd_iff_le hb).mpr (Nat.min_le_right _ _)⟩

  have nat_gcd_min_sub : ∀ (x y : ℕ), Nat.gcd (min x y) (max x y - min x y) = Nat.gcd x y := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]; exact Nat.gcd_sub_self_right h
    · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h, Nat.gcd_comm]

  have padicValNat_lcm_div_gcd : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.lcm a b / Nat.gcd a b) = max (padicValNat p a) (padicValNat p b) - min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    have hlcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
    have hdvd : Nat.gcd a b ∣ Nat.lcm a b := Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
    have hdiv : Nat.lcm a b / Nat.gcd a b ≠ 0 := by
      rw [Nat.div_ne_zero_iff]
      exact ⟨hgcd, Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)) hdvd⟩
    have h_mul : a * b = Nat.gcd a b * Nat.gcd a b * (Nat.lcm a b / Nat.gcd a b) := by
      rw [mul_assoc, Nat.mul_div_cancel' hdvd, Nat.gcd_mul_lcm]
    have h_val := congr_arg (padicValNat p) h_mul
    rw [padicValNat.mul ha hb, padicValNat.mul (mul_ne_zero hgcd hgcd) hdiv, padicValNat.mul hgcd hgcd,
        padicValNat_gcd_eq p a b ha hb] at h_val
    generalize padicValNat p a = u at *
    generalize padicValNat p b = v at *
    omega

  have gExp_move : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Move B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    dsimp [gExp]
    simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
    rw [padicValNat_gcd_eq p m n hm0 hn0, padicValNat_lcm_div_gcd p m n hm0 hn0]
    have H : Nat.gcd (padicValNat p m) (Nat.gcd (padicValNat p n) (map (padicValNat p) s).gcd) =
             Nat.gcd (Nat.gcd (padicValNat p m) (padicValNat p n)) (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    have H' : Nat.gcd (min (padicValNat p m) (padicValNat p n))
                (Nat.gcd (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n))
                  (map (padicValNat p) s).gcd) =
              Nat.gcd (Nat.gcd (min (padicValNat p m) (padicValNat p n))
                         (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n)))
                (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    rw [H', nat_gcd_min_sub, H]

  have gExp_reachable : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Reachable B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    induction h with
    | refl => rfl
    | tail _ hstep ih => rw [gExp_move p hstep, ih]

  have gcd_zero_of_all_one : ∀ (p : ℕ) (B : Board), (∀ x ∈ B, x = 1) → (B.map (padicValNat p)).gcd = 0 := by
    intro p B h
    induction B using Multiset.induction with
    | empty => rfl
    | cons x s ih =>
      have hx : x = 1 := h x (mem_cons_self _ _)
      have hs : ∀ y ∈ s, y = 1 := fun y hy => h y (mem_cons_of_mem hy)
      rw [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd, hx]
      simp [ih hs]

  have hge : ∀ x ∈ B', 1 ≤ x := board_ge_one_of_reachable hB₀ hreach
  unfold HasUniqueLarge IsTerminal at *
  by_contra hneq
  have hcard0 : (B'.filter (fun a => 1 < a)).card = 0 := by omega
  have hfilter : B'.filter (fun a => 1 < a) = 0 := card_eq_zero.mp hcard0
  have hall1 : ∀ x ∈ B', x = 1 := by
    intro x hx
    have h1 : ¬(1 < x) := fun hlt => by
      have : x ∈ B'.filter (fun a => 1 < a) := mem_filter.mpr ⟨hx, hlt⟩
      rw [hfilter] at this
      contradiction
    have h2 : 1 ≤ x := hge x hx
    omega
  rcases Multiset.card_pos_iff_exists_mem.mp (by rw [hB₀.1]; omega) with ⟨a, ha⟩
  have ha1 : 1 < a := hB₀.2 a ha
  have ha_minFac : Nat.Prime a.minFac := Nat.minFac_prime (by omega)
  haveI hp : Fact (Nat.Prime a.minFac) := ⟨ha_minFac⟩
  have hdvd : a.minFac ∣ a := Nat.minFac_dvd a
  have hdvd_pow : a.minFac ^ 1 ∣ a := by simpa using hdvd
  have hval_pos : 1 ≤ padicValNat a.minFac a := (padicValNat_dvd_iff_le (by omega)).mp hdvd_pow
  have hmem_map : padicValNat a.minFac a ∈ B₀.map (padicValNat a.minFac) := mem_map_of_mem _ ha
  have hgcd_dvd := Multiset.gcd_dvd hmem_map
  have hgExp0 : gExp a.minFac B₀ ≠ 0 := by
    intro hzero
    dsimp [gExp] at hzero
    rw [hzero] at hgcd_dvd
    have : 0 ∣ padicValNat a.minFac a := hgcd_dvd
    have : padicValNat a.minFac a = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have hgExp' : gExp a.minFac B' = gExp a.minFac B₀ := gExp_reachable a.minFac hreach
  have hgExp'_zero : gExp a.minFac B' = 0 := by
    dsimp [gExp]
    exact gcd_zero_of_all_one a.minFac B' hall1
  omega
                   

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
                     
  have board_ge_one_of_move : ∀ {B B' : Board}, Move B B' → (∀ x ∈ B, 1 ≤ x) → ∀ x ∈ B', 1 ≤ x := by
    intro B B' h hB
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have hgcd_pos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ (by omega)
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hgcd_pos
    · rw [Nat.one_le_div_iff hgcd_pos]
      exact Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) hdvd
    · exact hB x (by simp [hx])
  have board_ge_one_of_reachable : ∀ {B₀ B' : Board}, IsInitial B₀ → Reachable B₀ B' → ∀ x ∈ B', 1 ≤ x := by
    intro B₀ B' hB₀ hreach
    induction hreach with
    | refl => intro x hx; exact (hB₀.2 x hx).le
    | tail _ hstep ih => exact board_ge_one_of_move hstep ih

  have padicValNat_gcd_eq : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    apply Nat.le_antisymm
    · rw [le_min_iff]
      constructor
      · rw [← padicValNat_dvd_iff_le ha]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_left a b)
      · rw [← padicValNat_dvd_iff_le hb]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_right a b)
    · rw [← padicValNat_dvd_iff_le hgcd]
      rw [Nat.dvd_gcd_iff]
      exact ⟨(padicValNat_dvd_iff_le ha).mpr (Nat.min_le_left _ _),
             (padicValNat_dvd_iff_le hb).mpr (Nat.min_le_right _ _)⟩

  have nat_gcd_min_sub : ∀ (x y : ℕ), Nat.gcd (min x y) (max x y - min x y) = Nat.gcd x y := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]; exact Nat.gcd_sub_self_right h
    · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h, Nat.gcd_comm]

  have padicValNat_lcm_div_gcd : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.lcm a b / Nat.gcd a b) = max (padicValNat p a) (padicValNat p b) - min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    have hlcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
    have hdvd : Nat.gcd a b ∣ Nat.lcm a b := Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
    have hdiv : Nat.lcm a b / Nat.gcd a b ≠ 0 := by
      rw [Nat.div_ne_zero_iff]
      exact ⟨hgcd, Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)) hdvd⟩
    have h_mul : a * b = Nat.gcd a b * Nat.gcd a b * (Nat.lcm a b / Nat.gcd a b) := by
      rw [mul_assoc, Nat.mul_div_cancel' hdvd, Nat.gcd_mul_lcm]
    have h_val := congr_arg (padicValNat p) h_mul
    rw [padicValNat.mul ha hb, padicValNat.mul (mul_ne_zero hgcd hgcd) hdiv, padicValNat.mul hgcd hgcd,
        padicValNat_gcd_eq p a b ha hb] at h_val
    generalize padicValNat p a = u at *
    generalize padicValNat p b = v at *
    omega

  have gExp_move : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Move B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    dsimp [gExp]
    simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
    rw [padicValNat_gcd_eq p m n hm0 hn0, padicValNat_lcm_div_gcd p m n hm0 hn0]
    have H : Nat.gcd (padicValNat p m) (Nat.gcd (padicValNat p n) (map (padicValNat p) s).gcd) =
             Nat.gcd (Nat.gcd (padicValNat p m) (padicValNat p n)) (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    have H' : Nat.gcd (min (padicValNat p m) (padicValNat p n))
                (Nat.gcd (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n))
                  (map (padicValNat p) s).gcd) =
              Nat.gcd (Nat.gcd (min (padicValNat p m) (padicValNat p n))
                         (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n)))
                (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    rw [H', nat_gcd_min_sub, H]

  have gExp_reachable : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Reachable B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    induction h with
    | refl => rfl
    | tail _ hstep ih => rw [gExp_move p hstep, ih]

  have h_prod : ∀ (n : ℕ), n ≠ 0 → ∏ p ∈ n.primeFactors, p ^ padicValNat p n = n := by
    intro n hn
    rw [← Nat.support_factorization n]
    have : (∏ p ∈ n.factorization.support, p ^ padicValNat p n) = ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization n]; exact hp)
      rw [Nat.factorization_def n hp_prime]
    rw [this]
    exact Nat.factorization_prod_pow_eq_self hn

  have gcd_zero_of_all_one : ∀ (p : ℕ) (B : Board), (∀ x ∈ B, x = 1) → (B.map (padicValNat p)).gcd = 0 := by
    intro p B h
    induction B using Multiset.induction with
    | empty => rfl
    | cons x s ih =>
      have hx : x = 1 := h x (mem_cons_self _ _)
      have hs : ∀ y ∈ s, y = 1 := fun y hy => h y (mem_cons_of_mem hy)
      rw [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd, hx]
      simp [ih hs]

  have hmap_zero_gcd : ∀ (p : ℕ) (B : Board), (∀ v ∈ B.map (padicValNat p), v = 0) → (B.map (padicValNat p)).gcd = 0 := by
    intro p B h
    induction B using Multiset.induction with
    | empty => rfl
    | cons x s ih =>
      simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
      have hx0 : padicValNat p x = 0 := h (padicValNat p x) (mem_map_of_mem _ (mem_cons_self _ _))
      have hs0 : (s.map (padicValNat p)).gcd = 0 := ih (fun v hv => by
        rcases mem_map.mp hv with ⟨y, hy, rfl⟩
        exact h (padicValNat p y) (mem_map_of_mem _ (mem_cons_of_mem hy)))
      rw [hx0, hs0, Nat.gcd_zero_right]

  have terminal_eq_Mval : ∀ (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') (M : ℕ) (hM : 1 < M) (hMem : M ∈ B'), M = Mval B₀ := by
    intro B' hreach hterm M hM hMem
    have hge : ∀ x ∈ B', 1 ≤ x := board_ge_one_of_reachable hB₀ hreach
    rcases Multiset.exists_cons_of_mem hMem with ⟨s, rfl⟩
    have hs_ones : ∀ y ∈ s, y = 1 := by
      intro y hy
      have hy_ge : 1 ≤ y := hge y (mem_cons_of_mem hy)
      have hy_le : ¬(1 < y) := by
        intro hlt
        unfold IsTerminal at hterm
        have hsub : M ::ₘ y ::ₘ 0 ≤ (M ::ₘ s).filter (fun a => 1 < a) := by
          rw [Multiset.filter_cons, if_pos hM]
          have hy_mem : y ∈ s.filter (fun a => 1 < a) := mem_filter.mpr ⟨hy, hlt⟩
          exact Multiset.cons_le_cons M (Multiset.singleton_le.mpr hy_mem)
        have hcard_le := Multiset.card_le_card hsub
        simp at hcard_le
        omega
      omega

    have h_gExp_val : ∀ (p : ℕ) [Fact (Nat.Prime p)], gExp p (M ::ₘ s) = padicValNat p M := by
      intro p hp
      dsimp [gExp]
      simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
      have hs_zero : (s.map (padicValNat p)).gcd = 0 := gcd_zero_of_all_one p s hs_ones
      rw [hs_zero, Nat.gcd_zero_right]

    have hM0 : M ≠ 0 := by omega
    have hM_prod := (h_prod M hM0).symm
    rw [hM_prod]
    unfold Mval
    have h_pf_eq : M.primeFactors = B₀.prod.primeFactors := by
      ext p
      rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
      have hB₀_prod0 : B₀.prod ≠ 0 := by
        intro h0
        have : 0 ∈ B₀ := Multiset.prod_eq_zero_iff.mp h0
        have := hB₀.2 0 this
        omega
      constructor
      · intro ⟨hp, hdvd, _⟩
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        have hdvd1 : p ^ 1 ∣ M := by simpa using hdvd
        have hval : 1 ≤ padicValNat p M := (padicValNat_dvd_iff_le hM0).mp hdvd1
        have hgExp_B' : 1 ≤ gExp p (M ::ₘ s) := by rw [h_gExp_val p]; exact hval
        have hgExp_B₀ : 1 ≤ gExp p B₀ := by rw [← gExp_reachable p hreach]; exact hgExp_B'
        dsimp [gExp] at hgExp_B₀
        have hmap_nonempty : ∃ v ∈ B₀.map (padicValNat p), 1 ≤ v := by
          by_contra hnone
          push_neg at hnone
          have hgcd_zero : (B₀.map (padicValNat p)).gcd = 0 := hmap_zero_gcd p B₀ (fun v hv => by
            have := hnone v hv
            omega)
          rw [hgcd_zero] at hgExp_B₀
          omega
        rcases hmap_nonempty with ⟨v, hv, hv_pos⟩
        rcases Multiset.mem_map.mp hv with ⟨b, hb, rfl⟩
        have hb0 : b ≠ 0 := by have hgt := hB₀.2 b hb; omega
        have hp_dvd_b : p ∣ b := by simpa using (padicValNat_dvd_iff_le hb0).mpr hv_pos
        have hb_dvd_prod : b ∣ B₀.prod := Multiset.dvd_prod hb
        exact ⟨hp, Nat.dvd_trans hp_dvd_b hb_dvd_prod, hB₀_prod0⟩
      · intro ⟨hp, hdvd, _⟩
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        have hp_prime : Prime p := Nat.Prime.prime hp
        rcases hp_prime.exists_mem_multiset_dvd hdvd with ⟨b, hb, hp_dvd_b⟩
        have hb0 : b ≠ 0 := by have hgt := hB₀.2 b hb; omega
        have hp_dvd_b' : p ^ 1 ∣ b := by simpa using hp_dvd_b
        have hv_pos : 1 ≤ padicValNat p b := (padicValNat_dvd_iff_le hb0).mp hp_dvd_b'
        have hmem_map : padicValNat p b ∈ B₀.map (padicValNat p) := Multiset.mem_map_of_mem _ hb
        have hgcd_dvd := Multiset.gcd_dvd hmem_map
        have hgExp_pos : 1 ≤ gExp p B₀ := by
          dsimp [gExp]
          exact Nat.pos_of_ne_zero (by intro h0; rw [h0] at hgcd_dvd; have := Nat.eq_zero_of_zero_dvd hgcd_dvd; omega)
        have hgExp_B' : 1 ≤ gExp p (M ::ₘ s) := by rw [gExp_reachable p hreach]; exact hgExp_pos
        rw [h_gExp_val p] at hgExp_B'
        have hp_dvd_M : p ∣ M := by simpa using (padicValNat_dvd_iff_le hM0).mpr hgExp_B'
        exact ⟨hp, hp_dvd_M, hM0⟩

    rw [← h_pf_eq]
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
    rw [← h_gExp_val p, gExp_reachable p hreach]

  intro M
  constructor
  · intro ⟨hM1, hM1_mem⟩
    have hM_eq : M = Mval B₀ := terminal_eq_Mval B₁ h₁ t₁ M hM1 hM1_mem
    have hlarge2 := statement_a_unique_large B₀ hB₀ B₂ h₂ t₂
    unfold HasUniqueLarge at hlarge2
    rcases Multiset.card_eq_one.mp hlarge2 with ⟨M₂, hM₂_filter⟩
    have hM₂_mem_filter : M₂ ∈ B₂.filter (fun a => 1 < a) := by rw [hM₂_filter]; exact Multiset.mem_singleton_self M₂
    rw [mem_filter] at hM₂_mem_filter
    have hM₂_eq : M₂ = Mval B₀ := terminal_eq_Mval B₂ h₂ t₂ M₂ hM₂_mem_filter.2 hM₂_mem_filter.1
    subst hM_eq hM₂_eq
    exact ⟨hM₂_mem_filter.2, hM₂_mem_filter.1⟩
  · intro ⟨hM2, hM2_mem⟩
    have hM_eq : M = Mval B₀ := terminal_eq_Mval B₂ h₂ t₂ M hM2 hM2_mem
    have hlarge1 := statement_a_unique_large B₀ hB₀ B₁ h₁ t₁
    unfold HasUniqueLarge at hlarge1
    rcases Multiset.card_eq_one.mp hlarge1 with ⟨M₁, hM₁_filter⟩
    have hM₁_mem_filter : M₁ ∈ B₁.filter (fun a => 1 < a) := by rw [hM₁_filter]; exact Multiset.mem_singleton_self M₁
    rw [mem_filter] at hM₁_mem_filter
    have hM₁_eq : M₁ = Mval B₀ := terminal_eq_Mval B₁ h₁ t₁ M₁ hM₁_mem_filter.2 hM₁_mem_filter.1
    subst hM_eq hM₁_eq
    exact ⟨hM₁_mem_filter.2, hM₁_mem_filter.1⟩
                   

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
                     
  have board_ge_one_of_move : ∀ {B B' : Board}, Move B B' → (∀ x ∈ B, 1 ≤ x) → ∀ x ∈ B', 1 ≤ x := by
    intro B B' h hB
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
    have hgcd_pos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ (by omega)
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hgcd_pos
    · rw [Nat.one_le_div_iff hgcd_pos]
      exact Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) hdvd
    · exact hB x (by simp [hx])
  have board_ge_one_of_reachable : ∀ {B₀ B' : Board}, IsInitial B₀ → Reachable B₀ B' → ∀ x ∈ B', 1 ≤ x := by
    intro B₀ B' hB₀ hreach
    induction hreach with
    | refl => intro x hx; exact (hB₀.2 x hx).le
    | tail _ hstep ih => exact board_ge_one_of_move hstep ih

  have padicValNat_gcd_eq : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    apply Nat.le_antisymm
    · rw [le_min_iff]
      constructor
      · rw [← padicValNat_dvd_iff_le ha]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_left a b)
      · rw [← padicValNat_dvd_iff_le hb]
        exact Nat.dvd_trans (padicValNat_dvd_iff_le hgcd |>.mpr (by rfl)) (Nat.gcd_dvd_right a b)
    · rw [← padicValNat_dvd_iff_le hgcd]
      rw [Nat.dvd_gcd_iff]
      exact ⟨(padicValNat_dvd_iff_le ha).mpr (Nat.min_le_left _ _),
             (padicValNat_dvd_iff_le hb).mpr (Nat.min_le_right _ _)⟩

  have nat_gcd_min_sub : ∀ (x y : ℕ), Nat.gcd (min x y) (max x y - min x y) = Nat.gcd x y := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]; exact Nat.gcd_sub_self_right h
    · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h, Nat.gcd_comm]

  have padicValNat_lcm_div_gcd : ∀ (p a b : ℕ) [Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 →
      padicValNat p (Nat.lcm a b / Nat.gcd a b) = max (padicValNat p a) (padicValNat p b) - min (padicValNat p a) (padicValNat p b) := by
    intro p a b hp ha hb
    have hgcd : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
    have hlcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
    have hdvd : Nat.gcd a b ∣ Nat.lcm a b := Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
    have hdiv : Nat.lcm a b / Nat.gcd a b ≠ 0 := by
      rw [Nat.div_ne_zero_iff]
      exact ⟨hgcd, Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)) hdvd⟩
    have h_mul : a * b = Nat.gcd a b * Nat.gcd a b * (Nat.lcm a b / Nat.gcd a b) := by
      rw [mul_assoc, Nat.mul_div_cancel' hdvd, Nat.gcd_mul_lcm]
    have h_val := congr_arg (padicValNat p) h_mul
    rw [padicValNat.mul ha hb, padicValNat.mul (mul_ne_zero hgcd hgcd) hdiv, padicValNat.mul hgcd hgcd,
        padicValNat_gcd_eq p a b ha hb] at h_val
    generalize padicValNat p a = u at *
    generalize padicValNat p b = v at *
    omega

  have gExp_move : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Move B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    rcases h with ⟨m, n, s, hm, hn, rfl, rfl⟩
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    dsimp [gExp]
    simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
    rw [padicValNat_gcd_eq p m n hm0 hn0, padicValNat_lcm_div_gcd p m n hm0 hn0]
    have H : Nat.gcd (padicValNat p m) (Nat.gcd (padicValNat p n) (map (padicValNat p) s).gcd) =
             Nat.gcd (Nat.gcd (padicValNat p m) (padicValNat p n)) (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    have H' : Nat.gcd (min (padicValNat p m) (padicValNat p n))
                (Nat.gcd (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n))
                  (map (padicValNat p) s).gcd) =
              Nat.gcd (Nat.gcd (min (padicValNat p m) (padicValNat p n))
                         (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n)))
                (map (padicValNat p) s).gcd := by
      rw [Nat.gcd_assoc]
    rw [H', nat_gcd_min_sub, H]

  have gExp_reachable : ∀ (p : ℕ) [Fact (Nat.Prime p)] {B B' : Board}, Reachable B B' → gExp p B' = gExp p B := by
    intro p hp B B' h
    induction h with
    | refl => rfl
    | tail _ hstep ih => rw [gExp_move p hstep, ih]

  have h_prod : ∀ (n : ℕ), n ≠ 0 → ∏ p ∈ n.primeFactors, p ^ padicValNat p n = n := by
    intro n hn
    rw [← Nat.support_factorization n]
    have : (∏ p ∈ n.factorization.support, p ^ padicValNat p n) = ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization n]; exact hp)
      rw [Nat.factorization_def n hp_prime]
    rw [this]
    exact Nat.factorization_prod_pow_eq_self hn

  have gcd_zero_of_all_one : ∀ (p : ℕ) (B : Board), (∀ x ∈ B, x = 1) → (B.map (padicValNat p)).gcd = 0 := by
    intro p B h
    induction B using Multiset.induction with
    | empty => rfl
    | cons x s ih =>
      have hx : x = 1 := h x (mem_cons_self _ _)
      have hs : ∀ y ∈ s, y = 1 := fun y hy => h y (mem_cons_of_mem hy)
      rw [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd, hx]
      simp [ih hs]

  have hmap_zero_gcd : ∀ (p : ℕ) (B : Board), (∀ v ∈ B.map (padicValNat p), v = 0) → (B.map (padicValNat p)).gcd = 0 := by
    intro p B h
    induction B using Multiset.induction with
    | empty => rfl
    | cons x s ih =>
      simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
      have hx0 : padicValNat p x = 0 := h (padicValNat p x) (mem_map_of_mem _ (mem_cons_self _ _))
      have hs0 : (s.map (padicValNat p)).gcd = 0 := ih (fun v hv => by
        rcases mem_map.mp hv with ⟨y, hy, rfl⟩
        exact h (padicValNat p y) (mem_map_of_mem _ (mem_cons_of_mem hy)))
      rw [hx0, hs0, Nat.gcd_zero_right]

  have hge : ∀ x ∈ B', 1 ≤ x := board_ge_one_of_reachable hB₀ hreach
  rcases Multiset.exists_cons_of_mem hMem with ⟨s, rfl⟩
  have hs_ones : ∀ y ∈ s, y = 1 := by
    intro y hy
    have hy_ge : 1 ≤ y := hge y (mem_cons_of_mem hy)
    have hy_le : ¬(1 < y) := by
      intro hlt
      unfold IsTerminal at hterm
      have hsub : M ::ₘ y ::ₘ 0 ≤ (M ::ₘ s).filter (fun a => 1 < a) := by
        rw [Multiset.filter_cons, if_pos hM]
        have hy_mem : y ∈ s.filter (fun a => 1 < a) := mem_filter.mpr ⟨hy, hlt⟩
        exact Multiset.cons_le_cons M (Multiset.singleton_le.mpr hy_mem)
      have hcard_le := Multiset.card_le_card hsub
      simp at hcard_le
      omega
    omega

  have h_gExp_val : ∀ (p : ℕ) [Fact (Nat.Prime p)], gExp p (M ::ₘ s) = padicValNat p M := by
    intro p hp
    dsimp [gExp]
    simp only [map_cons, Multiset.gcd_cons, gcd_eq_nat_gcd]
    have hs_zero : (s.map (padicValNat p)).gcd = 0 := gcd_zero_of_all_one p s hs_ones
    rw [hs_zero, Nat.gcd_zero_right]

  have hM0 : M ≠ 0 := by omega
  have hM_prod := (h_prod M hM0).symm
  rw [hM_prod]
  unfold Mval
  have h_pf_eq : M.primeFactors = B₀.prod.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    have hB₀_prod0 : B₀.prod ≠ 0 := by
      intro h0
      have : 0 ∈ B₀ := Multiset.prod_eq_zero_iff.mp h0
      have := hB₀.2 0 this
      omega
    constructor
    · intro ⟨hp, hdvd, _⟩
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have hdvd1 : p ^ 1 ∣ M := by simpa using hdvd
      have hval : 1 ≤ padicValNat p M := (padicValNat_dvd_iff_le hM0).mp hdvd1
      have hgExp_B' : 1 ≤ gExp p (M ::ₘ s) := by rw [h_gExp_val p]; exact hval
      have hgExp_B₀ : 1 ≤ gExp p B₀ := by rw [← gExp_reachable p hreach]; exact hgExp_B'
      dsimp [gExp] at hgExp_B₀
      have hmap_nonempty : ∃ v ∈ B₀.map (padicValNat p), 1 ≤ v := by
        by_contra hnone
        push_neg at hnone
        have hgcd_zero : (B₀.map (padicValNat p)).gcd = 0 := hmap_zero_gcd p B₀ (fun v hv => by
          have := hnone v hv
          omega)
        rw [hgcd_zero] at hgExp_B₀
        omega
      rcases hmap_nonempty with ⟨v, hv, hv_pos⟩
      rcases Multiset.mem_map.mp hv with ⟨b, hb, rfl⟩
      have hb0 : b ≠ 0 := by have hgt := hB₀.2 b hb; omega
      have hp_dvd_b : p ∣ b := by simpa using (padicValNat_dvd_iff_le hb0).mpr hv_pos
      have hb_dvd_prod : b ∣ B₀.prod := Multiset.dvd_prod hb
      exact ⟨hp, Nat.dvd_trans hp_dvd_b hb_dvd_prod, hB₀_prod0⟩
    · intro ⟨hp, hdvd, _⟩
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have hp_prime : Prime p := Nat.Prime.prime hp
      rcases hp_prime.exists_mem_multiset_dvd hdvd with ⟨b, hb, hp_dvd_b⟩
      have hb0 : b ≠ 0 := by have hgt := hB₀.2 b hb; omega
      have hp_dvd_b' : p ^ 1 ∣ b := by simpa using hp_dvd_b
      have hv_pos : 1 ≤ padicValNat p b := (padicValNat_dvd_iff_le hb0).mp hp_dvd_b'
      have hmem_map : padicValNat p b ∈ B₀.map (padicValNat p) := Multiset.mem_map_of_mem _ hb
      have hgcd_dvd := Multiset.gcd_dvd hmem_map
      have hgExp_pos : 1 ≤ gExp p B₀ := by
        dsimp [gExp]
        exact Nat.pos_of_ne_zero (by intro h0; rw [h0] at hgcd_dvd; have := Nat.eq_zero_of_zero_dvd hgcd_dvd; omega)
      have hgExp_B' : 1 ≤ gExp p (M ::ₘ s) := by rw [gExp_reachable p hreach]; exact hgExp_pos
      rw [h_gExp_val p] at hgExp_B'
      have hp_dvd_M : p ∣ M := by simpa using (padicValNat_dvd_iff_le hM0).mpr hgExp_B'
      exact ⟨hp, hp_dvd_M, hM0⟩

  rw [← h_pf_eq]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  rw [← h_gExp_val p, gExp_reachable p hreach]
                   

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
                     
  rcases Multiset.card_pos_iff_exists_mem.mp (by rw [hB₀.1]; omega) with ⟨a, ha⟩
  have ha1 : 1 < a := hB₀.2 a ha
  have ha_minFac : Nat.Prime a.minFac := Nat.minFac_prime (by omega)
  haveI hp : Fact (Nat.Prime a.minFac) := ⟨ha_minFac⟩
  have hdvd_a : a.minFac ∣ a := Nat.minFac_dvd a
  have hdvd_prod : a ∣ B₀.prod := Multiset.dvd_prod ha
  have hdvd_p_prod : a.minFac ∣ B₀.prod := Nat.dvd_trans hdvd_a hdvd_prod
  have hprod0 : B₀.prod ≠ 0 := by
    intro h0
    have : 0 ∈ B₀ := Multiset.prod_eq_zero_iff.mp h0
    have := hB₀.2 0 this
    omega
  have hmem_pf : a.minFac ∈ B₀.prod.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨ha_minFac, hdvd_p_prod, hprod0⟩
  have hdvd_pow : a.minFac ^ 1 ∣ a := by simpa using hdvd_a
  have hval_pos : 1 ≤ padicValNat a.minFac a := (padicValNat_dvd_iff_le (by omega)).mp hdvd_pow
  have hmem_map : padicValNat a.minFac a ∈ B₀.map (padicValNat a.minFac) := Multiset.mem_map_of_mem _ ha
  have hgcd_dvd := Multiset.gcd_dvd hmem_map
  have hgExp_pos : 1 ≤ gExp a.minFac B₀ := by
    dsimp [gExp]
    refine Nat.pos_of_ne_zero ?_
    intro hzero
    rw [hzero] at hgcd_dvd
    have := Nat.eq_zero_of_zero_dvd hgcd_dvd
    omega
  unfold Mval
  have hpow_ge : 2 ≤ a.minFac ^ gExp a.minFac B₀ := by
    calc 2 ≤ a.minFac := ha_minFac.two_le
    _ = a.minFac ^ 1 := (pow_one _).symm
    _ ≤ a.minFac ^ gExp a.minFac B₀ := Nat.pow_le_pow_right ha_minFac.pos hgExp_pos
  have hprod_ge : a.minFac ^ gExp a.minFac B₀ ≤ ∏ p ∈ B₀.prod.primeFactors, p ^ gExp p B₀ := by
    exact Finset.single_le_prod' (fun p hp_mem => Nat.one_le_pow (gExp p B₀) p (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp_mem))) hmem_pf
  omega
```






