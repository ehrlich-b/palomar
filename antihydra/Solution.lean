/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Solution: Antihydra has no semilinear inductive safety invariant

This package uses Shawn Ligocki's shifted Antihydra recurrence. The proof is
adapted from the arithmetic portion of Bryan Ehrlich's
`AntihydraSemilinear.lean` (revision `9bb9d1b427ecee4f03900693818f82522a1d3e34`).
-/

@[expose] public section

namespace AntihydraPalomar

/-- One arithmetic round. `none` counts the attempted step that overspends. -/
def step (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if p.1 % 2 = 0 then some (3 * p.1 / 2, p.2 + 2)
  else if p.2 = 0 then none
  else some (3 * p.1 / 2, p.2 - 1)

/-- A set containing the seed whose every member takes a successful step within the set. -/
def IsSafetyInvariant (I : Set (ℕ × ℕ)) : Prop :=
  (8, 0) ∈ I ∧ ∀ p ∈ I, ∃ q ∈ I, step p = some q

/-- Run at most `n` rounds, with halting absorbing. -/
def run {α : Type*} (next : α → Option α) : ℕ → α → Option α
  | 0, p => some p
  | n + 1, p => (next p).bind (run next n)

private theorem run_of_invariant {I : Set (ℕ × ℕ)} (hI : IsSafetyInvariant I)
    {p : ℕ × ℕ} (hp : p ∈ I) (n : ℕ) :
    ∃ q ∈ I, run step n p = some q := by
  induction n generalizing p with
  | zero => exact ⟨p, hp, rfl⟩
  | succ n ih =>
    obtain ⟨q, hq, hstep⟩ := hI.2 p hp
    simpa [run, hstep] using ih hq

/-- An odd stride reaches the residue 1 modulo every power of two. -/
private theorem odd_stride_hits_one (a d : ℕ) (hd : d % 2 = 1) (k : ℕ) :
    ∃ j q : ℕ, a + j * d = 1 + 2 ^ k * q := by
  induction k with
  | zero => exact ⟨1, a + d - 1, by simp; omega⟩
  | succ k ih =>
    obtain ⟨j, q, h⟩ := ih
    by_cases hq : q % 2 = 0
    · refine ⟨j, q / 2, ?_⟩
      have hq' : q = 2 * (q / 2) := by omega
      calc
        a + j * d = 1 + 2 ^ k * q := h
        _ = 1 + 2 ^ (k + 1) * (q / 2) := by
          conv_lhs => rw [hq']
          rw [pow_succ]
          ring
    · refine ⟨j + 2 ^ k, (q + d) / 2, ?_⟩
      have hqd : q + d = 2 * ((q + d) / 2) := by omega
      calc
        a + (j + 2 ^ k) * d = (a + j * d) + 2 ^ k * d := by ring
        _ = 1 + 2 ^ k * (q + d) := by rw [h]; ring
        _ = 1 + 2 ^ (k + 1) * ((q + d) / 2) := by
          conv_lhs => rw [hqd]
          rw [pow_succ]
          ring

private theorem step_value_one_add (k q : ℕ) :
    3 * (1 + 2 ^ (k + 1) * q) / 2 = 1 + 2 ^ k * (3 * q) := by
  rw [pow_succ]
  have h : 3 * (1 + 2 ^ k * 2 * q) = 2 * (1 + 2 ^ k * (3 * q)) + 1 := by ring
  rw [h]
  omega

private theorem odd_run_halts (c q : ℕ) :
    run step (c + 1) (1 + 2 ^ (c + 1) * q, c) = none := by
  induction c generalizing q with
  | zero =>
    simp [run, step]
  | succ c ih =>
    have ho : (1 + 2 ^ (c + 1 + 1) * q) % 2 ≠ 0 := by
      rw [pow_succ]
      have h : 2 ^ (c + 1) * 2 * q = 2 * (2 ^ (c + 1) * q) := by ring
      omega
    simpa [run, step, ho, step_value_one_add] using ih (3 * q)

private theorem step_shift (a c d j : ℕ) :
    step (a + j * (2 * d), c) =
      (step (a, c)).map (fun p => (p.1 + j * (3 * d), p.2)) := by
  have hm : j * (2 * d) = 2 * (j * d) := by ring
  have hpar : (a + j * (2 * d)) % 2 = a % 2 := by rw [hm]; omega
  have hx : 3 * (a + j * (2 * d)) / 2 = 3 * a / 2 + j * (3 * d) := by
    have h : 3 * (a + j * (2 * d)) = 3 * a + 2 * (j * (3 * d)) := by ring
    rw [h]
    omega
  by_cases he : a % 2 = 0 <;> by_cases hc : c = 0 <;>
    simp [step, he, hc, hpar, hx]

private theorem step_credit {p q : ℕ × ℕ} (h : step p = some q) : q.2 ≤ p.2 + 2 := by
  unfold step at h
  split at h
  · cases h
    exact le_rfl
  · split at h
    · contradiction
    · cases h
      omega

private theorem ray_halts_factored (h a c u : ℕ) (hu : u % 2 = 1) :
    ∃ j t : ℕ, t ≤ c + 3 * h + 1 ∧ run step t (a + j * (2 ^ h * u), c) = none := by
  induction h generalizing a c u with
  | zero =>
    obtain ⟨j, q, hj⟩ := odd_stride_hits_one a u hu (c + 1)
    exact ⟨j, c + 1, by omega, by simpa [hj] using odd_run_halts c q⟩
  | succ h ih =>
    cases hs : step (a, c) with
    | none => exact ⟨0, 1, by omega, by simp [run, hs]⟩
    | some p =>
      have hcredit := step_credit hs
      have hu' : (3 * u) % 2 = 1 := by omega
      obtain ⟨j, t, ht, hrun⟩ := ih p.1 p.2 (3 * u) hu'
      have hd : 2 ^ (h + 1) * u = 2 * (2 ^ h * u) := by rw [pow_succ]; ring
      have hd' : 3 * (2 ^ h * u) = 2 ^ h * (3 * u) := by ring
      refine ⟨j, t + 1, by omega, ?_⟩
      simpa [run, hd, step_shift, hs, hd'] using hrun

/-- Every positive horizontal ray has a point that halts within the stated number of rounds. -/
theorem horizontal_ray_halts (a c d : ℕ) (hd : 0 < d) :
    ∃ j t : ℕ, t ≤ c + 3 * padicValNat 2 d + 1 ∧ run step t (a + j * d, c) = none := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := pow_padicValNat_dvd (p := 2) (n := d)
  have hu' : u % 2 = 1 := by
    by_contra hn
    have he : u = 2 * (u / 2) := by omega
    apply pow_succ_padicValNat_not_dvd (p := 2) hd.ne'
    refine ⟨u / 2, ?_⟩
    calc
      d = 2 ^ padicValNat 2 d * u := hu
      _ = 2 ^ (padicValNat 2 d + 1) * (u / 2) := by
        conv_lhs => rw [he]
        rw [pow_succ]
        ring
  simpa only [← hu] using ray_halts_factored (padicValNat 2 d) a c u hu'

private def HasHorizontalRay (I : Set (ℕ × ℕ)) : Prop :=
  ∃ a c d : ℕ, 0 < d ∧ ∀ j : ℕ, (a + j * d, c) ∈ I

private theorem invariant_ray_free {I : Set (ℕ × ℕ)} (hI : IsSafetyInvariant I) :
    ¬ HasHorizontalRay I := by
  rintro ⟨a, c, d, hd, hray⟩
  obtain ⟨j, t, _, ht⟩ := horizontal_ray_halts a c d hd
  obtain ⟨q, _, hq⟩ := run_of_invariant hI (hray j) t
  rw [ht] at hq
  contradiction

private theorem linear_bound {I : Set (ℕ × ℕ)} (hI : IsLinearSet I)
    (hray : ¬ HasHorizontalRay I) : ∃ K : ℕ, ∀ p ∈ I, p.1 ≤ K * (p.2 + 1) := by
  classical
  obtain ⟨a, S, rfl⟩ := isLinearSet_iff.mp hI
  let M := AddSubmonoid.closure (S : Set (ℕ × ℕ))
  let K := a.1 + ∑ p ∈ S, p.1
  have hgen (p : ℕ × ℕ) (hp : p ∈ S) : p.1 ≤ K * p.2 := by
    by_cases hpz : p.2 = 0
    · have hx : p.1 = 0 := by
        by_contra hn
        apply hray
        refine ⟨a.1, a.2, p.1, Nat.pos_of_ne_zero hn, fun j => ?_⟩
        have hj : j • p ∈ M := nsmul_mem (AddSubmonoid.subset_closure hp) j
        refine ⟨j • p, hj, ?_⟩
        change (a.1 + j • p.1, a.2 + j • p.2) = (a.1 + j * p.1, a.2)
        simp [hpz]
      simp [hx]
    · have hsum : p.1 ≤ ∑ q ∈ S, q.1 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
      exact (hsum.trans (Nat.le_add_left ..)).trans
        (Nat.le_mul_of_pos_right K (Nat.pos_of_ne_zero hpz))
  have hclosure (p : ℕ × ℕ) (hp : p ∈ M) : p.1 ≤ K * p.2 := by
    induction hp using AddSubmonoid.closure_induction with
    | mem p hp => exact hgen p hp
    | zero => simp
    | add p q _ _ hp hq =>
      simpa [mul_add] using Nat.add_le_add hp hq
  refine ⟨K, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have ha : a.1 ≤ K := Nat.le_add_right ..
  have hca : K * p.2 ≤ K * (a.2 + p.2) := Nat.mul_le_mul_left K (Nat.le_add_left ..)
  simpa [vadd_eq_add, mul_add, add_comm] using Nat.add_le_add ha ((hclosure p hp).trans hca)

private theorem semilinear_bound {I : Set (ℕ × ℕ)} (hI : IsSemilinearSet I)
    (hray : ¬ HasHorizontalRay I) : ∃ K : ℕ, ∀ p ∈ I, p.1 ≤ K * (p.2 + 1) := by
  classical
  obtain ⟨S, hS, rfl⟩ := isSemilinearSet_iff.mp hI
  have hbound (s : Set (ℕ × ℕ)) (hs : s ∈ S) :=
    linear_bound (hS s hs) (fun ⟨a, c, d, hd, hr⟩ =>
      hray ⟨a, c, d, hd, fun j => Set.mem_sUnion_of_mem (hr j) hs⟩)
  choose K hK using hbound
  refine ⟨∑ s ∈ S.attach, K s s.property, fun p hp => ?_⟩
  obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
  have hsum : K s hs ≤ ∑ s ∈ S.attach, K s s.property :=
    Finset.single_le_sum (f := fun s : {s // s ∈ S} => K s s.property)
      (fun _ _ => Nat.zero_le _) (Finset.mem_attach S ⟨s, hs⟩)
  exact (hK s hs p hps).trans (Nat.mul_le_mul_right _ hsum)

private theorem step_first {p q : ℕ × ℕ} (h : step p = some q) : q.1 = 3 * p.1 / 2 := by
  unfold step at h
  split at h
  · cases h
    rfl
  · split at h
    · contradiction
    · cases h
      rfl

/-- The orbit's first coordinate outgrows every affine bound in its credit. -/
private theorem invariant_orbit_growth {I : Set (ℕ × ℕ)} (hI : IsSafetyInvariant I) (t : ℕ) :
    ∃ p ∈ I, p.2 ≤ 2 * t ∧ 8 + 4 * t ≤ p.1 ∧ (t + 1)^2 ≤ p.1 := by
  induction t with
  | zero => exact ⟨(8, 0), hI.1, by decide, by decide, by decide⟩
  | succ t ih =>
    obtain ⟨p, hp, hc, hlin, hquad⟩ := ih
    obtain ⟨q, hq, hs⟩ := hI.2 p hp
    have hfirst := step_first hs
    have hcredit := step_credit hs
    have hdiff : p.1 + (4 + 2 * t) ≤ q.1 := by omega
    refine ⟨q, hq, by omega, by omega, ?_⟩
    calc
      (t + 1 + 1)^2 ≤ (t + 1)^2 + (4 + 2 * t) := by nlinarith
      _ ≤ q.1 := (Nat.add_le_add_right hquad _).trans hdiff

/-- No semilinear set of natural-number pairs is an inductive safety invariant
for the shifted Antihydra recurrence from `(8, 0)`. -/
theorem no_semilinear_safety_invariant (I : Set (ℕ × ℕ)) (hI : IsSemilinearSet I) :
    ¬ IsSafetyInvariant I := by
  intro hs
  obtain ⟨K, hK⟩ := semilinear_bound hI (invariant_ray_free hs)
  let t := 3 * K + 1
  obtain ⟨p, hp, hc, _, hquad⟩ := invariant_orbit_growth hs t
  have hupper := (hK p hp).trans (Nat.mul_le_mul_left K (Nat.add_le_add_right hc 1))
  have hcross : K * (2 * t + 1) < (t + 1)^2 := by
    dsimp [t]
    nlinarith
  exact (not_lt_of_ge (hquad.trans hupper)) hcross

/-- Interpret the two variable assignments as the arithmetic pair. -/
def assignmentState (v : Fin 2 → ℕ) : ℕ × ℕ := (v 0, v 1)

private def assignmentEquiv : (Fin 2 → ℕ) ≃+ ℕ × ℕ where
  toFun := assignmentState
  invFun p := ![p.1, p.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl

open FirstOrder.Language in
theorem no_presburger_safety_invariant (A : Set ℕ) (I : Set (Fin 2 → ℕ))
    (hI : A.Definable presburger I) : ¬ IsSafetyInvariant (assignmentState '' I) :=
  no_semilinear_safety_invariant _
    ((presburger.definable_iff_isSemilinearSet.mp hI).image assignmentEquiv)

end AntihydraPalomar
