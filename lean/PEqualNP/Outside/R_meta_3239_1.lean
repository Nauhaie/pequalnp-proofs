import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Remove the first gate by presenting its value as an extra input to the suffix.
-- Substitute constants and repeated wires into the suffix without spending any gates.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_3239_1
    (binary : ∀ (a b : Fin 10) (rightBit outBit : Bool) (D : BinaryCircuit), a ≠ b →
      [a.val, b.val] ≤ [[1, 0, 5, 8, 6, 2, 4, 7, 3].getD a.val a.val,
        [1, 0, 5, 8, 6, 2, 4, 7, 3].getD b.val b.val] →
      (∀ g ∈ D.gates, ∃ p q : Bool, g.op = fun x y => x == p && y == q) →
      (∀ x : Fin 9 → Bool,
        let u := List.ofFn x ++ [x 0 || x 1, false]
        (D.eval (u ++ [(u.getD a.val false == false) && (u.getD b.val false == rightBit)]) != outBit) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ D.size)
    (noExtra : ∀ (outBit : Bool) (D : BinaryCircuit),
      (∀ g ∈ D.gates, ∃ p q : Bool, g.op = fun x y => x == p && y == q) →
      (∀ x : Fin 9 → Bool,
        let u := List.ofFn x ++ [x 0 || x 1, false]
        (D.eval (u ++ [false]) != outBit) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ D.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C outBit basis firstRule computes
  let edges : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
      (3, 8), (5, 7), (6, 8), (8, 5)]
  let target (x : Fin 9 → Bool) := edges.any (fun e => x e.1 && x e.2)
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1, false]
  have hlength (x : Fin 9 → Bool) : (base x).length = 11 := by simp [base]
  have hcorrect (x : Fin 9 → Bool) : (C.eval (base x) != outBit) = target x := by
    simpa [base, target, edges, Bool.or_assoc] using computes x
  have hfalse (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) : (base x).getD i false = false := by
    by_cases h : i = 10
    · subst i
      simp [base, List.getD_eq_getElem?_getD]
    · exact List.getD_eq_default _ _ (by rw [hlength]; omega)
  cases hg : C.gates with
  | nil =>
    exfalso
    let sample (k : Fin 11) (i : Fin 9) : Bool :=
      if k.val < 9 then decide (i.val = k.val)
      else if k.val = 9 then false else decide (i = 0 ∨ i = 1)
    have noProjection : ∀ (j : Fin 12) (b : Bool), ∃ k : Fin 11,
        ((base (sample k)).getD j.val false != b) ≠ target (sample k) := by
      dsimp only [base, sample, target, edges]
      decide +kernel
    let j : Fin 12 := ⟨min C.output 11, by omega⟩
    obtain ⟨k, hk⟩ := noProjection j outBit
    have hread : (base (sample k)).getD C.output false = (base (sample k)).getD j.val false := by
      by_cases h : C.output < 11
      · simp [j, Nat.min_eq_left (Nat.le_of_lt h)]
      · have hout : 11 ≤ C.output := by omega
        simp only [j, Nat.min_eq_right hout]
        rw [hfalse _ C.output (by omega), hfalse _ 11 (by decide)]
    have h := hcorrect (sample k)
    change (((C.gates.foldl _ (base (sample k))).getD C.output false) != outBit) = _ at h
    rw [hg, List.foldl_nil, hread] at h
    exact hk h
  | cons first rest =>
    have hfirst := firstRule first (by simp [hg])
    obtain ⟨rightBit, hop⟩ := hfirst.1
    let suffix : BinaryCircuit := ⟨rest, C.output⟩
    have hbasis : ∀ g ∈ suffix.gates, ∃ p q : Bool, g.op = fun x y => x == p && y == q := by
      intro g hg'
      exact basis g (by rw [hg]; exact List.mem_cons_of_mem first hg')
    let firstValue (x : Fin 9 → Bool) :=
      ((base x).getD first.left false == false) && ((base x).getD first.right false == rightBit)
    have hsuffix (x : Fin 9 → Bool) :
        (suffix.eval (base x ++ [firstValue x]) != outBit) = target x := by
      have hstep : C.eval (base x) = suffix.eval (base x ++ [firstValue x]) := by
        change (C.gates.foldl _ (base x)).getD C.output false =
          (rest.foldl _ (base x ++ [firstValue x])).getD C.output false
        rw [hg, List.foldl_cons, hop]
      rw [← hstep]
      exact hcorrect x
    have sizeFromUnary (k : Fin 11) (bit : Bool)
        (h : ∀ x : Fin 9 → Bool, firstValue x = ((base x).getD k.val false == bit)) :
        13 ≤ suffix.size := by
      let source (i : ℕ) := if i = 11 then k.val else i
      let adjust (i : ℕ) (v : Bool) := if i = 11 then v == bit else v
      let read (w : List Bool) (i : ℕ) := adjust i (w.getD (source i) false)
      let substitute (g : BinaryGate) : BinaryGate :=
        ⟨fun a b => g.op (adjust g.left a) (adjust g.right b), source g.left, source g.right⟩
      let step (w : List Bool) (g : BinaryGate) :=
        w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
      have sourceBound (i n : ℕ) (hi : i < n) (hn : 12 ≤ n) : source i < n := by
        have hk := k.isLt
        by_cases h11 : i = 11
        · simp only [source, ite_eq_left h11]
          omega
        · simpa only [source, ite_eq_right h11] using hi
      have foldRead (gs : List BinaryGate) (v w : List Bool) (hlen : v.length = w.length)
          (hmin : 12 ≤ w.length) (he : ∀ i : ℕ, v.getD i false = read w i) (i : ℕ) :
          (gs.foldl step v).getD i false = read ((gs.map substitute).foldl step w) i := by
        induction gs generalizing v w with
        | nil => exact he i
        | cons g gs ih =>
          simp only [List.map_cons, List.foldl_cons]
          apply ih (step v g) (step w (substitute g))
          · simp [step, hlen]
          · simpa [step] using (show 12 ≤ w.length + 1 by omega)
          · intro j
            let value := g.op (read w g.left) (read w g.right)
            change (v ++ [g.op (v.getD g.left false) (v.getD g.right false)]).getD j false =
              read (w ++ [value]) j
            rw [he g.left, he g.right]
            change (v ++ [value]).getD j false = read (w ++ [value]) j
            by_cases hj : j < v.length
            · rw [List.getD_append _ _ _ _ hj, he j]
              have hs : source j < w.length := sourceBound j w.length (by omega) hmin
              change _ = adjust j ((w ++ [value]).getD (source j) false)
              rw [List.getD_append _ _ _ _ hs]
            · have h11 : j ≠ 11 := by omega
              simp only [read, source, adjust, ite_eq_right h11]
              rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), hlen]
      have initial (x : Fin 9 → Bool) (i : ℕ) :
          (base x ++ [((base x).getD k.val false == bit)]).getD i false =
            read (base x ++ [false]) i := by
        have hlen := hlength x
        by_cases h11 : i = 11
        · subst i
          have hk : k.val < (base x).length := by rw [hlen]; exact k.isLt
          simp only [read, source, adjust, ite_true]
          rw [List.getD_append _ _ _ _ hk, List.getD_append_right _ _ _ _ (by omega), hlen]
          rfl
        · simp only [read, source, adjust, ite_eq_right h11]
          by_cases hi : i < 11
          · have hi' : i < (base x).length := by omega
            rw [List.getD_append _ _ _ _ hi', List.getD_append _ _ _ _ hi']
          · have hi' : (base x).length + 1 ≤ i := by omega
            rw [List.getD_eq_default _ _ (by simpa using hi'),
              List.getD_eq_default _ _ (by simpa using hi')]
      have adjustTest (i : ℕ) (v p : Bool) :
          (adjust i v == p) = (v == (if i = 11 then p == bit else p)) := by
        by_cases hi : i = 11
        · simp only [adjust, hi, ite_true]
          cases v <;> cases p <;> cases bit <;> rfl
        · simp only [adjust, ite_eq_right hi]
      let D : BinaryCircuit := ⟨rest.map substitute, source C.output⟩
      have dBasis : ∀ g ∈ D.gates, ∃ p q : Bool, g.op = fun a b => a == p && b == q := by
        intro g hg'
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg'
        obtain ⟨p, q, hpq⟩ := hbasis old hold
        refine ⟨if old.left = 11 then p == bit else p,
          if old.right = 11 then q == bit else q, ?_⟩
        funext a b
        change old.op (adjust old.left a) (adjust old.right b) = _
        rw [hpq]
        simp only [adjustTest]
      let corrected := if C.output = 11 then bit == outBit else outBit
      have dCorrect (x : Fin 9 → Bool) :
          (D.eval (base x ++ [false]) != corrected) = target x := by
        have relate : suffix.eval (base x ++ [firstValue x]) =
            adjust C.output (D.eval (base x ++ [false])) := by
          rw [h x]
          exact foldRead rest _ _ (by simp) (by simp [hlength]) (initial x) C.output
        have value := hsuffix x
        rw [relate] at value
        have flip (v : Bool) : (adjust C.output v != outBit) = (v != corrected) := by
          by_cases h11 : C.output = 11
          · simp only [adjust, corrected, h11, ite_true]
            cases v <;> cases bit <;> cases outBit <;> rfl
          · simp only [adjust, corrected, ite_eq_right h11]
        simpa only [flip] using value
      have small := noExtra corrected D dBasis dCorrect
      change 13 ≤ (rest.map substitute).length at small
      change 13 ≤ rest.length
      simpa only [List.length_map] using small
    have hsize : 13 ≤ suffix.size := by
      by_cases hl : first.left < 10
      · by_cases hr : first.right < 10
        · by_cases hsame : first.left = first.right
          · cases rightBit
            · apply sizeFromUnary ⟨first.left, by omega⟩ false
              intro x
              simp [firstValue, hsame]
            · apply sizeFromUnary 10 true
              intro x
              change firstValue x = ((base x).getD 10 false == true)
              rw [hfalse x 10 (by decide)]
              simp only [firstValue, hsame]
              cases (base x).getD first.right false <;> rfl
          · apply binary ⟨first.left, hl⟩ ⟨first.right, hr⟩ rightBit outBit suffix
            · exact fun e => hsame (congrArg Fin.val e)
            · exact hfirst.2
            · exact hbasis
            · exact hsuffix
        · cases rightBit
          · apply sizeFromUnary ⟨first.left, by omega⟩ false
            intro x
            simp only [firstValue]
            rw [hfalse x first.right (by omega)]
            simp
          · apply sizeFromUnary 10 true
            intro x
            change firstValue x = ((base x).getD 10 false == true)
            unfold firstValue
            rw [hfalse x first.right (by omega), hfalse x 10 (by decide)]
            simp
      · by_cases hr : first.right < 10
        · apply sizeFromUnary ⟨first.right, by omega⟩ rightBit
          intro x
          simp only [firstValue]
          rw [hfalse x first.left (by omega)]
          rfl
        · apply sizeFromUnary 10 rightBit
          intro x
          change firstValue x = ((base x).getD 10 false == rightBit)
          unfold firstValue
          rw [hfalse x first.left (by omega), hfalse x first.right (by omega), hfalse x 10 (by decide)]
          rfl
    change 13 ≤ rest.length at hsize
    change 14 ≤ C.gates.length
    rw [hg, List.length_cons]
    omega
