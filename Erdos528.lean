/-
Copyright 2026 AItoBit.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos528
/-- A signed coordinate direction in $\mathbb Z^k$. -/
abbrev Direction (k : ℕ) := Fin k × Bool

/-- The unit displacement associated with a signed coordinate direction. -/
def displacement {k : ℕ} (d : Direction k) : Fin k → ℤ :=
  fun i => if i = d.1 then if d.2 then 1 else -1 else 0

/-- The $n+1$ visited vertices of a direction word of length $n$, starting at zero. -/
def vertices {k n : ℕ} (w : Fin n → Direction k) (t : Fin (n + 1)) : Fin k → ℤ :=
  ∑ j : Fin n, if j.val < t.val then displacement (w j) else 0

/-- A direction word is self-avoiding when all its visited vertices are distinct. -/
def IsSelfAvoiding {k n : ℕ} (w : Fin n → Direction k) : Prop :=
  Function.Injective (vertices w)

instance {k n : ℕ} (w : Fin n → Direction k) : Decidable (IsSelfAvoiding w) :=
  inferInstanceAs (Decidable (Function.Injective (vertices w)))

/-- The number of self-avoiding walks of $n$ steps from the origin in $\mathbb Z^k$.
Each walk is encoded by its sequence of signed coordinate directions. -/
def walkCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Direction k => IsSelfAvoiding w)).card

def firstPart {k m n : ℕ} (w : Fin (m+n) → Direction k) (i : Fin m) := w (i.castAdd n)
def lastPart {k m n : ℕ} (w : Fin (m+n) → Direction k) (i : Fin n) := w (i.natAdd m)

theorem vertices_firstPart {k m n : ℕ} (w : Fin (m+n) → Direction k)
    (t : Fin (m+1)) :
    vertices (firstPart w) t = vertices w ⟨t.val, by omega⟩ := by
  classical
  unfold vertices
  rw [Fin.sum_univ_add]
  have hz : ∑ j : Fin n,
      (if (j.natAdd m).val < t.val then displacement (w (j.natAdd m)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega)]
  rw [hz, add_zero]
  rfl

theorem vertices_lastPart {k m n : ℕ} (w : Fin (m+n) → Direction k)
    (t : Fin (n+1)) :
    vertices w ⟨m+t.val, by omega⟩ =
      vertices w ⟨m, by omega⟩ + vertices (lastPart w) t := by
  classical
  unfold vertices
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hleft : (∑ j : Fin m,
      if (j.castAdd n).val < m + t.val then displacement (w (j.castAdd n)) else 0) =
      ∑ j : Fin m, if (j.castAdd n).val < m then displacement (w (j.castAdd n)) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_castAdd]
    rw [if_pos (by omega), if_pos j.isLt]
  have hz : (∑ j : Fin n,
      if (j.natAdd m).val < m then displacement (w (j.natAdd m)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega)]
  rw [hleft, hz, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [lastPart]

theorem isSelfAvoiding_firstPart {k m n : ℕ} {w : Fin (m+n) → Direction k}
    (h : IsSelfAvoiding w) : IsSelfAvoiding (firstPart w) := by
  intro x y hxy
  rw [vertices_firstPart, vertices_firstPart] at hxy
  have he := h hxy
  have he' : x.val = y.val := congrArg (fun z : Fin (m+n+1) => z.val) he
  exact Fin.ext he'

theorem isSelfAvoiding_lastPart {k m n : ℕ} {w : Fin (m+n) → Direction k}
    (h : IsSelfAvoiding w) : IsSelfAvoiding (lastPart w) := by
  intro x y hxy
  have he : vertices w ⟨m+x.val, by omega⟩ = vertices w ⟨m+y.val, by omega⟩ := by
    rw [vertices_lastPart, vertices_lastPart, hxy]
  have he' := congrArg Fin.val (h he)
  change m + x.val = m + y.val at he'
  apply Fin.ext
  omega

theorem split_injective {k m n : ℕ} :
    Function.Injective (fun w : Fin (m+n) → Direction k => (firstPart w, lastPart w)) := by
  intro w v h
  have hp := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  funext i
  induction i using Fin.addCases with
  | left i => exact congrFun hp i
  | right i => exact congrFun hs i

theorem walkCount_submultiplicative (m n k : ℕ) :
    walkCount (m+n) k ≤ walkCount m k * walkCount n k := by
  classical
  unfold walkCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun w => (firstPart w, lastPart w))
  · intro w hw
    have hsa : IsSelfAvoiding w := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hw
    simpa only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] using
      And.intro (isSelfAvoiding_firstPart hsa) (isSelfAvoiding_lastPart hsa)
  · exact split_injective.injOn

theorem straight_vertices {k n : ℕ} (i : Fin k) (t : Fin (n+1)) :
    vertices (fun _ : Fin n => (i, true)) t i = (t.val : ℤ) := by
  classical
  have hc : (Finset.univ.filter (fun j : Fin n => j.val < t.val)).card = t.val := by
    conv_rhs => rw [← Fintype.card_fin t.val]
    apply Finset.card_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin t.val))
    · intro j hj
      simp
    · intro a ha b hb hab
      exact Fin.ext (congrArg (fun z : Fin t.val => z.val) hab)
    · intro j _
      refine ⟨⟨j.val, by omega⟩, ?_, rfl⟩
      simp [j.isLt]
  simp [vertices, displacement, Finset.sum_apply, ite_apply, Finset.sum_boole, hc]

theorem walkCount_pos (n k : ℕ) (hk : 0 < k) : 0 < walkCount n k := by
  classical
  let i : Fin k := ⟨0, hk⟩
  have hw : IsSelfAvoiding (fun _ : Fin n => (i,true)) := by
    intro s t hst
    have he := congrFun hst i
    rw [straight_vertices, straight_vertices] at he
    exact Fin.ext (Int.ofNat_inj.mp he)
  unfold walkCount
  apply Finset.card_pos.mpr
  exact ⟨fun _ => (i,true), by simp [hw]⟩

theorem limit_exists (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, Filter.Tendsto (fun n : ℕ => (walkCount n k : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds C) := by
  have hp (n : ℕ) : (0 : ℝ) < walkCount n k := by exact_mod_cast walkCount_pos n k hk
  have hs : Subadditive (fun n => Real.log (walkCount n k)) := by
    intro m n
    calc
      Real.log (walkCount (m+n) k) ≤ Real.log ((walkCount m k : ℝ) * walkCount n k) :=
        Real.log_le_log (hp _) (by exact_mod_cast walkCount_submultiplicative m n k)
      _ = Real.log (walkCount m k) + Real.log (walkCount n k) :=
        Real.log_mul (hp _).ne' (hp _).ne'
  have hb : BddBelow (Set.range (fun n : ℕ => Real.log (walkCount n k) / n)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n,rfl⟩
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (walkCount_pos n k hk)))
      (Nat.cast_nonneg _)
  refine ⟨Real.exp hs.lim, ?_⟩
  convert Real.continuous_exp.continuousAt.tendsto.comp (hs.tendsto_lim hb) using 1
  funext n
  rw [Real.rpow_def_of_pos (hp n)]
  congr 1
  simp only [div_eq_mul_inv, one_mul]

end Erdos528
