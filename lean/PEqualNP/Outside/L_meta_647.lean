import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_647

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Classical

-- The evaluation lemmas from stp to val_and follow the outside proof of row L-meta-613
-- in this repository (Apache-2.0), with names changed.

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl stp w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl stp w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [stp]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl stp w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl stp w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [stp, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [stp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl stp w).length) :
    (G.foldl stp w).getD i false = ((G.take t).foldl stp w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl stp w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl stp w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl stp w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

def Le {n : ℕ} (x x' : Fin n → Bool) : Prop := ∀ v, x v = true → x' v = true

theorem gate_ok (C : Circuit) (hM : Monotone2 C) (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) :
    (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
  have hm := hM h (List.mem_of_getElem? hg)
  refine ⟨?_, hm.2⟩
  have h1 := hm.1
  simpa [Set.mem_insert_iff] using h1

theorem gate_lt (C : Circuit) (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) : j < C.size :=
  (List.getElem?_eq_some_iff.mp hg).1

theorem val_mono (C : Circuit) (n : ℕ) (hM : Monotone2 C) (x x' : Fin n → Bool) (hle : Le x x') :
    ∀ w, val C n x w = true → val C n x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · rw [val_input C n x w hw] at hv
      rw [val_input C n x' w hw]
      exact hle _ hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases hg : C.gates[j]? with
      | none => rw [val_none C n x j hg] at hv; exact absurd hv (by simp)
      | some h =>
        rcases (gate_ok C hM j h hg).1 with hop | hop
        · rw [val_and C n x j h hg hop] at hv
          rw [val_and C n x' j h hg hop]
          intro c hc
          exact ⟨(hv c hc).1, ih c (hv c hc).1 (hv c hc).2⟩
        · rw [val_or C n x j h hg hop] at hv
          rw [val_or C n x' j h hg hop]
          obtain ⟨c, hc, hlt, hcv⟩ := hv
          exact ⟨c, hc, hlt, ih c hlt hcv⟩

def Free (C : Circuit) (n : ℕ) (X : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x x' : Fin n → Bool, (∀ v, v ∉ X → x v = x' v) → val C n x w = val C n x' w

theorem free_of_not_mem (C : Circuit) (n : ℕ) (hM : Monotone2 C) (X : Finset (Fin n)) (S : Set ℕ)
    (hX : ∀ l ∈ X, l.val ∈ S)
    (hcl : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j → i ∈ S →
      n + j ∈ S) :
    ∀ w, w ∉ S → Free C n X w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x x' hxx
    by_cases hwn : w < n
    · rw [val_input C n x w hwn, val_input C n x' w hwn]
      apply hxx
      intro hmem
      exact hw (hX _ hmem)
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases hg : C.gates[j]? with
      | none => rw [val_none C n x j hg, val_none C n x' j hg]
      | some h =>
        have hin : ∀ c ∈ h.inputs, c < n + j → val C n x c = val C n x' c := by
          intro c hc hlt
          exact ih c hlt (fun hcS => hw (hcl j h hg c hc hlt hcS)) x x' hxx
        rw [Bool.eq_iff_iff]
        rcases (gate_ok C hM j h hg).1 with hop | hop
        · rw [val_and C n x j h hg hop, val_and C n x' j h hg hop]
          constructor
          · intro hv c hc
            exact ⟨(hv c hc).1, by rw [← hin c hc (hv c hc).1]; exact (hv c hc).2⟩
          · intro hv c hc
            exact ⟨(hv c hc).1, by rw [hin c hc (hv c hc).1]; exact (hv c hc).2⟩
        · rw [val_or C n x j h hg hop, val_or C n x' j h hg hop]
          constructor
          · rintro ⟨c, hc, hlt, hcv⟩
            exact ⟨c, hc, hlt, by rw [← hin c hc hlt]; exact hcv⟩
          · rintro ⟨c, hc, hlt, hcv⟩
            exact ⟨c, hc, hlt, by rw [hin c hc hlt]; exact hcv⟩

def Setup (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : Prop :=
  Monotone2 C ∧
  (∀ u v : Fin n, G.Adj u v → (u ∈ X ↔ v ∉ X)) ∧
  (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) ∧
  (∀ (j : ℕ) (h : Gate) (a b : ℕ), C.gates[j]? = some h → h.op = GateOp.and →
      h.inputs = [a, b] → a < n + j → b < n + j → Free C n X a ∨ Free C n X b) ∧
  (∀ x : Fin n → Bool, val C n x C.output = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)

def zr {n : ℕ} : Fin n → Bool := fun _ => false

theorem e2_agree {n : ℕ} (X : Finset (Fin n)) (i j : Fin n) (hi : i ∈ X) :
    ∀ v, v ∉ X → e2 i j v = e1 j v := by
  intro v hv
  have hne : v ≠ i := fun h => hv (h ▸ hi)
  simp [e2, e1, hne]

theorem e1_agree {n : ℕ} (X : Finset (Fin n)) (i : Fin n) (hi : i ∈ X) :
    ∀ v, v ∉ X → e1 i v = zr v := by
  intro v hv
  have hne : v ≠ i := fun h => hv (h ▸ hi)
  simp [e1, zr, hne]

theorem le_e1_e2 {n : ℕ} (i j : Fin n) : Le (e1 j) (e2 i j) := by
  intro v hv
  simp only [e1, decide_eq_true_eq] at hv
  simp [e2, hv]

theorem le_e1_e2' {n : ℕ} (i j : Fin n) : Le (e1 i) (e2 i j) := by
  intro v hv
  simp only [e1, decide_eq_true_eq] at hv
  simp [e2, hv]

theorem le_zr {n : ℕ} (x : Fin n → Bool) : Le zr x := by
  intro v hv
  simp [zr] at hv

theorem not_edge_e1 {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) :
    ¬ ∃ u v : Fin n, G.Adj u v ∧ e1 c u = true ∧ e1 c v = true := by
  rintro ⟨u, v, hadj, hu, hv⟩
  simp only [e1, decide_eq_true_eq] at hu hv
  exact hadj.ne (hu.trans hv.symm)

theorem edge_e2 {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n)
    (h : ∃ u v : Fin n, G.Adj u v ∧ e2 a b u = true ∧ e2 a b v = true) : G.Adj a b := by
  obtain ⟨u, v, hadj, hu, hv⟩ := h
  simp only [e2, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl hadj.ne
  · exact hadj
  · exact hadj.symm
  · exact absurd rfl hadj.ne

def Step (C : Circuit) (n : ℕ) (u : Fin n → Bool) (a b : ℕ) : Prop :=
  ∃ (t : ℕ) (h : Gate), b = n + t ∧ C.gates[t]? = some h ∧ a ∈ h.inputs ∧ a < n + t ∧
    (h.op = GateOp.or ∨ ∀ c ∈ h.inputs, c ≠ a → (c < n + t ∧ val C n u c = true))

theorem step_sound (C : Circuit) (n : ℕ) (hM : Monotone2 C) (u z : Fin n → Bool) (hle : Le u z)
    (a b : ℕ) (hs : Step C n u a b) (hv : val C n z a = true) : val C n z b = true := by
  obtain ⟨t, h, rfl, hg, ha, hlt, hside⟩ := hs
  rcases (gate_ok C hM t h hg).1 with hop | hop
  · rw [val_and C n z t h hg hop]
    intro c hc
    by_cases hca : c = a
    · subst hca; exact ⟨hlt, hv⟩
    · rcases hside with hor | hside
      · rw [hop] at hor; cases hor
      · exact ⟨(hside c hc hca).1, val_mono C n hM u z hle c (hside c hc hca).2⟩
  · rw [val_or C n z t h hg hop]
    exact ⟨a, ha, hlt, hv⟩

theorem chain_sound (C : Circuit) (n : ℕ) (hM : Monotone2 C) (u z : Fin n → Bool) (hle : Le u z)
    (a b : ℕ) (hc : Relation.ReflTransGen (Step C n u) a b) (hv : val C n z a = true) :
    val C n z b = true := by
  induction hc with
  | refl => exact hv
  | tail _ hs ih => exact step_sound C n hM u z hle _ _ hs ih

theorem step_mono (C : Circuit) (n : ℕ) (hM : Monotone2 C) (u u' : Fin n → Bool) (hle : Le u u')
    (a b : ℕ) (hs : Step C n u a b) : Step C n u' a b := by
  obtain ⟨t, h, rfl, hg, ha, hlt, hside⟩ := hs
  refine ⟨t, h, rfl, hg, ha, hlt, ?_⟩
  rcases hside with hor | hside
  · exact Or.inl hor
  · exact Or.inr (fun c hc hca =>
      ⟨(hside c hc hca).1, val_mono C n hM u u' hle c (hside c hc hca).2⟩)

theorem chain_mono (C : Circuit) (n : ℕ) (hM : Monotone2 C) (u u' : Fin n → Bool) (hle : Le u u')
    (a b : ℕ) (hc : Relation.ReflTransGen (Step C n u) a b) :
    Relation.ReflTransGen (Step C n u') a b := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (step_mono C n hM u u' hle _ _ hs)

theorem step_lt (C : Circuit) (n : ℕ) (u : Fin n → Bool) (a b : ℕ) (hs : Step C n u a b) :
    a < b ∧ n ≤ b ∧ b < n + C.size := by
  obtain ⟨t, h, rfl, hg, ha, hlt, hside⟩ := hs
  have := gate_lt C t h hg
  omega

theorem pair_of_mem (l : List ℕ) (hl : l.length ≤ 2) (a c : ℕ) (ha : a ∈ l) (hc : c ∈ l)
    (hne : c ≠ a) : l = [a, c] ∨ l = [c, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [x], _ =>
    simp only [List.mem_singleton] at ha hc
    exact absurd (hc.trans ha.symm) hne
  | [x, y], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hne
  | _ :: _ :: _ :: _, h => simp at h

theorem witness_aux (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i j : Fin n) (hi : i ∈ X) :
    ∀ w, val C n (e2 i j) w = true →
      val C n (e1 j) w = true ∨ Relation.ReflTransGen (Step C n (e1 j)) i.val w := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · rw [val_input C n _ w hw] at hv
      simp only [e2, decide_eq_true_eq] at hv
      rcases hv with h | h
      · right
        have hwi : w = i.val := by rw [← h]
        rw [hwi]
      · left
        rw [val_input C n _ w hw]
        simp [e1, h]
    · obtain ⟨t, rfl⟩ : ∃ t, w = n + t := ⟨w - n, by omega⟩
      cases hg : C.gates[t]? with
      | none => rw [val_none C n _ t hg] at hv; exact absurd hv (by simp)
      | some h =>
        rcases (gate_ok C hM t h hg).1 with hop | hop
        · rw [val_and C n _ t h hg hop] at hv
          by_cases hall : ∀ c ∈ h.inputs, val C n (e1 j) c = true
          · left
            rw [val_and C n _ t h hg hop]
            exact fun c hc => ⟨(hv c hc).1, hall c hc⟩
          · simp only [not_forall] at hall
            obtain ⟨a, ha, hav⟩ := hall
            rcases ih a (hv a ha).1 (hv a ha).2 with h1 | h1
            · exact absurd h1 hav
            · right
              refine Relation.ReflTransGen.tail h1 ⟨t, h, rfl, hg, ha, (hv a ha).1, Or.inr ?_⟩
              intro c hc hca
              refine ⟨(hv c hc).1, ?_⟩
              have hfree : Free C n X a ∨ Free C n X c := by
                rcases pair_of_mem h.inputs (gate_ok C hM t h hg).2 a c ha hc hca with hl | hl
                · exact hK t h a c hg hop hl (hv a ha).1 (hv c hc).1
                · exact (hK t h c a hg hop hl (hv c hc).1 (hv a ha).1).symm
              rcases hfree with hfa | hfc
              · have := hfa (e2 i j) (e1 j) (e2_agree X i j hi)
                rw [(hv a ha).2] at this
                exact absurd this.symm hav
              · rw [← hfc (e2 i j) (e1 j) (e2_agree X i j hi)]
                exact (hv c hc).2
        · rw [val_or C n _ t h hg hop] at hv
          obtain ⟨a, ha, hlt, hav⟩ := hv
          rcases ih a hlt hav with h1 | h1
          · left
            rw [val_or C n _ t h hg hop]
            exact ⟨a, ha, hlt, h1⟩
          · right
            exact Relation.ReflTransGen.tail h1 ⟨t, h, rfl, hg, ha, hlt, Or.inl hop⟩

theorem witness (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i j : Fin n) (hi : i ∈ X) (hadj : G.Adj i j) :
    Relation.ReflTransGen (Step C n (e1 j)) i.val C.output := by
  have hf := hS.2.2.2.2
  have hout : val C n (e2 i j) C.output = true :=
    (hf _).mpr ⟨i, j, hadj, by simp [e2], by simp [e2]⟩
  rcases witness_aux C n G X hS i j hi C.output hout with h | h
  · exact absurd ((hf _).mp h) (not_edge_e1 G j)
  · exact h

theorem chain_split {α : Type} (R : α → α → Prop) (P : α → Prop) (a b : α)
    (h : Relation.ReflTransGen R a b) (ha : P a) (hb : ¬ P b) :
    ∃ c d, Relation.ReflTransGen R a c ∧ P c ∧ R c d ∧ ¬ P d ∧ Relation.ReflTransGen R d b := by
  revert ha
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro ha; exact absurd ha hb
  | head hac hcb ih =>
    rename_i a' c'
    intro ha
    by_cases hc : P c'
    · obtain ⟨c, d, h1, h2, h3, h4, h5⟩ := ih hc
      exact ⟨c, d, Relation.ReflTransGen.head hac h1, h2, h3, h4, h5⟩
    · exact ⟨a', c', Relation.ReflTransGen.refl, ha, hac, hc, hcb⟩

noncomputable def USet (C : Circuit) (n : ℕ) (X : Finset (Fin n)) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∈ X ∧ ∃ h : Gate, C.gates[t]? = some h ∧
    ∃ c ∈ h.inputs, c < n + t ∧ val C n (e1 v) c = true ∧ val C n zr c = false)

noncomputable def cenSet (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (t : ℕ) : Finset (Fin n) :=
  if (USet C n X t).card = 1 then USet C n X t
  else if 2 ≤ (USet C n X t).card then
    Finset.univ.filter (fun c => ∀ v ∈ USet C n X t, G.Adj v c)
  else ∅

theorem cenSet_card (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hC4 : ∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e)
    (t : ℕ) : (cenSet C n G X t).card ≤ 1 := by
  unfold cenSet
  split_ifs with h1 h2
  · omega
  · obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (USet C n X t).card)
    rw [Finset.card_le_one]
    intro c hc c' hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    rcases hC4 v c v' c' (hc v hv) (hc v' hv').symm (hc' v' hv') (hc' v hv).symm with h | h
    · exact absurd h hne
    · exact h
  · simp

theorem and_centre (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i j : Fin n) (hi : i ∈ X) (hadj : G.Adj i j) :
    ∃ (t : ℕ) (h : Gate), C.gates[t]? = some h ∧ h.op = GateOp.and ∧
      (i ∈ cenSet C n G X t ∨ j ∈ cenSet C n G X t) := by
  have hw := witness C n G X hS i j hi hadj
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  have hPi : val C n (e1 i) i.val = true := by
    rw [val_input C n _ _ i.isLt]; simp [e1]
  have hPo : ¬ val C n (e1 i) C.output = true := fun h => not_edge_e1 G i ((hf _).mp h)
  obtain ⟨a, d, hia, hPa, had, hPd, hdo⟩ :=
    chain_split (Step C n (e1 j)) (fun w => val C n (e1 i) w = true) _ _ hw hPi hPo
  obtain ⟨t, h, rfl, hg, ha, hlt, hside⟩ := had
  have hlen := (gate_ok C hM t h hg).2
  have hop : h.op = GateOp.and := by
    rcases (gate_ok C hM t h hg).1 with hop | hop
    · exact hop
    · exact absurd ((val_or C n _ t h hg hop).mpr ⟨a, ha, hlt, hPa⟩) hPd
  have hside' : ∀ c ∈ h.inputs, c ≠ a → c < n + t ∧ val C n (e1 j) c = true := by
    rcases hside with hor | hs
    · rw [hop] at hor; cases hor
    · exact hs
  have hstepad : Step C n (e1 j) a (n + t) := ⟨t, h, rfl, hg, ha, hlt, Or.inr hside'⟩
  have hreach_a : Relation.ReflTransGen (Step C n (e1 j)) a C.output :=
    Relation.ReflTransGen.head hstepad hdo
  have ha0 : val C n zr a = false := by
    by_contra h0
    have h0' : val C n zr a = true := by simpa using h0
    have h1 := val_mono C n hM zr (e1 j) (le_zr _) a h0'
    exact not_edge_e1 G j ((hf _).mp
      (chain_sound C n hM (e1 j) (e1 j) (fun _ hv => hv) a _ hreach_a h1))
  have hiU : i ∈ USet C n X t := by
    simp only [USet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, h, hg, a, ha, hlt, hPa, ha0⟩
  have hUadj : ∀ v ∈ USet C n X t, G.Adj v j := by
    intro v hv
    simp only [USet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨hvX, h', hg', c, hc, hclt, hcv, hc0⟩ := hv
    have hh : h' = h := by
      rw [hg] at hg'; exact (Option.some.inj hg').symm
    subst hh
    by_cases hca : c = a
    · subst hca
      apply edge_e2 G v j
      apply (hf _).mp
      apply chain_sound C n hM (e1 j) (e2 v j) (le_e1_e2 v j) (n + t) _ hdo
      rw [val_and C n _ t h' hg hop]
      intro c' hc'
      by_cases hc'a : c' = c
      · subst hc'a
        exact ⟨hlt, val_mono C n hM (e1 v) (e2 v j) (le_e1_e2' v j) _ hcv⟩
      · exact ⟨(hside' c' hc' hc'a).1,
          val_mono C n hM (e1 j) (e2 v j) (le_e1_e2 v j) _ (hside' c' hc' hc'a).2⟩
    · exfalso
      have hfree : Free C n X a ∨ Free C n X c := by
        rcases pair_of_mem h'.inputs hlen a c ha hc hca with hl | hl
        · exact hK t h' a c hg hop hl hlt hclt
        · exact (hK t h' c a hg hop hl hclt hlt).symm
      rcases hfree with hfa | hfc
      · have h3 := hfa (e1 i) zr (e1_agree X i hi)
        rw [hPa, ha0] at h3
        cases h3
      · have h3 := hfc (e1 v) zr (e1_agree X v hvX)
        rw [hcv, hc0] at h3
        cases h3
  refine ⟨t, h, hg, hop, ?_⟩
  unfold cenSet
  by_cases h1 : (USet C n X t).card = 1
  · left
    rw [if_pos h1]
    exact hiU
  · right
    have h2 : 2 ≤ (USet C n X t).card := by
      have := Finset.card_pos.mpr ⟨i, hiU⟩
      omega
    rw [if_neg h1, if_pos h2]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hUadj

noncomputable def andSet (C : Circuit) : Finset ℕ :=
  (Finset.range C.size).filter (fun t => ∃ h : Gate, C.gates[t]? = some h ∧ h.op = GateOp.and)

theorem and_count (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (k : ℕ)
    (hk : ∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) :
    k ≤ (andSet C).card := by
  have hC4 := hS.2.2.1
  have hbip := hS.2.1
  have key : ∀ i j : Fin n, i ∈ X → G.Adj i j →
      i ∈ (andSet C).biUnion (cenSet C n G X) ∨ j ∈ (andSet C).biUnion (cenSet C n G X) := by
    intro i j hi hij
    obtain ⟨t, h, hg, hop, hcen⟩ := and_centre C n G X hS i j hi hij
    have ht : t ∈ andSet C := by
      simp only [andSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨gate_lt C t h hg, h, hg, hop⟩
    rcases hcen with hc | hc
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨t, ht, hc⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨t, ht, hc⟩)
  have hT : ∀ u v : Fin n, G.Adj u v →
      u ∈ (andSet C).biUnion (cenSet C n G X) ∨ v ∈ (andSet C).biUnion (cenSet C n G X) := by
    intro u v huv
    by_cases hu : u ∈ X
    · exact key u v hu huv
    · have hv : v ∈ X := by
        by_contra hv
        exact hu ((hbip u v huv).mpr hv)
      exact (key v u hv huv.symm).symm
  calc k ≤ ((andSet C).biUnion (cenSet C n G X)).card := hk _ hT
    _ ≤ ∑ t ∈ andSet C, (cenSet C n G X t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ andSet C, 1 := Finset.sum_le_sum (fun t _ => cenSet_card C n G X hC4 t)
    _ = (andSet C).card := by simp

theorem shrink {α : Type} [DecidableEq α] (T A : Finset α) (parts : Finset (Finset α)) (c : ℕ)
    (hc : parts.card ≤ c + 1) (hA : A ⊆ parts.biUnion id)
    (hp : ∀ B ∈ parts, (B ∩ T).card ≤ 1) :
    ∃ T' : Finset α, T' ⊆ T ∧ T.card ≤ T'.card + c ∧ (A ∩ T').card ≤ 1 := by
  have hcard : (A ∩ T).card ≤ c + 1 := by
    have hsub : A ∩ T ⊆ parts.biUnion (fun B => B ∩ T) := by
      intro q hq
      obtain ⟨hqA, hqT⟩ := Finset.mem_inter.mp hq
      obtain ⟨B, hB, hqB⟩ := Finset.mem_biUnion.mp (hA hqA)
      exact Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_inter.mpr ⟨hqB, hqT⟩⟩
    calc (A ∩ T).card ≤ (parts.biUnion (fun B => B ∩ T)).card := Finset.card_le_card hsub
      _ ≤ ∑ B ∈ parts, (B ∩ T).card := Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ parts, 1 := Finset.sum_le_sum hp
      _ = parts.card := by simp
      _ ≤ c + 1 := hc
  by_cases hne : (A ∩ T).Nonempty
  · obtain ⟨q, hq⟩ := hne
    refine ⟨T \ ((A ∩ T).erase q), Finset.sdiff_subset, ?_, ?_⟩
    · have h1 : ((A ∩ T).erase q).card = (A ∩ T).card - 1 := Finset.card_erase_of_mem hq
      have h2 : (A ∩ T).erase q ⊆ T :=
        fun x hx => (Finset.mem_inter.mp (Finset.mem_of_mem_erase hx)).2
      have h3 := Finset.card_sdiff_add_card_eq_card h2
      omega
    · have hsub : A ∩ (T \ ((A ∩ T).erase q)) ⊆ {q} := by
        intro x hx
        obtain ⟨hxA, hxT⟩ := Finset.mem_inter.mp hx
        obtain ⟨hxT1, hxn⟩ := Finset.mem_sdiff.mp hxT
        by_contra hxq
        apply hxn
        exact Finset.mem_erase.mpr ⟨fun h => hxq (by simp [h]), Finset.mem_inter.mpr ⟨hxA, hxT1⟩⟩
      exact (Finset.card_le_card hsub).trans (by simp)
  · refine ⟨T, Finset.Subset.refl _, by omega, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

noncomputable def mI {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i : Fin n) :
    Fin n → Bool := fun v => decide (v ∉ X ∧ ¬ G.Adj i v)

noncomputable def Nb {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.Adj i j)

theorem mem_Nb {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) : j ∈ Nb G i ↔ G.Adj i j := by
  simp [Nb]

theorem le_e1_mI {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n)
    (hj : j ∉ X) (hna : ¬ G.Adj i j) : Le (e1 j) (mI G X i) := by
  intro v hv
  simp only [e1, decide_eq_true_eq] at hv
  subst hv
  simp [mI, hj, hna]

abbrev Chain (C : Circuit) (n : ℕ) (u : Fin n → Bool) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (Step C n u) a b

noncomputable def TV (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (i : Fin n) (w : ℕ) :
    Finset (Fin n) := (Nb G i).filter (fun j => val C n (e1 j) w = true)

def Vclean (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i : Fin n)
    (w : ℕ) : Prop := val C n (mI G X i) w = false

def IsOr (C : Circuit) (n : ℕ) (w : ℕ) : Prop :=
  ∃ (t : ℕ) (h : Gate), w = n + t ∧ C.gates[t]? = some h ∧ h.op = GateOp.or

noncomputable def cV (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) : ℕ :=
  if IsOr C n w ∧ Vclean C n G X i w ∧ 2 ≤ (TV C n G i w).card then 1 else 0

theorem phase1_step (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hM : Monotone2 C) (i : Fin n) (m : ℕ) (T : Finset (Fin n))
    (hT : ∀ w < m, Vclean C n G X i w → (TV C n G i w ∩ T).card ≤ 1) :
    ∃ T' : Finset (Fin n), T' ⊆ T ∧ T.card ≤ T'.card + cV C n G X i m ∧
      (Vclean C n G X i m → (TV C n G i m ∩ T').card ≤ 1) := by
  by_cases hcl : Vclean C n G X i m
  swap
  · exact ⟨T, Finset.Subset.refl _, by omega, fun h => absurd h hcl⟩
  by_cases hcard : (TV C n G i m).card ≤ 1
  · exact ⟨T, Finset.Subset.refl _, by omega,
      fun _ => (Finset.card_le_card Finset.inter_subset_left).trans hcard⟩
  have hkeep : ∀ c < m, Vclean C n G X i c → TV C n G i m ⊆ TV C n G i c →
      ∃ T' : Finset (Fin n), T' ⊆ T ∧ T.card ≤ T'.card + cV C n G X i m ∧
        (Vclean C n G X i m → (TV C n G i m ∩ T').card ≤ 1) := by
    intro c hcm hcc hsub
    exact ⟨T, Finset.Subset.refl _, by omega, fun _ =>
      (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans (hT c hcm hcc)⟩
  have hcl' : val C n (mI G X i) m = false := hcl
  by_cases hm : m < n
  · exfalso
    apply hcard
    have hsub : TV C n G i m ⊆ {⟨m, hm⟩} := by
      intro j hj
      simp only [TV, Finset.mem_filter] at hj
      have h2 := hj.2
      rw [val_input C n _ m hm] at h2
      simp only [e1, decide_eq_true_eq] at h2
      simp [h2]
    exact (Finset.card_le_card hsub).trans (by simp)
  · obtain ⟨t, rfl⟩ : ∃ t, m = n + t := ⟨m - n, by omega⟩
    cases hg : C.gates[t]? with
    | none =>
      exfalso
      apply hcard
      have hemp : TV C n G i (n + t) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        simp only [TV, Finset.mem_filter] at hj
        rw [val_none C n _ t hg] at hj
        exact absurd hj.2 (by simp)
      rw [hemp]
      simp
    | some h =>
      rcases (gate_ok C hM t h hg).1 with hop | hop
      · have hnot : ¬ ∀ c ∈ h.inputs, c < n + t ∧ val C n (mI G X i) c = true := by
          intro hall
          have h5 := (val_and C n _ t h hg hop).mpr hall
          rw [hcl'] at h5
          cases h5
        simp only [not_forall] at hnot
        obtain ⟨c, hc, hcn⟩ := hnot
        by_cases hlt : c < n + t
        · have hcc : Vclean C n G X i c := by
            unfold Vclean
            by_contra hx
            exact hcn ⟨hlt, by simpa using hx⟩
          refine hkeep c hlt hcc ?_
          intro j hj
          simp only [TV, Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, ((val_and C n _ t h hg hop).mp hj.2 c hc).2⟩
        · exfalso
          apply hcard
          have hemp : TV C n G i (n + t) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro j hj
            simp only [TV, Finset.mem_filter] at hj
            exact hlt ((val_and C n _ t h hg hop).mp hj.2 c hc).1
          rw [hemp]
          simp
      · have hcv : cV C n G X i (n + t) = 1 := by
          unfold cV
          rw [if_pos ⟨⟨t, h, rfl, hg, hop⟩, hcl, by omega⟩]
        have hclean : ∀ c ∈ h.inputs, c < n + t → Vclean C n G X i c := by
          intro c hc hlt
          unfold Vclean
          by_contra hx
          have hx' : val C n (mI G X i) c = true := by simpa using hx
          have h5 := (val_or C n _ t h hg hop).mpr ⟨c, hc, hlt, hx'⟩
          rw [hcl'] at h5
          cases h5
        have hp1 : ((h.inputs.toFinset.filter (fun c => c < n + t)).image (TV C n G i)).card
            ≤ 1 + 1 :=
          calc ((h.inputs.toFinset.filter (fun c => c < n + t)).image (TV C n G i)).card
              ≤ (h.inputs.toFinset.filter (fun c => c < n + t)).card := Finset.card_image_le
            _ ≤ h.inputs.toFinset.card := Finset.card_filter_le _ _
            _ ≤ h.inputs.length := List.toFinset_card_le _
            _ ≤ 1 + 1 := (gate_ok C hM t h hg).2
        have hp2 : TV C n G i (n + t) ⊆
            ((h.inputs.toFinset.filter (fun c => c < n + t)).image (TV C n G i)).biUnion id := by
          intro j hj
          simp only [TV, Finset.mem_filter] at hj
          obtain ⟨c, hc, hlt, hcv'⟩ := (val_or C n _ t h hg hop).mp hj.2
          refine Finset.mem_biUnion.mpr ⟨TV C n G i c, Finset.mem_image.mpr ⟨c, ?_, rfl⟩, ?_⟩
          · simp [hc, hlt]
          · simp only [id, TV, Finset.mem_filter]
            exact ⟨hj.1, hcv'⟩
        have hp3 : ∀ B ∈ (h.inputs.toFinset.filter (fun c => c < n + t)).image (TV C n G i),
            (B ∩ T).card ≤ 1 := by
          intro B hB
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
          simp only [Finset.mem_filter, List.mem_toFinset] at hc
          exact hT c hc.2 (hclean c hc.1 hc.2)
        obtain ⟨T', h1, h2, h3⟩ := shrink T (TV C n G i (n + t)) _ 1 hp1 hp2 hp3
        exact ⟨T', h1, by rw [hcv]; exact h2, fun _ => h3⟩

theorem phase1 (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hM : Monotone2 C) (i : Fin n) :
    ∀ m, ∃ T : Finset (Fin n), T ⊆ Nb G i ∧
      (Nb G i).card ≤ T.card + ∑ w ∈ Finset.range m, cV C n G X i w ∧
      ∀ w < m, Vclean C n G X i w → (TV C n G i w ∩ T).card ≤ 1 := by
  intro m
  induction m with
  | zero => exact ⟨Nb G i, Finset.Subset.refl _, by simp, fun w hw => absurd hw (by omega)⟩
  | succ m ih =>
    obtain ⟨T, hT1, hT2, hT3⟩ := ih
    obtain ⟨T', h1, h2, h3⟩ := phase1_step C n G X hM i m T hT3
    refine ⟨T', h1.trans hT1, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      omega
    · intro w hw hcl
      by_cases hwm : w = m
      · subst hwm
        exact h3 hcl
      · exact (Finset.card_le_card (Finset.inter_subset_inter_left h1)).trans
          (hT3 w (by omega) hcl)

noncomputable def JJ (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (i : Fin n) (w : ℕ) :
    Finset (Fin n) :=
  (Nb G i).filter (fun j => Chain C n (e1 j) i.val w ∧ Chain C n (e1 j) w C.output)

def Mclean (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i : Fin n)
    (w : ℕ) : Prop := ¬ Chain C n (mI G X i) w C.output

noncomputable def JP (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (i : Fin n) (w g : ℕ) :
    Finset (Fin n) :=
  (Nb G i).filter (fun j => Chain C n (e1 j) i.val w ∧ Step C n (e1 j) w g ∧
    Chain C n (e1 j) g C.output)

noncomputable def Rd (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (i : Fin n) (w : ℕ) :
    Finset ℕ :=
  (Finset.range (n + C.size)).filter (fun g => (JP C n G i w g).Nonempty)

noncomputable def cM (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) : ℕ :=
  if Mclean C n G X i w ∧ 2 ≤ (JJ C n G i w).card then (Rd C n G i w).card - 1 else 0

theorem phase2_step (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w0 : ℕ) (T : Finset (Fin n))
    (hV : ∀ c < n + C.size, Vclean C n G X i c → (TV C n G i c ∩ T).card ≤ 1)
    (hJ : ∀ g, w0 < g → g < n + C.size → Mclean C n G X i g → (JJ C n G i g ∩ T).card ≤ 1) :
    ∃ T' : Finset (Fin n), T' ⊆ T ∧ T.card ≤ T'.card + cM C n G X i w0 ∧
      (Mclean C n G X i w0 → (JJ C n G i w0 ∩ T').card ≤ 1) := by
  by_cases hcl : Mclean C n G X i w0
  swap
  · exact ⟨T, Finset.Subset.refl _, by omega, fun h => absurd h hcl⟩
  by_cases hcard : (JJ C n G i w0).card ≤ 1
  · exact ⟨T, Finset.Subset.refl _, by omega,
      fun _ => (Finset.card_le_card Finset.inter_subset_left).trans hcard⟩
  have hcm : cM C n G X i w0 = (Rd C n G i w0).card - 1 := by
    unfold cM
    rw [if_pos ⟨hcl, by omega⟩]
  have hne : w0 ≠ C.output := by
    intro h
    apply hcl
    rw [h]
  have hp1 : ((Rd C n G i w0).image (JP C n G i w0)).card ≤ ((Rd C n G i w0).card - 1) + 1 := by
    have h5 := Finset.card_image_le (s := Rd C n G i w0) (f := JP C n G i w0)
    omega
  have hp2 : JJ C n G i w0 ⊆ ((Rd C n G i w0).image (JP C n G i w0)).biUnion id := by
    intro j hj
    simp only [JJ, Finset.mem_filter] at hj
    obtain ⟨hjN, hfrom, hreach⟩ := hj
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨g, hstep, hg⟩
    · exact absurd heq hne
    · have hjP : j ∈ JP C n G i w0 g := by
        simp only [JP, Finset.mem_filter]
        exact ⟨hjN, hfrom, hstep, hg⟩
      have hgR : g ∈ Rd C n G i w0 := by
        simp only [Rd, Finset.mem_filter, Finset.mem_range]
        exact ⟨(step_lt C n _ _ _ hstep).2.2, ⟨j, hjP⟩⟩
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨g, hgR, rfl⟩, hjP⟩
  have hp3 : ∀ B ∈ (Rd C n G i w0).image (JP C n G i w0), (B ∩ T).card ≤ 1 := by
    intro B hB
    obtain ⟨g, hgR, rfl⟩ := Finset.mem_image.mp hB
    simp only [Rd, Finset.mem_filter, Finset.mem_range] at hgR
    obtain ⟨hgW, j0, hj0⟩ := hgR
    simp only [JP, Finset.mem_filter] at hj0
    obtain ⟨_, _, hstep0, _⟩ := hj0
    have hlt0 := (step_lt C n _ _ _ hstep0).1
    by_cases hgc : Mclean C n G X i g
    · have hsub : JP C n G i w0 g ⊆ JJ C n G i g := by
        intro j hj
        simp only [JP, Finset.mem_filter] at hj
        simp only [JJ, Finset.mem_filter]
        exact ⟨hj.1, Relation.ReflTransGen.tail hj.2.1 hj.2.2.1, hj.2.2.2⟩
      exact (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans
        (hJ g hlt0 hgW hgc)
    · have hgreach : Chain C n (mI G X i) g C.output := by
        unfold Mclean at hgc
        exact not_not.mp hgc
      have hnostep : ¬ Step C n (mI G X i) w0 g :=
        fun hs => hcl (Relation.ReflTransGen.head hs hgreach)
      obtain ⟨t, h, rfl, hg, ha, hlt, hside0⟩ := hstep0
      have hns : ¬ (h.op = GateOp.or ∨
          ∀ c ∈ h.inputs, c ≠ w0 → (c < n + t ∧ val C n (mI G X i) c = true)) :=
        fun hx => hnostep ⟨t, h, rfl, hg, ha, hlt, hx⟩
      simp only [not_or, not_forall] at hns
      obtain ⟨hnor, c, hc, hcw, hcn⟩ := hns
      have hsideof : ∀ j, Step C n (e1 j) w0 (n + t) →
          c < n + t ∧ val C n (e1 j) c = true := by
        intro j hs
        obtain ⟨t', h', heq, hg', _, _, hside⟩ := hs
        have ht : t' = t := by omega
        subst ht
        have hh : h' = h := by
          rw [hg] at hg'
          exact (Option.some.inj hg').symm
        subst hh
        rcases hside with hor | hs'
        · exact absurd hor hnor
        · exact hs' c hc hcw
      have hclt : c < n + t := (hsideof j0 ⟨t, h, rfl, hg, ha, hlt, hside0⟩).1
      have hcc : Vclean C n G X i c := by
        unfold Vclean
        by_contra hx
        exact hcn ⟨hclt, by simpa using hx⟩
      have hsub : JP C n G i w0 (n + t) ⊆ TV C n G i c := by
        intro j hj
        simp only [JP, Finset.mem_filter] at hj
        simp only [TV, Finset.mem_filter]
        exact ⟨hj.1, (hsideof j hj.2.2.1).2⟩
      exact (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans
        (hV c (by omega) hcc)
  obtain ⟨T', h1, h2, h3⟩ :=
    shrink T (JJ C n G i w0) _ ((Rd C n G i w0).card - 1) hp1 hp2 hp3
  exact ⟨T', h1, by rw [hcm]; exact h2, fun _ => h3⟩

theorem phase2 (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (T0 : Finset (Fin n))
    (hV : ∀ c < n + C.size, Vclean C n G X i c → (TV C n G i c ∩ T0).card ≤ 1) :
    ∀ m, m ≤ n + C.size → ∃ T : Finset (Fin n), T ⊆ T0 ∧
      T0.card ≤ T.card + ∑ w ∈ Finset.Ico (n + C.size - m) (n + C.size), cM C n G X i w ∧
      ∀ w, n + C.size - m ≤ w → w < n + C.size → Mclean C n G X i w →
        (JJ C n G i w ∩ T).card ≤ 1 := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨T0, Finset.Subset.refl _, by simp, fun w h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨T, hT1, hT2, hT3⟩ := ih (by omega)
    have hw0 : n + C.size - (m + 1) + 1 = n + C.size - m := by omega
    obtain ⟨T', h1, h2, h3⟩ := phase2_step C n G X i (n + C.size - (m + 1)) T
      (fun c hc hcc =>
        (Finset.card_le_card (Finset.inter_subset_inter_left hT1)).trans (hV c hc hcc))
      (fun g hg1 hg2 hgc => hT3 g (by omega) hg2 hgc)
    refine ⟨T', h1.trans hT1, ?_, ?_⟩
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n + C.size - (m + 1) < n + C.size), hw0]
      omega
    · intro w hw1 hw2 hcl
      by_cases hww : w = n + C.size - (m + 1)
      · subst hww
        exact h3 hcl
      · exact (Finset.card_le_card (Finset.inter_subset_inter_left h1)).trans
          (hT3 w (by omega) hw2 hcl)

theorem mclean_input (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i : Fin n) : Mclean C n G X i i.val := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  intro hch
  have hle : Le (mI G X i) (fun v => e1 i v || mI G X i v) := by
    intro v hv
    simp [hv]
  have hv : val C n (fun v => e1 i v || mI G X i v) i.val = true := by
    rw [val_input C n _ _ i.isLt]
    simp [e1]
  obtain ⟨u, v, hadj, hu, hv'⟩ := (hf _).mp (chain_sound C n hM _ _ hle _ _ hch hv)
  simp only [e1, mI, Bool.or_eq_true, decide_eq_true_eq] at hu hv'
  rcases hu with hu | ⟨huX, hun⟩ <;> rcases hv' with hv' | ⟨hvX, hvn⟩
  · exact hadj.ne (hu.trans hv'.symm)
  · rw [hu] at hadj
    exact hvn hadj
  · rw [hv'] at hadj
    exact hun hadj.symm
  · exact huX ((hbip u v hadj).mpr hvX)

theorem deg_bound (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i : Fin n) (hi : i ∈ X) :
    (Nb G i).card ≤ 1 + ∑ w ∈ Finset.range (n + C.size), cV C n G X i w +
      ∑ w ∈ Finset.range (n + C.size), cM C n G X i w := by
  have hM := hS.1
  obtain ⟨T1, hT1, hc1, hV1⟩ := phase1 C n G X hM i (n + C.size)
  obtain ⟨T, hT, hc2, hJ⟩ := phase2 C n G X i T1 hV1 (n + C.size) (le_refl _)
  rw [Nat.sub_self, ← Finset.range_eq_Ico] at hc2
  have hi_lt : i.val < n + C.size := by
    have := i.isLt
    omega
  have hJi := hJ i.val (by omega) hi_lt (mclean_input C n G X hS i)
  have hJJ : JJ C n G i i.val = Nb G i := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact ⟨Relation.ReflTransGen.refl, witness C n G X hS i j hi ((mem_Nb G i j).mp hj)⟩
  rw [hJJ] at hJi
  have hTsub : T ⊆ Nb G i := hT.trans hT1
  rw [Finset.inter_eq_right.mpr hTsub] at hJi
  omega

theorem sum_le_of_unique {ι : Type} (s : Finset ι) (f : ι → ℕ) (b : ℕ) (hb : ∀ i ∈ s, f i ≤ b)
    (hu : ∀ i ∈ s, ∀ i' ∈ s, f i ≠ 0 → f i' ≠ 0 → i = i') : ∑ i ∈ s, f i ≤ b := by
  by_cases h : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i0, hi0, hf0⟩ := h
    rw [Finset.sum_eq_single_of_mem i0 hi0 (fun i' hi' hne => by
      by_contra hfi
      exact hne (hu i' hi' i0 hi0 hfi hf0))]
    exact hb i0 hi0
  · simp only [not_exists, not_and, not_not] at h
    rw [Finset.sum_eq_zero h]
    exact Nat.zero_le _

theorem cV_le_one (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) : cV C n G X i w ≤ 1 := by
  unfold cV
  split_ifs <;> omega

theorem cV_ne_zero (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) (h : cV C n G X i w ≠ 0) :
    IsOr C n w ∧ Vclean C n G X i w ∧ 2 ≤ (TV C n G i w).card := by
  unfold cV at h
  by_contra hc
  rw [if_neg hc] at h
  exact h rfl

theorem cM_ne_zero (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) (h : cM C n G X i w ≠ 0) :
    Mclean C n G X i w ∧ 2 ≤ (JJ C n G i w).card := by
  unfold cM at h
  by_contra hc
  rw [if_neg hc] at h
  exact h rfl

theorem cM_le (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (i : Fin n) (w : ℕ) : cM C n G X i w ≤ (Rd C n G i w).card - 1 := by
  unfold cM
  split_ifs <;> omega

theorem c4_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e)
    (i i' j1 j2 : Fin n) (h1 : G.Adj i j1) (h2 : G.Adj i j2) (h1' : G.Adj i' j1)
    (h2' : G.Adj i' j2) (hne : j1 ≠ j2) : i = i' := by
  rcases hC4 i j1 i' j2 h1 h1'.symm h2' h2.symm with h | h
  · exact h
  · exact absurd h hne

theorem cV_unique (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i i' : Fin n) (hi : i ∈ X) (w : ℕ)
    (h1 : cV C n G X i w ≠ 0) (h2 : cV C n G X i' w ≠ 0) : i = i' := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  obtain ⟨_, _, hcard⟩ := cV_ne_zero C n G X i w h1
  obtain ⟨_, hcl, _⟩ := cV_ne_zero C n G X i' w h2
  have hcl' : val C n (mI G X i') w = false := hcl
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (TV C n G i w).card)
  simp only [TV, Finset.mem_filter, mem_Nb] at hj1 hj2
  have key : ∀ j, G.Adj i j → val C n (e1 j) w = true → G.Adj i' j := by
    intro j hadj hv
    by_contra hna
    have hjX : j ∉ X := (hbip i j hadj).mp hi
    have h5 := val_mono C n hM (e1 j) (mI G X i') (le_e1_mI G X i' j hjX hna) w hv
    rw [hcl'] at h5
    cases h5
  exact c4_unique G hC4 i i' j1 j2 hj1.1 hj2.1 (key j1 hj1.1 hj1.2) (key j2 hj2.1 hj2.2) hne

theorem cM_unique (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i i' : Fin n) (hi : i ∈ X) (w : ℕ)
    (h1 : cM C n G X i w ≠ 0) (h2 : cM C n G X i' w ≠ 0) : i = i' := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  obtain ⟨_, hcard⟩ := cM_ne_zero C n G X i w h1
  obtain ⟨hcl, _⟩ := cM_ne_zero C n G X i' w h2
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (JJ C n G i w).card)
  simp only [JJ, Finset.mem_filter, mem_Nb] at hj1 hj2
  have key : ∀ j, G.Adj i j → Chain C n (e1 j) w C.output → G.Adj i' j := by
    intro j hadj hch
    by_contra hna
    have hjX : j ∉ X := (hbip i j hadj).mp hi
    exact hcl (chain_mono C n hM (e1 j) (mI G X i') (le_e1_mI G X i' j hjX hna) w _ hch)
  exact c4_unique G hC4 i i' j1 j2 hj1.1 hj2.1 (key j1 hj1.1 hj1.2.2) (key j2 hj2.1 hj2.2.2) hne

noncomputable def orSet (C : Circuit) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + C.size)).filter (fun w => IsOr C n w)

noncomputable def orV (C : Circuit) (n : ℕ) (X : Finset (Fin n)) : Finset ℕ :=
  (orSet C n).filter (fun w => ∃ j : Fin n, j ∉ X ∧ val C n (e1 j) w = true)

def LRrel (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (w g : ℕ) : Prop :=
  ∃ i ∈ X, (JP C n G i w g).Nonempty

noncomputable def LR (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (w : ℕ) : Finset ℕ :=
  (Finset.range (n + C.size)).filter (fun g => LRrel C n G X w g)

noncomputable def Op (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (g : ℕ) : Finset ℕ :=
  (Finset.range (n + C.size)).filter (fun w => LRrel C n G X w g)

noncomputable def orL (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    Finset ℕ :=
  (orSet C n).filter (fun g => 2 ≤ (Op C n G X g).card)

theorem sumV (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) :
    ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cV C n G X i w ≤ (orV C n X).card := by
  have hbip := hS.2.1
  have h1 : ∀ w ∈ Finset.range (n + C.size),
      ∑ i ∈ X, cV C n G X i w ≤ (if w ∈ orV C n X then 1 else 0) := by
    intro w hw
    by_cases hz : ∀ i ∈ X, cV C n G X i w = 0
    · rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
    · simp only [not_forall] at hz
      obtain ⟨i, hi, hne⟩ := hz
      have hmem : w ∈ orV C n X := by
        obtain ⟨hor, _, hcard⟩ := cV_ne_zero C n G X i w hne
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (TV C n G i w).card)
        simp only [TV, Finset.mem_filter, mem_Nb] at hj
        simp only [orV, orSet, Finset.mem_filter]
        exact ⟨⟨hw, hor⟩, j, (hbip i j hj.1).mp hi, hj.2⟩
      rw [if_pos hmem]
      exact sum_le_of_unique X _ 1 (fun i _ => cV_le_one C n G X i w)
        (fun i hi i' _ h1 h2 => cV_unique C n G X hS i i' hi w h1 h2)
  calc ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cV C n G X i w
      ≤ ∑ w ∈ Finset.range (n + C.size), (if w ∈ orV C n X then 1 else 0) :=
        Finset.sum_le_sum h1
    _ = ((Finset.range (n + C.size)).filter (fun w => w ∈ orV C n X)).card :=
        (Finset.card_filter _ _).symm
    _ ≤ (orV C n X).card := Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)

theorem sumM (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) :
    ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cM C n G X i w ≤
      ∑ w ∈ Finset.range (n + C.size), ((LR C n G X w).card - 1) := by
  apply Finset.sum_le_sum
  intro w _
  apply sum_le_of_unique
  · intro i hi
    refine (cM_le C n G X i w).trans (Nat.sub_le_sub_right (Finset.card_le_card ?_) 1)
    intro g hg
    simp only [Rd, Finset.mem_filter] at hg
    simp only [LR, Finset.mem_filter]
    exact ⟨hg.1, i, hi, hg.2⟩
  · intro i hi i' _ h1 h2
    exact cM_unique C n G X hS i i' hi w h1 h2

theorem lr_data (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (w g : ℕ) (h : LRrel C n G X w g) :
    ∃ (i j : Fin n), i ∈ X ∧ G.Adj i j ∧ Chain C n (e1 j) i.val w ∧ Step C n (e1 j) w g ∧
      Chain C n (e1 j) g C.output := by
  obtain ⟨i, hi, j, hj⟩ := h
  simp only [JP, Finset.mem_filter, mem_Nb] at hj
  exact ⟨i, j, hi, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2⟩

theorem reach_no_single (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (j : Fin n) (w : ℕ) (hch : Chain C n (e1 j) w C.output) (hjX : j ∉ X)
    (j1 : Fin n) (hj1 : j1 ∉ X) : ¬ val C n (e1 j1) w = true := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  intro hv
  have h1 := val_mono C n hM (e1 j1) (e2 j1 j) (le_e1_e2' j1 j) w hv
  have h2 := chain_sound C n hM (e1 j) (e2 j1 j) (le_e1_e2 j1 j) w _ hch h1
  have hadj := edge_e2 G j1 j ((hf _).mp h2)
  exact hj1 ((hbip j1 j hadj).mpr hjX)

theorem live_not_free (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (i j : Fin n) (hi : i ∈ X) (w : ℕ)
    (hfrom : Chain C n (e1 j) i.val w) (hreach : Chain C n (e1 j) w C.output) :
    ¬ Free C n X w := by
  obtain ⟨hM, hbip, hC4, hK, hf⟩ := hS
  intro hfree
  have hi1 : val C n (e2 i j) i.val = true := by
    rw [val_input C n _ _ i.isLt]
    simp [e2]
  have h1 := chain_sound C n hM (e1 j) (e2 i j) (le_e1_e2 i j) _ _ hfrom hi1
  rw [hfree (e2 i j) (e1 j) (e2_agree X i j hi)] at h1
  exact not_edge_e1 G j ((hf _).mp
    (chain_sound C n hM (e1 j) (e1 j) (fun _ hv => hv) w _ hreach h1))

theorem op_card (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (g : ℕ) :
    (Op C n G X g).card ≤ (if (Op C n G X g).Nonempty then 1 else 0) +
      (if g ∈ orL C n G X then 1 else 0) := by
  by_cases hne : (Op C n G X g).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
  rw [if_pos hne]
  obtain ⟨w0, hw0⟩ := hne
  simp only [Op, Finset.mem_filter, Finset.mem_range] at hw0
  obtain ⟨i0, j0, hi0, hadj0, hfrom0, hstep0, hreach0⟩ := lr_data C n G X w0 g hw0.2
  obtain ⟨t, h, rfl, hg, ha0, hlt0, hside0⟩ := hstep0
  have hM := hS.1
  have hsub : Op C n G X (n + t) ⊆ h.inputs.toFinset := by
    intro w hw
    simp only [Op, Finset.mem_filter] at hw
    obtain ⟨i, j, hi, hadj, hfrom, hstep, hreach⟩ := lr_data C n G X w (n + t) hw.2
    obtain ⟨t', h', heq, hg', ha, _, _⟩ := hstep
    have ht : t' = t := by omega
    subst ht
    have hh : h' = h := by
      rw [hg] at hg'
      exact (Option.some.inj hg').symm
    subst hh
    exact List.mem_toFinset.mpr ha
  have hle2 : (Op C n G X (n + t)).card ≤ 2 :=
    (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (gate_ok C hM t h hg).2)
  by_cases hL : (n + t) ∈ orL C n G X
  · rw [if_pos hL]
    omega
  · rw [if_neg hL]
    by_contra hgt
    have h2 : 2 ≤ (Op C n G X (n + t)).card := by omega
    rcases (gate_ok C hM t h hg).1 with hop | hop
    · obtain ⟨w1, hw1, w2, hw2, hne12⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (Op C n G X (n + t)).card)
      have hin1 := List.mem_toFinset.mp (hsub hw1)
      have hin2 := List.mem_toFinset.mp (hsub hw2)
      simp only [Op, Finset.mem_filter] at hw1 hw2
      obtain ⟨i1, j1, hi1, hadj1, hfrom1, hstep1, hreach1⟩ := lr_data C n G X w1 (n + t) hw1.2
      obtain ⟨i2, j2, hi2, hadj2, hfrom2, hstep2, hreach2⟩ := lr_data C n G X w2 (n + t) hw2.2
      have hlt1 := (step_lt C n _ _ _ hstep1).1
      have hlt2 := (step_lt C n _ _ _ hstep2).1
      have hfree : Free C n X w1 ∨ Free C n X w2 := by
        rcases pair_of_mem h.inputs (gate_ok C hM t h hg).2 w1 w2 hin1 hin2 (Ne.symm hne12)
          with hl | hl
        · exact hS.2.2.2.1 t h w1 w2 hg hop hl hlt1 hlt2
        · exact (hS.2.2.2.1 t h w2 w1 hg hop hl hlt2 hlt1).symm
      rcases hfree with hf1 | hf2
      · exact live_not_free C n G X hS i1 j1 hi1 w1 hfrom1
          (Relation.ReflTransGen.head hstep1 hreach1) hf1
      · exact live_not_free C n G X hS i2 j2 hi2 w2 hfrom2
          (Relation.ReflTransGen.head hstep2 hreach2) hf2
    · apply hL
      simp only [orL, orSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨by have := gate_lt C t h hg; omega, t, h, rfl, hg, hop⟩, h2⟩

theorem live_count (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (hiso : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w) :
    X.card + ∑ w ∈ Finset.range (n + C.size), ((LR C n G X w).card - 1) ≤
      (orL C n G X).card + 1 := by
  have e1' : ∑ w ∈ Finset.range (n + C.size), (LR C n G X w).card =
      ((Finset.range (n + C.size)).filter (fun w => (LR C n G X w).Nonempty)).card +
        ∑ w ∈ Finset.range (n + C.size), ((LR C n G X w).card - 1) := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hne : (LR C n G X w).Nonempty
    · rw [if_pos hne]
      have := Finset.card_pos.mpr hne
      omega
    · rw [if_neg hne, Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have e2' : ∑ w ∈ Finset.range (n + C.size), (LR C n G X w).card =
      ∑ g ∈ Finset.range (n + C.size), (Op C n G X g).card := by
    simp only [LR, Op, Finset.card_filter]
    exact Finset.sum_comm
  have e3' : ∑ g ∈ Finset.range (n + C.size), (Op C n G X g).card ≤
      ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)).card +
        (orL C n G X).card := by
    calc ∑ g ∈ Finset.range (n + C.size), (Op C n G X g).card
        ≤ ∑ g ∈ Finset.range (n + C.size), ((if (Op C n G X g).Nonempty then 1 else 0) +
            (if g ∈ orL C n G X then 1 else 0)) :=
          Finset.sum_le_sum (fun g _ => op_card C n G X hS g)
      _ = ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)).card +
            ((Finset.range (n + C.size)).filter (fun g => g ∈ orL C n G X)).card := by
          rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
      _ ≤ _ := Nat.add_le_add_left
          (Finset.card_le_card (fun g hg => (Finset.mem_filter.mp hg).2)) _
  have e4' : X.card +
      ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)).card ≤
      ((Finset.range (n + C.size)).filter (fun w => (LR C n G X w).Nonempty)).card + 1 := by
    have hsub : (X.image (fun i : Fin n => i.val)) ∪
        ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)) ⊆
        insert C.output
          ((Finset.range (n + C.size)).filter (fun w => (LR C n G X w).Nonempty)) := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨j, hadj⟩ := hiso i
        have hw := witness C n G X hS i j hi hadj
        rcases Relation.ReflTransGen.cases_head hw with heq | ⟨g, hstep, hg⟩
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · apply Finset.mem_insert_of_mem
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by have := i.isLt; omega, g, ?_⟩
          simp only [LR, Finset.mem_filter, Finset.mem_range]
          refine ⟨(step_lt C n _ _ _ hstep).2.2, i, hi, j, ?_⟩
          simp only [JP, Finset.mem_filter, mem_Nb]
          exact ⟨hadj, Relation.ReflTransGen.refl, hstep, hg⟩
      · simp only [Finset.mem_filter, Finset.mem_range] at hv
        obtain ⟨hvW, w, hw⟩ := hv
        simp only [Op, Finset.mem_filter] at hw
        obtain ⟨i, j, hi, hadj, hfrom, hstep, hreach⟩ := lr_data C n G X w v hw.2
        rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨g', hstep', hg'⟩
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · apply Finset.mem_insert_of_mem
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨hvW, g', ?_⟩
          simp only [LR, Finset.mem_filter, Finset.mem_range]
          refine ⟨(step_lt C n _ _ _ hstep').2.2, i, hi, j, ?_⟩
          simp only [JP, Finset.mem_filter, mem_Nb]
          exact ⟨hadj, Relation.ReflTransGen.tail hfrom hstep, hstep', hg'⟩
    have hdisj : Disjoint (X.image (fun i : Fin n => i.val))
        ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv1
      simp only [Finset.mem_filter] at hv2
      obtain ⟨_, w, hw⟩ := hv2
      simp only [Op, Finset.mem_filter] at hw
      obtain ⟨_, _, _, _, _, hstep, _⟩ := lr_data C n G X w i.val hw.2
      have h5 := (step_lt C n _ _ _ hstep).2.1
      have h6 := i.isLt
      omega
    have hcardX : (X.image (fun i : Fin n => i.val)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    calc X.card + ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty)).card
        = ((X.image (fun i : Fin n => i.val)) ∪
            ((Finset.range (n + C.size)).filter (fun g => (Op C n G X g).Nonempty))).card := by
          rw [Finset.card_union_of_disjoint hdisj, hcardX]
      _ ≤ (insert C.output
            ((Finset.range (n + C.size)).filter (fun w => (LR C n G X w).Nonempty))).card :=
          Finset.card_le_card hsub
      _ ≤ _ := Finset.card_insert_le _ _
  omega

theorem orV_orL_disjoint (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) : Disjoint (orV C n X) (orL C n G X) := by
  rw [Finset.disjoint_left]
  intro g hV hL
  simp only [orV, Finset.mem_filter] at hV
  obtain ⟨_, j1, hj1X, hj1v⟩ := hV
  simp only [orL, Finset.mem_filter] at hL
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (Op C n G X g).card)
  simp only [Op, Finset.mem_filter] at hw
  obtain ⟨i, j, hi, hadj, hfrom, hstep, hreach⟩ := lr_data C n G X w g hw.2
  exact reach_no_single C n G X hS j g hreach ((hS.2.1 i j hadj).mp hi) j1 hj1X hj1v

theorem and_or_size (C : Circuit) (n : ℕ) : (andSet C).card + (orSet C n).card ≤ C.size := by
  have h1 : ((andSet C).image (fun t => n + t)).card = (andSet C).card :=
    Finset.card_image_of_injective _ (add_right_injective n)
  have hdisj : Disjoint ((andSet C).image (fun t => n + t)) (orSet C n) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw1
    simp only [andSet, Finset.mem_filter] at ht
    obtain ⟨_, h, hg, hop⟩ := ht
    rw [orSet, Finset.mem_filter] at hw2
    obtain ⟨_, t', h', heq, hg', hop'⟩ := hw2
    have ht' : t' = t := by omega
    subst ht'
    rw [hg] at hg'
    have hh := Option.some.inj hg'
    subst hh
    rw [hop] at hop'
    cases hop'
  have hsub : ((andSet C).image (fun t => n + t)) ∪ orSet C n ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      simp only [andSet, Finset.mem_filter, Finset.mem_range] at ht
      simp only [Finset.mem_Ico]
      omega
    · rw [orSet, Finset.mem_filter, Finset.mem_range] at hw
      obtain ⟨hlt, t, h, rfl, _, _⟩ := hw
      simp only [Finset.mem_Ico]
      omega
  calc (andSet C).card + (orSet C n).card
      = (((andSet C).image (fun t => n + t)) ∪ orSet C n).card := by
        rw [Finset.card_union_of_disjoint hdisj, h1]
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card hsub
    _ = C.size := by simp

theorem edge_count {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hbip : ∀ u v : Fin n, G.Adj u v → (u ∈ X ↔ v ∉ X)) :
    G.edgeSet.ncard ≤ ∑ i ∈ X, (Nb G i).card := by
  have hsub : G.edgeSet ⊆ ↑((X.biUnion (fun i => (Nb G i).image (fun j => (i, j)))).image
      (fun p : Fin n × Fin n => s(p.1, p.2))) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := by simpa using he
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      by_cases hu : u ∈ X
      · exact ⟨(u, v), Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr
          ⟨v, (mem_Nb G u v).mpr hadj, rfl⟩⟩, rfl⟩
      · have hv : v ∈ X := by
          by_contra hv
          exact hu ((hbip u v hadj).mpr hv)
        exact ⟨(v, u), Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr
          ⟨u, (mem_Nb G v u).mpr hadj.symm, rfl⟩⟩, Sym2.eq_swap⟩
  calc G.edgeSet.ncard
      ≤ (↑((X.biUnion (fun i => (Nb G i).image (fun j => (i, j)))).image
          (fun p : Fin n × Fin n => s(p.1, p.2))) : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((X.biUnion (fun i => (Nb G i).image (fun j => (i, j)))).image
          (fun p : Fin n × Fin n => s(p.1, p.2))).card := Set.ncard_coe_finset _
    _ ≤ (X.biUnion (fun i => (Nb G i).image (fun j => (i, j)))).card := Finset.card_image_le
    _ ≤ ∑ i ∈ X, ((Nb G i).image (fun j => (i, j))).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ X, (Nb G i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)

theorem main (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hS : Setup C n G X) (hiso : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w) (k : ℕ)
    (hk : ∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) :
    G.edgeSet.ncard + k ≤ C.size + 1 := by
  have h1 := edge_count G X hS.2.1
  have h2 : ∑ i ∈ X, (Nb G i).card ≤
      ∑ i ∈ X, (1 + ∑ w ∈ Finset.range (n + C.size), cV C n G X i w +
        ∑ w ∈ Finset.range (n + C.size), cM C n G X i w) :=
    Finset.sum_le_sum (fun i hi => deg_bound C n G X hS i hi)
  have hA : ∑ i ∈ X, ∑ w ∈ Finset.range (n + C.size), cV C n G X i w =
      ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cV C n G X i w := Finset.sum_comm
  have hB : ∑ i ∈ X, ∑ w ∈ Finset.range (n + C.size), cM C n G X i w =
      ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cM C n G X i w := Finset.sum_comm
  have h3 : ∑ i ∈ X, (1 + ∑ w ∈ Finset.range (n + C.size), cV C n G X i w +
        ∑ w ∈ Finset.range (n + C.size), cM C n G X i w) =
      X.card + ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cV C n G X i w +
        ∑ w ∈ Finset.range (n + C.size), ∑ i ∈ X, cM C n G X i w := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB]
    simp
  have h4 := sumV C n G X hS
  have h5 := sumM C n G X hS
  have h6 := live_count C n G X hS hiso
  have h7 := Finset.card_union_of_disjoint (orV_orL_disjoint C n G X hS)
  have h8 : (orV C n X ∪ orL C n G X).card ≤ (orSet C n).card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have h9 := and_or_size C n
  have h10 := and_count C n G X hS k hk
  omega

end PEqualNP.Outside.L_meta_647

theorem PEqualNP.Outside.L_meta_647 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin n, G.Adj u v → (u ∈ X ↔ v ∉ X)) → (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.Monotone2 C → (∃ S : Set ℕ, (∀ l ∈ X, l.val ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j → i ∈ S → n + j ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j → ¬ (a ∈ S ∧ b ∈ S))) → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → G.edgeSet.ncard + k ≤ C.size + 1 := by
  intro n k G X C hbip hC4 hiso hk hM hS hf
  obtain ⟨S, hSX, hScl, hSand⟩ := hS
  have hfree := PEqualNP.Outside.L_meta_647.free_of_not_mem C n hM X S hSX hScl
  have hSetup : PEqualNP.Outside.L_meta_647.Setup C n G X := by
    refine ⟨hM, hbip, hC4, ?_, ?_⟩
    · intro j h a b hg hop hl ha hb
      by_cases haS : a ∈ S
      · right
        apply hfree
        intro hbS
        exact hSand j h hg hop a b hl ha hb ⟨haS, hbS⟩
      · left
        exact hfree a haS
    · intro x
      exact hf x
  exact PEqualNP.Outside.L_meta_647.main C n G X hSetup hiso k hk
