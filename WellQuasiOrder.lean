import Mathlib.Tactic
import Mathlib.Order.Antichain
import Mathlib.Data.Set.Card

variable {α : Type*} [hp: Preorder α] {x y z : α} {A : Set α}

open Set
section prereqs

/- A version of Ramsey's theorem. Trying to prove this would be a separate project
 that probably belongs in another file. -/
theorem ramseyGraph (P : ℕ → ℕ → Prop) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      ((∀ {i j}, i < j → P (a i) (a j)) ∨ (∀ {i j}, i < j → ¬ P (a i) (a j))) :=
  sorry

end prereqs


/- This typeclass states that the relation `≤` is a well-quasi-order; that is: it is
  a preorder (aka quasi-order) such that every infinite sequence `a₀, a₁,...` contains
  a pair `a_i ≤ a_j` with `i < j`.
  We use Lean's `class` machinery here in the definition so that all the basic stuff
  about preorders can be pulled straight from mathlib rather than redone from scratch. -/
class IsWQO (α : Type*) [Preorder α] : Prop where
  (forall_seq_exists_le : ∀ (f : ℕ → α), ∃ i j, i < j ∧ f i ≤ f j)

/- WQOs don't have infinite descending chains -/
theorem not_exists_descending_chain (α : Type*) [Preorder α] [hwqo:IsWQO α] :
    ¬ ∃ (f : ℕ → α), ∀ i j, i < j → f j < f i := by
  -- Suppose that such an `f` exists.
  rintro ⟨f, hf⟩
  -- By the definition of a WQO, there is a pair `i,j` with `i < j` and `f i < f j`
  have h:=hwqo.forall_seq_exists_le f
  -- But this contradicts the choice of `f`, which states that `f j ≤ f i`.
  obtain ⟨i,j,h⟩:=h
  have hij:=hf i j  h.1
  have h:=h.2
  apply not_le_of_lt at hij
  contradiction



/- Antichains in a WQO are all finite. -/
theorem IsAntichain.Finite [hwqo:IsWQO α] (hA : IsAntichain (· ≤ ·) A) : A.Finite := by
  -- Suppose not, so `A` is finite
  rw [← not_infinite]
  intro h_infinite

  -- Since `A` is infinite, there is an injection `f : ℕ → A`.
  obtain ⟨f, hf⟩ := h_infinite.natEmbedding

  -- To apply `forall_seq_exists_lt`, we actually need a function from `ℕ` to `α`,
  -- so we compose `f` with the coercion from `A` to `α`
  -- Lean can 'see through' this definition, so we don't actually need to rewrite with it.
  set f' : ℕ → α := fun x ↦ (f x : α)

  -- By the definition of a `WQO`, there is a pair `i < j` with `f' i ≤ f j`.
  obtain⟨i,j,hij,hfij⟩ :=hwqo.forall_seq_exists_le f'
  -- Since `f i ∈ A` and `f j ∈ A`, the definition of an antichain gives that `f i = f j`.
  -- (Well, actually... it gives that `f i` and `f j` are the same when coerced to `α`.)
  have hfij: f i≤ f j := hfij
  have hneq: f i ≠ f j := by
    have h :i ≠ j := hij.ne
    by_contra heq
    apply h
    exact hf heq
  have h:=hA (f i).mem (f j).mem
  simp at h
  rw[not_imp_not] at h
  apply h at hfij
  -- By the injectivity of coercion, this also means that `f i = f j`, and by the injectivity
  have hfij: f i = f j := by
    rw [Subtype.val_inj] at hfij
    exact hfij
  -- of `f`, we get that `i = j`.
  have := hf hfij
  -- This contradicts `i < j`.
  tauto


theorem isAntichain_iff_forall_le_imp_eq {α : Type*} [Preorder α] {A : Set α} :
    IsAntichain (· ≤ ·) A ↔ ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≤ y → x = y := by
  simp [IsAntichain, Set.Pairwise, ne_eq, Pi.compl_apply, compl_iff_not, not_imp_not]


-- We now show that the definition of a WQO could have been replaced with the previous two theorems.
-- Because `IsWQO` was defined as a class, the first step of the proof is a little different.
theorem WQO_of_no_infinite_antichain_or_descending_chain
    (h_desc : ¬ ∃ (f : ℕ → α), ∀ i j, i < j → f j < f i)
    (h_antichain : ∀ (A : Set α), IsAntichain (· ≤ ·) A → A.Finite) : IsWQO α := by
  refine ⟨?_⟩
  intro f
  by_contra! hcon

  have hf : f.Injective := by
    intro i j hij
    have h1:= imp_not_comm.2 (hcon i j) (le_of_eq hij)
    have h2:= imp_not_comm.2 (hcon j i) (le_of_eq hij.symm)
    simp at h1
    simp at h2
    exact le_antisymm h2 h1

  -- Apply Ramsey's theorem
  obtain ⟨a, ha_mono, ha⟩ := ramseyGraph (fun i j ↦ f j < f i)

  obtain (h | h) := ha
  · -- use `h_desc` to find a contradiction.
    apply h_desc
    use f ∘ a
    simp
    intro i j
    exact h


  have hac : IsAntichain (· ≤ ·) (range (f ∘ a))
  · rw [isAntichain_iff_forall_le_imp_eq]
    -- use `simp` here.
    simp
    intro i j hij
    obtain (h0|h0):= lt_or_le i j
    have := h h0
    have h2:= imp_not_comm.2 (hcon (a i) (a j))
    have h3:= h2 hij
    rw[not_lt] at h3
    have h4:= ha_mono h0
    tauto
    obtain (h0|h0):=h0.eq_or_lt
    rw[h0]
    have h1:= h h0
    by_contra
    apply h1
    apply (hp.lt_iff_le_not_le (f (a i)) (f (a j))).2
    simp[hij]
    have h3:= ha_mono h0
    exact hcon (a j) (a i) h3


  -- But antichains are finite, and the range of `f ∘ a` ought to be infinite!
  apply h_antichain (range (f ∘ a)) at hac
  -- have a look at `Set.infinite_range_of_injective`, and set things up so you can apply it.
  have ha:Function.Injective a:=by
    unfold Function.Injective
    intro i j hij
    obtain (h0|h0):= lt_or_le i j
    apply ha_mono at h0
    have h0:=h0.ne
    contradiction
    obtain (h0|h0):=h0.eq_or_lt
    tauto
    apply ha_mono at h0
    have h0:=h0.ne.symm
    contradiction
  have hinj:=Function.Injective.comp hf ha
  have h0:= Set.infinite_range_of_injective hinj
  contradiction

lemma finite_range_of_not_injective [Infinite α] (f:α→β) (hf : (range f).Finite):
    ¬ (Function.Injective f):=by
  by_contra hcon
  have h0:=Set.infinite_range_of_injective hcon
  tauto

theorem WQO_of_increasing_subsequence
    (h_inc : ∀ (f : ℕ → α), ∃ (g:ℕ→ℕ), (StrictMono g)∧ (∀ i j, i < j → f (g i) ≤  f (g j))) : IsWQO α := by
  refine ⟨?_⟩
  intro f
  obtain⟨ g,hg,hij⟩ :=h_inc f
  use (g 0),(g 1)
  have h01:0<1:=by trivial
  simp[hg (h01)]
  simp[hij 0 1 h01]

theorem increasing_subsequence (α : Type*) [Preorder α] [IsWQO α] :
    ∀ (f : ℕ → α), ∃ (g:ℕ→ℕ), (StrictMono g)∧ (∀ i j, i < j → f (g i) ≤  f (g j)) := by
  intro f
  obtain ⟨a, ha_mono, (ha|ha)⟩ := ramseyGraph (fun i j ↦ f i ≤  f j)
  use a
  obtain ⟨b, hb_mono, (hb|hb)⟩ := ramseyGraph (fun i j ↦ f (a j) <  f (a i))
  have h_desc:=not_exists_descending_chain α
  by_contra!
  apply h_desc
  use f∘ a ∘ b
  simp
  intro i j hij
  exact hb hij
  have hc:IsAntichain (· ≤ ·) (range (f ∘ a∘ b)):=by
    rw [isAntichain_iff_forall_le_imp_eq]
    simp
    intro i j hfij
    obtain (hij|hij):= lt_or_le i j
    have hbij:=hb_mono hij
    apply ha at hbij
    tauto
    obtain (hij|hij):=hij.eq_or_lt
    tauto
    have hbij:=hb_mono hij
    apply ha at hbij
    apply hb at hij
    rw[Preorder.lt_iff_le_not_le,not_and,not_not] at hij
    apply hij at hfij
    tauto
  have hac:= IsAntichain.Finite hc
  have h0:= finite_range_of_not_injective (f∘ a∘ b) hac
  rw[Function.not_injective_iff] at h0
  obtain⟨x,y,hfxy,hxy⟩ :=h0
  obtain(hxy|hyx):=Nat.lt_or_gt.1 hxy
  apply hb_mono at hxy
  have ha0:=ha hxy
  simp at hfxy
  have hfxy:=hfxy.le
  contradiction
  apply hb_mono at hyx
  have ha0:=ha hyx
  simp at hfxy
  have hfyx:=hfxy.symm.le
  contradiction

section product




instance WQO.Prod {α β : Type*} [Preorder α] [Preorder β] [IsWQO α] [IsWQO β] : IsWQO (α × β) := by
  suffices h_inc : ∀ (f : ℕ → α×β ), ∃ (g:ℕ→ℕ), (StrictMono g)∧ (∀ i j, i < j → f (g i) ≤  f (g j))
  exact WQO_of_increasing_subsequence h_inc
  intro f
  set f1:=(fun x=>(f x).1) with hf1
  have hf1:=increasing_subsequence α f1
  obtain ⟨g1,hg1_mono,hg1⟩:=hf1
  set f2:=(fun x=>(f (g1 x)).2) with hf2
  have hf2:=increasing_subsequence β f2
  obtain ⟨g2,hg2_mono,hg2⟩:=hf2
  use g1∘ g2
  simp[StrictMono.comp hg1_mono hg2_mono]
  intro i j hij
  have hgij:=hg2_mono hij
  have h1:=hg1 (g2 i) (g2 j) hgij
  have h2:=hg2 i j hij
  simp[hf1] at h1
  simp[hf2] at h2
  trivial

def fin_restrict {i d:ℕ } (hi:i<d): Fin d where
  val:= i
  isLt:= hi

def fin_prod {α: Type*} [Preorder α]  {d:ℕ} :
    OrderIso (Fin (d + 1) → α) ((Fin (d) → α)× α) where

  toFun:=by
    exact (fun x=> ((fun i=>(x i)),(x d)))
  invFun:=(fun (x,y)=>(fun i=> if hi:i.val<d then (x (fin_restrict hi)) else y))
  left_inv:=by
    unfold Function.LeftInverse
    intro x
    simp
    ext i
    obtain(hi|hi):=lt_or_ge i.val d
    simp[hi]
    trivial
    have := i.isLt
    have hi0:i.val=d:=by linarith
    unfold fin_restrict
    simp[hi]
    have hi1:(d:Fin (d+1))= i:= by
      have hi1:(d:Fin (d+1)).val = i.val:=by
        simp[hi0]
      exact Fin.eq_of_val_eq hi1
    rw[← hi1]
    simp
  right_inv:=by
    unfold Function.RightInverse
    intro x
    simp
    ext i
    simp
    unfold fin_restrict
    simp
    simp
  map_rel_iff':=by
    intro a b
    simp
    constructor
    intro h0
    obtain⟨h1,h2⟩:=h0
    have :∀ i, (a i)≤ (b i):=by
      intro i
      obtain(hi|hi):=lt_or_ge i.val d
      have h2:= h1 (fin_restrict hi)
      simp at h2
      have h3:(fin_restrict hi).castSucc=i:= by
        have h4:(fin_restrict hi).castSucc.val=i.val:= by trivial
        exact Fin.eq_of_val_eq h4
      rw[← h3]
      exact h2
      have hi:i.val =d :=by linarith [i.isLt]
      have h3:(Fin.last d)=i:=by
        unfold Fin.last
        exact Fin.eq_of_val_eq hi.symm
      rw[h3] at h2
      exact h2
    trivial
    intro hab
    constructor
    have :∀ j, (fun (i:Fin d) ↦ a i.castSucc) j ≤ (fun i ↦ b i.castSucc) j:=by
      intro j
      simp
      exact hab j.castSucc
    trivial
    exact hab (Fin.last d)





/- *BONUS*
`n`-tuples of elements in a well-quasi-order form a well-quasi-order.
This is mathematically just an induction using the previous fact, but setting it up correctly
is likely a challenge. -/
instance WQO.tuple {α : Type*} [Preorder α] [IsWQO α] : IsWQO (Fin n → α) := by
  induction n with
  | zero=>
    refine ⟨?_⟩
    intro f
    by_contra! hcon
    simp at hcon
    have:=hcon 1 2
    tauto
  |succ d hd =>
    refine ⟨?_⟩
    by_contra! hcon
    obtain⟨f,hf⟩:=hcon
    have h0:∃ f:ℕ→((Fin (d) → α)× α), ∀ (i j : ℕ), i < j → ¬ (f i) ≤ (f j):=by
      use fin_prod∘f
      simp
      exact hf
    have h1:IsWQO ((Fin (d) → α)× α):=WQO.Prod
    have h2:=h1.forall_seq_exists_le
    obtain⟨g,hg⟩:=h0
    have h3:= h2 g
    obtain⟨ i,j,hij,hgij⟩:=h3
    have h4:= hg i j hij
    contradiction

end product
