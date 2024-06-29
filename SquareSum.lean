import Mathlib.Tactic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Set.Card

/-
Here we are formalizing Zagier's 'one-sentence proof' that each prime congruent to one modulo four
is the sum of two squares. You can find it at

`https://en.wikipedia.org/wiki/Fermat%27s_theorem_on_sums_of_two_squares`

Even informally, there is quite a lot going on in the proof.

One of the challenges with formalizing is that, while it's a proof about natural numbers,
it uses subtraction, and the definition of subtraction in `ℕ` is awkward, since for example
`(4 : ℕ) - (17 : ℕ) = (0 : ℕ)`. There are ways to keep track of this carefully, but we
adopt the alternative approach of working in the integers, where subtraction behaves nicely
and the `ring` tactic works.

Another challenge is that we need to work with cardinality,
which requires thinking about finiteness. Finiteness is more complicated than you might think,
and in fact there are a few different notions of set cardinality.
The most commonly used one is `Finset.card` - a `Finset` is a 'bundled' finite set.
Some of the syntax for finsets is a bit complicated though, so we opt for
We use `Set.ncard`, which looks notationally more like what you would expect.

-/

open Nat

variable {p : Nat}

section Prime

/-
  A few lemmas about primality when working in the integers. What they say is simple enough,
  but the proofs are a bit in the weeds; just read and understand the statements.
-/

lemma Int.eq_one_or_eq_one_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : m = 1 ∨ n = 1 := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  by_contra! hmn
  exact Int.not_prime_of_int_mul (fun hm' ↦ hmn.1 <| by simpa [hm'])
    (fun hn' ↦ hmn.2 <| by simpa [hn']) hmnp hp

lemma Int.eq_or_eq_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : (m = 1 ∧ n = p) ∨ (m = p ∧ n = 1) := by
  obtain (rfl | rfl) := Int.eq_one_or_eq_one_of_mul_prime hm hn hp hmnp
  · simp [← hmnp]
  simp [← hmnp]

lemma Int.square_not_prime (m : ℤ) (p : ℕ) (hmp : m^2 = p) : ¬ p.Prime := by
  have hp' : (m.natAbs)^2 = p := by
    zify; simp [← hmp]
  rw [← hp']
  exact Nat.Prime.not_prime_pow rfl.le

lemma Int.four_mul_not_prime (m : ℤ) (p : ℕ) (hmp : 4*m = p) : ¬ p.Prime := by
  lift m to ℕ using (by linarith)
  norm_cast at hmp
  rw [← hmp, Nat.prime_mul_iff]
  simp [(by decide : ¬ Nat.Prime 4)]


end Prime

section invo

variable {α : Type*}

/-- an involution is a function `f` with `f (f x) = x` for all `x`. -/
def IsInvolution (f : α → α) := ∀ a, f (f a) = a

open Classical in

noncomputable def swap (x:α) (y:α) (f: α → α): α→ α :=
  fun a:α ↦
    if a=x then f y
    else if a=y then f x
    else f a


theorem add_even_iff_even {a b : ℕ } (ha : Even a): Even b ↔ Even (a + b) := by
  constructor
  obtain ⟨m, ha⟩:= ha
  intro hb
  obtain ⟨n, hb⟩:= hb
  simp[ha,hb]
  use (m+n)
  ring
  intro hab
  by_contra hb
  rw[← odd_iff_not_even] at hb
  have h: Odd (a+b):= Even.add_odd ha hb
  rw[odd_iff_not_even] at h
  tauto

lemma setOf_not_fixedPoint_even [Fintype α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x ≠ x}.ncard := by
  -- don't worry about this for now.
  obtain (h|⟨x, hx:f x ≠ x⟩):=Set.eq_empty_or_nonempty  {x | f x ≠ x}
  simp [h]
  let f':= swap x (f x) f
  have hinvo: IsInvolution f':=by
    unfold IsInvolution at hf
    intro a
    have ha: (a=x ∨ a=f x) ∨ (¬ (a=x∨ a=f x)):= by tauto
    obtain ((h|h)|h):=ha
    simp[f',h,swap,hf]
    simp[f',h,swap,hf,hx]
    rw[not_or] at h
    obtain ⟨h1,h2⟩ :=h
    have h3: f a ≠ f x:= by
      by_contra h
      have h0: f (f a) = f (f x) := by rw[h]
      simp[hf] at h0
      tauto
    have h4: f a ≠ x:= by
      by_contra h
      have h0: f (f a) = f x := by rw[h]
      simp[hf] at h0
      tauto
    simp[f',h1,h2,h3,h4,swap,hf,hx]
  have hf_two: {a|f' a≠ a}.ncard+2={a|f a ≠ a}.ncard := by
    unfold IsInvolution at hf
    have h: {a|f a≠ a}= insert (f x) (insert x {a|f' a ≠ a}):= by
      ext b
      constructor
      intro hb
      unfold insert
      simp
      simp at hb
      have hbb: (b=x ∨ b=f x) ∨ (¬ (b=x∨ b=f x)):= by tauto
      obtain ((h|h)|h):=hbb
      tauto
      tauto
      right
      right
      rw[not_or] at h
      simp[f',swap,h]
      tauto
      intro hb
      unfold insert at hb
      simp at hb
      simp
      obtain (h|h|h):=hb
      simp[h,hf]
      tauto
      rw[h]
      tauto
      have hbb: (b=x ∨ b=f x) ∨ (¬ (b=x∨ b=f x)):= by tauto
      obtain ((hb|hb)|hb):=hbb
      rw[hb];tauto;simp[hb,hf];tauto;
      rw[not_or] at hb
      simp[f',swap,hb] at h
      tauto
    have h1: x∉ {a|f' a≠ a}:= by
      simp[f',swap,hf]
    have h2: f x ∉ insert x {a|f' a ≠ a}:= by
      simp[Set.insert,hx,f',swap]
    rw[h]
    have h3 :=Set.ncard_insert_of_not_mem h2
    rw[h3]
    have h4 :=Set.ncard_insert_of_not_mem h1
    rw[h4]
  have : {a | f' a ≠ a}.ncard < {a | f a ≠ a}.ncard:= by linarith
  have hind:= setOf_not_fixedPoint_even f' hinvo
  rw[← hf_two]
  rw[← add_even_iff_even hind]
  trivial
termination_by  {x | f x ≠ x}.ncard



lemma even_iff_ncard_fixedPoint_even [Finite α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x = x}.ncard ↔ Even (Nat.card α) := by
  have hafin := Fintype.ofFinite α
  have hnfix: Even {x | f x ≠ x}.ncard := setOf_not_fixedPoint_even f hf
  have huniv: Even {x | f x = x}.ncard ↔ Even {x|f x≠ x ∨ f x = x}.ncard := by
    rw[Set.setOf_or]
    rw[Set.ncard_union_eq]
    exact add_even_iff_even hnfix
    intro S hS1 hS2
    intro x hx
    have h1:= hS1 hx
    have h2:= hS2 hx
    tauto
  rw[huniv]
  rw[← Set.ncard_univ]
  have htaut (x:α ):  (f x ≠ x) ∨ (f x = x):= by
    cases eq_or_ne (f x) x
    tauto
    tauto
  have h:Set.univ = {x|f x≠ x ∨ f x = x}:= by
    ext x
    unfold Set.univ
    simp[htaut]
  simp[h]
end invo

section Triple

/-
The type of triples of nonnegative integers `x,y,z` with `x² + 4yz = p`.
These are what make Zagier's proof work. They are the
-/
@[ext] structure Triple (p : ℕ) where
  (x : ℤ)
  (hx : 0 ≤ x)
  (y : ℤ)
  (hy : 0 ≤ y)
  (z : ℤ)
  (hz : 0 ≤ z)
  (h_eq : x^2 + 4 * y * z = p)

/-- There are only finitely many such triples for a given `p`. Don't worry about the proof for now.-/
--instance {p : ℕ} (hp : p.Prime) : Finite (Triple p) := sorry

def Triple.xpos (t : Triple p) (hp : p.Prime) : 0 < t.x := by
  refine t.hx.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  simp only [← h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    mul_assoc] at hmul
  exact Int.four_mul_not_prime _ _ hmul hp

def Triple.ypos (t : Triple p) (hp : p.Prime) : 0 < t.y := by
  refine t.hy.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  rw[← h0] at hmul
  simp at hmul
  exact Int.square_not_prime _ _ hmul hp

/-- Define the obvious involution which swaps the values of `y` and `z`. -/
def flipInv (p : ℕ) (t : Triple p) : Triple p where
  x:=t.x
  hx:= t.hx
  y:=t.z
  hy:= t.hz
  z:=t.y
  hz:=t.hy
  h_eq := by
    simp_rw [← t.h_eq]
    ring

def Triple.zpos (t : Triple p) (hp : p.Prime) : 0 < t.z := by
  exact (flipInv p t).ypos hp



/-- Show it is an involution. -/
theorem flipInv_involution (p : ℕ) : IsInvolution (flipInv p) := by
  unfold IsInvolution
  intro a
  ext
  trivial
  trivial
  trivial

/-
Before defining Zagier's weird involution, we define predicates corresponding to the case split.
This allows us to separate the computation from the logic a bit more easily.
-/

def TypeOne (t : Triple p) := t.x ≤ t.y - t.z

def TypeTwo (t : Triple p) := t.y - t.z < t.x ∧ t.x < 2 * t.y

def TypeThree (t : Triple p) := 2 * t.y ≤ t.x

lemma typeThree_of_not_typeOne_typeTwo (t : Triple p) (h1 : ¬ TypeOne t) (h2 : ¬ TypeTwo t) :
    TypeThree t := by
  rw [TypeOne, not_le] at h1
  rw [TypeTwo, not_and, not_lt] at h2
  unfold TypeThree
  exact h2 h1

lemma TypeTwo.not_typeOne {t : Triple p} (ht : TypeTwo t) : ¬ TypeOne t :=
  not_le.2 ht.1


lemma TypeThree.not_typeTwo {t : Triple p} (ht : TypeThree t) : ¬ TypeTwo t := by
  rw[TypeTwo,not_and,not_lt]
  tauto


lemma TypeThree.not_typeOne {t : Triple p} (ht : TypeThree t) (hp : p.Prime) : ¬ TypeOne t := by
  unfold TypeOne
  unfold TypeThree at ht
  by_contra h1
  have h2:= le_trans ht h1
  rw[two_mul] at h2
  rw[← le_add_neg_iff_add_le] at h2
  rw[add_comm,← add_sub_assoc] at h2
  rw[neg_add_self] at h2
  rw[zero_sub] at h2
  have hz: -t.z≤ 0 := by
    rw[neg_le]
    exact t.hz
  apply le_trans h2 at hz
  have hy:=t.ypos hp
  have hy0: t.y=0:= Int.eq_iff_le_and_ge.2 ⟨hz,hy.le⟩
  have hy1:= hy.ne
  tauto


@[simps] def A1 (t : Triple p) (ht : TypeOne t) : Triple p where
  x := t.x + 2 * t.z
  hx := by linarith [t.hx, t.hz]
  y := t.z
  hy := t.hz
  z := t.y - t.x - t.z
  hz := by unfold TypeOne at ht; linarith
  h_eq := by simp_rw [← t.h_eq]; ring

lemma A1_typeThree {t : Triple p} (ht : TypeOne t) : TypeThree (A1 t ht) := by
  unfold TypeThree
  unfold TypeOne at ht
  simp [A1, t.hx]

@[simps] def A2 (t : Triple p) (ht : TypeTwo t) : Triple p where
  x := 2*t.y-t.x
  hx := by linarith [ht.2]
  y := t.y
  hy := t.hy
  z := t.x-t.y+t.z
  hz := by linarith [ht.1]
  h_eq := by simp_rw [← t.h_eq]; ring

lemma A2_typeTwo (hp : p.Prime) {t : Triple p} (ht : TypeTwo t) : TypeTwo (A2 t ht) := by
  unfold TypeTwo
  unfold TypeTwo at ht
  simp [A2,t.xpos hp]
  linarith [ht.1,ht.2,t.zpos hp]


@[simps] def A3 (t : Triple p) (ht : TypeThree t) : Triple p where
  x := t.x-2*t.y
  hx := by unfold TypeThree at ht;simp [ht]
  y := t.x-t.y+t.z
  hy := by unfold TypeThree at ht; linarith [ht,t.hz,t.hx]
  z := t.y
  hz := t.hy
  h_eq := by simp_rw [← t.h_eq]; ring

lemma A3_typeOne {t : Triple p} (ht : TypeThree t) : TypeOne (A3 t ht) := by
  unfold TypeOne
  unfold TypeThree at ht
  simp [A3]
  linarith[t.hz]

/- The actual definition of `otherInv`. Its value at `t` is `A_i t`, where `t` has type `i`. -/
open Classical in
noncomputable def otherInv (p : ℕ) (t : Triple p) : Triple p :=
  if h1 : TypeOne t then A1 t h1
  else if h2 : TypeTwo t then A2 t h2
  else A3 t (typeThree_of_not_typeOne_typeTwo t h1 h2)

lemma otherInv_apply_typeOne {t : Triple p} (h1 : TypeOne t) : otherInv p t = A1 t h1 := by
  simp [otherInv, h1]

lemma otherInv_apply_typeTwo {t : Triple p} (h2 : TypeTwo t) : otherInv p t = A2 t h2 := by
  simp [otherInv, h2.not_typeOne, h2]

lemma otherInv_apply_typeThree (hp : p.Prime) {t : Triple p} (h3 : TypeThree t) :
    otherInv p t = A3 t h3 := by
  simp [otherInv, h3.not_typeOne hp, h3.not_typeTwo]

lemma types (t : Triple p): TypeOne t ∨ TypeTwo t ∨ TypeThree t:= by
  by_contra h
  rw[not_or,not_or] at h
  have ht :TypeThree t:= (typeThree_of_not_typeOne_typeTwo t h.1 h.2.1)
  tauto


lemma otherInv_inv (hp : p.Prime) : IsInvolution (otherInv p) := by
  unfold IsInvolution
  intro t
  obtain(h|h|h):= types t
  simp[otherInv_apply_typeOne h]
  have h3: TypeThree (A1 t h) := A1_typeThree h
  simp[otherInv_apply_typeThree hp h3]
  unfold A1
  unfold A3
  ext
  simp
  simp
  ring
  simp
  simp[otherInv_apply_typeTwo h]
  have h2: TypeTwo (A2 t h) := A2_typeTwo hp h
  simp[otherInv_apply_typeTwo h2]
  unfold A2
  ext
  simp
  simp
  ring
  simp[otherInv_apply_typeThree hp h]
  have h1: TypeOne (A3 t h) := A3_typeOne h
  simp[otherInv_apply_typeOne h1]
  unfold A1
  unfold A3
  ext
  simp
  simp
  ring







def otherInvFixedPt {k : ℕ} (hpk : p = 4 * k+1) : Triple p where
  x := 1
  hx := zero_le_one
  y := 1
  hy := zero_le_one
  z := k
  hz := by simp
  h_eq := by linarith

lemma otherInvFixedPt.typeTwo (hp : p.Prime) (hpk : p = 4 * k+1) :
    TypeTwo (otherInvFixedPt hpk) := by
  unfold TypeTwo
  unfold otherInvFixedPt
  simp
  by_contra h
  rw[not_lt] at h
  rw[Nat.le_zero] at h
  rw[h] at hpk
  rw[mul_zero,zero_add] at hpk
  have h0:= (Nat.prime_def_lt.1 hp).1
  linarith

lemma otherInv_fixed_iff {k : ℕ} (hp : p.Prime) (hpk : p = 4 * k+1) (t : Triple p) :
    otherInv p t = t ↔ t = otherInvFixedPt hpk := by
  constructor
  intro ht
  obtain(h|h|h):= types t
  simp[otherInv_apply_typeOne h] at ht
  have hx:(A1 t h).x=t.x:=by tauto
  simp[A1] at hx
  have hz:=(t.zpos hp)
  by_contra
  linarith
  simp[otherInv_apply_typeTwo h] at ht
  have hz:(A2 t h).z=t.z:=by tauto
  simp[A2] at hz
  have heq:=t.h_eq
  rw[sub_eq_zero] at hz
  rw[hz] at heq
  have hpp: p= t.y*(4*t.z+t.y):= by rw[← heq];ring
  have hy:t.y=1:= by
    by_contra hy
    have hz0:=t.zpos hp
    have hy0:=t.ypos hp
    have hy: t.y.natAbs ≠ 1:=by
      by_contra hyy
      have hyyy:=Int.natAbs_eq t.y
      rw[hyy] at hyyy
      simp at hyyy
      obtain (h|h):=hyyy
      tauto
      linarith
    have hne:4*t.z+t.y≠ 1 :=by linarith
    have hne: (4*t.z+t.y).natAbs ≠ 1:=by
      by_contra h
      have hh:=Int.natAbs_eq (4*t.z+t.y)
      rw[h] at hh
      simp at hh
      obtain (h|h):=hh
      tauto
      linarith
    have hpp:=Int.not_prime_of_int_mul hy hne hpp.symm
    tauto
  ext
  simp[otherInvFixedPt]
  simp[hz,hy]
  simp[otherInvFixedPt]
  simp[hy]
  simp[otherInvFixedPt]
  rw[hy] at hpp
  simp at hpp
  linarith
  simp[otherInv_apply_typeThree hp h] at ht
  have hx:(A3 t h).x=t.x:=by tauto
  simp[A3] at hx
  have hy:=(t.ypos hp)
  by_contra
  linarith
  intro h
  rw[h]
  simp[otherInv_apply_typeTwo (otherInvFixedPt.typeTwo hp hpk)]
  simp[otherInvFixedPt,A2]

def Triple.xle (t : Triple p) (hp : p.Prime) : t.x < p := by
  have hmul := t.h_eq
  by_contra hxx
  rw[not_lt] at hxx
  have hx:=t.xpos hp
  have hy:=t.ypos hp
  have hz:=t.zpos hp
  rw[← Int.add_one_le_iff] at hx
  rw[← Int.add_one_le_iff] at hy
  rw[← Int.add_one_le_iff] at hz
  simp at hx;simp at hy;simp at hz;
  rw[← hmul] at hxx
  have h0:t.x≤ t.x^2 := by
    have :(0:ℤ)≤ 1:= by trivial
    have hxx:t.x≤ t.x:= by trivial
    have :=Int.mul_le_mul hx hxx t.hx t.hx
    linarith
  have h1:1≤  t.y*t.z := by
    have h00:(0:ℤ)≤ 0+1:=by trivial
    have hyy:0≤ t.y:= by linarith
    exact Int.mul_le_mul hy hz h00 hyy
  have :4≤ 4*t.y*t.z := by linarith
  have :t.x+2≤ t.x^2+4*t.y*t.z+1 := by linarith
  linarith

def Triple.yle (t : Triple p) (hp : p.Prime) : t.y < p := by
  have hmul := t.h_eq
  by_contra hxx
  rw[not_lt] at hxx
  have hx:=t.xpos hp
  have hy:=t.hy
  have hz:=t.zpos hp
  rw[← Int.add_one_le_iff] at hx
  rw[← Int.add_one_le_iff] at hz
  simp at hx;simp at hz;
  rw[← hmul] at hxx
  have h0:t.y≤ 4*t.y*t.z := by
    have h01:(0:ℤ)≤ 1:= by trivial
    have hyy:t.y≤ t.y:= by trivial
    have :=Int.mul_le_mul hyy hz h01 hy
    linarith
  have h1:1≤ t.x^2 := by
    have h01:(0:ℤ)≤ 1:= by trivial
    have :=Int.mul_le_mul hx hx h01 t.hx
    linarith
  have :t.y+1≤ t.x^2+4*t.y*t.z+1 := by linarith
  linarith




def Triple.zle (t : Triple p) (hp : p.Prime) : t.z < p := by
  exact (flipInv p t).yle hp

def g  {p : ℕ} (hp:p.Prime) (t : Triple p) : Fin (3*p*p*p+1) where
  val:=  t.x.natAbs*(p^2)+ t.y.natAbs*p +t.z.natAbs
  isLt:= by
    have hx:=t.xpos hp
    have :=t.ypos hp
    have :=t.zpos hp
    have hx1:=t.xle hp
    have hy1:=t.yle hp
    have hz1:=t.zle hp
    have hx2:t.x.natAbs≤ p := by
      have h0:t.x.natAbs≤ (p:ℤ).natAbs:= by
        rw[Int.natAbs_le_iff_sq_le]
        have hp:0≤ (p:ℤ):= by linarith
        have hxx:0≤ t.x+1:= by linarith[t.hx]
        have:= Int.mul_le_mul hx1 hx1 hxx hp
        linarith
      simp at h0
      tauto
    have hx3: t.x.natAbs *p ^2≤ p*p^2:= by
      have :p^3=p*p^2:= by ring
      have h1:=Nat.Prime.pos hp
      have h2:= (mul_lt_mul_iff_of_pos_left h1).2 h1
      rw[← sq] at h2
      simp at h2
      have h3:=(mul_le_mul_right h2).2 hx2
      simp at h3
      trivial
    have hy2:t.y.natAbs≤ p := by
      have h0:t.y.natAbs≤ (p:ℤ).natAbs:= by
        rw[Int.natAbs_le_iff_sq_le]
        have hp:0≤ (p:ℤ):= by linarith
        have hyy:0≤ t.y+1:= by linarith[t.hy]
        have:= Int.mul_le_mul hy1 hy1 hyy hp
        linarith
      simp at h0
      tauto
    have hy3: t.y.natAbs *p≤ p*p:= by
      have h1:=Nat.Prime.pos hp
      exact (mul_le_mul_right h1).2 hy2

    have hz2:t.z.natAbs≤ p := by
      have h0:t.z.natAbs≤ (p:ℤ).natAbs:= by
        rw[Int.natAbs_le_iff_sq_le]
        have hp:0≤ (p:ℤ):= by linarith
        have hzz:0≤ t.z+1:= by linarith[t.hz]
        have:= Int.mul_le_mul hz1 hz1 hzz hp
        linarith
      simp at h0
      tauto
    have : t.x.natAbs * p ^ 2 + t.y.natAbs * p + t.z.natAbs≤ p*p^2+p*p+p:= by linarith
    have h20:2≠ 0  :=by trivial
    have h1:p ≤ p^2:=  Nat.le_self_pow h20 p
    have :1≤ p:= by
      have:=Nat.Prime.two_le hp
      linarith
    have :1≤ p^2 :=by linarith
    have h3: p ^ 2 + p  + 1≤ 3*p^2 := by linarith

    have h4:= (mul_le_mul_left (Nat.Prime.pos hp)).2 h3
    linarith



lemma ineq {a b :ℤ} (hab:a<b) (hb:0≤ b) (ha:0<a+1): a.natAbs< b.natAbs :=by
  rw[Int.natAbs_lt_iff_sq_lt]
  have:= Int.mul_lt_mul hab hab ha hb
  linarith

lemma abseq {a b :ℤ} (ha:0< a) (hb:0< b) (h:a.natAbs=b.natAbs): a=b :=by
  rw[Int.natAbs_eq_iff] at h
  obtain (h|h):=h
  symm at h
  simp at h
  rw[abs_eq] at h
  obtain (h|h):=h
  tauto
  linarith
  exact ha.le
  linarith





lemma exists_fixedPoint (hp : p.Prime) (hpk : p = 4 * k + 1) (f : Triple p → Triple p)
    (hf : IsInvolution f) : ∃ t, f t = t := by
  have : Finite (Triple p) := by
    have hb:Finite (Fin (3*p*p*p+1)) := Finite.of_fintype (Fin (3*p*p*p+1))
    have H:Function.Injective (g hp):= by
      unfold Function.Injective
      intro t1 t2 hf
      simp[g ] at hf
      have h0:(t1.x.natAbs * p ^ 2 + t1.y.natAbs * p + t1.z.natAbs)% p = (t2.x.natAbs * p ^ 2 + t2.y.natAbs * p + t2.z.natAbs)%p := by
        rw[hf]
      simp [sq,add_mod] at h0
      rw[← mul_assoc] at h0
      rw[← mul_assoc] at h0
      simp at h0
      have hz1:t1.z.natAbs< p := by
        have hpp:0≤ (p:ℤ):= by linarith
        have hzz:0< t1.z+1:= by linarith[t1.hz]
        have h0:=ineq (t1.zle hp) hpp hzz
        simp at h0
        tauto
      have hz1:t1.z.natAbs % p=t1.z.natAbs:= Nat.mod_eq_of_lt hz1
      have hz2:t2.z.natAbs< p := by
        have hpp:0≤ (p:ℤ):= by linarith
        have hzz:0< t2.z+1:= by linarith[t2.hz]
        have h0:=ineq (t2.zle hp) hpp hzz
        simp at h0
        tauto
      have hz2:t2.z.natAbs % p=t2.z.natAbs:= Nat.mod_eq_of_lt hz2
      have h1:t1.z = t2.z:= by
        rw[hz1,hz2] at h0
        apply abseq (t1.zpos hp) (t2.zpos hp) at h0
        tauto
      rw[h1] at hf
      simp at hf
      have h0:(t1.x.natAbs * p ^ 2 + t1.y.natAbs * p )% (p^2) = (t2.x.natAbs * p ^ 2 + t2.y.natAbs * p )%(p^2) := by
        rw[hf]
      simp [sq,add_mod] at h0
      have hy1:t1.y.natAbs*p< p*p := by
        have hpp:0≤ (p:ℤ):= by linarith
        have hyy:0< t1.y+1:= by linarith[t1.hy]
        have h0:=ineq (t1.yle hp) hpp hyy
        simp at h0
        exact (mul_lt_mul_right (Nat.Prime.pos hp)).2 h0
      have hy2:t2.y.natAbs*p< p*p := by
        have hpp:0≤ (p:ℤ):= by linarith
        have hyy:0< t2.y+1:= by linarith[t2.hy]
        have h0:=ineq (t2.yle hp) hpp hyy
        simp at h0
        exact (mul_lt_mul_right (Nat.Prime.pos hp)).2 h0
      have hy1:t1.y.natAbs*p % (p*p)=t1.y.natAbs*p:= Nat.mod_eq_of_lt hy1
      have hy2:t2.y.natAbs*p % (p*p)=t2.y.natAbs*p:= Nat.mod_eq_of_lt hy2
      have h2:t1.y = t2.y:= by
        rw[hy1,hy2] at h0
        have h0:=Nat.mul_right_cancel (Nat.Prime.pos hp) h0
        apply abseq (t1.ypos hp) (t2.ypos hp) at h0
        tauto
      rw[h2] at hf
      simp at hf
      obtain(hf|hf):=hf
      have h3:t1.x = t2.x:=abseq (t1.xpos hp) (t2.xpos hp) hf
      ext
      tauto
      tauto
      tauto
      have := (Nat.Prime.pos hp).ne
      tauto
    exact Finite.of_injective (g hp) H









  have hnevf: ¬ Even {t|otherInv p t = t}.ncard:= by
    have hfix:{t|otherInv p t = t}={otherInvFixedPt hpk}:= by
      simp[otherInv_fixed_iff hp hpk]
    rw[hfix]
    rw[Set.ncard_singleton]
    tauto
  have hnev:¬ Even (Nat.card (Triple p)):= by
    have h:=(even_iff_ncard_fixedPoint_even (otherInv p) (otherInv_inv hp)).2
    rw[← not_imp_not] at h
    tauto
  have h:=(even_iff_ncard_fixedPoint_even f hf).1
  rw[← not_imp_not] at h
  apply h at hnev
  by_contra hnele
  have hemp:{t|f t = t}=∅  := by
    by_contra hne
    rw[Set.eq_empty_iff_forall_not_mem] at hne
    rw[not_forall] at hne
    simp at hne
    tauto

  have h0:{x | f x = x}.ncard= 0 := by
    rw[hemp]
    exact Set.ncard_empty (Triple p)
  rw[h0] at hnev
  tauto

lemma exists_sum_squares (hp : p.Prime) (hpk : p = 4 * k + 1) : ∃ (a b : ℤ), p = a^2 + b^2 := by
  have h0:= exists_fixedPoint hp hpk (flipInv p) (flipInv_involution p)
  obtain ⟨t,ht⟩  := h0
  have h1:= t.h_eq
  have h2:t.y=t.z:=by
   have h3:t.y= (flipInv p t).y:=by tauto
   simp[flipInv] at h3
   tauto
  rw[h2] at h1
  use t.x
  use 2*t.z
  rw[← h1]
  ring


end Triple
