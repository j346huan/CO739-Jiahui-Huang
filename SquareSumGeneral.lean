import CO739.Exercises.SquareSum
import Mathlib.Data.ZMod.Basic

/-
Continuing from the square sum theorem for prime numbers, we prove Fermat's criteria for when a natural number can be written as a square sum.

Theorem: A natural number is a sum of squares if and only if its prime factorization contains an even number of primes of form 4k+3.
-/


open Nat


def IsSumSquare (n:ℕ): Prop:= ∃ x y, n=x^2+y^2

/-
First recall the theorem for the prime case.
-/

theorem exists_sum_squares_prime {p:ℕ} (hp : p.Prime) (hpk :∃ k, p = 4 * k + 1) :IsSumSquare p := by
  obtain⟨ k,hpk⟩ :=hpk
  obtain⟨ a,b,hab⟩:= exists_sum_squares hp hpk
  use a.natAbs,b.natAbs
  zify
  rw[sq_abs,sq_abs]
  tauto


/-
Lemma: If p does not divide n, then n is invertible in ℤ_p.
-/


lemma inverse_mod_prime (hp : p.Prime) (hpn: ¬ p∣ n):
  ∃ m, m*(n:ZMod p) = 1 := by
  use (n:ZMod p)⁻¹
  rw[mul_comm]
  rw[ZMod.mul_inv_eq_gcd]
  have h0:= (hp.coprime_iff_not_dvd).2  hpn
  apply Nat.coprime_iff_gcd_eq_one.1 at h0
  unfold Nat.gcd at h0
  simp[hp.ne_zero] at h0
  simp[h0]


/-
Lemma: If a prime is 3 mod 4 and divides a sum of square, then it divides one of the summands.
-/

lemma dvd_summand_three_mod_four (hp : p.Prime) (hpk :p = 4 * k + 3) (hn:n=x^2+y^2) :
  (p ∣  n) →  p∣ x :=by
  intro hpn
  by_contra hpx
  have hz:= inverse_mod_prime hp hpx
  obtain ⟨ z,hz⟩ :=hz
  have h0:(n:ZMod p)=((x^2+y^2):ZMod p):= by
    rw[hn]
    simp
  have h1:=(ZMod.natCast_zmod_eq_zero_iff_dvd n p).2 hpn
  rw[h1] at h0
  have h2:0=z^2*(x^2+y^2):=by
    simp[← h0]
  rw[mul_add,sq,sq,mul_assoc,← mul_assoc z x x,hz,one_mul,hz] at h2
  have h3: 0=1+(z*y)^2:=by
    rw[h2]
    ring
  have h4: -1+0=-1+1+(z*y)^2:=by
    simp[h3]
  simp at h4
  let hpf: Fact p.Prime:= fact_iff.2 hp
  have h5:IsSquare (-1 :ZMod p) := by
    unfold IsSquare
    use z*y
    rw[h4]
    ring
  rw[ZMod.exists_sq_eq_neg_one_iff] at h5
  have h6:p%4=3:=by
    rw[hpk]
    rw[add_mod]
    simp
  contradiction

/-
Proposition: If n=x^2+y^2, then any prime factors of n that is 3 mod 4 must be of multiplicity at least 2.
-/

lemma dvd_sq_three_mod_four (hp : p.Prime) (hpk :p = 4 * k + 3) (hn:IsSumSquare n) :
  (p ∣  n) →  (p^2 ∣  n):= by
  intro hpn
  unfold IsSumSquare at hn
  obtain ⟨ x,y,hn⟩ :=hn
  have hpx:=dvd_summand_three_mod_four hp hpk hn hpn
  have hpy:p∣ y:= by
    have hn: n=y^2+x^2:=by
      rw[hn]
      rw[add_comm]
    exact dvd_summand_three_mod_four hp hpk hn hpn
  have hpx2:=pow_dvd_pow_of_dvd hpx 2
  have hpy2:=pow_dvd_pow_of_dvd hpy 2
  have hpn2:=dvd_add hpx2 hpy2
  rw[hn]
  exact hpn2


/-
lemma: If n is a sum of squares and m is a sum of squares then so is n*m.
-/
lemma sum_sq_mul {n m:ℕ}(hn:IsSumSquare n) (hm:IsSumSquare m) :
  IsSumSquare (n*m) := by
  unfold IsSumSquare at hn hm ⊢
  obtain ⟨a,b,hn⟩ :=hn
  obtain ⟨c,d,hm⟩ :=hm
  zify at hn hm ⊢
  have h0: ∃ x y :ℤ, 0≤ x∧ 0≤ y∧ n*m=x^2+y^2:=by
    use |a*c-b*d|
    use |a*d+b*c|
    rw[hm,hn]
    rw[sq_abs,sq_abs]
    refine ⟨by simp,by simp,by ring⟩
  obtain ⟨x,y,_?,_?,h0⟩:=h0
  use x.natAbs,y.natAbs
  simp[Int.natCast_natAbs,h0]

/-
lemma: If n is a square and m is a sum of squares then n*m is a sum of squares.
-/
lemma sum_sq_mul_sq (hn:IsSquare n) (hm:IsSumSquare m) :
  IsSumSquare (n*m) := by
  unfold IsSquare at hn
  unfold IsSumSquare at hm ⊢
  obtain ⟨a,hn⟩ :=hn
  obtain ⟨c,d,hm⟩ :=hm
  use a*c, a*d
  rw[hn,hm]
  linarith

/-
lemma: If n is a sum of squares then n^m is a sum of squares.
-/
lemma sum_sq_pow (m:ℕ) (hn:IsSumSquare n) :
  IsSumSquare (n^m) := by
  induction m with
  | zero=>
    simp
    use 1,0
    simp
  | succ d hd=>
    rw[pow_add]
    simp
    exact sum_sq_mul hd hn


/-
Proposition: A product of sum of squares together with some squares is a sum of squares.
-/

def Finsupp.fun_div_two (f:ℕ→₀ℕ) (hf:∀m∈f.support, Even (f m)):ℕ→₀ℕ where
  support:=f.support
  toFun:ℕ → ℕ:=(fun m=>(f m)/2)
  mem_support_toFun:= by
    intro a
    constructor
    intro ha
    simp
    by_contra ha2
    have hfa:=hf a ha
    unfold Even at hfa
    simp at ha
    obtain ⟨r,hr⟩:= hfa
    rw[hr] at ha2
    rw[← mul_two] at ha2
    simp at ha2
    rw[ha2] at hr
    contradiction
    simp
    intro ha2
    by_contra ha
    rw[ha] at ha2
    contradiction

def Finsupp.reduce (f:ℕ→₀ℕ) (m:ℕ):ℕ→₀ℕ where
  support:=f.support \ {m}
  toFun:ℕ → ℕ:=(fun x=>
    if x≠ m then f x
    else 0
    )
  mem_support_toFun:= by
    intro a
    constructor
    intro ha
    simp
    simp at ha
    simp[ha]
    intro ha
    simp at ha
    simp[ha]

lemma reduce_supp (f:ℕ→₀ℕ) (m:ℕ):
  (f.reduce m).support = f.support\ {m}:= by
  unfold Finsupp.reduce
  simp

lemma reduce_fun (f:ℕ→₀ℕ) (m:ℕ):
  (f.reduce m) x =(fun x=>if x≠ m then f x else 0) x:= by
  unfold Finsupp.reduce
  simp

lemma sum_sq_prod {n:ℕ}(f:ℕ→₀ℕ) (hf: ∀m∈ f.support, (Even (f m)) ∨ IsSumSquare m) (hn:n=(f.prod (fun (x y:ℕ )=>x^y))):
  IsSumSquare n:=by
  unfold Finsupp.prod at hn
  simp at hn
  obtain (h0|⟨m, hm⟩):=Set.eq_empty_or_nonempty {m∈f.support | IsSumSquare m}
  have h1: ∀ m∈ f.support, Even (f m):=by
    intro m hm
    have h2:=hf m hm
    by_contra h3
    simp [h3] at h2
    have h4:m∈ {m | m ∈ f.support ∧ IsSumSquare m}:=by
      exact ⟨hm,h2⟩
    rw[h0]at h4
    contradiction
  unfold IsSumSquare
  use ((f.fun_div_two h1).prod (fun (x y:ℕ )=>x^y)),0
  simp
  rw[sq,← Finsupp.prod_mul]
  unfold Finsupp.prod
  unfold Finsupp.fun_div_two
  simp
  have h2:(fun x ↦ x ^ (f x / 2) * x ^ (f x / 2))=(fun x ↦ x ^ (f x)):=by
    ext x
    rw[← sq]
    rw[← pow_mul]
    obtain (h2|h3):= eq_or_ne (f x) 0
    simp[h2]
    have h4:x∈ f.support := by
      simp[h3]
    have h5:=h1 x h4
    unfold Even at h5
    obtain⟨r,hx⟩:=h5
    rw[← mul_two] at hx
    simp[hx]
  rw[h2]
  exact hn
  set f':= f.reduce m
  have hf0: {m∈f'.support | IsSumSquare m}.ncard+1={m∈f.support | IsSumSquare m}.ncard:=by
    have h0:{m | m ∈ f'.support ∧ IsSumSquare m}.insert m = {m∈f.support | IsSumSquare m}:=by
      unfold Set.insert
      ext a
      constructor
      intro ha
      obtain(ha|ha):=ha
      rw[ha]
      simp at hm
      simp[hm]
      have ha0:a∈ f.support:=by
        rw[reduce_supp] at ha
        have ha1:=ha.1
        simp at ha1
        simp[ha1]
      simp at ha ha0
      simp[ha,ha0]
      intro ha
      simp
      simp at ha
      simp[ha]
      obtain(ha1|ha1):=eq_or_ne a m
      left
      exact ha1
      right
      rw[reduce_fun]
      simp
      simp[ha,ha1]
    have hm0:m∉{m | m ∈ f'.support ∧ IsSumSquare m}:= by
      by_contra hm1
      rw[reduce_supp] at hm1
      have hm2:=hm1.1
      apply Finset.mem_sdiff.1 at hm2
      have hm3:=hm2.2
      apply hm3
      simp
    have hfin:{m | m ∈ f'.support ∧ IsSumSquare m}.Finite:=by
      have h1:{m | m ∈ f'.support ∧ IsSumSquare m}⊆f'.support:= by
        intro m hm1
        have hm2:=hm1.1
        exact hm2
      have h2:=(f'.support).finite_toSet
      exact Set.Finite.subset h2 h1
    have h1:= (Set.ncard_insert_of_not_mem hm0 hfin).symm
    unfold Set.insert at h0
    unfold insert at h1
    unfold Set.instInsert at h1
    simp only [Set.insert] at h1
    rw[h0] at h1
    exact h1
  have hf': ∀m∈ f'.support, (Even (f' m)) ∨ IsSumSquare m:=by
    rw[reduce_supp]
    intro x hx
    rw[Finset.mem_sdiff] at hx
    have ⟨h1,h2⟩:=hx
    rw[reduce_fun]
    simp at h2
    simp[h2]
    exact hf x h1
  have : {x|¬ (f.reduce m) x=0 ∧  IsSumSquare x}.ncard<{x|¬ f x =0 ∧ IsSumSquare x}.ncard:=by
    simp at hf0
    linarith
  have hind:= sum_sq_prod f' hf' (Eq.refl (f'.prod (fun (x y:ℕ )=>x^y)))
  have hunion:f'.support ∪ {m}= f.support:=by
    rw[reduce_supp]
    simp at hm
    simp[hm]
  have hdisj: Disjoint f'.support {m} := by
    have h1:m∉f'.support := by
      by_contra h2
      rw[reduce_supp] at h2
      rw[Finset.mem_sdiff] at h2
      have h3:=h2.2
      simp at h3
    exact Finset.disjoint_singleton_right.2 h1
  have hprod:(f'.support ∪ {m}).prod (fun (x:ℕ )=>x^(f x)) =  ((f'.support.prod (fun (x:ℕ )=>x^(f x))):ℕ )*(({m}:Finset ℕ ).prod (fun (x:ℕ )=>x^(f x)):ℕ) :=Finset.prod_union hdisj
  rw[hunion] at hprod
  unfold Finsupp.prod at hind
  simp at hind
  rw[Finset.prod_singleton] at hprod
  have hpow:=sum_sq_pow (f m) hm.2
  rw[hn,hprod]
  have hst:∀ (i : ℕ), (i∈ f'.support)↔ (((Equiv.refl ℕ) i) ∈f'.support):=by
    simp
  have hfg: ∀ i∈ f'.support, i^(f' i) = i^(f ((Equiv.refl ℕ) i)):=by
    intro i hi
    rw[reduce_supp] at hi
    simp
    rw[reduce_fun]
    simp at hi
    simp[hi.2]
  have hf':(f'.support.prod fun x ↦ x ^ f' x)= (f'.support.prod fun x ↦ x ^ f x):= Finset.prod_equiv (Equiv.refl ℕ) hst hfg
  rw[← hf']
  exact sum_sq_mul hind hpow
termination_by  {x∈f.support | IsSumSquare x}.ncard



/-
Theorem: A natural number is a sum of squares if and only if its prime factorization contains an even number of primes of form 4k+3.
-/


/-
Begin with some lemmas that help us convert between different notions of mod, div, pow for ℚ,ℤ,ℕ.
-/
lemma mod_iff_exists_nat_factor (hkn:k≤ n) (hkm:k< m) (hm:m≠ 0) :
  (n%m=k)→ (∃ (c:ℕ), n=m*c+k):= by
  intro hn0
  have h0:(Nat.ModEq m) k n:=by
    unfold Nat.ModEq
    rw[hn0]
    exact (Nat.mod_eq_iff_lt hm).2 hkm
  rw[Nat.modEq_iff_dvd] at h0
  zify
  rw[dvd_iff_exists_eq_mul_right] at h0
  obtain ⟨c,hc⟩:=h0
  zify at hkn
  have h1:(m:ℤ)≠ 0:= Int.natCast_ne_zero.2 hm
  rw[Int.natCast_ne_zero_iff_pos] at h1
  rw[← Int.natCast_pos] at h1
  have h2:0≤ c*m:= by linarith
  have h3:0≤ c:= by
    by_contra hc0
    simp at hc0
    have h4:=Int.mul_lt_mul_of_neg_left h1 hc0
    simp at h4
    rw[lt_iff_not_le] at h4
    contradiction
  lift c to ℕ using h3
  use c
  rw[← hc]
  simp

lemma qify_div {a b:ℕ} (hab:a∣b):
  (Rat.divInt b a) =((b:ℤ)/(a:ℤ) :ℤ):=by
  rw[Rat.divInt_eq_div]
  simp[hab]

lemma zify_pow {a b:ℕ}:
  ((a^b):ℕ) =(a:ℤ )^b:=by
  simp


/-
Step 1: Prove the first implication in the case one of the summands is 0.
-/

lemma one_summand_zero (n x: ℕ) (hn : n = x ^ 2) (hpx2:(x^2).factorization p = 2 * x.factorization p):
  Even (n.factorization p):=by
  rw[hn]
  rw[hpx2]
  simp

/-
Step 2: Prove the first implication in the case one of summand has a smaller power of p in its factorization.
-/

lemma one_factorization_small {n p: ℕ} ( x y:ℕ ) (hn : n = x ^ 2 + y ^ 2) (hp : p.Prime) (hpk : ∃ k, p = 4 * k + 3) (hpx2 : (x ^ 2).factorization p = 2 * x.factorization p) (hn0 : n ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hp0 : x.factorization p ≤ y.factorization p):
  n.factorization p = min (x.factorization p) (y.factorization p) + min (x.factorization p) (y.factorization p):=by
  simp[hp0]
  rw[← two_mul]
  rw[← hpx2]
  set c:= x.factorization p with hc
  have h0:2*c= (x ^ 2).factorization p:= by simp
  have h1:x^2≠ 0 := (sq_pos_of_ne_zero hx0).ne.symm
  have h2:p^(2*c)∣ (x^2) :=(Nat.Prime.pow_dvd_iff_le_factorization hp h1).2 h0.le
  have h3:p^(c)∣ (x) :=(Nat.Prime.pow_dvd_iff_le_factorization hp hx0).2 hc.le
  have h4:p^(c)∣ (y) :=(Nat.Prime.pow_dvd_iff_le_factorization hp hy0).2 hp0
  have hnc:n.factorization p≥ 2*c:= by
    have h3:2*c≤  (y ^ 2).factorization p:= by
      simp
      exact hp0
    have h4:y^2≠ 0 := (sq_pos_of_ne_zero hy0).ne.symm
    have h5:p^(2*c)∣ (y^2) :=(Nat.Prime.pow_dvd_iff_le_factorization hp h4).2 h3
    have h6:=Nat.dvd_add h2 h5
    rw[← hn] at h6
    apply (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).1
    exact h6
  have hpne02:(((p ^ c):ℕ):ℤ) ^ 2≠ 0:= by
    simp[hp.ne_zero]
  have hpne0:(((p ^ c):ℕ):ℤ)≠ 0:= by
    simp[hp.ne_zero]
  have :p=0→c=0:=by
    intro hpeq0
    rw[hc,hpeq0]
    simp
  have hcn:n.factorization p≤ 2*c:=by
    by_contra hnc'
    simp at hnc'
    rw[← succ_le] at hnc'
    rw[← add_one] at hnc'
    apply (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).2 at hnc'
    have hpn:p∣ n/(p^(2*c)):= by
      rw[pow_add] at hnc'
      simp at hnc'
      rw[← Nat.dvd_div_iff] at hnc'
      exact hnc'
      obtain ⟨d,hd⟩:=hnc'
      use p*d
      simp[hd]
      ring
    have h5:(n / p ^ (2 * c))=(x/(p^c))^2+(y/(p^c))^2:= by
      qify
      rw[← zify_pow,← zify_pow,← qify_div h3,sq,Rat.divInt_mul_divInt,← sq,← sq]
      rw[← qify_div h4]
      nth_rw 3 [sq]
      rw[Rat.divInt_mul_divInt,← sq,← sq,Rat.divInt_add_divInt,← add_mul,← Rat.divInt_mul_divInt,Rat.divInt_mul_divInt_cancel]
      rw[← qify_div]
      rw[hn]
      simp
      rw[mul_comm,pow_mul]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).2 hnc
      repeat {assumption}
    obtain ⟨k,hpk⟩:=hpk
    apply dvd_summand_three_mod_four hp hpk h5 at hpn
    rw[Nat.dvd_div_iff h3] at hpn
    nth_rw 2[← pow_one p] at hpn
    rw[← pow_add] at hpn
    have hx1:=(Nat.Prime.pow_dvd_iff_le_factorization hp hx0).1 hpn
    rw[hc,add_one,succ_le] at hx1
    have hx2:=hx1.ne
    contradiction
  rw[hpx2]
  exact Nat.eq_iff_le_and_ge.2 ⟨hcn,hnc⟩

/-
Step 3: Prove the second implication.
-/

theorem exists_sum_squares_general {n:ℕ} :
  IsSumSquare n↔ ∀ (p:ℕ), (p.Prime)→ (∃ k, p=4*k+3) → Even (n.factorization p):=by
  constructor
  unfold IsSumSquare
  intro h
  obtain⟨x,y,hn⟩:=h
  intro p hp hpk
  have hpx2:(x^2).factorization p = 2 * x.factorization p:= by simp
  have hpy2:(y^2).factorization p = 2 * y.factorization p:= by simp
  obtain(hn0|hn0):=eq_or_ne n 0
  rw[hn0]
  simp
  obtain (hx0|hx0):= eq_or_ne x 0
  simp[hx0] at hn
  exact one_summand_zero n y hn hpy2
  obtain (hy0|hy0):= eq_or_ne y 0
  simp[hy0] at hn
  exact one_summand_zero n x hn hpx2
  use min (x.factorization p) (y.factorization p)
  obtain (hp0|hp0):= le_or_lt (x.factorization p) (y.factorization p)
  exact one_factorization_small x y hn hp hpk hpx2 hn0 hx0 hy0 hp0
  rw[add_comm] at hn
  rw[min_comm]
  exact one_factorization_small y x hn hp hpk hpy2 hn0 hy0 hx0 hp0.le
  obtain(hn|hn):=eq_or_ne n 0
  intro _?
  use 0,0
  simp[hn]
  intro h
  have hf: ∀p∈ n.factorization.support, (Even (n.factorization p)) ∨ IsSumSquare p:= by
    rw[Nat.support_factorization]
    intro p hp
    rw[Nat.mem_primeFactors] at hp
    obtain ⟨hp,_?⟩:=hp
    obtain (hp2|hp2):=eq_or_ne p 2
    right
    use 1,1
    simp[hp2]
    let hpf: Fact p.Prime:= fact_iff.2 hp
    have hp0:=Nat.Prime.mod_two_eq_one_iff_ne_two.2 hp2
    rw[odd_mod_four_iff] at hp0
    obtain (hp0|hp0):=hp0
    have hpk:∃ k,p=4*k+1 := by
      have h1:1≤ p:= by
        simp[hp.one_le]
      have h2:1< 4:= by trivial
      have h3:4≠ 0:= by trivial
      exact mod_iff_exists_nat_factor h1 h2 h3 hp0
    simp[exists_sum_squares_prime hp hpk]
    have hpk:∃ k,p=4*k+3 := by
      have h1:3≤ p:= by
        have h2:=hp.two_le
        have h3:= lt_iff_le_and_ne.2 ⟨h2 ,hp2.symm⟩
        linarith
      have h2:3< 4:= by trivial
      have h3:4≠ 0:= by trivial
      exact mod_iff_exists_nat_factor h1 h2 h3 hp0
    simp[h p hp hpk]
  exact sum_sq_prod n.factorization hf (n.factorization_prod_pow_eq_self hn).symm
