import Mathlib.Tactic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card


open Nat




/-
Continuing from the square sum theorem for prime numbers, we prove Fermat's criteria for when a natural number can be written as a square sum.

Theorem: A natural number is a sum of squares if and only if its prime factorization contains an even number of primes of form 4k+3.
-/

/-first we define what it means for a natural number to be a sum of squares for better readability.-/

def IsSumSquare (n:ℕ): Prop:= ∃ x y, n=x^2+y^2

/-
Recall the theorem for the prime case. I will exclude the proof so that I do not have to import the whole file.
-/
lemma exists_sum_squares (hp : (p:ℕ).Prime) (hpk : p = 4 * k + 1) : ∃ (a b : ℤ), p = a^2 + b^2 :=sorry
/-
Here is the version where all variables involved are natural numbers, because we are taking squares anyway. The proof simply uses the tactic zify.
-/
theorem exists_sum_squares_prime {p:ℕ} (hp : p.Prime) (hpk :∃ k, p = 4 * k + 1) :
    IsSumSquare p := by
  obtain⟨k,hpk⟩ :=hpk
  obtain⟨a,b,hab⟩:= exists_sum_squares hp hpk
  use a.natAbs,b.natAbs
  zify
  rw[sq_abs,sq_abs]
  tauto

/-
Lemma: If p does not divide n, then n is invertible in ℤ_p. This is proven in the ZMod package, but we reformulate the following more readable version.
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
Lemma: If a prime p is 3 mod 4 and divides a sum of square n=x^2+y^2, then p divides x.
-/
lemma dvd_summand_three_mod_four (hp : p.Prime) (hpk :p = 4 * k + 3) (hn:n=x^2+y^2) :
    (p ∣  n) →  p∣ x :=by
  intro hpn
  /-suppose otherwise, then x is invertible mod p, and the assumption p|n says x^2+y^2=0 mod p.-/
  by_contra hpx
  have hz:= inverse_mod_prime hp hpx
  obtain ⟨ z,hz⟩ :=hz
  have h0:(n:ZMod p)=((x^2+y^2):ZMod p):= by rw[hn];simp
  have h1:=(ZMod.natCast_zmod_eq_zero_iff_dvd n p).2 hpn
  rw[h1] at h0
  /-So we multiply both sides by the inverse of x, say z. Then (yz)^2=-1 mod p-/
  have h2:0=z^2*(x^2+y^2):=by simp[← h0]
  rw[mul_add,sq,sq,mul_assoc,← mul_assoc z x x,hz,one_mul,hz] at h2
  have h3: 0=1+(z*y)^2:=by rw[h2];ring
  have h4: -1+0=-1+1+(z*y)^2:=by simp[h3]
  simp at h4
  /-But this contradicts the fact that -1 is a square mod p iff p≠3 mod 4. To apply this fact, we need to rewrite p.Prime as a [Fact] instance. -/
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
    /-This is a direct consequence of the previous lemma. We know p|x and p|y, meaning p^2|x^2+y^2=n.-/
  intro hpn
  unfold IsSumSquare at hn
  obtain ⟨ x,y,hn⟩ :=hn
  have hpx:=dvd_summand_three_mod_four hp hpk hn hpn
  /-To get p|y, we just write n^2=y^2+x^2 and apply the same lemma.-/
  have hpy:p∣ y:= by
    have hn: n=y^2+x^2:=by rw[hn,add_comm]
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
  /-If n=a^2+b^2, m=c^2+d^2, then nm=(ac-bd)^2+(ad+bc)^2. To use subtraction, we move to integers first.-/
  zify at hn hm ⊢
  have h0: ∃ x y :ℤ, 0≤ x∧ 0≤ y∧ n*m=x^2+y^2:=by
    use |a*c-b*d|,|a*d+b*c|
    rw[hm,hn,sq_abs,sq_abs]
    refine ⟨by simp,by simp,by ring⟩
  obtain ⟨x,y,_?,_?,h0⟩:=h0
  use x.natAbs,y.natAbs
  simp[Int.natCast_natAbs,h0]

/-
lemma: If n is a sum of squares then n^m is a sum of squares.
-/
lemma sum_sq_pow (m:ℕ) (hn:IsSumSquare n) :
    IsSumSquare (n^m) := by
    /-This follows directly from induction.-/
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
  ring

/-
lemma: If f:ℕ→ℕ is a map with finite support with even values (its image has only finitely many non-zero values), then f/2 also has the same support.
-/
def Finsupp.fun_div_two (f:ℕ→₀ℕ) (hf:∀m∈f.support, Even (f m)):ℕ→₀ℕ where
  /-We may directly check the definitions by simplyfying and doing some obvious rewrites. The result is due to the support could only change if f(x)=1, where 1/2 would evaluate to 0. -/
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
    rw[hr,← mul_two] at ha2
    simp at ha2
    rw[ha2] at hr
    contradiction
    simp
    intro ha2
    by_contra ha
    rw[ha] at ha2
    contradiction

/-
lemma: If f:ℕ→ℕ is a map with finite support. If m is a natural number, then we may define (f.reduce m) by sending m to 0, and have it be the same as f everywhere else. Then (f.reduce m) is also of finite support.
-/
def Finsupp.reduce (f:ℕ→₀ℕ) (m:ℕ):ℕ→₀ℕ where
  /-The proof is again by directly checking definitions.-/
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

/-
lemma: A wrapper function to extract the support of the function (f.reduce m).
-/
lemma reduce_supp (f:ℕ→₀ℕ) (m:ℕ):
    (f.reduce m).support = f.support\ {m}:= by
  unfold Finsupp.reduce
  simp

/-
lemma: A wrapper function to extract the function of the Finsupp object (f.reduce m).
-/
lemma reduce_fun (f:ℕ→₀ℕ) (m:ℕ):
    (f.reduce m) x =(fun x=>if x≠ m then f x else 0) x:= by
  unfold Finsupp.reduce
  simp


/-
Proposition: If n=∏ aᵢ² ∏ bᵢ^{kᵢ} is a finite product where bᵢ are sum of sqaures. Then n is a sum of squares.
-/
/-The finite product condition is phrased using the prod function of a function of finite support as follows.-/
lemma sum_sq_prod {n:ℕ}(f:ℕ→₀ℕ) (hf: ∀m∈ f.support, (Even (f m)) ∨ IsSumSquare m) (hn:n=(f.prod (fun (x y:ℕ )=>x^y))):
    IsSumSquare n:=by
  unfold Finsupp.prod at hn
  simp at hn
  /-The proof is by induction on the number of bᵢ's. First we split into two cases, either it is 0 (base case) or non-zero (inductive step). The induction is phrased in terms of termination on the cardinality of the set {m∈f.support | IsSumSquare m}. -/
  obtain (h0|⟨m, hm⟩):=Set.eq_empty_or_nonempty {m∈f.support | IsSumSquare m}
  /-In the first case, we simply conclude that n=(∏ aᵢ)²+0^2. -/
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
  /-To express the term ∏ aᵢ, we need to divide f by 2, this uses the previous lemma that says f/2 is still a finitely supported function.-/
  use ((f.fun_div_two h1).prod (fun (x y:ℕ )=>x^y)),0
  simp
  rw[sq,← Finsupp.prod_mul]
  unfold Finsupp.prod
  unfold Finsupp.fun_div_two
  simp
  /-To show n=(∏ aᵢ)^2, i.e. f.prod=((f.fun_div_two).prod)^2, we expand and simplify using definition.-/
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
  /-Now for the inductive step, say bₘ^{kₘ} is a factor of  n=∏ aᵢ² ∏ bᵢ^{kᵢ}, and n' is the product with bₘ^{kₘ} removed. Then by induction hypothesis, n' is a sum of squares. By the previous lemma, so is n.-/
  set f':= f.reduce m
  /-The size of {m∈f.support | IsSumSquare m} indeed goes down by 1 when we take f':=(f.reduce m). This proof is routine with the use of Finite and Finset package.-/
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
  /-Here we check f' indeed satisfies the induction hypothesis.-/
  have hf': ∀m∈ f'.support, (Even (f' m)) ∨ IsSumSquare m:=by
    rw[reduce_supp]
    intro x hx
    rw[Finset.mem_sdiff] at hx
    have ⟨h1,h2⟩:=hx
    rw[reduce_fun]
    simp at h2
    simp[h2]
    exact hf x h1
  /-We show the size of the set does go down so that lean recognize that the induction terminates.-/
  have : {x|¬ (f.reduce m) x=0 ∧  IsSumSquare x}.ncard < {x|¬ f x =0 ∧ IsSumSquare x}.ncard:=by simp at hf0;linarith
  /-The induction is performed in the style of a recursion.-/
  have hind:= sum_sq_prod f' hf' (Eq.refl (f'.prod (fun (x y:ℕ )=>x^y)))
  /-Next we show n'*bₘ^{kₘ}=n. This is easy using Finset.mem_sdiff and Finset.prod_equiv where the equivalence is just the identity ℕ≅ℕ.-/
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
  /-Apply the previous lemma to show bₘ^{kₘ} is a sum of squares.-/
  have hpow:=sum_sq_pow (f m) hm.2
  rw[hn,hprod]
  have hst:∀ (i : ℕ), (i∈ f'.support)↔ (((Equiv.refl ℕ) i) ∈f'.support):=by simp
  have hfg: ∀ i∈ f'.support, i^(f' i) = i^(f ((Equiv.refl ℕ) i)):=by
    intro i hi
    rw[reduce_supp] at hi
    simp
    rw[reduce_fun]
    simp at hi
    simp[hi.2]
  have hf':(f'.support.prod fun x ↦ x ^ f' x)= (f'.support.prod fun x ↦ x ^ f x):= Finset.prod_equiv (Equiv.refl ℕ) hst hfg
  rw[← hf']
  /-Apply the previous lemma to show n is a sum of squares.-/
  exact sum_sq_mul hind hpow
termination_by  {x∈f.support | IsSumSquare x}.ncard



/-
Theorem: A natural number is a sum of squares if and only if its prime factorization contains an even number of primes of form 4k+3.
-/
/-
Lemma: A wrapper function that converts n=k mod m to the statement ∃c, n=m*c+k.
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
/-
Lemma: A wrapper function that converts Rat.divInt to integer division. Sometimes we will work in rational numbers for division.
-/
lemma qify_div {a b:ℕ} (hab:a∣b):
  (Rat.divInt b a) =((b:ℤ)/(a:ℤ) :ℤ):=by
  rw[Rat.divInt_eq_div]
  simp[hab]
/-
Lemma: A wrapper function that converts powers of natural numbers to powers of integers, so that we can use subtraction.
-/
lemma zify_pow {a b:ℕ}:
  ((a^b):ℕ) =(a:ℤ )^b:=by
  simp


/-
Step 1: Prove the fisrt case of the first implication: If one of the summands is 0, then the theorem is trivial.
-/
lemma one_summand_zero (n x: ℕ) (hn : n = x ^ 2):
    Even (n.factorization p):=by
  rw[hn]
  have hpx2:(x^2).factorization p = 2 * x.factorization p:= by simp
  rw[hpx2]
  simp

/-
Step 2: Consider the factorization of x and y. Suppose p is a factor of n with p=3 mod 4, then by the previous lemma p|x and p|y. Therefore the multiplicity of p will be twice that of x and y. Without loss of generality, we assume the multiplicity of p in x is less than or equal to that of y.
-/

lemma one_factorization_small {n p: ℕ} ( x y:ℕ ) (hn : n = x ^ 2 + y ^ 2) (hp : p.Prime) (hpk : ∃ k, p = 4 * k + 3) (hn0 : n ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hp0 : x.factorization p ≤ y.factorization p):
    n.factorization p = 2*x.factorization p:=by
  /-The proof is routine using functions of Nat.Prime and sometimes converting to rational numbers for division.-/
  have hpx2:(x^2).factorization p = 2 * x.factorization p:= by simp
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
    rw[← succ_le,← add_one] at hnc'
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
      rw[← qify_div,hn]
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
Step 3: Combine all the lemmas into the final proof of the theorem.
-/
theorem exists_sum_squares_general {n:ℕ} :
    IsSumSquare n↔ ∀ (p:ℕ), (p.Prime)→ (∃ k, p=4*k+3) → Even (n.factorization p):=by
  constructor
  /-If n is a sum of square, then by the above lemma the numtiplicity of p for p=4k+3 is even.-/
  unfold IsSumSquare
  intro h
  obtain⟨x,y,hn⟩:=h
  intro p hp hpk
  have hpy2:(y^2).factorization p = 2 * y.factorization p:= by simp
  /-The case n=0 is trivial.-/
  obtain(hn0|hn0):=eq_or_ne n 0
  rw[hn0]
  simp
  /-The cases x,y=0 are done above.-/
  obtain (hx0|hx0):= eq_or_ne x 0
  simp[hx0] at hn
  exact one_summand_zero n y hn
  obtain (hy0|hy0):= eq_or_ne y 0
  simp[hy0] at hn
  exact one_summand_zero n x hn
  use min (x.factorization p) (y.factorization p)
  /-The rest of the cases are also done above.-/
  obtain (hp0|hp0):= le_or_lt (x.factorization p) (y.factorization p)
  simp[hp0,← two_mul]
  exact one_factorization_small x y hn hp hpk hn0 hx0 hy0 hp0
  rw[add_comm] at hn
  rw[min_comm]
  simp[hp0.le,← two_mul]
  exact one_factorization_small y x hn hp hpk hn0 hy0 hx0 hp0.le
  /-If there are an even number of prime factors of form 4k+3, then by the previous proposition n is a sum of squares. The case n=0 is trivial.-/
  obtain(hn|hn):=eq_or_ne n 0
  intro _?
  use 0,0
  simp[hn]
  /-Check the prime factorization of n satisfies the conditions of the proposition.-/
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
  /-Use Nat.factorization_prod_pow_eq_self to show the product of the prime factorization of n is equal to n.-/
  exact sum_sq_prod n.factorization hf (n.factorization_prod_pow_eq_self hn).symm
