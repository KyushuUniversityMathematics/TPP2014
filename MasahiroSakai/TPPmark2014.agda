-----------------------------------------------------------------------------
-- |
-- Module      :  TPPmark2014
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
--
-- TPPmark2014 problem.
-- See <http://imi.kyushu-u.ac.jp/lasm/tpp2014/tppmark2014-2.pdf> for details.
--
-- Checked with and Agda-2.4.2.1 and agda-stdlib-0.9.
--
-- Latest version is available at <https://github.com/msakai/TPPmark2014>.
--
-----------------------------------------------------------------------------
module TPPmark2014 where

open import Algebra
open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Function
open import Induction.Nat

open Data.Nat.Properties.SemiringSolver

private
  module DTO = DecTotalOrder Data.Nat.decTotalOrder
  module CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

-- ---------------------------------------------------------------------------
-- Basic arithmetic lemma

cancel-+-right : ∀ i {j k} → j + i ≡ k + i → j ≡ k
cancel-+-right i {j} {k} P = cancel-+-left i $ 
    begin
      i + j
    ≡⟨ CS.+-comm i j ⟩
      j + i
    ≡⟨ P ⟩
      k + i
    ≡⟨ CS.+-comm k i ⟩
      i + k
    ∎
  where
    open ≡-Reasoning

-- m≥1 ∧ n≥2 ⇒ m<n*m
s<ss*s : ∀ m n → suc m < suc (suc n) * suc m
s<ss*s m n =
    begin
      2 + m
    ≤⟨ m≤m+n (2 + m) (m + (n + n * m)) ⟩
      (2 + m) + (m + (n + n * m))
    ≤⟨ DTO.reflexive 2+m+m+n+nm≡ssn*sm ⟩
      (2 + n) * (1 + m)
    ∎
  where
    open ≤-Reasoning
    2+m+m+n+nm≡ssn*sm : (2 + m) + (m + (n + n * m)) ≡ (2 + n) * (1 + m)
    2+m+m+n+nm≡ssn*sm = solve 2 (λ m n → (con 2 :+ m) :+ (m :+ (n :+ n :* m)) := (con 2 :+ n) :* (con 1 :+ m)) refl m n

-- m≥1 ∧ n≥2 ⇒ m<m*n
s<s*ss : ∀ m n → suc m < suc m * suc (suc n)
s<s*ss m n rewrite (CS.*-comm (1 + m) (2 + n)) = s<ss*s m n

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ {zero} {suc b} (s≤s 0≤b) ()
<⇒≢ {suc a} {suc b} (s≤s a<b) 1+a≡1+b = <⇒≢ a<b (cancel-+-left 1 1+a≡1+b)

-- ---------------------------------------------------------------------------
-- Lemmas about Fin

cancel-toℕ : ∀ {n} (a b : Fin n) → toℕ a ≡ toℕ b → a ≡ b
cancel-toℕ Fin.zero Fin.zero P = refl
cancel-toℕ Fin.zero (Fin.suc b) ()
cancel-toℕ (Fin.suc a) Fin.zero ()
cancel-toℕ (Fin.suc a) (Fin.suc b) P = cong suc (cancel-toℕ a b (cancel-+-left 1 P))

toℕ<n : ∀ {n} (a : Fin n) → toℕ a < n
toℕ<n {zero} ()
toℕ<n {suc m} Fin.zero = DTO.refl {1} +-mono (z≤n)
toℕ<n {suc m} (Fin.suc x) = DTO.refl {1} +-mono (toℕ<n x)

-- ---------------------------------------------------------------------------
-- Some lemmas on divisibility and modulo arithmetic

rem≡0⇒∣ : ∀ {a n} → (a mod suc n ≡ Fin.zero) → (suc n ∣ a)
rem≡0⇒∣ {a} {n} P = divides (a div m) $ begin
      a
    ≡⟨ DivMod.property (a divMod m) ⟩
      toℕ (a mod m) + (a div m) * m
    ≡⟨ cong (λ x → toℕ x + (a div m) * m) P ⟩
      toℕ (Fin.zero {n}) + (a div m) * m
    ≡⟨ refl ⟩
      (a div m) * m
    ∎
  where
    open ≡-Reasoning
    m = suc n

*∣* : ∀ {a₁ n₁ a₂ n₂} → (suc n₁ ∣ a₁) → (suc n₂ ∣ a₂) → (suc n₁ * suc n₂ ∣ a₁ * a₂)
*∣* {a₁} {n₁} {a₂} {n₂} (divides q₁ a₁≡q₁*m₁) (divides q₂ a₂≡q₂*m₂) = divides (q₁ * q₂) $
    begin
      a₁ * a₂
    ≡⟨ cong (λ x → x * a₂) a₁≡q₁*m₁ ⟩
      (q₁ * m₁) * a₂
    ≡⟨ cong (λ x → (q₁ * m₁) * x) a₂≡q₂*m₂ ⟩
      (q₁ * m₁) * (q₂ * m₂)
    ≡⟨ solve 4 (λ q₁ m₁ q₂ m₂ → (q₁ :* m₁) :* (q₂ :* m₂) := (q₁ :* q₂) :* (m₁ :* m₂)) refl q₁ m₁ q₂ m₂ ⟩
      (q₁ * q₂) * (m₁ * m₂)
    ∎
  where
    open ≡-Reasoning
    m₁ = suc n₁
    m₂ = suc n₂

-- m≥2 ∧ n≥1 ∧ m∣n ⇒ n div m < n
2+m∣1+n⇒quot<1+n : ∀ {m} {n} → (2+m∣1+n : 2 + m ∣ 1 + n) → (quotient 2+m∣1+n < 1 + n)
2+m∣1+n⇒quot<1+n {m} {n} (divides zero ())
2+m∣1+n⇒quot<1+n {m} {n} (divides (suc o) sn≡so*ssm) rewrite sn≡so*ssm = s<s*ss o m

div-uniq-lemma : ∀ {n} (r1 r2 : Fin n) q1 k → toℕ r1 + q1 * n < toℕ r2 + suc (q1 + k) * n
div-uniq-lemma {zero} ()
div-uniq-lemma {suc n-1} r1 r2 q1 k =
    begin
      suc (toℕ r1) + q1 * n
    ≤⟨ toℕ<n r1 +-mono DTO.refl ⟩
      n + q1 * n
    ≤⟨ DTO.refl ⟩
      (suc q1) * n
    ≤⟨ 1+q1≤q2 *-mono DTO.refl {n} ⟩
      q2 * n
    ≤⟨ n≤m+n (toℕ r2) (q2 * n) ⟩
      toℕ r2 + q2 * n        
    ∎
  where
    open ≤-Reasoning
    n = suc n-1
    q2 = suc (q1 + k)

    1+q1≤q2 : suc q1 ≤ q2
    1+q1≤q2 =
      begin
        suc q1
      ≤⟨ m≤m+n (suc q1) k ⟩ 
        suc q1 + k
      ≤⟨ DTO.refl ⟩
        q2
      ∎

div-uniq : ∀ {n} (r1 r2 : Fin n) q1 q2 → toℕ r1 + q1 * n ≡ toℕ r2 + q2 * n → q1 ≡ q2
div-uniq {zero} ()
div-uniq {suc _} r1 r2 q1 q2 P with compare q1 q2
div-uniq {suc _} r1 r2 .m .m P | equal m = refl
div-uniq {suc n-1} r1 r2 .q1 .(suc (q1 + k)) r1+q1*n≡r2+q2*n | less q1 k = ⊥-elim (r1+q1*n≢r2+q2*n r1+q1*n≡r2+q2*n)
  where
    n = suc n-1
    q2 = suc (q1 + k)
    r1+q1*n<r2+q2*n : suc (toℕ r1) + q1 * n ≤ toℕ r2 + q2 * n
    r1+q1*n<r2+q2*n = div-uniq-lemma r1 r2 q1 k
    r1+q1*n≢r2+q2*n : toℕ r1 + q1 * n ≢ toℕ r2 + q2 * n
    r1+q1*n≢r2+q2*n = <⇒≢ r1+q1*n<r2+q2*n
div-uniq {suc n-1} r1 r2 .(suc (q2 + k)) .q2 r1+q1*n≡r2+q2*n | greater q2 k = ⊥-elim (r2+q2*n≢r1+q1*n (sym r1+q1*n≡r2+q2*n))
  where
    n = suc n-1
    q1 = suc (q2 + k)
    r2+q2*n<r1+q1*n : suc (toℕ r2) + q2 * n ≤ toℕ r1 + q1 * n
    r2+q2*n<r1+q1*n = div-uniq-lemma r2 r1 q2 k
    r2+q2*n≢r1+q1*n : toℕ r2 + q2 * n ≢ toℕ r1 + q1 * n
    r2+q2*n≢r1+q1*n = <⇒≢ r2+q2*n<r1+q1*n

mod-uniq : ∀ {n} (r1 r2 : Fin n) q1 q2 → toℕ r1 + q1 * n ≡ toℕ r2 + q2 * n → r1 ≡ r2
mod-uniq {zero} ()
mod-uniq {suc m} r1 r2 q1 q2 P = cancel-toℕ r1 r2 $ cancel-+-right (q1 * n) $ 
    begin
      toℕ r1 + q1 * n
    ≡⟨  P ⟩ 
      toℕ r2 + q2 * n
    ≡⟨  cong (λ x → toℕ r2 + x * n) (sym (div-uniq r1 r2 q1 q2 P)) ⟩ 
      toℕ r2 + q1 * n
    ∎
  where
    open ≡-Reasoning
    n = suc m

mod-lemma : ∀ {n} a b k →  a ≡ b + k * suc n → a mod suc n ≡ b mod suc n
mod-lemma {n} a b k P = mod-uniq {m} (a mod m) (b mod m) (a div m) (b div m + k) $
    begin
      toℕ (a mod m) + (a div m) * m
    ≡⟨  sym (DivMod.property (a divMod m)) ⟩
      a
    ≡⟨  P ⟩
      b + k * m
    ≡⟨  cong (λ x → x + k * m) (DivMod.property (b divMod m)) ⟩ 
      (toℕ (b mod m) + (b div m) * m) + k * m
    ≡⟨ solve 4 (λ bm bd m k → (bm :+ bd :* m) :+ k :* m := bm :+ (bd :+ k) :* m) refl (toℕ (b mod m)) (b div m) m k ⟩
      toℕ (b mod m) + (b div m + k) * m
    ∎
  where
    open ≡-Reasoning
    m : ℕ
    m = suc n

abstract
  mod-dist-+ : ∀ {n} a b → (a + b) mod suc n ≡ (toℕ (a mod suc n) + toℕ (b mod suc n)) mod suc n
  mod-dist-+ {n} a b = mod-lemma (a + b) (toℕ (a mod m) + toℕ (b mod m)) (qa + qb) $
      begin
        a + b
      ≡⟨ cong (λ x → x + b) (DivMod.property (a divMod m)) ⟩ 
        (toℕ ra + qa * m) + b
      ≡⟨ cong (λ x → toℕ ra + qa * m + x) (DivMod.property (b divMod m)) ⟩ 
        (toℕ ra + qa * m) + (toℕ rb + qb * m)
      ≡⟨ solve 5 (λ ra rb qa qb m →
                   (ra :+ qa :* m) :+ (rb :+ qb :* m) := (ra :+ rb) :+ (qa :+ qb) :* m)
            refl (toℕ ra) (toℕ rb) qa qb m ⟩
        toℕ ra + toℕ rb + (qa + qb) * m
      ∎
    where
      open ≡-Reasoning
      m : ℕ
      m = 1 + n
      qa : ℕ
      qa = a div m
      qb : ℕ
      qb = b div m
      ra : Fin (suc n)
      ra = a mod m
      rb : Fin (suc n)
      rb = b mod m

abstract
  mod-dist-* : ∀ {n} a b → (a * b) mod suc n ≡ (toℕ (a mod suc n) * toℕ (b mod suc n)) mod suc n
  mod-dist-* {n} a b = mod-lemma (a * b) (toℕ ra * toℕ rb) (toℕ ra * qb + qa * toℕ rb + qa * m * qb) $
      begin
        a * b
      ≡⟨ cong (λ x → x * b) (DivMod.property (a divMod m)) ⟩ 
        (toℕ ra + qa * m) * b
      ≡⟨ cong (λ x → (toℕ ra + qa * m) * x) (DivMod.property (b divMod m)) ⟩ 
        (toℕ ra + qa * m) * (toℕ rb + qb * m)
      ≡⟨ solve 5 (λ qa qb ra rb m →
                      (ra :+ qa :* m) :* (rb :+ qb :* m)
                      := ra :* rb :+ (ra :* qb :+ qa :* rb :+ qa :* m :* qb) :* m)
           refl qa qb (toℕ ra) (toℕ rb) m ⟩
        toℕ ra * toℕ rb + (toℕ ra * qb + qa * toℕ rb + qa * m * qb) * m
      ∎
    where
      open ≡-Reasoning
      m : ℕ
      m = 1 + n
      qa : ℕ
      qa = a div m
      qb : ℕ
      qb = b div m
      ra : Fin (suc n)
      ra = a mod m
      rb : Fin (suc n)
      rb = b mod m

-- ---------------------------------------------------------------------------
-- Definition of _² and its properties

_² : ℕ → ℕ
_² n = n * n

∣⇒²∣² : ∀ {a n} → (suc n ∣ a) → ((suc n) ² ∣ a ²)
∣⇒²∣² {a} {n} 1+n∣a = *∣* 1+n∣a 1+n∣a

-- ---------------------------------------------------------------------------
-- Lemmas specific to modulo-3 arithmetic

abstract
  -- TODO: use primality of 3 instead of enumerating cases of "a mod 3" and "b mod 3"
  3∣*-split : ∀ a b → (3 ∣ a * b) → (3 ∣ a) ⊎ (3 ∣ b)
  3∣*-split a b (divides q a*b≡q*3) = body
    where
      open ≡-Reasoning
  
      lem1 : (toℕ (a mod 3) * toℕ (b mod 3)) mod 3 ≡ Fin.zero
      lem1 = begin
            (toℕ (a mod 3) * toℕ (b mod 3)) mod 3
          ≡⟨ lem1-a ⟩
            (a * b) mod 3
          ≡⟨ cong (λ x → x mod 3) a*b≡q*3 ⟩
            (q * 3) mod 3
          ≡⟨ cong (λ x → x mod 3) (CS.*-comm q 3) ⟩
            (3 * q) mod 3
          ≡⟨ lem1-b ⟩
            Fin.zero
          ∎
        where
          -- If I inline these lemmas, Agda takes significant time to type-check. Why?
          lem1-a : (toℕ (a mod 3) * toℕ (b mod 3)) mod 3 ≡ (a * b) mod 3
          lem1-a = sym (mod-dist-* a b)
          lem1-b : (3 * q) mod 3 ≡ Fin.zero
          lem1-b = mod-dist-* 3 q
  
      lem2 : ∀ (a b : Fin 3) → ((toℕ a * toℕ b) mod 3 ≡ Fin.zero) → (a ≡ Fin.zero) ⊎ (b ≡ Fin.zero)
      lem2 Fin.zero _ _ = inj₁ refl
      lem2 _ Fin.zero _ = inj₂ refl
      lem2 (Fin.suc Fin.zero) (Fin.suc Fin.zero) ()
      lem2 (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero)) ()
      lem2 (Fin.suc Fin.zero) (Fin.suc (Fin.suc (Fin.suc ())))
      lem2 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero) ()
      lem2 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc Fin.zero)) ()
      lem2 (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc (Fin.suc ())))
      lem2 (Fin.suc (Fin.suc (Fin.suc ()))) _
  
      body : (3 ∣ a) ⊎ (3 ∣ b)
      body with lem2 (a mod 3) (b mod 3) lem1
      ... | inj₁ Q = inj₁ (rem≡0⇒∣ Q)
      ... | inj₂ Q = inj₂ (rem≡0⇒∣ Q)

3∣²⇒3∣ : ∀ {a} → (3 ∣ a ²) → (3 ∣ a)
3∣²⇒3∣ {a} P with 3∣*-split a a P
... | inj₁ p = p
... | inj₂ p = p

-- ---------------------------------------------------------------------------
-- (i) For any a ∈ N, (a² mod 3) = 0 or (a² mod 3) = 1.

prop1 : ∀ a → (a ² mod 3 ≡ Fin.zero) ⊎ (a ² mod 3 ≡ Fin.suc (Fin.zero))
prop1 a rewrite mod-dist-* {2} a a with a mod 3
... | Fin.zero = inj₁ refl
... | (Fin.suc Fin.zero) = inj₂ refl
... | (Fin.suc (Fin.suc Fin.zero)) = inj₂ refl
... | (Fin.suc (Fin.suc (Fin.suc ())))

-- ---------------------------------------------------------------------------
-- (ii) Let a ∈ N, b ∈ N and c ∈ N. If a² + b² = 3c² then (3 | a), (3 | b) and (3 | c).

prop2a : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ a)
prop2a a b c a²+b²≡3c² = 3∣²⇒3∣ 3∣a²
  where
    open ≡-Reasoning

    lem1 : (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3 ≡ Fin.zero
    lem1 = begin
        (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
          ≡⟨ sym (mod-dist-+ (a ²) (b ²)) ⟩
        (a ² + b ²) mod 3
          ≡⟨ cong (λ x → x mod 3) a²+b²≡3c² ⟩
        (3 * c ²) mod 3
          ≡⟨ mod-dist-* 3 (c ²) ⟩
        Fin.zero
          ∎
    
    a²mod3≡0 : a ² mod 3 ≡ Fin.zero
    a²mod3≡0 with prop1 a | prop1 b
    ... | inj₁ p | _ = p
    ... | inj₂ p | inj₁ q = ⊥-elim (1≢0 1≡0)
      where
        1≢0 : ¬ Fin.suc Fin.zero ≡ Fin.zero {2}
        1≢0 ()
    
        1≡0 : Fin.suc Fin.zero ≡ Fin.zero {2}
        1≡0 =
          begin
            Fin.suc Fin.zero
          ≡⟨ refl ⟩
            (toℕ (Fin.suc (Fin.zero {1})) + toℕ (Fin.zero {2})) mod 3
          ≡⟨ cong (λ x → (toℕ x + toℕ (Fin.zero {2})) mod 3) (sym p) ⟩
            (toℕ (a ² mod 3) + toℕ (Fin.zero {2})) mod 3
          ≡⟨ cong (λ x → (toℕ (a ² mod 3) + toℕ x) mod 3) (sym q) ⟩
            (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
          ≡⟨ lem1 ⟩
            Fin.zero
          ∎
    ... | inj₂ p | inj₂ q = ⊥-elim (2≢0 2≡0)
      where
        2≢0 : ¬ Fin.suc (Fin.suc Fin.zero) ≡ Fin.zero {2}
        2≢0 ()
    
        2≡0 : Fin.suc (Fin.suc Fin.zero) ≡ Fin.zero {2}
        2≡0 =
          begin
            Fin.suc (Fin.suc (Fin.zero {0}))
          ≡⟨ refl ⟩
            (toℕ (Fin.suc (Fin.zero {1})) + toℕ (Fin.suc (Fin.zero {1}))) mod 3
          ≡⟨ cong (λ x → (toℕ x + toℕ (Fin.suc (Fin.zero {1}))) mod 3) (sym p) ⟩
            (toℕ (a ² mod 3) + toℕ (Fin.suc (Fin.zero {1}))) mod 3
          ≡⟨ cong (λ x → (toℕ (a ² mod 3) + toℕ x) mod 3) (sym q) ⟩
            (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
          ≡⟨ lem1 ⟩
            Fin.zero
          ∎

    3∣a² : 3 ∣ a ²
    3∣a² = rem≡0⇒∣ a²mod3≡0

prop2b : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ b)
prop2b a b c a²+b²≡3c² = prop2a b a c $
    begin
      b ² + a ²
    ≡⟨ CS.+-comm (b ²) (a ²) ⟩
      a ² + b ²
    ≡⟨ a²+b²≡3c² ⟩
      3 * c ²
    ∎
  where
    open ≡-Reasoning

prop2c : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ c)
prop2c a b c P = 3∣²⇒3∣ 3∣c²
  where
    9∣a² : 9 ∣ a ²
    9∣a² = ∣⇒²∣² (prop2a a b c P)

    9∣b² : 9 ∣ b ²
    9∣b² = ∣⇒²∣² (prop2b a b c P)

    9∣a²+b² : 9 ∣ a ² + b ²
    9∣a²+b² = ∣-+ 9∣a² 9∣b²

    9∣3*c² : 9 ∣ 3 * c ²
    9∣3*c² = subst (λ x → 9 ∣ x) P 9∣a²+b²

    3∣c² : 3 ∣ c ²
    3∣c² = /-cong 2 9∣3*c²

-- ---------------------------------------------------------------------------
-- (iii) Let a ∈ N, b ∈ N and c ∈ N. If a² + b² = 3c² then a = b = c = 0.

private
  prop3-lemma : ∀ a b c → (a * 3) ² + (b * 3) ² ≡ 3 * (c * 3) ² → a ² + b ² ≡ 3 * c ²
  prop3-lemma a b c P = cancel-*-right (a ² + b ²) (3 * c ²) $ 
      begin
        (a ² + b ²) * 3 ²
      ≡⟨ solve 2 (λ a b → (a :* a :+ b :* b) :* con 9 := (a :* con 3) :* (a :* con 3) :+ (b :* con 3) :* (b :* con 3)) refl a b ⟩
        (a * 3) ² + (b * 3) ²
      ≡⟨ P ⟩
        3 * (c * 3) ²
      ≡⟨ solve 1 (λ c → con 3 :* ((c :* con 3) :* (c :* con 3)) := (con 3 :* (c :* c)) :* con 9) refl c ⟩
        (3 * c ²) * 3 ²
      ∎
    where  
      open ≡-Reasoning

prop3a-step
  : ∀ a
  → (∀ a' → (a' <′ a) → ∀ b' c' → (a' ² + b' ² ≡ 3 * c' ²) → a' ≡ 0)
  → ∀ b c → (a ² + b ² ≡ 3 * c ²) → a ≡ 0
prop3a-step zero rec b c P = refl
prop3a-step (suc n) rec b c P = body
  where
    open ≡-Reasoning
    a = suc n

    body : a ≡ 0
    body with (prop2a a b c P) | (prop2b a b c P) | (prop2c a b c P)
    ... | divides a' a≡a'*3 | divides b' b≡b'*3 | divides c' c≡c'*3 =
        begin
          a
        ≡⟨ a≡a'*3 ⟩
          a' * 3
        ≡⟨ cong (λ x → x * 3) a'≡0 ⟩
          0 * 3
        ≡⟨ refl ⟩
          0
        ∎
      where
        a'≡0 : a' ≡ 0
        a'≡0 = rec a' (≤⇒≤′ a'<a) b' c' lem2
          where
            lem1 : (a' * 3) ² + (b' * 3) ² ≡ 3 * (c' * 3) ²
            lem1 rewrite (sym a≡a'*3) | (sym b≡b'*3) | (sym c≡c'*3) = P
            lem2 : a' ² + b' ² ≡ 3 * c' ²
            lem2 = prop3-lemma a' b' c' lem1
            a'<a : a' < a
            a'<a = 2+m∣1+n⇒quot<1+n (divides a' a≡a'*3)

prop3a : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → a ≡ 0
prop3a a = <-rec (λ n → ∀ b c → (n ² + b ² ≡ 3 * c ²) → n ≡ 0) prop3a-step a

prop3b : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → b ≡ 0
prop3b a b c a²+b²≡3c² = prop3a b a c $
    begin
      b ² + a ²
    ≡⟨ CS.+-comm (b ²) (a ²) ⟩
      a ² + b ²
    ≡⟨ a²+b²≡3c² ⟩
      3 * c ²
    ∎
  where
    open ≡-Reasoning

prop3c-step
  : ∀ c
  → (∀ c' → (c' <′ c) → ∀ a' b' → (a' ² + b' ² ≡ 3 * c' ²) → c' ≡ 0)
  → ∀ a b → (a ² + b ² ≡ 3 * c ²) → c ≡ 0
prop3c-step zero rec a b P = refl
prop3c-step (suc n) rec a b P = body
  where
    open ≡-Reasoning
    c = suc n

    body : c ≡ 0
    body with (prop2a a b c P) | (prop2b a b c P) | (prop2c a b c P)
    ... | divides a' a≡a'*3 | divides b' b≡b'*3 | divides c' c≡c'*3 =
        begin
          c
        ≡⟨ c≡c'*3 ⟩
          c' * 3
        ≡⟨ cong (λ x → x * 3) c'≡0 ⟩
          0 * 3
        ≡⟨ refl ⟩
          0
        ∎
      where
        c'≡0 : c' ≡ 0
        c'≡0 = rec c' (≤⇒≤′ c'<c) a' b' lem2
          where
            lem1 : (a' * 3) ² + (b' * 3) ² ≡ 3 * (c' * 3) ²
            lem1 rewrite (sym a≡a'*3) | (sym b≡b'*3) | (sym c≡c'*3) = P
            lem2 : a' ² + b' ² ≡ 3 * c' ²
            lem2 = prop3-lemma a' b' c' lem1
            c'<c : c' < c
            c'<c = 2+m∣1+n⇒quot<1+n (divides c' c≡c'*3)

prop3c : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → c ≡ 0
prop3c a b c = <-rec (λ n → ∀ a₁ b₁ → a₁ ² + b₁ ² ≡ 3 * n ² → n ≡ 0) prop3c-step c a b
