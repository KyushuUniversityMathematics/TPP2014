-----------------------------------------------------------------------------
-- |
-- Module      :  TPPmark2014
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
--
-- TPPmark2014 problem.
-- See <http://imi.kyushu-u.ac.jp/lasm/tpp2014/tppmark2014-2.pdf> for details.
--
-- Checked with and Agda-2.4.2 and agda-stdlib-0.8.1.
--
-- TODO:
--
-- * use CommutativeSemiring module and SemiringSolver module
--
-----------------------------------------------------------------------------
module TPPmark2014 where

open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import Induction.Nat

private
  module DTO = DecTotalOrder Data.Nat.decTotalOrder

-- ---------------------------------------------------------------------------
-- Basic arithmetic lemma

distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distribˡ-*-+ m n o =
  begin
    m * (n + o)
  ≡⟨  *-comm m (n + o) ⟩
    (n + o) * m
  ≡⟨  distribʳ-*-+ m n o ⟩
    n * m + o * m
  ≡⟨  cong (λ x → x + o * m) (*-comm n m) ⟩
    m * n + o * m
  ≡⟨  cong (λ x → m * n + x) (*-comm o m) ⟩
    m * n + m * o
  ∎
  where
    open ≡-Reasoning

*-left-identity : ∀ n → 1 * n ≡ n
*-left-identity n = +-right-identity n

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n = trans (*-comm n 1) (*-left-identity n)

cancel-+-right : ∀ i {j k} → j + i ≡ k + i → j ≡ k
cancel-+-right i {j} {k} P = cancel-+-left i lem
  where
    open ≡-Reasoning
    lem : i + j ≡ i + k
    lem =
      begin
        i + j
      ≡⟨ +-comm i j ⟩
        j + i
      ≡⟨ P ⟩
        k + i
      ≡⟨ +-comm k i ⟩
        i + k
      ∎

-- m≥1 ∧ n≥2 ⇒ m<n*m
s<ss*s : ∀ m n → suc m < suc (suc n) * suc m
s<ss*s m n = subst (λ x → 1 + m < x) 2+m+m+n+nm≡ssn*sm 1+m<2+m+m+n+nm
  where
    open ≡-Reasoning

    2+m≤2+m : 2 + m ≤ 2 + m
    2+m≤2+m = DTO.refl

    2+m≤2+m+m+n+nm : 2 + m ≤ (2 + m) + (m + (n + n * m))
    2+m≤2+m+m+n+nm = m≤m+n (2 + m) (m + (n + n * m))
    
    1+m<2+m+m+n+nm : 1 + m < (2 + m) + (m + (n + n * m))
    1+m<2+m+m+n+nm = 2+m≤2+m+m+n+nm
  
    2+m+m+n+nm≡ssn*sm : (2 + m) + (m + (n + n * m)) ≡ (2 + n) * (1 + m)
    2+m+m+n+nm≡ssn*sm = sym $
      begin
        (2 + n) * (1 + m)
      ≡⟨ distribʳ-*-+ (1 + m) 2 n ⟩
        2 * (1 + m) + n * (1 + m)
      ≡⟨ cong (λ x → x + n * (1 + m)) (distribˡ-*-+ 2 1 m) ⟩
        (2 + 2 * m) + n * (1 + m)
      ≡⟨ cong (λ x → 2 + 2 * m + x) (distribˡ-*-+ n 1 m) ⟩
        (2 + 2 * m) + (n * 1 + n * m)
      ≡⟨ refl ⟩
        (2 + (m + (m + 0))) + (n * 1 + n * m)
      ≡⟨ cong (λ x → 2 + (m + x) + (n * 1 + n * m)) (+-right-identity m) ⟩
        (2 + (m + m)) + (n * 1 + n * m)
      ≡⟨  cong (λ x → 2 + (m + m) + (x + n * m)) (*-right-identity n) ⟩
        (2 + (m + m)) + (n + n * m)
      ≡⟨  cong (λ x → x + (n + n * m)) (sym (+-assoc 2 m m)) ⟩
        ((2 + m) + m) + (n + n * m)
      ≡⟨  +-assoc (2 + m) m (n + n * m) ⟩
        (2 + m) + (m + (n + n * m))
      ∎

    P : 1 + m < (2 + n) * (1 + m)
    P = subst (λ x → 1 + m < x) 2+m+m+n+nm≡ssn*sm 1+m<2+m+m+n+nm

-- m≥1 ∧ n≥2 ⇒ m<m*n
s<s*ss : ∀ m n → suc m < suc m * suc (suc n)
s<s*ss m n rewrite (*-comm (1 + m) (2 + n)) = s<ss*s m n

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ {zero} {suc b} (s≤s 0≤b) 0≡1+b with 0≡1+b
... | ()
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

rem≡0⇒∣ : ∀ {a n} → (a mod (suc n) ≡ Fin.zero) → (suc n ∣ a)
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
    ≡⟨ sym (*-assoc (q₁ * m₁) q₂ m₂) ⟩
      ((q₁ * m₁) * q₂) * m₂
    ≡⟨ cong (λ x → x * m₂) (*-assoc q₁ m₁ q₂) ⟩
      (q₁ * (m₁ * q₂)) * m₂
    ≡⟨ cong (λ x → (q₁ * x) * m₂) (*-comm m₁ q₂) ⟩
      (q₁ * (q₂ * m₁)) * m₂
    ≡⟨ cong (λ x → x * m₂) (sym (*-assoc q₁ q₂ m₁)) ⟩
      ((q₁ * q₂) * m₁) * m₂
    ≡⟨ *-assoc (q₁ * q₂) m₁ m₂ ⟩
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
div-uniq-lemma {suc n-1} r1 r2 q1 k = r1+q1*n<r2+q2*n
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

    n+q1*n≤q2*n : n + q1 * n ≤ q2 * n -- (suc q1) * n ≤ q2 * n
    n+q1*n≤q2*n = 1+q1≤q2 *-mono DTO.refl {n}

    r1+q1*n<r2+q2*n : suc (toℕ r1) + q1 * n ≤ toℕ r2 + q2 * n -- toℕ r1 + q1 * n < toℕ r2 + q2 * n
    r1+q1*n<r2+q2*n =
      begin
        suc (toℕ r1) + q1 * n
      ≤⟨ toℕ<n r1 +-mono DTO.refl ⟩
        n + q1 * n
      ≤⟨ n+q1*n≤q2*n ⟩
        q2 * n
      ≤⟨ n≤m+n (toℕ r2) (q2 * n) ⟩
        toℕ r2 + q2 * n        
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
mod-uniq {suc m} r1 r2 q1 q2 P = cancel-toℕ r1 r2 lem2
  where
    open ≡-Reasoning
    n = suc m

    lem1 : toℕ r1 + q1 * n ≡ toℕ r2 + q1 * n
    lem1 =
      begin
        toℕ r1 + q1 * n
      ≡⟨  P ⟩ 
        toℕ r2 + q2 * n
      ≡⟨  cong (λ x → toℕ r2 + x * n) (sym (div-uniq r1 r2 q1 q2 P)) ⟩ 
        toℕ r2 + q1 * n
      ∎

    lem2 : toℕ r1 ≡ toℕ r2
    lem2 = cancel-+-right (q1 * n) lem1

mod-lemma : ∀ {n} a b k →  a ≡ b + k * suc n → a mod (suc n) ≡ b mod (suc n)
mod-lemma {n} a b k P = mod-uniq {m} (a mod m) (b mod m) (a div m) (b div m + k) lem
  where
    open ≡-Reasoning
    m = suc n

    lem : toℕ (a mod m) + (a div m) * m ≡ toℕ (b mod m) + ((b div m) + k) * m
    lem =
     begin
       toℕ (a mod m) + (a div m) * m
     ≡⟨  sym (DivMod.property (a divMod m)) ⟩
       a
     ≡⟨  P ⟩
       b + k * m
     ≡⟨  cong (λ x → x + k * m) (DivMod.property (b divMod m)) ⟩ 
       (toℕ (b mod m) + (b div m) * m) + k * m
     ≡⟨  +-assoc (toℕ (b mod m)) (b div m * m) (k * m) ⟩
       toℕ (b mod m) + ((b div m) * m + k * m)
     ≡⟨  cong (λ x → toℕ (b mod m) + x) (sym (distribʳ-*-+ m (b div m) k)) ⟩
       toℕ (b mod m) + ((b div m) + k) * m
     ∎

mod-dist-+ : ∀ {n} a b → (a + b) mod (suc n) ≡ (toℕ (a mod (suc n)) + toℕ (b mod (suc n))) mod (suc n)
mod-dist-+ {n} a b = mod-lemma (a + b) (toℕ (a mod m) + toℕ (b mod m)) (qa + qb) lem2
  where
    open ≡-Reasoning
    m = 1 + n
    qa = a div m
    qb = b div m
    ra = a mod m
    rb = b mod m

    lem1 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lem1 a b c d =
      begin
        (a + b) + (c + d)
      ≡⟨  +-assoc a b (c + d) ⟩ 
        a + (b + (c + d))
      ≡⟨  cong (λ x → a + x) (sym (+-assoc b c d)) ⟩ 
        a + ((b + c) + d)
      ≡⟨  cong (λ x → a + (x + d)) (+-comm b c) ⟩ 
        a + ((c + b) + d)
      ≡⟨  cong (λ x → a + x) (+-assoc c b d) ⟩ 
        a + (c + (b + d))
      ≡⟨  sym (+-assoc a c (b + d)) ⟩ 
        (a + c) + (b + d)
      ∎

    lem2 : a + b ≡ toℕ ra + toℕ rb + (qa + qb) * m
    lem2 =
      begin
        a + b
      ≡⟨  cong (λ x → x + b) (DivMod.property (a divMod m)) ⟩ 
        (toℕ ra + qa * m) + b
      ≡⟨  cong (λ x → toℕ ra + qa * m + x) (DivMod.property (b divMod m)) ⟩ 
        (toℕ ra + qa * m) + (toℕ rb + qb * m)
      ≡⟨  lem1 (toℕ ra) (qa * m) (toℕ rb) (qb * m) ⟩ 
        (toℕ ra + toℕ rb) + (qa * m + qb * m)
      ≡⟨  cong (λ x → toℕ ra + toℕ rb + x) (sym (distribʳ-*-+ m qa qb)) ⟩ 
        toℕ ra + toℕ rb + (qa + qb) * m
      ∎

mod-dist-* : ∀ {n} a b → (a * b) mod (suc n) ≡ (toℕ (a mod (suc n)) * toℕ (b mod (suc n))) mod (suc n)
mod-dist-* {n} a b = mod-lemma (a * b) (toℕ ra * toℕ rb) (toℕ ra * qb + qa * toℕ rb + qa * m * qb) lem2
  where
    open ≡-Reasoning
    m = 1 + n
    qa = a div m
    qb = b div m
    ra = a mod m
    rb = b mod m

    expand-+*+ : ∀ a b c d → (a + b) * (c + d) ≡ a * c + a * d + b * c + b * d
    expand-+*+ a b c d =
      begin
        (a + b) * (c + d)
      ≡⟨ distribʳ-*-+ (c + d) a b ⟩
        a * (c + d) + b * (c + d)
      ≡⟨ cong (λ x → x + b * (c + d)) (distribˡ-*-+ a c d) ⟩
        (a * c + a * d) + b * (c + d)
      ≡⟨ cong (λ x → a * c + a * d + x) (distribˡ-*-+ b c d) ⟩
        (a * c + a * d) + (b * c + b * d)
      ≡⟨ sym (+-assoc (a * c + a * d) (b * c) (b * d)) ⟩
        ((a * c + a * d) + b * c) + b * d
      ∎

    lem1 : toℕ ra * (qb * m) + (((qa * m) * toℕ rb) + (qa * m) * (qb * m)) ≡ (toℕ ra * qb + qa * toℕ rb + qa * m * qb) * m
    lem1 =
      begin
        toℕ ra * (qb * m) + (((qa * m) * toℕ rb) + (qa * m) * (qb * m))
      ≡⟨ sym (+-assoc (toℕ ra * (qb * m)) (qa * m * toℕ rb) (qa * m * (qb * m))) ⟩
        (toℕ ra * (qb * m) + (qa * m) * toℕ rb) + (qa * m) * (qb * m)
      ≡⟨ cong (λ x → toℕ ra * (qb * m) + qa * m * toℕ rb + x) (sym (*-assoc (qa * m) qb m)) ⟩
        (toℕ ra * (qb * m) + (qa * m) * toℕ rb) + ((qa * m) * qb) * m
      ≡⟨ cong (λ x → x + qa * m * toℕ rb + qa * m * qb * m) (sym (*-assoc (toℕ ra) qb m)) ⟩
        ((toℕ ra * qb) * m + (qa * m) * toℕ rb) + ((qa * m) * qb) * m
      ≡⟨ cong (λ x → toℕ ra * qb * m + x + ((qa * m) * qb) * m) (*-assoc qa m (toℕ rb)) ⟩
        ((toℕ ra * qb) * m + qa * (m * toℕ rb)) + ((qa * m) * qb) * m
      ≡⟨ cong (λ x → toℕ ra * qb * m + qa * x + qa * m * qb * m) (*-comm m (toℕ rb)) ⟩
        ((toℕ ra * qb) * m + qa * (toℕ rb * m)) + ((qa * m) * qb) * m
      ≡⟨ cong (λ x → toℕ ra * qb * m + x + qa * m * qb * m) (sym (*-assoc qa (toℕ rb) m)) ⟩
        ((toℕ ra * qb) * m + (qa * toℕ rb) * m) + ((qa * m) * qb) * m
      ≡⟨ cong (λ x → x + qa * m * qb * m) (sym (distribʳ-*-+ m (toℕ ra * qb) (qa * toℕ rb))) ⟩
        ((toℕ ra * qb) + (qa * toℕ rb)) * m + ((qa * m) * qb) * m
      ≡⟨ sym (distribʳ-*-+ m (toℕ ra * qb + qa * toℕ rb) (qa * m * qb)) ⟩
        (((toℕ ra * qb) + (qa * toℕ rb)) + ((qa * m) * qb)) * m
      ∎

    lem2 : a * b ≡ toℕ ra * toℕ rb + (toℕ ra * qb + qa * toℕ rb + qa * m * qb) * m
    lem2 =
      begin
        a * b
      ≡⟨ cong (λ x → x * b) (DivMod.property (a divMod m)) ⟩ 
        (toℕ ra + qa * m) * b
      ≡⟨ cong (λ x → (toℕ ra + qa * m) * x) (DivMod.property (b divMod m)) ⟩ 
        (toℕ ra + qa * m) * (toℕ rb + qb * m)
      ≡⟨ expand-+*+ (toℕ ra) (qa * m) (toℕ rb) (qb * m) ⟩
        toℕ ra * toℕ rb + toℕ ra * (qb * m) + (qa * m) * toℕ rb + (qa * m) * (qb * m)
      ≡⟨ +-assoc (toℕ ra * toℕ rb + toℕ ra * (qb * m)) (qa * m * toℕ rb) (qa * m * (qb * m)) ⟩
        (toℕ ra * toℕ rb + toℕ ra * (qb * m)) + ((qa * m) * toℕ rb + (qa * m) * (qb * m))
      ≡⟨ +-assoc (toℕ ra * toℕ rb) (toℕ ra * (qb * m)) (qa * m * toℕ rb + qa * m * (qb * m)) ⟩
        toℕ ra * toℕ rb + (toℕ ra * (qb * m) + (((qa * m) * toℕ rb) + (qa * m) * (qb * m)))
      ≡⟨ cong (λ x → toℕ ra * toℕ rb + x) lem1 ⟩
        toℕ ra * toℕ rb + (toℕ ra * qb + qa * toℕ rb + qa * m * qb) * m
      ∎

-- ---------------------------------------------------------------------------
-- Definition of _² and its properties

_² : ℕ → ℕ
_² n = n * n

distrib-²-* : ∀ m n → (m * n) ² ≡ m ² * n ²
distrib-²-* m n =
  begin
    (m * n) ²
  ≡⟨ refl ⟩
    (m * n) * (m * n)
  ≡⟨ *-assoc m n (m * n) ⟩
    m * (n * (m * n))
  ≡⟨ cong (λ x → m * x) (*-comm n (m * n)) ⟩
    m * ((m * n) * n)
  ≡⟨ cong (λ x → m * x) (*-assoc m n n) ⟩
    m * (m * (n * n))
  ≡⟨ sym (*-assoc m m (n * n)) ⟩
    (m * m) * (n * n)
  ≡⟨ refl ⟩
    m ² * n ²
  ∎
  where
    open ≡-Reasoning

∣⇒²∣² : ∀ {a n} → (suc n ∣ a) → ((suc n) ² ∣ a ²)
∣⇒²∣² {a} {n} 1+n∣a = *∣* 1+n∣a 1+n∣a

-- ---------------------------------------------------------------------------
-- Lemmas specific to modulo-3 arithmetic

-- TODO: use primality of 3 instead of enumerating cases of "a mod 3" and "b mod 3"
3∣*-split : ∀ a b → (3 ∣ a * b) → (3 ∣ a) ⊎ (3 ∣ b)
3∣*-split a b (divides q a*b≡q*3) = body
  where
    open ≡-Reasoning

    lem1 : (toℕ (a mod 3) * toℕ (b mod 3)) mod 3 ≡ Fin.zero
    lem1 = begin
          (toℕ (a mod 3) * toℕ (b mod 3)) mod 3
        ≡⟨ sym (mod-dist-* a b) ⟩
          (a * b) mod 3
        ≡⟨ cong (λ x → x mod 3) a*b≡q*3 ⟩
          (q * 3) mod 3
        ≡⟨ cong (λ x → x mod 3) (*-comm q 3) ⟩
          (3 * q) mod 3
        ≡⟨ mod-dist-* 3 q ⟩
          Fin.zero
        ∎

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
    a²mod3≡0 with prop1 a
    ... | inj₁ p = p
    ... | inj₂ p with prop1 b
    ...     | inj₁ q = ⊥-elim (1≢0 1≡0)
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
    ...     | inj₂ q = ⊥-elim (2≢0 2≡0)
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
prop2b a b c a²+b²≡3c² = prop2a b a c b²+a²≡3*c²
  where
    open ≡-Reasoning

    b²+a²≡3*c² : (b ² + a ² ≡ 3 * c ²)
    b²+a²≡3*c² = begin
        b ² + a ²
      ≡⟨ +-comm (b ²) (a ²) ⟩
        a ² + b ²
      ≡⟨ a²+b²≡3c² ⟩
        3 * c ²
      ∎

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
  prop3-lemma a b c P = cancel-*-right (a ² + b ²) (3 * c ²) lem
    where  
      open ≡-Reasoning

      lem : (a ² + b ²) * 3 ² ≡ (3 * c ²) * 3 ²
      lem = begin
            (a ² + b ²) * 3 ²
          ≡⟨ distribʳ-*-+ (3 ²) (a ²) (b ²) ⟩
            a ² * 3 ² + b ² * 3 ²
          ≡⟨ cong (λ x → x + b ² * 3 ²) (sym (distrib-²-* a 3)) ⟩
            (a * 3) ² + b ² * 3 ²
          ≡⟨ cong (λ x → (a * 3) ² + x) (sym (distrib-²-* b 3)) ⟩
            (a * 3) ² + (b * 3) ²
          ≡⟨ P ⟩
            3 * (c * 3) ²
          ≡⟨ cong (λ x → 3 * x) (distrib-²-* c 3) ⟩
            3 * (c ² * 3 ²)
          ≡⟨ sym (*-assoc 3 (c ²) (3 ²)) ⟩
            (3 * c ²) * 3 ²
          ∎

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
prop3b a b c a²+b²≡3c² = prop3a b a c b²+a²≡3*c²
  where
    open ≡-Reasoning

    b²+a²≡3*c² : b ² + a ² ≡ 3 * c ²
    b²+a²≡3*c² = begin
        b ² + a ²
      ≡⟨ +-comm (b ²) (a ²) ⟩
        a ² + b ²
      ≡⟨ a²+b²≡3c² ⟩
        3 * c ²
      ∎

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
