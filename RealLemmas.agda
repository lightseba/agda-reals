{-# OPTIONS --allow-unsolved-metas #-}

module RealLemmas where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _^_ to _^ₙ_)
open import Data.Nat.Logarithm as ℕ using (⌊log₂_⌋)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base as ℤ using (ℤ; +[1+_]; -[1+_]; 1ℤ)
import Data.Integer.Properties as ℤ
open import Data.Integer.DivMod using ([n/d]*d≤n)
open import Data.Rational.Base as ℚ using (ℚ; _<_; _>_; _/_; 1/_; _≤_; _+_; _-_; -_; _*_; 1ℚ; 0ℚ; ½; toℚᵘ; fromℚᵘ; _⊔_; _⊓_)
import Data.Rational.Properties as ℚ
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; mkℚᵘ; *≡*; *≤*; *<*; 1ℚᵘ; 0ℚᵘ)
  renaming
  ( ↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_; ↧ₙ_ to ↧ₙᵘ_
  ; _≃_ to _≃ᵘ_; _≤_ to _≤ᵘ_; _<_ to _<ᵘ_
  ; _>_ to _>ᵘ_; _≥_ to _≥ᵘ_; _/_ to _/ᵘ_
  ; _+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_
  ; floor to floorᵘ; ceiling to ceilingᵘ
  ; 1/_ to 1/ᵘ_; ½ to ½ᵘ; _≄_ to _≄ᵘ_ 
  )

import Data.Rational.Unnormalised.Properties as ℚᵘ
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; icong; sym; subst; trans; module ≡-Reasoning)
open import Relation.Nullary.Decidable.Core as Dec using (yes; no)

open import Algebra.Definitions {A = ℚ} _≡_

open import Logic

------------------------------------------------------------------------
-- Constants

¼ : ℚ
¼ = 1ℤ / 4

¾ : ℚ
¾ = (ℤ.+ 3) / 4

2ℚ : ℚ
2ℚ = 1ℚ + 1ℚ

3ℚ : ℚ
3ℚ = (ℤ.+ 3) / 1

2ℚᵘ : ℚᵘ
2ℚᵘ = (ℤ.+ 2) /ᵘ 1


------------------------------------------------------------------------
-- Some boring lemmas about rational arithmetic

¾^3<½ : ¾ * ¾ * ¾ < ½
¾^3<½ = fromDec (¾ * ¾ * ¾ ℚ.<? ½)

q-1<q : ∀ (q : ℚ) → q - 1ℚ < q
q-1<q q = begin-strict 
  q - 1ℚ  <⟨ ℚ.+-monoʳ-< q (ℚ.negative⁻¹ (- 1ℚ)) ⟩
  q + 0ℚ  ≡⟨ ℚ.+-identityʳ q ⟩
  q       ∎ where open ℚ.≤-Reasoning

q<q+1 : ∀ (q : ℚ) → q < q + 1ℚ
q<q+1 q = begin-strict 
  q       ≡⟨ ℚ.+-identityʳ q ⟨
  q + 0ℚ  <⟨ ℚ.+-monoʳ-< q (ℚ.positive⁻¹ 1ℚ) ⟩
  q + 1ℚ  ∎ where open ℚ.≤-Reasoning

<-weak-linearity : ∀ q₀ {q r} → q < r → q < q₀ ∨ q₀ < r
<-weak-linearity q₀ {q} q<r with q ℚ.<? q₀
... | yes q<q₀ = left q<q₀
... | no x = right (ℚ.≤-<-trans (ℚ.≮⇒≥ x) q<r)

a<b→0<b-a : ∀ {a b : ℚ} → a < b → 0ℚ < b - a
a<b→0<b-a {a} {b} a<b = begin-strict 
  0ℚ      ≡⟨ ℚ.+-inverseʳ a ⟨
  a - a   <⟨ ℚ.+-monoˡ-< (- a) a<b ⟩
  b - a   ∎ where open ℚ.≤-Reasoning

a<b→a-b<0 : ∀ {a b : ℚ} → a < b → a - b < 0ℚ
a<b→a-b<0 {a} {b} a<b = begin-strict 
  a - b   <⟨ ℚ.+-monoˡ-< (- b) a<b ⟩
  b - b   ≡⟨ ℚ.+-inverseʳ b ⟩
  0ℚ      ∎ where open ℚ.≤-Reasoning
  
0<d→x-d<x : ∀ {d} x → 0ℚ < d → x - d < x
0<d→x-d<x {d} x 0<d = begin-strict
  x - d          ≡⟨ ℚ.+-identityʳ (x - d) ⟨
  x - d + 0ℚ     <⟨ ℚ.+-monoʳ-< (x - d) 0<d ⟩
  (x - d) + d    ≡⟨ ℚ.+-assoc x (- d) d ⟩
  x + (- d + d)  ≡⟨ cong (x +_) (ℚ.+-inverseˡ d) ⟩
  x + 0ℚ         ≡⟨ ℚ.+-identityʳ x ⟩
  x              ∎ where open ℚ.≤-Reasoning

0<d→x<x+d : ∀ {d} x → 0ℚ < d → x < x + d
0<d→x<x+d {d} x 0<d = begin-strict
  x          ≡⟨ ℚ.+-identityʳ x ⟨
  x + 0ℚ     <⟨ ℚ.+-monoʳ-< x 0<d ⟩
  x + d      ∎ where open ℚ.≤-Reasoning

d<0→x<x-d : ∀ {d} x → d < 0ℚ → x < x - d
d<0→x<x-d x 0<d = 0<d→x<x+d x (ℚ.neg-antimono-< 0<d)

split-half : ∀ (x : ℚ) → x ≡ x * ½ + x * ½
split-half x = begin 
  x                     ≡⟨ ℚ.*-identityʳ x ⟨
  x * 1ℚ                ≡⟨ cong (x *_) (ℚ.*-inverseˡ ½) ⟨
  x * (½ * 2ℚ)          ≡⟨ ℚ.*-assoc x ½ 2ℚ ⟨
  x * ½ * 2ℚ            ≡⟨ refl ⟩
  d * (1ℚ + 1ℚ)         ≡⟨ ℚ.*-distribˡ-+ d 1ℚ 1ℚ ⟩
  (d * 1ℚ) + (d * 1ℚ)   ≡⟨ cong ((d * 1ℚ) +_) (ℚ.*-identityʳ d) ⟩
  (d * 1ℚ) + d          ≡⟨ cong (_+ d) (ℚ.*-identityʳ d) ⟩
  d + d                 ∎
  where 
  open ≡-Reasoning
  d = x * ½

neg-involutive : (x : ℚ) → - (- x) ≡ x
neg-involutive x = sym (begin
  x                       ≡⟨ ℚ.+-identityʳ x ⟨
  x - 0ℚ                  ≡⟨ cong (_-_ x) (ℚ.+-inverseʳ x) ⟨
  x - (x - x)             ≡⟨ cong (x +_) (ℚ.neg-distrib-+ x (- x)) ⟩
  x + (- x + - (- x))     ≡⟨ ℚ.+-assoc x (- x) (- (- x)) ⟨
  (x + - x) + - (- x)     ≡⟨ cong (_+ - (- x)) (ℚ.+-inverseʳ x) ⟩
  0ℚ + - (- x)            ≡⟨ ℚ.+-identityˡ (- (- x)) ⟩
  - (- x)                 ∎)
  where open ≡-Reasoning

distrib-diff : ∀ q x a b → x ≡ a + b → q ≡ (a - (x - q) * ½) + (b - (x - q) * ½)
distrib-diff q x a b x=a+b = q=a'+b'
  where
  d = (x - q) * ½
  q=a'+b' = begin
    q                     ≡⟨ ℚ.+-identityˡ q ⟨
    0ℚ + q                ≡⟨ cong (_+ q) (ℚ.+-inverseʳ x) ⟨
    x - x + q             ≡⟨ ℚ.+-assoc x (- x) q ⟩
    x + (- x + q)         ≡⟨ cong (λ x₁ → x + (- x + x₁)) (neg-involutive q) ⟨
    x + (- x - (- q))     ≡⟨ cong (x +_) (ℚ.neg-distrib-+ x  (- q)) ⟨
    x - (x - q)           ≡⟨ cong (_-_ x) (split-half (x - q)) ⟩
    x - (d + d)           ≡⟨ cong (x +_) (ℚ.neg-distrib-+ d d) ⟩
    x + (- d - d)         ≡⟨ ℚ.+-assoc x (- d) (- d) ⟨
    x - d - d             ≡⟨ cong (λ x₁ → x₁ - d - d) x=a+b ⟩
    a + b - d - d         ≡⟨ cong (_- d) (ℚ.+-assoc a b (- d))  ⟩
    a + (b - d) - d       ≡⟨ cong (λ x₁ → a + x₁ - d) (ℚ.+-comm b (- d)) ⟩
    a + (- d + b) - d     ≡⟨ cong (_- d) (ℚ.+-assoc a (- d) b) ⟨
    a - d + b - d         ≡⟨ refl ⟩
    (a - d) + b - d       ≡⟨ ℚ.+-assoc (a - d) b (- d) ⟩
    (a - d) + (b - d)     ∎ where open ≡-Reasoning


-- refine-lemma₁ : ∀ a b → a + (b - a) * ¼ + (b - a) * ½ ≡ b - (b - a) * ¼
-- refine-lemma₁ = solve-∀

eps-eq : ∀ ε → ε - ε * ¼ ≡ ε * ¾
eps-eq ε = begin
  ε - ε/4             ≡⟨ cong (ε +_) (ℚ.neg-distribʳ-* ε ¼) ⟩
  ε + ε * (- ¼)       ≡⟨ cong (_+ ε * (- ¼)) (ℚ.*-identityʳ ε) ⟨
  ε * 1ℚ + ε * (- ¼)  ≡⟨ ℚ.*-distribˡ-+ ε 1ℚ (- ¼) ⟨
  ε * ¾               ∎
  where 
  open ≡-Reasoning
  ε/4 = ε * ¼


u<v : ∀ {a b} → a < b → a + (b - a) * ¼ < b - (b - a) * ¼ 
u<v {a} {b} a<b = begin-strict
  a + ε/4             ≡⟨ ℚ.+-identityʳ (a + ε/4) ⟨
  a + ε/4 + 0ℚ        <⟨ ℚ.+-monoʳ-< (a + ε/4) ε/2>0 ⟩ 
  a + ε/4 + ε/2       ≡⟨ ℚ.+-assoc a ε/4 ε/2 ⟩ 
  a + (ε/4 + ε/2)     ≡⟨ cong (a +_) (ℚ.*-distribˡ-+ ε ¼ ½) ⟨
  a + ε * ¾           ≡⟨ cong (a +_) (eps-eq ε) ⟨
  a + (ε - ε/4)       ≡⟨ ℚ.+-assoc a ε (- ε/4) ⟨
  a + (b - a) - ε/4   ≡⟨ cong (_- ε/4) (ℚ.+-comm a (b - a)) ⟩ 
  b - a + a - ε/4     ≡⟨ cong (_- ε/4) (ℚ.+-assoc b (- a) a) ⟩ 
  b + (- a + a) - ε/4 ≡⟨ cong (λ x₁ → b + x₁ - ε/4) (ℚ.+-inverseˡ a) ⟩ 
  b + 0ℚ - ε/4        ≡⟨ cong (_- ε/4) (ℚ.+-identityʳ b) ⟩ 
  b - ε/4       ∎
  where 
    open ℚ.≤-Reasoning
    ε = (b - a)
    ε/2 = (b - a) * ½
    ε/4 = (b - a) * ¼
    ε/2>0 = ℚ.*-monoˡ-<-pos ½ (a<b→0<b-a a<b)


-- pattern matching FTW!
1/-mono-* : ∀ p q .{{_ : ℚᵘ.Positive p}} .{{_ : ℚᵘ.Positive q}} → (1/ᵘ (p *ᵘ q)) {{ℚᵘ.pos⇒nonZero (p *ᵘ q) {{ℚᵘ.pos*pos⇒pos p q}}}} ≡ (1/ᵘ p) {{ℚᵘ.pos⇒nonZero p}} *ᵘ (1/ᵘ q) {{ℚᵘ.pos⇒nonZero q}}
1/-mono-* (mkℚᵘ +[1+ _ ] _) (mkℚᵘ +[1+ _ ] _) = refl

1/-antimono-<-pos : ∀ {p q} .{{_ : ℚᵘ.Positive p}} .{{_ : ℚᵘ.Positive q}} → p <ᵘ q → (1/ᵘ q) {{ℚᵘ.pos⇒nonZero q}} <ᵘ (1/ᵘ p) {{ℚᵘ.pos⇒nonZero p}}
1/-antimono-<-pos {p@(mkℚᵘ +[1+ _ ] _)} {q@(mkℚᵘ +[1+ _ ] _)} (*<* lhs<rhs) = *<* (begin-strict
  ↧ᵘ q ℤ.* ↥ᵘ p ≡⟨ ℤ.*-comm (↧ᵘ q) (↥ᵘ p) ⟩
  ↥ᵘ p ℤ.* ↧ᵘ q <⟨ lhs<rhs ⟩
  ↥ᵘ q ℤ.* ↧ᵘ p ≡⟨ ℤ.*-comm (↥ᵘ q) (↧ᵘ p) ⟩
  ↧ᵘ p ℤ.* ↥ᵘ q ∎)
  where open ℤ.≤-Reasoning

fromℚᵘ-mono-< : ∀ {p q} → p <ᵘ q → fromℚᵘ p < fromℚᵘ q
fromℚᵘ-mono-< {p} {q} p<q = ℚ.toℚᵘ-cancel-< (begin-strict
  toℚᵘ (fromℚᵘ p) ≃⟨ ℚ.toℚᵘ-fromℚᵘ p ⟩
  p               <⟨ p<q ⟩
  q               ≃⟨ ℚ.toℚᵘ-fromℚᵘ q ⟨
  toℚᵘ (fromℚᵘ q) ∎)
  where open ℚᵘ.≤-Reasoning

*-cancel-neg : ∀ p q → p * q ≡ - p * - q
*-cancel-neg p q = begin
  p * q           ≡⟨ neg-involutive (p * q) ⟨
  - (- (p * q))   ≡⟨ cong -_ (ℚ.neg-distribˡ-* p q) ⟩
  - (- p * q)     ≡⟨ ℚ.neg-distribʳ-* (- p) q ⟩
  - p * - q       ∎ where open ≡-Reasoning
  
pos*pos⇒pos : ∀ p q .{{_ : ℚ.Positive p}} .{{_ : ℚ.Positive q}} → ℚ.Positive (p * q)
pos*pos⇒pos p@record{} q@record{} = ℚ.positive (begin-strict 
  0ℚ                              ≡⟨ refl ⟩
  fromℚᵘ 0ℚᵘ                      <⟨ fromℚᵘ-mono-< (ℚᵘ.positive⁻¹ ((toℚᵘ p) *ᵘ (toℚᵘ q))) ⟩
  fromℚᵘ ((toℚᵘ p) *ᵘ (toℚᵘ q))   ≡⟨ ℚ.fromℚᵘ-cong (ℚ.toℚᵘ-homo-* p q) ⟨
  fromℚᵘ (toℚᵘ (p * q))           ≡⟨ ℚ.fromℚᵘ-toℚᵘ (p * q) ⟩
  p * q                           ∎)
  where 
  open ℚ.≤-Reasoning
  instance
    _ : ℚᵘ.Positive ((toℚᵘ p) *ᵘ (toℚᵘ q))
    _ = ℚᵘ.pos*pos⇒pos (toℚᵘ p) (toℚᵘ q)


neg*neg⇒pos : ∀ p q .{{_ : ℚ.Negative p}} .{{_ : ℚ.Negative q}} → ℚ.Positive (p * q)
neg*neg⇒pos p@(ℚ.mkℚ -[1+ _ ] _ _) q@(ℚ.mkℚ -[1+ _ ] _ _) = subst ℚ.Positive eq -p*-q-pos
  where
  -p*-q-pos = pos*pos⇒pos (- p) (- q)
  eq = sym (*-cancel-neg p q)

-- pos*neg⇒neg : ∀ p q .{{_ : ℚ.Positive p}} .{{_ : ℚ.Negative q}} → ℚ.Negative (p * q)
-- pos*neg⇒neg = {!   !}

-- neg*pos⇒neg : ∀ p q .{{_ : ℚ.Negative p}} .{{_ : ℚ.Positive q}} → ℚ.Negative (p * q)
-- neg*pos⇒neg p q = subst ℚ.Negative eq q*p-neg
--   where
--   q*p-neg = pos*neg⇒neg q p
--   eq = ℚ.*-comm q p


------------------------------------------------------------------------
-- Rational exponentiation

pow : ℕ → ℚ → ℚ
pow zero _ = 1ℚ
pow (suc n) a = a * pow n a

a>0→pow>0 : ∀ n a .{{_ : ℚ.Positive a}} → pow n a > 0ℚ
a>0→pow>0 zero _ = ℚ.positive⁻¹ 1ℚ
a>0→pow>0 (suc n) a = begin-strict
  0ℚ              ≡⟨ ℚ.*-zeroʳ a ⟨
  a * 0ℚ          <⟨ ℚ.*-monoʳ-<-pos a (a>0→pow>0 n a) ⟩
  a * pow n a     ≡⟨ refl ⟩
  pow (suc n) a   ∎ where open ℚ.≤-Reasoning

pow-pos : ∀ n a .{{_ : ℚ.Positive a}} → ℚ.Positive (pow n a)
pow-pos n a = ℚ.positive (a>0→pow>0 n a)

pow-bound : ∀ n → pow (n *ₙ 3) ¾ ≤ pow n ½
pow-bound zero = ℚ.≤-refl
pow-bound (suc n) = begin
  pow ((suc n) *ₙ 3) ¾ ≡⟨ refl ⟩
  ¾ * (¾ * (¾ * pow (n *ₙ 3) ¾))  ≡⟨ cong (¾ *_) (ℚ.*-assoc ¾ ¾ (pow (n *ₙ 3) ¾)) ⟨
  ¾ * ((¾ * ¾) * pow (n *ₙ 3) ¾)  ≡⟨ ℚ.*-assoc ¾ (¾ * ¾) (pow (n *ₙ 3) ¾) ⟨
  ¾ * (¾ * ¾) * pow (n *ₙ 3) ¾    ≡⟨ cong (_* pow (n *ₙ 3) ¾) (ℚ.*-assoc ¾ ¾ ¾) ⟨
  (¾ * ¾ * ¾) * pow (n *ₙ 3) ¾    <⟨ ℚ.*-monoˡ-<-pos (pow (n *ₙ 3) ¾) ¾^3<½  ⟩
  ½ * pow (n *ₙ 3) ¾              ≤⟨ ℚ.*-monoˡ-≤-nonNeg ½ (pow-bound n) ⟩
  ½ * pow n ½                     ≡⟨ refl ⟩
  pow (suc n) ½                   ∎ 
  where 
  open ℚ.≤-Reasoning 
  instance 
    _ = pow-pos (n *ₙ 3) ¾

------------------------------------------------------------------------
-- Unnormalised rational exponentiation

powᵘ : ℕ → ℚᵘ → ℚᵘ
powᵘ zero _ = 1ℚᵘ
powᵘ (suc n) a = a *ᵘ powᵘ n a

powᵘ-pos : ∀ n a .{{_ : ℚᵘ.Positive a}} → ℚᵘ.Positive (powᵘ n a)
powᵘ-pos zero _ = _
powᵘ-pos (suc n) a = ℚᵘ.pos*pos⇒pos a (powᵘ n a)
  where instance _ = powᵘ-pos n a

powᵘ-inverse : ∀ n a .{{_ : ℚᵘ.Positive a}} → (1/ᵘ (powᵘ n a)) {{ℚᵘ.pos⇒nonZero (powᵘ n a) {{powᵘ-pos n a}}}} ≡ powᵘ n ((1/ᵘ a) {{ℚᵘ.pos⇒nonZero a}})
powᵘ-inverse zero _ = refl 
powᵘ-inverse (suc n) a = begin
  1/ᵘ (powᵘ (suc n) a)      ≡⟨ refl ⟩
  1/ᵘ (a *ᵘ powᵘ n a)       ≡⟨ 1/-mono-* a (powᵘ n a) ⟩
  1/ᵘ a *ᵘ 1/ᵘ powᵘ n a     ≡⟨ cong (1/ᵘ a *ᵘ_) (powᵘ-inverse n a) ⟩
  1/ᵘ a *ᵘ powᵘ n (1/ᵘ a)   ≡⟨ refl ⟩
  powᵘ (suc n) (1/ᵘ a)      ∎
  where 
  open ≡-Reasoning
  instance
    _ = powᵘ-pos n a
    _ = powᵘ-pos (suc n) a
    _ = ℚᵘ.pos⇒nonZero a
    _ = ℚᵘ.pos⇒nonZero (powᵘ (suc n) a)
    _ = ℚᵘ.pos⇒nonZero (powᵘ n a)

powᵘ-cong : ∀ n {a b} → a ≃ᵘ b → powᵘ n a ≃ᵘ powᵘ n b
powᵘ-cong zero _ = *≡* refl
powᵘ-cong (suc n) {a} {b} a=b = begin 
  powᵘ (suc n) a    ≡⟨ refl ⟩
  a *ᵘ (powᵘ n a)   ≈⟨ ℚᵘ.*-congʳ a=b ⟩
  b *ᵘ (powᵘ n a)   ≈⟨ ℚᵘ.*-congˡ {b} (powᵘ-cong n {a} {b} a=b) ⟩
  b *ᵘ (powᵘ n b)   ≡⟨ refl ⟩
  powᵘ (suc n) b    ∎ where open ℚᵘ.≃-Reasoning


------------------------------------------------------------------------
-- Properties of toℚᵘ/fromℚᵘ and pow

toℚᵘ-homo-pow : ∀ n a → toℚᵘ (pow n a) ≃ᵘ powᵘ n (toℚᵘ a)
toℚᵘ-homo-pow zero _ = *≡* refl
toℚᵘ-homo-pow (suc n) a = begin
  toℚᵘ (pow (suc n) a)            ≡⟨ refl ⟩
  toℚᵘ (a * (pow n a))            ≈⟨ ℚ.toℚᵘ-homo-* a (pow n a) ⟩
  (toℚᵘ a) *ᵘ (toℚᵘ (pow n a))    ≈⟨ ℚᵘ.*-congˡ {toℚᵘ a} (toℚᵘ-homo-pow n a) ⟩
  (toℚᵘ a) *ᵘ (powᵘ n (toℚᵘ a))   ≡⟨ refl ⟩
  powᵘ (suc n) (toℚᵘ a)           ∎ where open ℚᵘ.≃-Reasoning

fromℚᵘ-homo-pow : ∀ n a → fromℚᵘ (powᵘ n a) ≡ pow n (fromℚᵘ a)
fromℚᵘ-homo-pow n a = begin 
  fromℚᵘ (powᵘ n a)                   ≡⟨ ℚ.fromℚᵘ-cong (powᵘ-cong n (ℚ.toℚᵘ-fromℚᵘ a)) ⟨
  fromℚᵘ (powᵘ n (toℚᵘ (fromℚᵘ a)))   ≡⟨ ℚ.fromℚᵘ-cong (toℚᵘ-homo-pow n (fromℚᵘ a)) ⟨
  fromℚᵘ (toℚᵘ (pow n (fromℚᵘ a)))    ≡⟨ ℚ.fromℚᵘ-toℚᵘ (pow n (fromℚᵘ a)) ⟩
  pow n (fromℚᵘ a)                    ∎ where open ≡-Reasoning



⌊x⌋ᵘ≤x : ∀ x → (floorᵘ x) /ᵘ 1 ≤ᵘ x
⌊x⌋ᵘ≤x x@record{} = *≤* (begin
  ((↥ᵘ x) ℤ./ (↧ᵘ x)) ℤ.* ↧ᵘ x  ≤⟨ [n/d]*d≤n (↥ᵘ x) (↧ᵘ x) ⟩
  ↥ᵘ x                          ≡⟨ ℤ.*-identityʳ (↥ᵘ x) ⟨
  (↥ᵘ x) ℤ.* 1ℤ                 ∎)
  where open ℤ.≤-Reasoning

x≤⌈x⌉ᵘ : ∀ x → x ≤ᵘ (ceilingᵘ x) /ᵘ 1
x≤⌈x⌉ᵘ x@record{} = *≤* (begin
  ↥ᵘ x ℤ.* 1ℤ                         ≡⟨ ℤ.*-identityʳ (↥ᵘ x) ⟩
  ↥ᵘ x                                ≡⟨ ℤ.neg-involutive (↥ᵘ x) ⟨
  ℤ.- (ℤ.- (↥ᵘ x))                    ≡⟨ refl ⟩
  ℤ.- (↥ᵘ (-ᵘ x))                     ≤⟨ ℤ.neg-mono-≤ ([n/d]*d≤n (↥ᵘ (-ᵘ x)) (↧ᵘ (-ᵘ x))) ⟩  
  ℤ.- ((floorᵘ (-ᵘ x)) ℤ.* ↧ᵘ (-ᵘ x)) ≡⟨ refl ⟩
  ℤ.- ((floorᵘ (-ᵘ x)) ℤ.* ↧ᵘ x)      ≡⟨ ℤ.neg-distribˡ-* (floorᵘ (-ᵘ x)) (↧ᵘ x) ⟩
  (ceilingᵘ x) ℤ.* ↧ᵘ x               ∎)
  where open ℤ.≤-Reasoning

n<2^[1+⌊log₂n⌋] : ∀ n → n ℕ.< 2 ℕ.^ (suc ⌊log₂ n ⌋)
n<2^[1+⌊log₂n⌋] n with n ℕ.<? (2 ℕ.^ (suc ⌊log₂ n ⌋))
... | yes res = res
... | no ¬res = ⊥-elim (ℕ.<⇒≱ 1+k>k 1+k≤k)
  where
  k = ⌊log₂ n ⌋
  1+k≤k : suc k ℕ.≤ k
  1+k≤k = begin
    suc k                 ≡⟨ ℕ.⌊log₂[2^n]⌋≡n (suc k) ⟨
    ⌊log₂ 2 ℕ.^ (suc k) ⌋ ≤⟨ ℕ.⌊log₂⌋-mono-≤ (ℕ.≮⇒≥ ¬res) ⟩
    k                     ∎
    where open ℕ.≤-Reasoning
  1+k>k = ℕ.n<1+n k

pows-same : ∀ a n → (ℤ.+ (a ^ₙ n)) /ᵘ 1 ≡ powᵘ n (ℤ.+ a /ᵘ 1)
pows-same _ zero = refl
pows-same a (suc n) = begin
  ℤ.+ a ^ₙ suc n /ᵘ 1                     ≡⟨ refl ⟩
  ℤ.+ (a *ₙ (a ℕ.^ n)) /ᵘ 1               ≡⟨ cong (ℚᵘ._/ 1) (ℤ.pos-* a (a ℕ.^ n)) ⟩
  ℤ.+ a ℤ.* ℤ.+ (a ℕ.^ n) /ᵘ 1            ≡⟨ refl ⟩
  ℤ.+ a ℤ.* ℤ.+ (a ℕ.^ n) /ᵘ (1 *ₙ 1)     ≡⟨ refl ⟩
  (ℤ.+ a /ᵘ 1) *ᵘ (ℤ.+ (a ℕ.^ n) /ᵘ 1)  ≡⟨ cong ((ℤ.+ a /ᵘ 1) *ᵘ_) (pows-same a n) ⟩
  powᵘ (suc n) (ℤ.+ a /ᵘ 1)               ∎ where open ≡-Reasoning

-- just doing this out of laziness, 
-- otherwise i have to show x > 0 → ceiling x ≥ 0, 
-- which gets annoying
i≤+|i| : ∀ i → i ℤ.≤ ℤ.+ ℤ.∣ i ∣
i≤+|i| i with ℤ.+∣i∣≡i⊎+∣i∣≡-i i
... | left +∣i∣≡i = ℤ.≤-reflexive (sym +∣i∣≡i)
... | right +∣i∣≡-i = begin
  i                   ≡⟨ ℤ.neg-involutive i ⟨
  ℤ.- ℤ.- i           ≡⟨ cong  ℤ.-_ +∣i∣≡-i ⟨
  ℤ.- (ℤ.+ ℤ.∣ i ∣)   ≤⟨ ℤ.neg-≤-pos ⟩
  ℤ.+ ℤ.∣ i ∣         ∎ where open ℤ.≤-Reasoning 

/d-mono-≤ᵘ : ∀ {i j} d .{{_ : ℕ.NonZero d}} → i ℤ.≤ j → (i /ᵘ d) ≤ᵘ (j /ᵘ d)
/d-mono-≤ᵘ (suc d) i≤j = *≤* (ℤ.*-monoʳ-≤-nonNeg (ℤ.+ (suc d)) i≤j)

/d-mono-<ᵘ : ∀ {i j} d .{{_ : ℕ.NonZero d}} → i ℤ.< j → (i /ᵘ d) <ᵘ (j /ᵘ d)
/d-mono-<ᵘ (suc d) i≤j = ℚᵘ.*<* (ℤ.*-monoʳ-<-pos (ℤ.+ (suc d)) i≤j)

x<2^[1+lg⌈x⌉]ᵘ : ∀ x → x <ᵘ powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ x) ∣) ⌋) 2ℚᵘ
x<2^[1+lg⌈x⌉]ᵘ x = begin-strict
  x                                                     ≤⟨ x≤⌈x⌉ᵘ x ⟩
  (ceilingᵘ x) /ᵘ 1                                   ≤⟨ /d-mono-≤ᵘ 1 (i≤+|i| (ceilingᵘ x)) ⟩
  (ℤ.+ ℤ.∣ (ceilingᵘ x) ∣) /ᵘ 1                       <⟨ /d-mono-<ᵘ 1 (ℤ.+<+ (n<2^[1+⌊log₂n⌋] ℤ.∣ (ceilingᵘ x) ∣)) ⟩
  (ℤ.+ (2 ^ₙ (suc ⌊log₂ ℤ.∣ (ceilingᵘ x) ∣ ⌋))) /ᵘ 1   ≡⟨ pows-same 2 (suc ⌊log₂ ℤ.∣ (ceilingᵘ x) ∣ ⌋) ⟩
  powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ x) ∣) ⌋) 2ℚᵘ           ∎ where open ℚᵘ.≤-Reasoning

x>½^[1+lg⌈1/x⌉]ᵘ : ∀ x .{{_ : ℚᵘ.Positive x}} → powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ ((1/ᵘ x) {{ℚᵘ.pos⇒nonZero x}})) ∣) ⌋) ½ᵘ <ᵘ x
x>½^[1+lg⌈1/x⌉]ᵘ x@(mkℚᵘ +[1+ _ ] _) = begin-strict
  powᵘ n ½ᵘ ≡⟨ powᵘ-inverse n 2ℚᵘ ⟨
  1/ᵘ (powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋) 2ℚᵘ) <⟨ 1/-antimono-<-pos weird ⟩
  1/ᵘ (1/ᵘ x)     ≡⟨ ℚᵘ.1/-involutive-≡ x ⟩
  x ∎
  where 
  open ℚᵘ.≤-Reasoning
  n = (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋)
  instance 
    _ : ℚᵘ.NonZero x
    _ = ℚᵘ.pos⇒nonZero x
    _ : ℚᵘ.Positive (powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋) 2ℚᵘ)
    _ = powᵘ-pos (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋) 2ℚᵘ
    _ : ℚᵘ.NonZero (powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋) 2ℚᵘ)
    _ = ℚᵘ.pos⇒nonZero (powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (1/ᵘ x)) ∣) ⌋) 2ℚᵘ)
  
  weird : (1/ᵘ x) <ᵘ (powᵘ n 2ℚᵘ) 
  weird = x<2^[1+lg⌈x⌉]ᵘ (1/ᵘ x)

log½ : ∀ (x : ℚ) .{{_ : ℚ.Positive x}} → ℕ
log½ x = (suc ⌊log₂ (ℤ.∣ (ceilingᵘ (toℚᵘ (1/ x))) ∣) ⌋)
  where instance _ = ℚ.pos⇒nonZero x

refine-steps : ∀ (ε : ℚ) .{{_ : ℚ.Positive ε}} → ℕ
refine-steps ε = (log½ ε) *ₙ 3

pow-log : ∀ ε .{{_ : ℚ.Positive ε}} → pow (refine-steps ε) ¾ < ε
pow-log ε@(ℚ.mkℚ +[1+ _ ] _ _) = begin-strict
  pow (refine-steps ε) ¾          ≤⟨ pow-bound (log½ ε) ⟩
  pow (log½ ε) ½                  ≡⟨ ℚ.fromℚᵘ-toℚᵘ (pow (log½ ε) ½) ⟨
  fromℚᵘ (toℚᵘ (pow (log½ ε) ½))  ≡⟨ ℚ.fromℚᵘ-cong (toℚᵘ-homo-pow (log½ ε) ½) ⟩
  fromℚᵘ (powᵘ (log½ ε) ½ᵘ)       <⟨ fromℚᵘ-mono-< (x>½^[1+lg⌈1/x⌉]ᵘ (toℚᵘ ε)) ⟩
  fromℚᵘ (toℚᵘ ε)                 ≡⟨ ℚ.fromℚᵘ-toℚᵘ ε ⟩
  ε                               ∎
  where 
  open ℚ.≤-Reasoning
  instance
    _ : ℚᵘ.NonZero (toℚᵘ ε)
    _ = ℚᵘ.pos⇒nonZero (toℚᵘ ε)
    _ : ℚᵘ.Positive (powᵘ (log½ ε) 2ℚᵘ)
    _ = powᵘ-pos (log½ ε) 2ℚᵘ
    _ : ℚᵘ.NonZero (powᵘ (log½ ε) 2ℚᵘ)
    _ = ℚᵘ.pos⇒nonZero (powᵘ (log½ ε) 2ℚᵘ)
    _ : ℚᵘ.Positive (1/ᵘ toℚᵘ ε)
    _ = ℚᵘ.1/pos⇒pos (toℚᵘ ε)
    _ : ℚᵘ.NonZero (1/ᵘ toℚᵘ ε)
    _ = ℚᵘ.pos⇒nonZero(1/ᵘ toℚᵘ ε)


------------------------------------------------------------------------
-- Lifting equalities of inequalities

<-equalityℕ : ∀ {m n} (m<n₁ m<n₂ : m ℕ.< n) → m<n₁ ≡ m<n₂
<-equalityℕ {zero} {suc n} (ℕ.s≤s ℕ.z≤n) (ℕ.s≤s ℕ.z≤n) = refl
<-equalityℕ {suc m} {suc n} (ℕ.s≤s m<n₁) (ℕ.s≤s m<n₂) = cong ℕ.s≤s (<-equalityℕ m<n₁ m<n₂)

<-equalityℤ : ∀ {x y} (x<y₁ x<y₂ : x ℤ.< y) → x<y₁ ≡ x<y₂
<-equalityℤ {ℤ.+_ _} {ℤ.+_ _} (ℤ.+<+ m<n₁) (ℤ.+<+ m<n₂) = cong ℤ.+<+ (<-equalityℕ m<n₁ m<n₂)
<-equalityℤ { -[1+ _ ]} {ℤ.+_ _} ℤ.-<+ ℤ.-<+ = refl
<-equalityℤ { -[1+ _ ]} { -[1+ _ ]} (ℤ.-<- n<m₁) (ℤ.-<- n<m₂) = cong ℤ.-<- (<-equalityℕ n<m₁ n<m₂) 

<-equalityℚ : ∀ {p q} (p<q₁ p<q₂ : p < q) → p<q₁ ≡ p<q₂
<-equalityℚ (_<_.*<* l<r₁) (_<_.*<* l<r₂) = cong _<_.*<* (<-equalityℤ l<r₁ l<r₂) 


------------------------------------------------------------------------
-- Lemmas for _*_


<-split-⊓ : ∀ {q} x y → q < x ⊓ y → q < x ∧ q < y
<-split-⊓ {q} x y q<x⊓y = q<x , q<y
  where
  q<x = ℚ.<-≤-trans q<x⊓y (ℚ.p⊓q≤p x y)
  q<y = ℚ.<-≤-trans q<x⊓y (ℚ.p⊓q≤q x y)

<-join-⊓ : ∀ {q x y} → q < x → q < y → q < x ⊓ y
<-join-⊓ {q} {x} {y} q<x q<y with ℚ.⊓-sel x y
... | left x⊓y≡x = ℚ.<-≤-trans q<x (ℚ.≤-reflexive (sym x⊓y≡x))
... | right x⊓y≡y = ℚ.<-≤-trans q<y (ℚ.≤-reflexive (sym x⊓y≡y))

<-split-⊓⁴ : ∀ {q} w x y z → q < w ⊓ x ⊓ y ⊓ z → q < w ∧ q < x ∧ q < y ∧ q < z
<-split-⊓⁴ {q} w x y z q<w⊓x⊓y⊓z = 
  let q<w⊓x⊓y , q<z = <-split-⊓ (w ⊓ x ⊓ y) z q<w⊓x⊓y⊓z
      q<w⊓x , q<y = <-split-⊓ (w ⊓ x) y q<w⊓x⊓y
      q<w , q<x = <-split-⊓ w x q<w⊓x
  in q<w , q<x , q<y , q<z

<-join-⊓⁴ : ∀ {q w x y z} → q < w → q < x → q < y → q < z → q < w ⊓ x ⊓ y ⊓ z
<-join-⊓⁴ {q} {w} {x} {y} {z} q<w q<x q<y q<z = q<w⊓x⊓y⊓z
  where
  q<w⊓x = <-join-⊓ q<w q<x
  q<w⊓x⊓y = <-join-⊓ q<w⊓x q<y
  q<w⊓x⊓y⊓z = <-join-⊓ q<w⊓x⊓y q<z

⊓-⊔-mono-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a ⊓ c ≤ b ⊔ d
⊓-⊔-mono-≤ {a} {b} {c} {d} a≤b c≤d = begin
  a ⊓ c ≤⟨ ℚ.⊓-mono-≤ a≤b c≤d ⟩
  b ⊓ d ≤⟨ ℚ.p⊓q≤p⊔q b d ⟩
  b ⊔ d ∎ where open ℚ.≤-Reasoning

-- <-split-⊓ˡ : ∀ {q} x y → q < x ⊓ y → q < x
-- <-split-⊓ˡ x y q<x⊓y = proj₁ (<-split-⊓ x y q<x⊓y)

-- <-split-⊓ʳ : ∀ {q} x y → q < x ⊓ y → q < y
-- <-split-⊓ʳ x y q<x⊓y = proj₂ (<-split-⊓ x y q<x⊓y)

>-split-⊔ : ∀ {q} x y → q > x ⊔ y → q > x ∧ q > y
>-split-⊔ {q} x y q>x⊔y = q>x , q>y
  where 
  q>x = ℚ.≤-<-trans (ℚ.p≤p⊔q x y) q>x⊔y
  q>y = ℚ.≤-<-trans (ℚ.p≤q⊔p x y) q>x⊔y

>-join-⊔ : ∀ {q x y} → q > x → q > y → q > x ⊔ y
>-join-⊔ {q} {x} {y} q>x q>y with ℚ.⊔-sel x y
... | left x⊔y≡x = ℚ.≤-<-trans (ℚ.≤-reflexive x⊔y≡x) q>x
... | right x⊔y≡y = ℚ.≤-<-trans (ℚ.≤-reflexive x⊔y≡y) q>y


*-lo : ℚ → ℚ → ℚ → ℚ → ℚ
*-lo a b c d = (a * c) ⊓ (a * d) ⊓ (b * c) ⊓ (b * d)
*-hi : ℚ → ℚ → ℚ → ℚ → ℚ
*-hi a b c d = a * c ⊔ a * d ⊔ b * c ⊔ b * d

variable
  _∘_ : ℚ → ℚ → ℚ
infixl 6 _∘_
*-lo-hi-comm : ∀ a b c d → Associative _∘_ → Commutative _∘_ → 
  a * c ∘ a * d ∘ b * c ∘ b * d ≡ c * a ∘ c * b ∘ d * a ∘ d * b
*-lo-hi-comm {_∘_} a b c d ◻-assoc ◻-comm = begin
  a * c ◻ a * d ◻ b * c ◻ b * d     ≡⟨ cong (_◻ (b * d)) (◻-assoc (a * c) (a * d) (b * c)) ⟩
  a * c ◻ (a * d ◻ b * c) ◻ b * d   ≡⟨ cong (λ x → a * c ◻ x ◻ b * d) (◻-comm (a * d) (b * c)) ⟩
  a * c ◻ (b * c ◻ a * d) ◻ b * d   ≡⟨ cong (_◻ (b * d)) (◻-assoc (a * c) (b * c) (a * d)) ⟨
  a * c ◻ b * c ◻ a * d ◻ b * d     ≡⟨ cong (λ x → x ◻ b * c ◻ a * d ◻ b * d) (ℚ.*-comm a c) ⟩
  c * a ◻ b * c ◻ a * d ◻ b * d     ≡⟨ cong (λ x → c * a ◻ x ◻ a * d ◻ b * d) (ℚ.*-comm b c) ⟩
  c * a ◻ c * b ◻ a * d ◻ b * d     ≡⟨ cong (λ x → c * a ◻ c * b ◻ x ◻ b * d) (ℚ.*-comm a d) ⟩
  c * a ◻ c * b ◻ d * a ◻ b * d     ≡⟨ cong (c * a ◻ c * b ◻ d * a ◻_) (ℚ.*-comm b d) ⟩
  c * a ◻ c * b ◻ d * a ◻ d * b     ∎ where open ≡-Reasoning; infixl 6 _◻_; _◻_ = _∘_

*-lo-hi-neg : ∀ a b c d → Associative _∘_ → Commutative _∘_ → 
  a * c ∘ a * d ∘ b * c ∘ b * d ≡ - b * - d ∘ - b * - c ∘ - a * - d ∘ - a * - c
*-lo-hi-neg {_∘_} a b c d ◻-assoc ◻-comm = begin
  a * c ◻ a * d ◻ b * c ◻ b * d                       ≡⟨ cong (λ x → x ◻ a * d ◻ b * c ◻ b * d) (*-cancel-neg a c) ⟩
  - a * - c ◻ a * d ◻ b * c ◻ b * d                   ≡⟨ cong (λ x → - a * - c ◻ x ◻ b * c ◻ b * d) (*-cancel-neg a d) ⟩
  - a * - c ◻ - a * - d ◻ b * c ◻ b * d               ≡⟨ cong (λ x → - a * - c ◻ - a * - d ◻ x ◻ b * d) (*-cancel-neg b c) ⟩
  - a * - c ◻ - a * - d ◻ - b * - c ◻ b * d           ≡⟨ cong (- a * - c ◻ - a * - d ◻ - b * - c ◻_) (*-cancel-neg b d) ⟩
  - a * - c ◻ - a * - d ◻ - b * - c ◻ - b * - d       ≡⟨ ◻-comm (- a * - c ◻ - a * - d ◻ - b * - c) (- b * - d) ⟩
  - b * - d ◻ (- a * - c ◻ - a * - d ◻ - b * - c)     ≡⟨ cong (- b * - d ◻_) (◻-comm (- a * - c ◻ - a * - d) (- b * - c)) ⟩
  - b * - d ◻ (- b * - c ◻ (- a * - c ◻ - a * - d))   ≡⟨ cong (λ x → - b * - d ◻ (- b * - c ◻ x)) (◻-comm (- a * - c) (- a * - d)) ⟩
  - b * - d ◻ (- b * - c ◻ (- a * - d ◻ - a * - c))   ≡⟨ ◻-assoc (- b * - d) (- b * - c)  (- a * - d ◻ - a * - c) ⟨
  - b * - d ◻ - b * - c ◻ (- a * - d ◻ - a * - c)     ≡⟨ ◻-assoc (- b * - d ◻ - b * - c) (- a * - d) (- a * - c) ⟨
  - b * - d ◻ - b * - c ◻ - a * - d ◻ - a * - c       ∎ where open ≡-Reasoning; infixl 6 _◻_; _◻_ = _∘_

*-lo-comm : ∀ a b c d → *-lo a b c d ≡ *-lo c d a b
*-lo-comm a b c d = *-lo-hi-comm a b c d ℚ.⊓-assoc ℚ.⊓-comm

*-hi-comm : ∀ a b c d → *-hi a b c d ≡ *-hi c d a b
*-hi-comm a b c d = *-lo-hi-comm a b c d ℚ.⊔-assoc ℚ.⊔-comm

*-lo-neg : ∀ a b c d → *-lo a b c d ≡ *-lo (- b) (- a) (- d) (- c)
*-lo-neg a b c d = *-lo-hi-neg a b c d  ℚ.⊓-assoc ℚ.⊓-comm

*-hi-neg : ∀ a b c d → *-hi a b c d ≡ *-hi (- b) (- a) (- d) (- c)
*-hi-neg a b c d = *-lo-hi-neg a b c d ℚ.⊔-assoc ℚ.⊔-comm

-p≡p*-1 : ∀ p → - p ≡ p * - 1ℚ
-p≡p*-1 p = begin
  - p         ≡⟨ cong (-_) (ℚ.*-identityʳ p) ⟨
  - (p * 1ℚ)  ≡⟨ ℚ.neg-distribʳ-* p 1ℚ ⟩
  p * - 1ℚ    ∎ where open ≡-Reasoning

neg-distrib-⊓ : ∀ p q → - (p ⊓ q) ≡ (- p) ⊔ (- q)
neg-distrib-⊓ p q = begin
  - (p ⊓ q)               ≡⟨ -p≡p*-1 (p ⊓ q) ⟩
  (p ⊓ q) * - 1ℚ          ≡⟨ ℚ.*-distribʳ-⊓-nonPos (- 1ℚ) p q ⟩
  (p * - 1ℚ) ⊔ (q * - 1ℚ) ≡⟨ cong ((p * - 1ℚ) ⊔_) (-p≡p*-1 q) ⟨
  (p * - 1ℚ) ⊔ (- q)      ≡⟨ cong (_⊔ (- q)) (-p≡p*-1 p) ⟨
  (- p) ⊔ (- q)           ∎ where open ≡-Reasoning
  
neg-distrib-⊔ : ∀ p q → - (p ⊔ q) ≡ (- p) ⊓ (- q)
neg-distrib-⊔ p q = begin
  - (p ⊔ q)               ≡⟨ -p≡p*-1 (p ⊔ q) ⟩
  (p ⊔ q) * - 1ℚ          ≡⟨ ℚ.*-distribʳ-⊔-nonPos (- 1ℚ) p q ⟩
  (p * - 1ℚ) ⊓ (q * - 1ℚ) ≡⟨ cong ((p * - 1ℚ) ⊓_) (-p≡p*-1 q) ⟨
  (p * - 1ℚ) ⊓ (- q)      ≡⟨ cong (_⊓ (- q)) (-p≡p*-1 p) ⟨
  (- p) ⊓ (- q)           ∎ where open ≡-Reasoning
  
*-hi-flipˡ : ∀ a b c d → *-hi a b c d ≡ - (*-lo (- b) (- a) c d)
*-hi-flipˡ a b c d = begin
  *-hi a b c d                                        ≡⟨ neg-involutive (*-hi a b c d) ⟨
  - (- (*-hi a b c d))                                ≡⟨ cong (-_) (neg-distrib-⊔ (a * c ⊔ a * d ⊔ b * c) (b * d)) ⟩
  - (- (a * c ⊔ a * d ⊔ b * c) ⊓ - (b * d))           ≡⟨ cong (λ x → - (x ⊓ - (b * d))) (neg-distrib-⊔ (a * c ⊔ a * d) (b * c)) ⟩
  - (- (a * c ⊔ a * d) ⊓ - (b * c) ⊓ - (b * d))       ≡⟨ cong (λ x → - (x ⊓ - (b * c) ⊓ - (b * d))) (neg-distrib-⊔ (a * c) (a * d)) ⟩
  - (- (a * c) ⊓ - (a * d) ⊓ - (b * c) ⊓ - (b * d))   ≡⟨ cong (-_) (ℚ.⊓-assoc (- (a * c) ⊓ - (a * d)) (- (b * c)) (- (b * d))) ⟩
  - (- (a * c) ⊓ - (a * d) ⊓ (- (b * c) ⊓ - (b * d))) ≡⟨ cong (-_) (ℚ.⊓-comm (- (a * c) ⊓ - (a * d)) (- (b * c) ⊓ - (b * d))) ⟩
  - (- (b * c) ⊓ - (b * d) ⊓ (- (a * c) ⊓ - (a * d))) ≡⟨ cong (-_) (ℚ.⊓-assoc (- (b * c) ⊓ - (b * d)) (- (a * c)) (- (a * d))) ⟨
  - (- (b * c) ⊓ - (b * d) ⊓ - (a * c) ⊓ - (a * d))   ≡⟨ cong (λ x → - (x ⊓ - (b * d) ⊓ - (a * c) ⊓ - (a * d))) (ℚ.neg-distribˡ-* b c) ⟩
  - ((- b * c) ⊓ - (b * d) ⊓ - (a * c) ⊓ - (a * d))   ≡⟨ cong (λ x → - ((- b * c) ⊓ x ⊓ - (a * c) ⊓ - (a * d))) (ℚ.neg-distribˡ-* b d) ⟩
  - ((- b * c) ⊓ (- b * d) ⊓ - (a * c) ⊓ - (a * d))   ≡⟨ cong (λ x → - ((- b * c) ⊓ (- b * d) ⊓ x ⊓ - (a * d))) (ℚ.neg-distribˡ-* a c) ⟩
  - ((- b * c) ⊓ (- b * d) ⊓ (- a * c) ⊓ - (a * d))   ≡⟨ cong (λ x → - ((- b * c) ⊓ (- b * d) ⊓ (- a * c) ⊓ x)) (ℚ.neg-distribˡ-* a d) ⟩
  - (*-lo (- b) (- a) c d)                            ∎ where open ≡-Reasoning

*-hi-flipʳ : ∀ a b c d → *-hi a b c d ≡ - (*-lo a b (- d) (- c))
*-hi-flipʳ a b c d = begin
  *-hi a b c d              ≡⟨ *-hi-comm a b c d ⟩
  *-hi c d a b              ≡⟨ *-hi-flipˡ c d a b ⟩
  - (*-lo (- d) (- c) a b)  ≡⟨ cong (-_) (*-lo-comm (- d) (- c) a b) ⟩
  - (*-lo a b (- d) (- c))  ∎ where open ≡-Reasoning

*-lo-pos-pos : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → 0ℚ ≤ c → *-lo a b c d ≡ a * c
*-lo-pos-pos {a} {b} {c} {d} a<b c<d a≥0 c≥0 = lo≡ac
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  d≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans c≥0 c<d)
  c⊓d≥0 = ℚ.⊓-glb c≥0 d≥0
  instance _ = ℚ.nonNegative a≥0; _ = ℚ.nonNegative b≥0; _ = ℚ.nonNegative c⊓d≥0
  lo≡ac = begin
    *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
    (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≤q⇒p⊓q≡p (ℚ.*-monoʳ-≤-nonNeg (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
    a * (c ⊓ d)                         ≡⟨ cong (a *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    a * c                               ∎ where open ≡-Reasoning

*-lo-pos-nonPos : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → c ≤ 0ℚ → *-lo a b c d ≡ b * c
*-lo-pos-nonPos {a} {b} {c} {d} a<b c<d a≥0 c≤0 = lo≡bc 
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  c⊓d≤0 = ℚ.p≤q⇒p⊓r≤q d c≤0
  instance _ = ℚ.nonNegative a≥0; _ = ℚ.nonNegative b≥0; _ = ℚ.nonPositive c⊓d≤0
  lo≡bc = begin
    *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
    (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≥q⇒p⊓q≡q (ℚ.*-monoʳ-≤-nonPos (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
    b * (c ⊓ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    b * c                               ∎ where open ≡-Reasoning

*-lo-zero-zero : ∀ {a b c d} → a < b → c < d → a ≤ 0ℚ → 0ℚ ≤ b → c ≤ 0ℚ → 0ℚ ≤ d → *-lo a b c d ≡ (a * d) ⊓ (b * c)
*-lo-zero-zero {a} {b} {c} {d} a<b c<d a≤0 b≥0 c≤0 d≥0 = lo≡ad⊓bc
  where
  instance _ = ℚ.nonPositive a≤0; _ = ℚ.nonNegative b≥0
  lo≡ad⊓bc = begin
    *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊔-nonPos a c d) ⟨
    (a * (c ⊔ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
    (a * (c ⊔ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
    (a * (c ⊔ d)) ⊓ (b * (c ⊓ d))       ≡⟨ cong (λ x → (a * x) ⊓ (b * (c ⊓ d))) (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    (a * d) ⊓ (b * (c ⊓ d))             ≡⟨ cong (λ x → (a * d) ⊓ (b * x)) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    (a * d) ⊓ (b * c)                   ∎ where open ≡-Reasoning

*-lo-nonPos-pos : ∀ {a b c d} → a < b → c < d → a ≤ 0ℚ → 0ℚ ≤ c → *-lo a b c d ≡ a * d
*-lo-nonPos-pos {a} {b} {c} {d} a<b c<d a≤0 c≥0
  rewrite *-lo-comm a b c d = trans lo≡da (ℚ.*-comm d a)
  where lo≡da = *-lo-pos-nonPos c<d a<b c≥0 a≤0
  
*-lo-neg-neg : ∀ {a b c d} → a < b → c < d → b ≤ 0ℚ → d ≤ 0ℚ → *-lo a b c d ≡ b * d
*-lo-neg-neg {a} {b} {c} {d} a<b c<d b≤0 d≤0
  rewrite *-lo-neg a b c d = trans lo≡-b-d (sym (*-cancel-neg b d))
    where
    -b<-a = ℚ.neg-antimono-< a<b
    -d<-c = ℚ.neg-antimono-< c<d
    -b≥0 = ℚ.neg-antimono-≤ b≤0
    -d≥0 = ℚ.neg-antimono-≤ d≤0
    lo≡-b-d = *-lo-pos-pos -b<-a -d<-c -b≥0 -d≥0

*-lo-neg-nonNeg : ∀ {a b c d} → a < b → c < d → b ≤ 0ℚ → 0ℚ ≤ d → *-lo a b c d ≡ a * d
*-lo-neg-nonNeg {a} {b} {c} {d} a<b c<d b≤0 d≥0
  rewrite *-lo-neg a b c d = trans lo≡-a-d (sym (*-cancel-neg a d))
    where
    -b<-a = ℚ.neg-antimono-< a<b
    -d<-c = ℚ.neg-antimono-< c<d
    -b≥0 = ℚ.neg-antimono-≤ b≤0
    -d≤0 = ℚ.neg-antimono-≤ d≥0
    lo≡-a-d = *-lo-pos-nonPos -b<-a -d<-c -b≥0 -d≤0

*-lo-nonNeg-neg : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ b → d ≤ 0ℚ → *-lo a b c d ≡ b * c
*-lo-nonNeg-neg {a} {b} {c} {d} a<b c<d b≥0 d≤0
  rewrite *-lo-comm a b c d = trans lo≡cb (ℚ.*-comm c b)
  where lo≡cb = *-lo-neg-nonNeg c<d a<b d≤0 b≥0


*-hi-pos-neg : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → d ≤ 0ℚ → *-hi a b c d ≡ a * d
*-hi-pos-neg {a} {b} {c} {d} a<b c<d a≥0 d≤0 = hi≡ad 
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  c≤0 = ℚ.<⇒≤ (ℚ.<-≤-trans c<d d≤0)
  c⊔d≤0 = ℚ.⊔-lub c≤0 d≤0
  instance _ = ℚ.nonNegative a≥0; _ = ℚ.nonNegative b≥0; _ = ℚ.nonPositive c⊔d≤0
  hi≡ad = begin
    *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊔-nonNeg a c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * c) ⊔ (b * d)   ≡⟨ ℚ.⊔-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
    (a * (c ⊔ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * (c ⊔ d))       ≡⟨ ℚ.p≥q⇒p⊔q≡p (ℚ.*-monoʳ-≤-nonPos (c ⊔ d) (ℚ.<⇒≤ a<b)) ⟩
    a * (c ⊔ d)                         ≡⟨ cong (a *_)  (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    a * d                               ∎ where open ≡-Reasoning

*-hi-pos-nonNeg : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → 0ℚ ≤ d → *-hi a b c d ≡ b * d
*-hi-pos-nonNeg {a} {b} {c} {d} a<b c<d a≥0 d≥0 = hi≡bc
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  c⊔d≥0 = ℚ.p≤q⇒p≤r⊔q c d≥0
  instance _ = ℚ.nonNegative a≥0; _ = ℚ.nonNegative b≥0; _ = ℚ.nonNegative c⊔d≥0
  hi≡bc = begin
    *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊔-nonNeg a c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * c) ⊔ (b * d)   ≡⟨ ℚ.⊔-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
    (a * (c ⊔ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * (c ⊔ d))       ≡⟨ ℚ.p≤q⇒p⊔q≡q (ℚ.*-monoʳ-≤-nonNeg (c ⊔ d) (ℚ.<⇒≤ a<b)) ⟩
    b * (c ⊔ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    b * d                               ∎ where open ≡-Reasoning

*-hi-zero-zero : ∀ {a b c d} → a < b → c < d → a ≤ 0ℚ → 0ℚ ≤ b → c ≤ 0ℚ → 0ℚ ≤ d → *-hi a b c d ≡ (a * c) ⊔ (b * d)
*-hi-zero-zero {a} {b} {c} {d} a<b c<d a≤0 b≥0 c≤0 d≥0 = hi≡ad⊔bc
  where
  instance _ = ℚ.nonPositive a≤0; _ = ℚ.nonNegative b≥0
  hi≡ad⊔bc = begin
    *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊓-nonPos a c d) ⟨
    (a * (c ⊓ d)) ⊔ (b * c) ⊔ (b * d)   ≡⟨ ℚ.⊔-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
    (a * (c ⊓ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
    (a * (c ⊓ d)) ⊔ (b * (c ⊔ d))       ≡⟨ cong (λ x → (a * x) ⊔ (b * (c ⊔ d))) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    (a * c) ⊔ (b * (c ⊔ d))             ≡⟨ cong (λ x → (a * c) ⊔ (b * x)) (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    (a * c) ⊔ (b * d)                   ∎ where open ≡-Reasoning

*-hi-nonNeg-pos : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ b → 0ℚ ≤ c → *-hi a b c d ≡ b * d
*-hi-nonNeg-pos {a} {b} {c} {d} a<b c<d b≥0 c≥0
  rewrite *-hi-comm a b c d = trans hi≡db (ℚ.*-comm d b)
  where hi≡db = *-hi-pos-nonNeg c<d a<b c≥0 b≥0
  
*-hi-neg-pos : ∀ {a b c d} → a < b → c < d → b ≤ 0ℚ → 0ℚ ≤ c → *-hi a b c d ≡ b * c
*-hi-neg-pos {a} {b} {c} {d} a<b c<d b≤0 c≥0
  rewrite *-hi-neg a b c d = trans hi≡-b-c (sym (*-cancel-neg b c))
    where
    -b<-a = ℚ.neg-antimono-< a<b
    -d<-c = ℚ.neg-antimono-< c<d
    -b≥0 = ℚ.neg-antimono-≤ b≤0
    -c≤0 = ℚ.neg-antimono-≤ c≥0
    hi≡-b-c = *-hi-pos-neg -b<-a -d<-c -b≥0 -c≤0

*-hi-neg-nonPos : ∀ {a b c d} → a < b → c < d → b ≤ 0ℚ → c ≤ 0ℚ → *-hi a b c d ≡ a * c
*-hi-neg-nonPos {a} {b} {c} {d} a<b c<d b≤0 c≤0
  rewrite *-hi-neg a b c d = trans hi≡-a-c (sym (*-cancel-neg a c))
    where
    -b<-a = ℚ.neg-antimono-< a<b
    -d<-c = ℚ.neg-antimono-< c<d
    -b≥0 = ℚ.neg-antimono-≤ b≤0
    -c≥0 = ℚ.neg-antimono-≤ c≤0
    hi≡-a-c = *-hi-pos-nonNeg -b<-a -d<-c -b≥0 -c≥0

*-hi-nonPos-neg : ∀ {a b c d} → a < b → c < d → a ≤ 0ℚ → d ≤ 0ℚ → *-hi a b c d ≡ a * c
*-hi-nonPos-neg {a} {b} {c} {d} a<b c<d a≤0 d≤0
  rewrite *-hi-comm a b c d = trans hi≡ca (ℚ.*-comm c a)
  where hi≡ca = *-hi-neg-nonPos c<d a<b d≤0 a≤0


*-lo≤ac : ∀ a b c d → *-lo a b c d ≤ a * c
*-lo≤ac a b c d = ac⊓ad⊓bc⊓bd≤ac
  where
  ac⊓ad≤ac = ℚ.p⊓q≤p (a * c) (a * d)
  ac⊓ad⊓bc≤ac = ℚ.p≤q⇒p⊓r≤q (b * c) ac⊓ad≤ac
  ac⊓ad⊓bc⊓bd≤ac = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤ac

*-lo≤ad : ∀ a b c d → *-lo a b c d ≤ a * d
*-lo≤ad a b c d = ac⊓ad⊓bc⊓bd≤ad
  where
  ac⊓ad≤ad = ℚ.p⊓q≤q (a * c) (a * d)
  ac⊓ad⊓bc≤ad = ℚ.p≤q⇒p⊓r≤q (b * c) ac⊓ad≤ad
  ac⊓ad⊓bc⊓bd≤ad = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤ad

*-lo≤bc : ∀ a b c d → *-lo a b c d ≤ b * c
*-lo≤bc a b c d = ac⊓ad⊓bc⊓bd≤bc
  where
  ac⊓ad⊓bc≤bc = ℚ.p⊓q≤q ((a * c) ⊓ (a * d)) (b * c)
  ac⊓ad⊓bc⊓bd≤bc = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤bc

*-lo≤bd : ∀ a b c d → *-lo a b c d ≤ b * d
*-lo≤bd a b c d = ℚ.p⊓q≤q ((a * c) ⊓ (a * d) ⊓ (b * c)) (b * d)

data *-lo-cases : ℚ → ℚ → ℚ → ℚ → Set where 
  =ac : ∀ {a b c d} → *-lo a b c d ≡ a * c → *-lo-cases a b c d 
  =ad : ∀ {a b c d} → *-lo a b c d ≡ a * d → *-lo-cases a b c d 
  =bc : ∀ {a b c d} → *-lo a b c d ≡ b * c → *-lo-cases a b c d 
  =bd : ∀ {a b c d} → *-lo a b c d ≡ b * d → *-lo-cases a b c d 

split-lo : ∀ a b c d → *-lo-cases a b c d 
split-lo a b c d with ℚ.⊓-sel ((a * c) ⊓ (a * d) ⊓ (b * c)) (b * d)
... | right bd = =bd bd
... | left ¬bd with ℚ.⊓-sel ((a * c) ⊓ (a * d)) (b * c) 
... | right bc = =bc (trans ¬bd bc)
... | left ¬bc with ℚ.⊓-sel (a * c) (a * d) 
... | left ac = =ac (trans (trans ¬bd ¬bc) ac)
... | right ad = =ad (trans (trans ¬bd ¬bc) ad)

-- *-lo-bc : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → c ≤ 0ℚ → *-lo a b c d ≡ b * c
-- *-lo-bc {a} {b} {c} {d} a<b c<d a≥0 c≤0 = lo≡bc 
--   where
--   b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
--   c⊓d≤0 = ℚ.p≤q⇒p⊓r≤q d c≤0
--   instance _ = ℚ.nonNegative a≥0; _ = ℚ.nonNegative b≥0; _ = ℚ.nonPositive c⊓d≤0
--   lo≡bc = begin
--     *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
--     (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
--     (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
--     (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≥q⇒p⊓q≡q (ℚ.*-monoʳ-≤-nonPos (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
--     b * (c ⊓ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
--     b * c                               ∎ where open ≡-Reasoning



-- *-lo-ad : ∀ {a b c d} → a < b → c < d → a ≤ 0ℚ → 0ℚ ≤ d → *-lo a b c d ≡ a * d
-- *-lo-ad {a} {b} {c} {d} a<b c<d a≤0 d≥0
--   rewrite *-lo-neg a b c d = trans *-lo-bc c<d a<b d≥0
--     where
--     -b<-a = ℚ.neg-antimono-< a<b
--     -d<-c = ℚ.neg-antimono-< c<d
--     -a≥0 = ℚ.neg-antimono-≤ a≤0
--     -d≤0 = ℚ.neg-antimono-≤ d≥0
--     lo≡-a-d = *-lo-bc -b<-a -d<-c -a≥0 -d≤0

*-pos-pos : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → 0ℚ ≤ c → *-lo a b c d ≡ a * c ∧ *-hi a b c d ≡ b * d
*-pos-pos {a} {b} {c} {d} a<b c<d a≥0 c≥0 = lo≡ac , hi≡bd
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  d≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans c≥0 c<d)
  c⊓d≥0 = ℚ.⊓-glb c≥0 d≥0
  c⊔d≥0 = ℚ.p≤q⇒p≤q⊔r d c≥0
  instance
    _ = ℚ.nonNegative a≥0
    _ = ℚ.nonNegative b≥0
    _ = ℚ.nonNegative c≥0
    _ = ℚ.nonNegative d≥0
    _ = ℚ.nonNegative c⊓d≥0
    _ = ℚ.nonNegative c⊔d≥0
  lo≡ac = begin
    *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
    (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≤q⇒p⊓q≡p (ℚ.*-monoʳ-≤-nonNeg (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
    a * (c ⊓ d)                         ≡⟨ cong (a *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    a * c                               ∎ where open ≡-Reasoning
  hi≡bd = begin
    *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊔-nonNeg a c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * c) ⊔(b * d)    ≡⟨ ℚ.⊔-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
    (a * (c ⊔ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * (c ⊔ d))       ≡⟨ ℚ.p≤q⇒p⊔q≡q (ℚ.*-monoʳ-≤-nonNeg (c ⊔ d) (ℚ.<⇒≤ a<b)) ⟩
    b * (c ⊔ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    b * d                               ∎ where open ≡-Reasoning

*-pos-neg : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → d ≤ 0ℚ → *-lo a b c d ≡ b * c ∧ *-hi a b c d ≡ a * d
*-pos-neg {a} {b} {c} {d} a<b c<d a≥0 d≤0 = lo≡bc , hi≡ad
  where
  b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
  c≤0 = ℚ.<⇒≤ (ℚ.<-≤-trans c<d d≤0)
  c⊓d≤0 = ℚ.p≤q⇒p⊓r≤q d c≤0
  c⊔d≤0 = ℚ.⊔-lub c≤0 d≤0
  instance
    _ = ℚ.nonNegative a≥0
    _ = ℚ.nonNegative b≥0
    _ = ℚ.nonPositive c≤0
    _ = ℚ.nonPositive d≤0
    _ = ℚ.nonPositive c⊓d≤0
    _ = ℚ.nonPositive c⊔d≤0
  lo≡bc = begin
    *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
    (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
    (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≥q⇒p⊓q≡q (ℚ.*-monoʳ-≤-nonPos (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
    b * (c ⊓ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
    b * c                               ∎ where open ≡-Reasoning
  hi≡ad = begin
    *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊔-nonNeg a c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * c) ⊔(b * d)    ≡⟨ ℚ.⊔-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
    (a * (c ⊔ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
    (a * (c ⊔ d)) ⊔ (b * (c ⊔ d))       ≡⟨ ℚ.p≥q⇒p⊔q≡p (ℚ.*-monoʳ-≤-nonPos (c ⊔ d) (ℚ.<⇒≤ a<b)) ⟩
    a * (c ⊔ d)                         ≡⟨ cong (a *_)  (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
    a * d                               ∎ where open ≡-Reasoning

-- *-pos-zero : ∀ {a b c d} → a < b → c < d → 0ℚ ≤ a → c < 0ℚ → 0ℚ < d → *-lo a b c d ≡ b * c ∧ *-hi a b c d ≡ b * d
-- *-pos-zero {a} {b} {c} {d} a<b c<d a≥0 c<0 d>0 = lo≡bc , {!   !}
--   where
--   b≥0 = ℚ.<⇒≤ (ℚ.≤-<-trans a≥0 a<b)
--   c≤0 = ℚ.<⇒≤ c<0
--   d≥0 = ℚ.<⇒≤ d>0
--   c⊓d≤0 = ℚ.p≤q⇒p⊓r≤q d c≤0
--   c⊔d≥0 = ℚ.p≤q⇒p≤r⊔q c d≥0
--   instance
--     _ = ℚ.nonNegative a≥0
--     _ = ℚ.nonNegative b≥0
--     _ = ℚ.nonPositive c≤0
--     _ = ℚ.nonNegative d≥0
--     _ = ℚ.nonPositive c⊓d≤0
--     _ = ℚ.nonNegative c⊔d≥0
--   lo≡bc = begin
--     *-lo a b c d                        ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.*-distribˡ-⊓-nonNeg a c d) ⟨
--     (a * (c ⊓ d)) ⊓ (b * c) ⊓ (b * d)   ≡⟨ ℚ.⊓-assoc (a * (c ⊓ d)) (b * c) (b * d) ⟩
--     (a * (c ⊓ d)) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * (c ⊓ d)) ⊓_) (ℚ.*-distribˡ-⊓-nonNeg b c d) ⟨
--     (a * (c ⊓ d)) ⊓ (b * (c ⊓ d))       ≡⟨ ℚ.p≥q⇒p⊓q≡q (ℚ.*-monoʳ-≤-nonPos (c ⊓ d) (ℚ.<⇒≤ a<b)) ⟩
--     b * (c ⊓ d)                         ≡⟨ cong (b *_)  (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ c<d)) ⟩
--     b * c                               ∎ where open ≡-Reasoning
--   -- hi≡ad = begin
--   --   *-hi a b c d                        ≡⟨ cong (λ x → x ⊔ (b * c) ⊔ (b * d)) (ℚ.*-distribˡ-⊔-nonNeg a c d) ⟨
--   --   (a * (c ⊔ d)) ⊔ (b * c) ⊔(b * d)    ≡⟨ ℚ.⊔-assoc (a * (c ⊔ d)) (b * c) (b * d) ⟩
--   --   (a * (c ⊔ d)) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ cong ((a * (c ⊔ d)) ⊔_) (ℚ.*-distribˡ-⊔-nonNeg b c d) ⟨
--   --   (a * (c ⊔ d)) ⊔ (b * (c ⊔ d))       ≡⟨ ℚ.p≥q⇒p⊔q≡p (ℚ.*-monoʳ-≤-nonPos (c ⊔ d) (ℚ.<⇒≤ a<b)) ⟩
--   --   a * (c ⊔ d)                         ≡⟨ cong (a *_)  (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ c<d)) ⟩
--   --   a * d                               ∎ where open ≡-Reasoning

-- *-neg-neg : ∀ {a b c d} → a < b → c < d → b ≤ 0ℚ → d ≤ 0ℚ → *-lo a b c d ≡ b * d ∧ *-hi a b c d ≡ a * c
-- *-neg-neg {a} {b} {c} {d} a<b c<d b≤0 d≤0 
--   rewrite *-lo-neg a b c d | *-hi-neg a b c d = 
--     let (lo≡-b-d , hi≡-a-c) = (*-pos-pos -b<-a -d<-c -b≥0 -d≥0) 
--         lo≡bd = trans lo≡-b-d (sym (*-cancel-neg b d))
--         hi≡ac = trans hi≡-a-c (sym (*-cancel-neg a c))
--     in lo≡bd , hi≡ac
--   where
--   -b<-a = ℚ.neg-antimono-< a<b
--   -d<-c = ℚ.neg-antimono-< c<d
--   -b≥0 = ℚ.neg-antimono-≤ b≤0
--   -d≥0 = ℚ.neg-antimono-≤ d≤0

-- case where 0 < a < b
interval-*' : ∀ {a b c d} → a < b → c < d → 0ℚ < a → *-lo a b c d < *-hi a b c d
interval-*' {a} {b} {c} {d} a<b c<d a>0 
  with c ℚ.>? 0ℚ | d ℚ.<? 0ℚ 
... | yes c>0 | _ = lo<hi -- [ac, bd]
  where
  instance
    _ = ℚ.positive a>0
    _ = ℚ.positive (ℚ.<-trans a>0 a<b)
    _ = ℚ.positive c>0
    _ = ℚ.positive (ℚ.<-trans c>0 c<d)

  ac<bc = ℚ.*-monoˡ-<-pos c a<b
  ac<ad = ℚ.*-monoʳ-<-pos a c<d
  bc<bd = ℚ.*-monoʳ-<-pos b c<d
  ad<bd = ℚ.*-monoˡ-<-pos d a<b
  ac<bd = ℚ.<-trans ac<bc bc<bd
  
  lo<hi : *-lo a b c d < *-hi a b c d
  lo<hi = begin-strict
    *-lo a b c d                            ≡⟨ cong (λ x → x ⊓ (b * c) ⊓ (b * d)) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ ac<ad)) ⟩
    (a * c) ⊓ (b * c) ⊓ (b * d)             ≡⟨ cong (_⊓ (b * d)) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ ac<bc)) ⟩
    (a * c) ⊓ (b * d)                       ≡⟨ ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ ac<bd) ⟩
    a * c                                   <⟨ ac<bd ⟩
    b * d                                   ≡⟨ ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ ac<bd) ⟨
    (a * c) ⊔ (b * d)                       ≡⟨ cong ((a * c) ⊔_) (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ ad<bd)) ⟨
    (a * c) ⊔ ((a * d) ⊔ (b * d))           ≡⟨ ℚ.⊔-assoc (a * c) (a * d) (b * d) ⟨
    (a * c) ⊔ (a * d) ⊔ (b * d)             ≡⟨ cong ((a * c) ⊔ (a * d) ⊔_) (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ bc<bd)) ⟨
    (a * c) ⊔ (a * d) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ ℚ.⊔-assoc ((a * c) ⊔ (a * d)) (b * c) (b * d) ⟨
    *-hi a b c d                            ∎ where open ℚ.≤-Reasoning
    
... | _ | yes d<0 = lo<hi -- [bc, ad]
  where
  instance
    _ = ℚ.positive a>0
    _ = ℚ.positive (ℚ.<-trans a>0 a<b)
    _ = ℚ.negative d<0
    _ = ℚ.negative (ℚ.<-trans c<d d<0)

  bc<ac = ℚ.*-monoˡ-<-neg c a<b
  bc<bd = ℚ.*-monoʳ-<-pos b c<d
  ac<ad = ℚ.*-monoʳ-<-pos a c<d
  bd<ad = ℚ.*-monoˡ-<-neg d a<b
  bc<ad = ℚ.<-trans bc<ac ac<ad

  lo<hi : *-lo a b c d < *-hi a b c d
  lo<hi = begin-strict
    *-lo a b c d                            ≡⟨ ℚ.⊓-assoc ((a * c) ⊓ (a * d)) (b * c) (b * d) ⟩
    (a * c) ⊓ (a * d) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * c) ⊓ (a * d) ⊓_) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ bc<bd)) ⟩
    (a * c) ⊓ (a * d) ⊓ (b * c)             ≡⟨ ℚ.⊓-assoc (a * c)  (a * d)  (b * c) ⟩
    (a * c) ⊓ ((a * d) ⊓ (b * c))           ≡⟨ cong ((a * c) ⊓_) (ℚ.p≥q⇒p⊓q≡q (ℚ.<⇒≤ bc<ad)) ⟩
    (a * c) ⊓ (b * c)                       ≡⟨ ℚ.p≥q⇒p⊓q≡q (ℚ.<⇒≤ bc<ac) ⟩
    b * c                                   <⟨ bc<ad ⟩
    a * d                                   ≡⟨ ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ ac<ad) ⟨
    (a * c) ⊔ (a * d)                       ≡⟨ cong ((a * c) ⊔_) (ℚ.p≥q⇒p⊔q≡p (ℚ.<⇒≤ bd<ad)) ⟨
    (a * c) ⊔ ((a * d) ⊔ (b * d))           ≡⟨ ℚ.⊔-assoc (a * c) (a * d) (b * d)  ⟨
    (a * c) ⊔ (a * d) ⊔ (b * d)             ≡⟨ cong (λ x → (a * c) ⊔ x ⊔ (b * d)) (ℚ.p≥q⇒p⊔q≡p (ℚ.<⇒≤ bc<ad))  ⟨
    (a * c) ⊔ ((a * d) ⊔ (b * c)) ⊔ (b * d) ≡⟨ cong (_⊔ (b * d)) (ℚ.⊔-assoc (a * c) (a * d) (b * c))  ⟨
    *-hi a b c d                            ∎ where open ℚ.≤-Reasoning

... | no ¬c>0 | no ¬d<0 = lo<hi -- [bc , bd]
  where
  c≤0 = ℚ.≮⇒≥ ¬c>0
  d≥0 = ℚ.≮⇒≥ ¬d<0
  instance
    _ = ℚ.positive a>0
    _ = ℚ.positive (ℚ.<-trans a>0 a<b)
    _ = ℚ.nonNegative d≥0
    _ = ℚ.nonPositive c≤0
  
  bc<bd = ℚ.*-monoʳ-<-pos b c<d
  bc≤ac = ℚ.*-monoʳ-≤-nonPos c (ℚ.<⇒≤ a<b)
  ac<ad = ℚ.*-monoʳ-<-pos a c<d
  bc<ad = ℚ.≤-<-trans bc≤ac ac<ad
  ad≤bd = ℚ.*-monoʳ-≤-nonNeg d (ℚ.<⇒≤ a<b) -- name of ℚ.*-monoʳ-≤-nonNeg is wrong
  ac<bd = ℚ.<-≤-trans ac<ad ad≤bd

  lo<hi : *-lo a b c d < *-hi a b c d
  lo<hi = begin-strict
    *-lo a b c d                            ≡⟨ ℚ.⊓-assoc ((a * c) ⊓ (a * d)) (b * c) (b * d) ⟩
    (a * c) ⊓ (a * d) ⊓ ((b * c) ⊓ (b * d)) ≡⟨ cong ((a * c) ⊓ (a * d) ⊓_) (ℚ.p≤q⇒p⊓q≡p (ℚ.<⇒≤ bc<bd)) ⟩
    (a * c) ⊓ (a * d) ⊓ (b * c)             ≡⟨ ℚ.⊓-assoc (a * c)  (a * d)  (b * c) ⟩
    (a * c) ⊓ ((a * d) ⊓ (b * c))           ≡⟨ cong ((a * c) ⊓_) (ℚ.p≥q⇒p⊓q≡q (ℚ.<⇒≤ bc<ad)) ⟩
    (a * c) ⊓ (b * c)                       ≡⟨ ℚ.p≥q⇒p⊓q≡q bc≤ac ⟩
    b * c                                   <⟨ bc<bd ⟩
    b * d                                   ≡⟨ ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ ac<bd) ⟨
    (a * c) ⊔ (b * d)                       ≡⟨ cong ((a * c) ⊔_) (ℚ.p≤q⇒p⊔q≡q ad≤bd) ⟨
    (a * c) ⊔ ((a * d) ⊔ (b * d))           ≡⟨ ℚ.⊔-assoc (a * c) (a * d) (b * d) ⟨
    (a * c) ⊔ (a * d) ⊔ (b * d)             ≡⟨ cong ((a * c) ⊔ (a * d) ⊔_) (ℚ.p≤q⇒p⊔q≡q (ℚ.<⇒≤ bc<bd)) ⟨
    (a * c) ⊔ (a * d) ⊔ ((b * c) ⊔ (b * d)) ≡⟨ ℚ.⊔-assoc ((a * c) ⊔ (a * d)) (b * c) (b * d) ⟨
    *-hi a b c d                            ∎ where open ℚ.≤-Reasoning

interval-* : ∀ {a b c d} → a < b → c < d → *-lo a b c d < *-hi a b c d
interval-* {a} {b} {c} {d} a<b c<d 
  with a ℚ.>? 0ℚ | c ℚ.>? 0ℚ | b ℚ.<? 0ℚ | d ℚ.<? 0ℚ 
... | yes a>0 | _ | _ | _ = interval-*' a<b c<d a>0
... | _ | yes c>0 | _ | _ = begin-strict 
  *-lo a b c d  ≡⟨ *-lo-comm a b c d ⟩ 
  *-lo c d a b  <⟨ interval-*' c<d a<b c>0 ⟩ 
  *-hi c d a b  ≡⟨ *-hi-comm a b c d ⟨
  *-hi a b c d  ∎ where open ℚ.≤-Reasoning 
... | _ | _ | yes b<0 | _ = begin-strict 
  *-lo a b c d                  ≡⟨ *-lo-neg a b c d ⟩ 
  *-lo (- b) (- a) (- d) (- c)  <⟨ interval-*' (ℚ.neg-antimono-< a<b) (ℚ.neg-antimono-< c<d) (ℚ.neg-antimono-< b<0) ⟩ 
  *-hi (- b) (- a) (- d) (- c)  ≡⟨ *-hi-neg a b c d ⟨
  *-hi a b c d                  ∎ where open ℚ.≤-Reasoning 
... | _ | _ | _ | yes d<0 = begin-strict 
  *-lo a b c d                  ≡⟨ *-lo-comm a b c d ⟩ 
  *-lo c d a b                  ≡⟨ *-lo-neg c d a b ⟩ 
  *-lo (- d) (- c) (- b) (- a)  <⟨ interval-*' (ℚ.neg-antimono-< c<d) (ℚ.neg-antimono-< a<b) (ℚ.neg-antimono-< d<0) ⟩ 
  *-hi (- d) (- c) (- b) (- a)  ≡⟨ *-hi-neg c d a b ⟨
  *-hi c d a b                  ≡⟨ *-hi-comm a b c d ⟨
  *-hi a b c d                  ∎ where open ℚ.≤-Reasoning 
... | no ¬a>0 | no ¬c>0 | no ¬b<0 | no ¬d<0 = lo<hi -- [ad ⊓ bc, ac ⊔ bd]
  where
  a≤0 = ℚ.≮⇒≥ ¬a>0
  b≥0 = ℚ.≮⇒≥ ¬b<0
  c≤0 = ℚ.≮⇒≥ ¬c>0
  d≥0 = ℚ.≮⇒≥ ¬d<0
  instance
    _ = ℚ.nonPositive a≤0
    _ = ℚ.nonNegative b≥0
    _ = ℚ.nonPositive c≤0
    _ = ℚ.nonNegative d≥0

  ad≤0 = begin
    a * d   ≤⟨ ℚ.*-monoʳ-≤-nonNeg d a≤0 ⟩
    0ℚ * d  ≡⟨ ℚ.*-zeroˡ d ⟩
    0ℚ      ∎ where open ℚ.≤-Reasoning
  ac≥0 = begin
    0ℚ      ≡⟨ ℚ.*-zeroˡ c ⟨
    0ℚ * c  ≤⟨ ℚ.*-monoʳ-≤-nonPos c a≤0 ⟩
    a * c   ∎ where open ℚ.≤-Reasoning
  bc≤0 = begin
    b * c   ≤⟨ ℚ.*-monoˡ-≤-nonNeg b c≤0 ⟩
    b * 0ℚ  ≡⟨ ℚ.*-zeroʳ b ⟩
    0ℚ      ∎ where open ℚ.≤-Reasoning
  bd≥0 = begin
    0ℚ      ≡⟨ ℚ.*-zeroˡ d ⟨
    0ℚ * d  ≤⟨ ℚ.*-monoʳ-≤-nonNeg d b≥0 ⟩
    b * d   ∎ where open ℚ.≤-Reasoning
    
  lo = *-lo a b c d
  hi = *-hi a b c d

  ac⊓ad≤0 = ℚ.p≤q⇒r⊓p≤q (a * c) ad≤0
  ac⊓ad⊓bc≤0 = ℚ.p≤q⇒p⊓r≤q (b * c) ac⊓ad≤0
  lo≤0 = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤0

  ac⊔ad≥0 = ℚ.p≤q⇒p≤q⊔r (a * d) ac≥0
  ac⊔ad⊔bc≥0 = ℚ.p≤q⇒p≤q⊔r (b * c) ac⊔ad≥0
  hi≥0 = ℚ.p≤q⇒p≤q⊔r (b * d) ac⊔ad⊔bc≥0

  lo<hi : lo < hi 
  lo<hi with lo ℚ.<? 0ℚ | hi ℚ.>? 0ℚ 
  ... | yes lo<0 | _ = ℚ.<-≤-trans lo<0 hi≥0
  ... | _ | yes hi>0 = ℚ.≤-<-trans lo≤0 hi>0
  ... | no ¬lo<0 | no ¬hi>0 = ⊥-elim (ℚ.<-irrefl refl 0<0)
    where
    lo≡0 = ℚ.≤-antisym lo≤0 (ℚ.≮⇒≥ ¬lo<0)
    hi≡0 = ℚ.≤-antisym (ℚ.≮⇒≥ ¬hi>0) hi≥0

    0<0 : 0ℚ < 0ℚ
    0<0 with a ℚ.<? 0ℚ
    ... | yes a<0 = begin-strict
      0ℚ    ≡⟨ lo≡0 ⟨
      lo    ≤⟨ lo≤ad ⟩
      a * d <⟨ ad<ac ⟩
      a * c ≤⟨ ac≤hi ⟩
      hi    ≡⟨ hi≡0 ⟩
      0ℚ    ∎
      where 
      open ℚ.≤-Reasoning
      instance _ = ℚ.negative a<0
      ad<ac = ℚ.*-monoʳ-<-neg a c<d
      
      ac⊓ad≤ad = ℚ.p⊓q≤q (a * c) (a * d)
      ac⊓ad⊓bc≤ad = ℚ.p≤q⇒p⊓r≤q (b * c) ac⊓ad≤ad
      lo≤ad = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤ad
      
      ac≤ac⊔ad = ℚ.p≤p⊔q (a * c) (a * d)
      ac≤ac⊔ad⊔bc = ℚ.p≤q⇒p≤q⊔r (b * c) ac≤ac⊔ad
      ac≤hi = ℚ.p≤q⇒p≤q⊔r (b * d) ac≤ac⊔ad⊔bc
    ... | no ¬a<0 = begin-strict
      0ℚ    ≡⟨ lo≡0 ⟨
      lo    ≤⟨ lo≤bc ⟩
      b * c <⟨ bc<bd ⟩
      b * d ≤⟨ bd≤hi ⟩
      hi    ≡⟨ hi≡0 ⟩
      0ℚ    ∎  
      where
      open ℚ.≤-Reasoning
      a≡0 = ℚ.≤-antisym a≤0 (ℚ.≮⇒≥ ¬a<0)
      b>0 = subst (_< b) a≡0 a<b 
      instance _ = ℚ.positive b>0
      bc<bd = ℚ.*-monoʳ-<-pos b c<d
      
      ac⊓ad⊓bc≤bc = ℚ.p⊓q≤q ((a * c) ⊓ (a * d)) (b * c)
      lo≤bc = ℚ.p≤q⇒p⊓r≤q (b * d) ac⊓ad⊓bc≤bc
      bd≤hi = ℚ.p≤q⊔p (a * c ⊔ a * d ⊔ b * c) (b * d) 

data Interval : Set where
  int : ∀ a b → a < b → Interval

Iˡ : Interval → ℚ
Iˡ (int a b a<b) = a
Iʳ : Interval → ℚ
Iʳ (int a b a<b) = b
I-< : ∀ i → Iˡ i < Iʳ i
I-< (int a b a<b) = a<b

infix 4 _⊂_ _∈_
data _⊂_ : Interval → Interval → Set where
  cont : ∀ {i j} → Iˡ j ≤ Iˡ i → Iʳ i ≤ Iʳ j → i ⊂ j

data _∈_ : ℚ → Interval → Set where
  in-< : ∀ {x i} → (a≤x : Iˡ i ≤ x) → (x≤b : x ≤ Iʳ i) → x ∈ i

data sign-cases : Interval → Set where
  neg : ∀ {i} → (a<0 : Iˡ i < 0ℚ) → (b≤0 : Iʳ i ≤ 0ℚ) → sign-cases i
  pos : ∀ {i} → (a≥0 : 0ℚ ≤ Iˡ i) → (b>0 : 0ℚ < Iʳ i) → sign-cases i
  zero : ∀ {i} → (a<0 : Iˡ i < 0ℚ) → (b>0 : 0ℚ < Iʳ i) → sign-cases i

I-sign : ∀ i → sign-cases i
I-sign (int a b a<b) with a ℚ.≥? 0ℚ | b ℚ.≤? 0ℚ 
... | yes a≥0 | _ = pos a≥0 b>0
  where b>0 = ℚ.≤-<-trans a≥0 a<b
... | _ | yes b≤0 = neg a<0 b≤0
  where a<0 = ℚ.<-≤-trans a<b b≤0
... | no ¬a≥0 | no ¬b≤0 = zero (ℚ.≰⇒> ¬a≥0) (ℚ.≰⇒> ¬b≤0)

infixl 6 _*ᴵ_
_*ᴵ_ : Interval → Interval → Interval
int a b a<b *ᴵ int c d c<d = int lo hi (interval-* a<b c<d)
  where
  lo = *-lo a b c d
  hi = *-hi a b c d

point-inside : ∀ {i j x y} → x ∈ i → y ∈ j → x * y ∈ i *ᴵ j
point-inside {i@(int a b a<b)} {j@(int c d c<d)} {x} {y} (in-< a≤x x≤b) (in-< c≤y y≤d) 
  with I-sign i | I-sign j 
... | neg a<0 b≤0 | neg c<0 d≤0 = {!   !}
... | pos a≥0 b>0 | neg c<0 d≤0 = {!   !}
... | zero a<0 b>0 | neg c<0 d≤0 = {!   !}
... | neg a<0 b≤0 | pos c≥0 d>0 = {!   !}
... | pos a≥0 b>0 | pos c≥0 d>0 = {!   !}
... | zero a<0 b>0 | pos c≥0 d>0 = {!   !}
... | neg a<0 b≤0 | zero c<0 d>0 = {!   !}
... | pos a≥0 b>0 | zero c<0 d>0 = {!   !}
... | zero a<0 b>0 | zero c<0 d>0 = {!   !}

-- infixl 6 _*ᴵ_
-- _*ᴵ_ : Interval → Interval → Interval
-- i *ᴵ j = int lo hi lo<hi
--   where
--   lo = *-lo (Iˡ i) (Iʳ i) (Iˡ j) (Iʳ j)
--   hi = *-hi (Iˡ i) (Iʳ i) (Iˡ j) (Iʳ j)
--   lo<hi = interval-* (I-< i) (I-< j)

int-≡' : ∀ a b a<b c d c<d → a ≡ c → b ≡ d → (int a b a<b) ≡ (int c d c<d)
int-≡' a b a<b c d c<d a≡c b≡d rewrite a≡c | b≡d | <-equalityℚ a<b c<d = refl

int-≡ : ∀ i j → Iˡ i ≡ Iˡ j → Iʳ i ≡ Iʳ j → i ≡ j
int-≡ (int a b a<b) (int c d c<d) a≡c b≡d = int-≡' a b a<b c d c<d a≡c b≡d

*ᴵ-comm : ∀ i j → i *ᴵ j ≡ j *ᴵ i
*ᴵ-comm i@(int a b a<b) j@(int c d c<d) = int-≡ (i *ᴵ j) (j *ᴵ i) (*-lo-comm a b c d) (*-hi-comm a b c d)

-- <-cmp : Trichotomous _≡_ _<_
-- <-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
-- ... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ drop-*≡* ∘ ≡⇒≃) (≯ ∘ drop-*<*)
-- ... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ (*≡* ≡))   (≯ ∘ drop-*<*)
-- ... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ drop-*≡* ∘ ≡⇒≃) (*<* >)

-- contains : ∀ {i i' j} → i' ⊂ i → i' *ᴵ j ⊂ i *ᴵ j
-- contains = {!   !}

     