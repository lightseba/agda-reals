-- {-# OPTIONS --allow-unsolved-metas #-}

module RealLemmas where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_; _^_ to _^ₙ_)
open import Data.Nat.Logarithm as ℕ using (⌊log₂_⌋; ⌈log₂_⌉)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base as ℤ using (ℤ; +0; +[1+_]; -[1+_]; 0ℤ; 1ℤ; -1ℤ)
import Data.Integer.Properties as ℤ
open import Data.Integer.DivMod using ([n/d]*d≤n)
open import Data.Rational as ℚ using (ℚ; _<_; _>_; 1/_; _≤_; _+_; _-_; -_; _*_; 1ℚ; 0ℚ; ½; toℚᵘ; fromℚᵘ; floor; ceiling; ↥_; ↧_)
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
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong′; icong; icong′; sym; ≢-sym; trans; subst; module ≡-Reasoning)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary.Decidable.Core as Dec using (yes; no)
open import Relation.Binary.Core using (_⇒_)
open import Logic using (_∨_; _∧_; left; right; _,_; swap; proj₁; proj₂; fromDec)

¼ : ℚ
¼ = 1ℤ ℚ./ 4

¾ : ℚ
¾ = (ℤ.+ 3) ℚ./ 4

2ℚ : ℚ
2ℚ = 1ℚ + 1ℚ

3ℚ : ℚ
3ℚ = (ℤ.+ 3) ℚ./ 1

2ℚᵘ : ℚᵘ
2ℚᵘ = (ℤ.+ 2) ℚᵘ./ 1

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

<-lemma : ∀ q₀ {q r} → q < r → q < q₀ ∨ q₀ < r
<-lemma q₀ {q} {r} q<r with q ℚ.<? q₀
... | yes q<q₀ = left q<q₀
... | no x = right (ℚ.≤-<-trans (ℚ.≮⇒≥ x) q<r)

a<b→0<b-a : ∀ {a b : ℚ} → a < b → 0ℚ < b - a
a<b→0<b-a {a} {b} a<b = begin-strict 
  0ℚ      ≡⟨ ℚ.+-inverseʳ a ⟨
  a - a   <⟨ ℚ.+-monoˡ-< (- a) a<b ⟩
  b - a   ∎ where open ℚ.≤-Reasoning

a<b→a-b<0 : ∀ {a b : ℚ} → a < b → a - b < 0ℚ
a<b→a-b<0 {a} {b} a<b = begin-strict 
  a - b <⟨ ℚ.+-monoˡ-< (- b) a<b ⟩
  b - b ≡⟨ ℚ.+-inverseʳ b ⟩
  0ℚ   ∎ where open ℚ.≤-Reasoning
  
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
d<0→x<x-d {d} x 0<d = 0<d→x<x+d x (ℚ.neg-antimono-< 0<d)


split-half : ∀ (x : ℚ) → x ≡ x * ½ + x * ½
split-half x = begin 
  x                       ≡⟨ ℚ.*-identityʳ x ⟨
  x * 1ℚ                ≡⟨ cong (x ℚ.*_) (ℚ.*-inverseˡ ½) ⟨
  x * (½ * 2ℚ)        ≡⟨ ℚ.*-assoc x ½ 2ℚ ⟨
  x * ½ * 2ℚ          ≡⟨ refl ⟩
  d * (1ℚ + 1ℚ)         ≡⟨ ℚ.*-distribˡ-+ d 1ℚ 1ℚ ⟩
  (d * 1ℚ) + (d * 1ℚ) ≡⟨ cong ((d * 1ℚ) +_) (ℚ.*-identityʳ d) ⟩
  (d * 1ℚ) + d          ≡⟨ cong (_+ d) (ℚ.*-identityʳ d) ⟩
  d + d                   ∎
  where 
  open ≡-Reasoning
  d = x * ½

-- already wrote this proof and im too lazy to reverse it or whatever
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

eps-eq : ∀ {a b} → a < b → (b - a) - (b - a) * ¼ ≡ (b - a) * ¾
eps-eq {a} {b} a<b = begin
  ε - ε/4             ≡⟨ cong (ε +_) (ℚ.neg-distribʳ-* ε ¼) ⟩
  ε + ε * (- ¼)       ≡⟨ cong (_+ ε * (- ¼)) (ℚ.*-identityʳ ε) ⟨
  ε * 1ℚ + ε * (- ¼)  ≡⟨ ℚ.*-distribˡ-+ ε 1ℚ (- ¼) ⟨
  ε * ¾               ∎
  where 
    open ≡-Reasoning
    ε = (b - a)
    ε/2 = (b - a) * ½
    ε/4 = (b - a) * ¼


u<v : ∀ {a b} → a < b → a + (b - a) * ¼ < b - (b - a) * ¼ 
u<v {a} {b} a<b = begin-strict
  a + ε/4             ≡⟨ ℚ.+-identityʳ (a + ε/4) ⟨
  a + ε/4 + 0ℚ        <⟨ ℚ.+-monoʳ-< (a + ε/4) ε/2>0 ⟩ 
  a + ε/4 + ε/2       ≡⟨ ℚ.+-assoc a ε/4 ε/2 ⟩ 
  a + (ε/4 + ε/2)     ≡⟨ cong (a +_) (ℚ.*-distribˡ-+ ε ¼ ½) ⟨
  a + ε * ¾           ≡⟨ cong (a +_) (eps-eq a<b) ⟨
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

pow : ℕ → ℚ → ℚ
pow ℕ.zero a = 1ℚ
pow (ℕ.suc n) a = a * pow n a

powᵘ : ℕ → ℚᵘ → ℚᵘ
powᵘ ℕ.zero a = 1ℚᵘ
powᵘ (ℕ.suc n) a = a *ᵘ powᵘ n a

pow-l : ∀ n {a} → pow (ℕ.suc n) a ≡ a * pow n a
pow-l n = refl
pow-r : ∀ n {a} → pow (ℕ.suc n) a ≡ pow n a * a
pow-r n {a} = ℚ.*-comm a (pow n a)

a>0→pow>0 : ∀ n a .{{_ : ℚ.Positive a}} → pow n a > 0ℚ
a>0→pow>0 ℕ.zero a = ℚ.positive⁻¹ 1ℚ
a>0→pow>0 (suc n) a = begin-strict
  0ℚ              ≡⟨ ℚ.*-zeroʳ a ⟨
  a * 0ℚ          <⟨ ℚ.*-monoʳ-<-pos a (a>0→pow>0 n a) ⟩
  a * pow n a     ≡⟨ refl ⟩
  pow (suc n) a   ∎ where open ℚ.≤-Reasoning

pow-pos : ∀ n a .{{_ : ℚ.Positive a}} → ℚ.Positive (pow n a)
pow-pos n a = ℚ.positive (a>0→pow>0 n a)

¾^3<½ : ¾ * ¾ * ¾ < ½
¾^3<½ = fromDec (¾ * ¾ * ¾ ℚ.<? ½)

pow-bound : ∀ n → pow (n *ₙ 3) ¾ ≤ pow n ½
pow-bound ℕ.zero = ℚ.≤-refl
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
    pow-3n-pos = pow-pos (n *ₙ 3) ¾

powᵘ-pos : ∀ n a .{{_ : ℚᵘ.Positive a}} → ℚᵘ.Positive (powᵘ n a)
powᵘ-pos ℕ.zero a = record { pos = Data.Unit.tt }
powᵘ-pos (suc n) a = ℚᵘ.pos*pos⇒pos a (powᵘ n a)
  where instance pow-n-pos = powᵘ-pos n a

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

powᵘ-inverse : ∀ n a .{{_ : ℚᵘ.Positive a}} → (1/ᵘ (powᵘ n a)) {{ℚᵘ.pos⇒nonZero (powᵘ n a) {{powᵘ-pos n a}}}} ≡ powᵘ n ((1/ᵘ a) {{ℚᵘ.pos⇒nonZero a}})
powᵘ-inverse ℕ.zero a = refl 
powᵘ-inverse (suc n) a = begin
  1/ᵘ (powᵘ (suc n) a)      ≡⟨ refl ⟩
  1/ᵘ (a *ᵘ powᵘ n a)       ≡⟨ 1/-mono-* a (powᵘ n a) ⟩
  1/ᵘ a *ᵘ 1/ᵘ powᵘ n a     ≡⟨ cong (1/ᵘ a *ᵘ_) (powᵘ-inverse n a) ⟩
  1/ᵘ a *ᵘ powᵘ n (1/ᵘ a)   ≡⟨ refl ⟩
  powᵘ (suc n) (1/ᵘ a)      ∎
  where 
  open ≡-Reasoning
  instance
    pow-n>0 = powᵘ-pos n a
    pow-n+1>0 = powᵘ-pos (suc n) a
    a≠0 = ℚᵘ.pos⇒nonZero a
    pow-n+1≠0 = ℚᵘ.pos⇒nonZero (powᵘ (suc n) a)
    pow-n≠0 = ℚᵘ.pos⇒nonZero (powᵘ n a)

powᵘ-cong : ∀ n {a b} → a ≃ᵘ b → powᵘ n a ≃ᵘ powᵘ n b
powᵘ-cong ℕ.zero {a} {b} a=b = *≡* refl
powᵘ-cong (suc n) {a} {b} a=b = begin 
  powᵘ (suc n) a    ≡⟨ refl ⟩
  a *ᵘ (powᵘ n a)   ≈⟨ ℚᵘ.*-congʳ a=b ⟩
  b *ᵘ (powᵘ n a)   ≈⟨ ℚᵘ.*-congˡ {b} (powᵘ-cong n {a} {b} a=b) ⟩
  b *ᵘ (powᵘ n b)   ≡⟨ refl ⟩
  powᵘ (suc n) b    ∎ where open ℚᵘ.≃-Reasoning

toℚᵘ-homo-pow : ∀ n a → toℚᵘ (pow n a) ≃ᵘ powᵘ n (toℚᵘ a)
toℚᵘ-homo-pow ℕ.zero a = *≡* refl
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

fromℚᵘ-mono-< : ∀ {p q} → p <ᵘ q → fromℚᵘ p < fromℚᵘ q
fromℚᵘ-mono-< {p} {q} p<q = ℚ.toℚᵘ-cancel-< (begin-strict
  toℚᵘ (fromℚᵘ p) ≃⟨ ℚ.toℚᵘ-fromℚᵘ p ⟩
  p               <⟨ p<q ⟩
  q               ≃⟨ ℚ.toℚᵘ-fromℚᵘ q ⟨
  toℚᵘ (fromℚᵘ q) ∎)
  where open ℚᵘ.≤-Reasoning

pos*pos⇒pos : ∀ p q .{{_ : ℚ.Positive p}} .{{_ : ℚ.Positive q}} → ℚ.Positive (p * q)
pos*pos⇒pos p@record{} q@record{} = ℚ.positive (begin-strict 
  0ℚ ≡⟨ refl ⟩
  fromℚᵘ 0ℚᵘ <⟨ fromℚᵘ-mono-< (ℚᵘ.positive⁻¹ ((toℚᵘ p) *ᵘ (toℚᵘ q))) ⟩
  fromℚᵘ ((toℚᵘ p) *ᵘ (toℚᵘ q)) ≡⟨ ℚ.fromℚᵘ-cong (ℚ.toℚᵘ-homo-* p q) ⟨
  fromℚᵘ (toℚᵘ (p * q)) ≡⟨ ℚ.fromℚᵘ-toℚᵘ (p * q) ⟩
  p * q ∎)
  where 
  open ℚ.≤-Reasoning
  num-p = ℚ.drop-*<* (ℚ.positive⁻¹ p)
  instance
    pᵘ-pos : ℚᵘ.Positive (toℚᵘ p)
    pᵘ-pos = ℚᵘ.positive {(toℚᵘ p)} (*<* (ℚ.drop-*<* (ℚ.positive⁻¹ p)))
    qᵘ-pos : ℚᵘ.Positive (toℚᵘ q)
    qᵘ-pos = ℚᵘ.positive {(toℚᵘ q)} (*<* (ℚ.drop-*<* (ℚ.positive⁻¹ q)))
    p*ᵘq-pos : ℚᵘ.Positive ((toℚᵘ p) *ᵘ (toℚᵘ q))
    p*ᵘq-pos = ℚᵘ.pos*pos⇒pos (toℚᵘ p) (toℚᵘ q)

⌊x⌋ᵘ≤x : ∀ x → (floorᵘ x) ℚᵘ./ 1 ≤ᵘ x
⌊x⌋ᵘ≤x x@record{} = *≤* (begin
  ((↥ᵘ x) ℤ./ (↧ᵘ x)) ℤ.* ↧ᵘ x  ≤⟨ [n/d]*d≤n (↥ᵘ x) (↧ᵘ x) ⟩
  ↥ᵘ x                          ≡⟨ ℤ.*-identityʳ (↥ᵘ x) ⟨
  (↥ᵘ x) ℤ.* 1ℤ                 ∎)
  where open ℤ.≤-Reasoning

x≤⌈x⌉ᵘ : ∀ x → x ≤ᵘ (ceilingᵘ x) ℚᵘ./ 1
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

pows-same : ∀ a n → (ℤ.+ (a ^ₙ n)) ℚᵘ./ 1 ≡ powᵘ n (ℤ.+ a ℚᵘ./ 1)
pows-same a ℕ.zero = refl
pows-same a (suc n) = begin
  ℤ.+ a ^ₙ suc n ℚᵘ./ 1                     ≡⟨ refl ⟩
  ℤ.+ (a *ₙ (a ℕ.^ n)) ℚᵘ./ 1               ≡⟨ cong (ℚᵘ._/ 1) (ℤ.pos-* a (a ℕ.^ n)) ⟩
  ℤ.+ a ℤ.* ℤ.+ (a ℕ.^ n) ℚᵘ./ 1            ≡⟨ refl ⟩
  ℤ.+ a ℤ.* ℤ.+ (a ℕ.^ n) ℚᵘ./ (1 *ₙ 1)     ≡⟨ refl ⟩
  (ℤ.+ a ℚᵘ./ 1) *ᵘ (ℤ.+ (a ℕ.^ n) ℚᵘ./ 1)  ≡⟨ cong ((ℤ.+ a ℚᵘ./ 1) *ᵘ_) (pows-same a n) ⟩
  powᵘ (suc n) (ℤ.+ a ℚᵘ./ 1)               ∎ where open ≡-Reasoning

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

/d-mono-≤ᵘ : ∀ {i j} d .{{_ : ℕ.NonZero d}} → i ℤ.≤ j → (i ℚᵘ./ d) ≤ᵘ (j ℚᵘ./ d)
/d-mono-≤ᵘ (suc d) i≤j = *≤* (ℤ.*-monoʳ-≤-nonNeg (ℤ.+ (suc d)) i≤j)

/d-mono-<ᵘ : ∀ {i j} d .{{_ : ℕ.NonZero d}} → i ℤ.< j → (i ℚᵘ./ d) <ᵘ (j ℚᵘ./ d)
/d-mono-<ᵘ (suc d) i≤j = ℚᵘ.*<* (ℤ.*-monoʳ-<-pos (ℤ.+ (suc d)) i≤j)

x<2^[1+lg⌈x⌉]ᵘ : ∀ x → x <ᵘ powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ x) ∣) ⌋) 2ℚᵘ
x<2^[1+lg⌈x⌉]ᵘ x = begin-strict
  x                                                     ≤⟨ x≤⌈x⌉ᵘ x ⟩
  (ceilingᵘ x) ℚᵘ./ 1                                   ≤⟨ /d-mono-≤ᵘ 1 (i≤+|i| (ceilingᵘ x)) ⟩
  (ℤ.+ ℤ.∣ (ceilingᵘ x) ∣) ℚᵘ./ 1                       <⟨ /d-mono-<ᵘ 1 (ℤ.+<+ (n<2^[1+⌊log₂n⌋] ℤ.∣ (ceilingᵘ x) ∣)) ⟩
  (ℤ.+ (2 ^ₙ (suc ⌊log₂ ℤ.∣ (ceilingᵘ x) ∣ ⌋))) ℚᵘ./ 1   ≡⟨ pows-same 2 (suc ⌊log₂ ℤ.∣ (ceilingᵘ x) ∣ ⌋) ⟩
  powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ x) ∣) ⌋) 2ℚᵘ           ∎ where open ℚᵘ.≤-Reasoning

x>½^[1+lg⌈1/x⌉]ᵘ : ∀ x .{{_ : ℚᵘ.Positive x}} → powᵘ (suc ⌊log₂ (ℤ.∣ (ceilingᵘ ((1/ᵘ x) {{ℚᵘ.pos⇒nonZero x}})) ∣) ⌋) ½ᵘ <ᵘ x
x>½^[1+lg⌈1/x⌉]ᵘ x@(mkℚᵘ +[1+ nn ] dd) = begin-strict
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
  where instance x≠0 = ℚ.pos⇒nonZero x

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
