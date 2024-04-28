{-# OPTIONS --safe #-}

module Real where

import Data.List as List
import Data.List.Properties as List
import Data.Nat.Properties as Nat

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Nat using (ℕ) -- «_⊔_» for maximum
open import Data.Integer using (ℤ)
open import Data.Rational as ℚ using (ℚ; _<_; _>_; _÷_; _+_; _-_; -_; _*_; 1/_; 1ℚ; 0ℚ; ½; _⊔_; _⊓_)
import Data.Rational.Properties as ℚ
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; sym; trans; subst; module ≡-Reasoning)

open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary using (yes; no; Dec)

open import Logic using (_∨_; _∧_; left; right; _,_; swap; proj₁; proj₂)
open import RealLemmas

------------------------------------------------------------------------
-- Types

record ℝ : Set₁ where
  constructor real
  field
    L U : ℚ → Set
    inhabited : ∃[ q ] (L q) ∧ ∃[ q ] (U q) 
    rounded : ∀ (q r : ℚ) → 
      L q ⇔ (∃[ r ] q < r ∧ L r) ∧
      U r ⇔ (∃[ q ] q < r ∧ U q) --- flipped to make it a little easier
    disjoint : ∀ (q : ℚ) → ¬ (L q ∧ U q)
    located : ∀ {q r} → q < r → L q ∨ U r

open ℝ

------------------------------------------------------------------------
-- Construction

ℚ→ℝ : ℚ → ℝ
ℚ→ℝ q₀ = record 
  { L = λ r → r < q₀
  ; U = λ r → q₀ < r
  ; inhabited = q₀ - 1ℚ , q-1<q q₀ , q₀ + 1ℚ , q<q+1 q₀
  ; rounded = λ q r → 
    record 
      { to = ℚ.<-dense 
      ; from = λ{ (x , q<x , x<q₀) → ℚ.<-trans q<x x<q₀ } 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      } , 
    record 
      { to = λ q₀<r → let (z , q₀<z , z<r) = ℚ.<-dense q₀<r
                      in z , z<r , q₀<z 
      ; from = λ{ (x , q₀<x , x<r) → ℚ.<-trans  x<r  q₀<x} 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      }
  ; disjoint = λ{ q (q<q₀ , q₀<q) → ℚ.<-irrefl refl (ℚ.<-trans q<q₀ q₀<q) } 
  ; located = <-lemma q₀
  }

------------------------------------------------------------------------
-- Constants

0ℝ : ℝ
0ℝ = ℚ→ℝ 0ℚ

1ℝ : ℝ
1ℝ = ℚ→ℝ 1ℚ

------------------------------------------------------------------------
-- useful lemma

reverse-located : ∀ (x : ℝ) {a b : ℚ} → L x a → U x b → a < b
reverse-located x {a} {b} La Ub with ℚ.<-cmp a b 
... | tri< a<b _ _ = a<b
... | tri≈ _ refl _ = ⊥-elim (disjoint x a (La , Ub))
... | tri> _ _ a>b = ⊥-elim (disjoint x a (La , Ua))
  where Ua = Equivalence.from (proj₂ (rounded x a a)) (_ , a>b , Ub)


------------------------------------------------------------------------
-- Estimate a real within arbitary ε

refine : ∀ x a b → L x a → U x b → Σ[ (u , v) ∈ ℚ × ℚ ] (L x u ∧ U x v ∧ v - u ≡ (b - a) * ¾)
refine x a b La Ub = res
  where
  ε = b - a
  ε/4 = ε * ¼
  ε/2 = ε * ½
  u = a + ε/4
  v = b - ε/4
  a<b = reverse-located x La Ub
  ε>0 = a<b→0<b-a a<b
  ε/2>0 = ℚ.*-monoˡ-<-pos ½ ε>0
  ε/4>0 = ℚ.*-monoˡ-<-pos ¼ ε>0


  res : Σ[ (u , v) ∈ ℚ × ℚ ] (L x u ∧ U x v ∧ v - u ≡ (b - a) * ¾)
  res with located x (u<v a<b)
  ... | left Lu = (u , b) , Lu , Ub , eq
    where
    eq = begin
      b - (a + ε/4)     ≡⟨ cong (b +_) (ℚ.neg-distrib-+ a ε/4) ⟩
      b + (- a - ε/4)   ≡⟨ ℚ.+-assoc b (- a) (- ε/4) ⟨
      ε - ε/4           ≡⟨ eps-eq a<b ⟩
      ε * ¾             ∎ where open ≡-Reasoning
  ... | right Uv = (a , v) , La , Uv , eq
    where 
    eq = begin
      (b - ε/4) - a     ≡⟨ ℚ.+-assoc b (- ε/4) (- a) ⟩
      b + (- ε/4 - a)   ≡⟨ cong (b +_)  (ℚ.+-comm (- ε/4) (- a)) ⟩
      b + (- a - ε/4)   ≡⟨ ℚ.+-assoc b (- a) (- ε/4) ⟨
      ε - ε/4           ≡⟨ eps-eq a<b ⟩
      ε * ¾             ∎ where open ≡-Reasoning


refine-n : ∀ n x a b → L x a → U x b → Σ[ (u , v) ∈ ℚ × ℚ ] L x u ∧ U x v ∧ v - u ≡ (b - a) * (pow n ¾)
refine-n ℕ.zero x a b La Ub = _ , La , Ub , sym (ℚ.*-identityʳ (b - a))
refine-n (ℕ.suc n) x a b La Ub = 
  let ((u₁ , v₁) , Lu₁ , Uv₁ , eq₁) = refine-n n x a b La Ub
      ((u₂ , v₂) , Lu₂ , Uv₂ , eq₂) = refine x u₁ v₁ Lu₁ Uv₁
      eq₃ = let open ≡-Reasoning in begin
        v₂ - u₂                     ≡⟨ eq₂ ⟩
        (v₁ - u₁) * ¾               ≡⟨ cong (_* ¾) eq₁ ⟩
        (b - a) * pow n ¾ * ¾       ≡⟨ ℚ.*-assoc (b - a) (pow n ¾) ¾ ⟩
        (b - a) * (pow n ¾ * ¾)     ≡⟨ cong ((b - a) *_) (pow-r n) ⟨
        (b - a) * pow (ℕ.suc n) ¾   ∎
  in (u₂ , v₂) , Lu₂ , Uv₂ , eq₃


estimate : ∀ x {ε} → ε > 0ℚ → Σ[ (u , v) ∈ ℚ × ℚ ] L x u ∧ U x v ∧ v - u < ε
estimate x {ε} ε>0 = 
  let q , Lq , r , Ur = inhabited x
      ε₀ = r - q
      q<r = reverse-located x Lq Ur
      ε₀>0 = a<b→0<b-a q<r
      instance 
        ε-pos = ℚ.positive ε>0
        ε₀-pos = ℚ.positive ε₀>0
        ε₀-nonZero = ℚ.pos⇒nonZero ε₀
        1/ε₀-pos = ℚ.1/pos⇒pos ε₀
      ratio = ε ÷ ε₀
      instance ratio-pos = pos*pos⇒pos ε (1/ ε₀)
      n = refine-steps ratio
      ((u , v) , Lu , Uv , v-u=ε₀*¾^n) = refine-n n x q r Lq Ur
      v-u<ε : v - u < ε
      v-u<ε = let open ℚ.≤-Reasoning in (begin-strict
        v - u             ≡⟨ v-u=ε₀*¾^n ⟩
        ε₀ * (pow n ¾)    <⟨ ℚ.*-monoʳ-<-pos ε₀ (pow-log ratio) ⟩
        ε₀ * ratio        ≡⟨ cong (ε₀ *_) (ℚ.*-comm ε (1/ ε₀)) ⟩ 
        ε₀ * (1/ ε₀ * ε)  ≡⟨ ℚ.*-assoc  ε₀ (1/ ε₀) ε ⟨
        ε₀ * 1/ ε₀ * ε    ≡⟨ cong (_* ε) (ℚ.*-inverseʳ ε₀) ⟩ 
        1ℚ * ε            ≡⟨ ℚ.*-identityˡ ε ⟩ 
        ε                 ∎)

  in (u , v) , Lu , Uv , v-u<ε


------------------------------------------------------------------------
-- Ordering

data _≤ᵣ_ : ℝ → ℝ → Set₁ where
  *≤* : ∀ {x y} → (∀ {q} → L x q → L y q) → x ≤ᵣ y

data _<ᵣ_ : ℝ → ℝ → Set₁ where
  *<* : ∀ {x y} q → U x q → L y q → x <ᵣ y


------------------------------------------------------------------------
-- Addition and additive inverse

_+ᵣ_ : ℝ → ℝ → ℝ
v₁ +ᵣ v₂ = real L' U' inhabited' rounded' disjoint' located'
  where
  L' = λ q → ∃[ (r , s) ] (L v₁ r ∧ L v₂ s ∧ (q ≡ r + s))
  U' = λ q → ∃[ (r , s) ] (U v₁ r ∧ U v₂ s ∧ (q ≡ r + s))

  inhabited' = let (l₁ , L₁l₁ , r₁ , U₁r₁) = inhabited v₁
                   (l₂ , L₂l₂ , r₂ , U₂r₂) = inhabited v₂
               in l₁ + l₂ , ((l₁ , l₂) , L₁l₁ , L₂l₂ , refl) , 
                  r₁ + r₂ , ((r₁ , r₂) , U₁r₁ , U₂r₂ , refl)
                 
  rounded' : ∀ (q r : ℚ) → 
    L' q ⇔ (∃[ r ] q < r ∧ L' r) ∧
    U' r ⇔ (∃[ q ] q < r ∧ U' q)
  rounded' q r = 
    record 
      { to = λ{ ((a , b) , L₁a , L₂b , q=a+b) → 
                  let (r , a<r , L₁r) = Equivalence.to (proj₁ (rounded v₁ a a)) L₁a
                      (s , b<s , L₂s) = Equivalence.to (proj₁ (rounded v₂ b b)) L₂b
                      a+b<r+s = ℚ.+-mono-< a<r b<s
                      q<r+s = ℚ.≤-<-trans (ℚ.≤-reflexive q=a+b) a+b<r+s
                  in _ , q<r+s , _ , L₁r , L₂s , refl }
      ; from = λ{ (x , q<x , (a' , b') , L₁a' , L₂b' , x=a'+b') → 
                  let d = (x - q) * ½
                      a = a' - d
                      b = b' - d
                      0<d = ℚ.*-monoˡ-<-pos ½ (a<b→0<b-a q<x)
                      a<a' = 0<d→x-d<x a' 0<d
                      b<b' = 0<d→x-d<x b' 0<d
                      L₁a = Equivalence.from (proj₁ (rounded v₁ a a)) (a' , a<a' , L₁a')
                      L₂b = Equivalence.from (proj₁ (rounded v₂ b b)) (b' , b<b' , L₂b')
                      q=a+b = distrib-diff q x a' b' x=a'+b'
                  in (a , b) , L₁a , L₂b , q=a+b} 
      ; to-cong = λ{ refl → refl }
      ; from-cong = λ{ refl → refl } 
      } , 
    record 
      { to = λ{ ((a , b) , U₁a , U₂b , r=a+b) → 
                  let (p , p<a , U₁p) = Equivalence.to (proj₂ (rounded v₁ a a)) U₁a
                      (q , q<b , U₂q) = Equivalence.to (proj₂ (rounded v₂ b b)) U₂b
                      p+q<a+b = ℚ.+-mono-< p<a q<b
                      p+q<r = ℚ.<-≤-trans p+q<a+b (ℚ.≤-reflexive (sym r=a+b)) 
                  in _ , p+q<r , _  , U₁p , U₂q , refl }
      ; from = λ{ (x , x<r , (a' , b') , U₁a' , U₂b' , x=a'+b') → 
                  let d = (x - r) * ½ 
                      a = a' - d
                      b = b' - d
                      d<0 = ℚ.*-monoˡ-<-pos ½ (a<b→a-b<0 x<r)
                      a'<a = d<0→x<x-d a' d<0
                      b'<b = d<0→x<x-d b' d<0
                      U₁a = Equivalence.from (proj₂ (rounded v₁ a a)) (a' , a'<a , U₁a')
                      U₂b = Equivalence.from (proj₂ (rounded v₂ b b)) (b' , b'<b , U₂b')
                      r=a+b : r ≡ a + b
                      r=a+b = distrib-diff r x a' b' x=a'+b'
                  in (a , b) , U₁a , U₂b , r=a+b } 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      }
  
  disjoint' : ∀ (q : ℚ) → ¬ (L' q ∧ U' q)
  disjoint' q (((a , b) , L₁a , L₂b , q=a+b) , (c , d) , U₁c , U₂d , q=c+d) = ℚ.<⇒≢ q<q refl 
    where
    q<q = begin-strict
      q       ≡⟨ q=a+b ⟩
      a + b   <⟨ ℚ.+-monoˡ-< b (reverse-located v₁ L₁a U₁c) ⟩
      c + b   <⟨ ℚ.+-monoʳ-< c (reverse-located v₂ L₂b U₂d) ⟩
      c + d   ≡⟨ q=c+d ⟨
      q       ∎ where open ℚ.≤-Reasoning
    
  located' : ∀ {q r} → q < r → L' q ∨ U' r
  located' {q} {r} q<r = located-helper (estimate v₁ ε/2>0) (estimate v₂ ε/2>0)
    where
    ε = r - q
    ε/2 = ε * ½
    ε>0 = a<b→0<b-a q<r
    ε/2>0 : ε/2 > 0ℚ
    ε/2>0 = ℚ.positive⁻¹ ε/2
      where instance 
        _ = ℚ.positive ε>0
        _ = pos*pos⇒pos ε ½

    located-helper : (Σ[ (u , v) ∈ ℚ × ℚ ] L v₁ u ∧ U v₁ v ∧ v - u < (r - q) * ½) → 
      (Σ[ (u , v) ∈ ℚ × ℚ ] L v₂ u ∧ U v₂ v ∧ v - u < (r - q) * ½) → 
      L' q ∨ U' r
    located-helper ((a , b) , L₁a , U₁b , b-a<ε/2) ((c , d) , L₂c , U₂d , d-c<ε/2) 
      with q ℚ.<? a + c
    ...   | yes q<a+c = left (Equivalence.from (proj₁ (rounded' q q)) (_ , q<a+c , _ , L₁a , L₂c , refl))
    ...   | no q≮a+c = right (Equivalence.from (proj₂ (rounded' r r)) (_ , b+d<r , _ , U₁b , U₂d , refl))
        where
        y<ε/2+x : ∀ x y → y - x < ε/2 → y < ε/2 + x
        y<ε/2+x x y y-x<ε/2 = begin-strict
          y               ≡⟨ ℚ.+-identityʳ y ⟨
          y + 0ℚ          ≡⟨ cong (y +_) (ℚ.+-inverseˡ x) ⟨
          y + (- x + x)   ≡⟨ ℚ.+-assoc y (- x) x ⟨
          y - x + x       <⟨ ℚ.+-monoˡ-< x y-x<ε/2 ⟩
          ε/2 + x         ∎ where open ℚ.≤-Reasoning
        b+d<r = begin-strict
          b + d                   <⟨ ℚ.+-mono-< (y<ε/2+x a b b-a<ε/2) (y<ε/2+x c d d-c<ε/2) ⟩
          (ε/2 + a) + (ε/2 + c)   ≡⟨ cong (_+ (ε/2 + c)) (ℚ.+-comm ε/2 a) ⟩
          (a + ε/2) + (ε/2 + c)   ≡⟨ ℚ.+-assoc (a + ε/2) ε/2 c ⟨
          a + ε/2 + ε/2 + c       ≡⟨ cong (_+ c) (ℚ.+-assoc a ε/2 ε/2) ⟩
          a + (ε/2 + ε/2) + c     ≡⟨ cong (λ x → a + x + c) (split-half ε) ⟨
          a + ε + c               ≡⟨ cong (_+ c) (ℚ.+-comm a ε) ⟩
          ε + a + c               ≡⟨ ℚ.+-assoc ε a c ⟩
          ε + (a + c)             ≤⟨ ℚ.+-monoʳ-≤ ε (ℚ.≮⇒≥ q≮a+c) ⟩
          r - q + q               ≡⟨ ℚ.+-assoc r (- q) q ⟩
          r + (- q + q)           ≡⟨ cong (r +_) (ℚ.+-inverseˡ q) ⟩
          r + 0ℚ                  ≡⟨ ℚ.+-identityʳ r ⟩
          r                       ∎ where open ℚ.≤-Reasoning

-ᵣ_ : ℝ → ℝ
-ᵣ v = real L' U' inhabited' rounded' disjoint' located'
  where
  L' U' : ℚ → Set
  L' q =  U v (- q)
  U' q = L v (- q)
  
  inhabited' = let (x , Lx , y , Uy) = inhabited v
               in (- y) , subst (U v) (sym (neg-involutive y)) Uy , 
                  (- x) , subst (L v) (sym (neg-involutive x)) Lx

  rounded' : ∀ (q r : ℚ) → 
      L' q ⇔ (∃[ r ] q < r ∧ L' r) ∧
      U' r ⇔ (∃[ q ] q < r ∧ U' q)
  rounded' q r =
    record 
      { to = λ U-q → 
          let (x , x<-q , Ux) = Equivalence.to (proj₂ (rounded v (- q) (- q))) U-q 
              q<-x = subst (_< - x) (neg-involutive q) (ℚ.neg-antimono-< x<-q)
          in - x , q<-x , (subst (U v) (sym (neg-involutive x)) Ux) 
      ; from = λ{ (x , q<x , U-x) → 
          let -x<-q = ℚ.neg-antimono-< q<x
          in Equivalence.from (proj₂ (rounded v (- q) (- q))) (- x , -x<-q , U-x) } 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      } , 
    record 
      { to = λ L-r → 
          let (x , -r<x , Lx) = Equivalence.to (proj₁ (rounded v (- r) (- r))) L-r
              -x<r = subst (- x <_) (neg-involutive r) (ℚ.neg-antimono-< -r<x)
          in - x , -x<r , (subst (L v) (sym (neg-involutive x)) Lx)
      ; from = λ{ (x , x<r , L-x) → 
          let -r<-x = ℚ.neg-antimono-< x<r
          in Equivalence.from (proj₁ (rounded v (- r) (- r))) (- x , -r<-x , L-x) }
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      }
  
  disjoint' = λ{ q (U-q , L-q) → disjoint v (- q) (L-q , U-q) }

  located' : ∀ {q r} → q < r → L' q ∨ U' r
  located' {q} {r} q<r with located v (ℚ.neg-antimono-< q<r) 
  ... | left L-r = right L-r  
  ... | right U-q = left U-q      


-- _*ᵣ_ : ℝ → ℝ → ℝ
-- v₁ *ᵣ v₂ = real L' U' inhabited' rounded' disjoint' located'
--   where
--   L' = λ q → Σ[ (a , b , c , d) ∈ ℚ × ℚ × ℚ × ℚ ] (L v₁ a ∧ U v₁ b ∧ L v₂ c ∧ U v₂ d ∧ q < a * c ⊓ a * d ⊓ b * c ⊓ b * d)
--   U' = λ q → Σ[ (a , b , c , d) ∈ ℚ × ℚ × ℚ × ℚ ] (L v₁ a ∧ U v₁ b ∧ L v₂ c ∧ U v₂ d ∧ a * c ⊔ a * d ⊔ b * c ⊔ b * d < q)

--   inhabited' = let (a , L₁a , b , U₁b) = inhabited v₁
--                    (c , L₂c , d , U₂d) = inhabited v₂
--                    lo = a * c ⊓ a * d ⊓ b * c ⊓ b * d
--                    hi = a * c ⊔ a * d ⊔ b * c ⊔ b * d
--                in lo - 1ℚ , (_ , L₁a , U₁b , L₂c , U₂d , q-1<q lo) ,
--                   hi + 1ℚ , (_ , L₁a , U₁b , L₂c , U₂d , q<q+1 hi)
                  
--   rounded' : ∀ (q r : ℚ) → 
--     L' q ⇔ (∃[ r ] q < r ∧ L' r) ∧
--     U' r ⇔ (∃[ q ] q < r ∧ U' q)
--   rounded' q r = 
--     record 
--       { to = λ{ ((a , b , c , d) , L₁a , U₁b , L₂c , U₂d , q<lo) → 
--           let (a' , a<a' , L₁a') = Equivalence.to (proj₁ (rounded v₁ a a)) L₁a
--               (b' , b'<b , U₁b') = Equivalence.to (proj₂ (rounded v₁ b b)) U₁b
--               (c' , c<c' , L₂c') = Equivalence.to (proj₁ (rounded v₂ c c)) L₂c
--               (d' , d'<d , U₂d') = Equivalence.to (proj₂ (rounded v₂ d d)) U₂d
--               lo' = a' * c' ⊓ a' * d' ⊓ b' * c' ⊓ b' * d'
--           in {!   !} , {!   !} , {!   !} , L₁a' , U₁b' , L₂c' , U₂d' , {!   !} }
--       ; from = {!   !} 
--       ; to-cong = {!   !} 
--       ; from-cong = {!   !} 
--       } , 
--     record 
--       { to = {!   !} 
--       ; from = {!   !} 
--       ; to-cong = {!   !} 
--       ; from-cong = {!   !} 
--       }

--   disjoint' = {!   !} 
--   located' : ∀ {q r} → q < r → L' q ∨ U' r
--   located' {q} {r} q<r = {!   !}