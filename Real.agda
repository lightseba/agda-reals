{-# OPTIONS --safe #-}

module Real where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _<_; _≤_; _÷_; _+_; _-_; -_; _*_; 1/_; 1ℚ; 0ℚ; ½; _⊔_; _⊓_)
open import Data.Rational.Properties as ℚ using (<-cmp)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst; module ≡-Reasoning)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; yes; no)

open import Logic using (_∨_; _∧_; left; right; _,_; proj₁; proj₂)
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
  ; rounded = λ _ _ → 
    record 
      { to = ℚ.<-dense 
      ; from = λ{ (_ , q<x , x<q₀) → ℚ.<-trans q<x x<q₀ } 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      } , 
    record 
      { to = λ q₀<r → let (z , q₀<z , z<r) = ℚ.<-dense q₀<r
                      in z , z<r , q₀<z 
      ; from = λ{ (_ , q₀<x , x<r) → ℚ.<-trans  x<r  q₀<x} 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      }
  ; disjoint = λ{ _ (q<q₀ , q₀<q) → ℚ.<-irrefl refl (ℚ.<-trans q<q₀ q₀<q) } 
  ; located = <-weak-linearity q₀
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
reverse-located x {a} {b} La Ub with <-cmp a b 
... | tri< a<b _ _ = a<b
... | tri≈ _ refl _ = ⊥-elim (disjoint x a (La , Ub))
... | tri> _ _ a>b = ⊥-elim (disjoint x a (La , Ua))
  where Ua = Equivalence.from (proj₂ (rounded x a a)) (_ , a>b , Ub)


------------------------------------------------------------------------
-- Estimate a real within arbitary ε

private
  refine : ∀ x a b → L x a → U x b → Σ[ (u , v) ∈ ℚ × ℚ ] (L x u ∧ U x v ∧ v - u ≡ (b - a) * ¾)
  refine x a b La Ub = res
    where
    ε = b - a
    ε/4 = ε * ¼
    u = a + ε/4
    v = b - ε/4
    a<b = reverse-located x La Ub

    res : Σ[ (u , v) ∈ ℚ × ℚ ] (L x u ∧ U x v ∧ v - u ≡ (b - a) * ¾)
    res with located x (u<v a<b)
    ... | left Lu = (u , b) , Lu , Ub , eq
      where
      eq = begin
        b - (a + ε/4)     ≡⟨ cong (b +_) (ℚ.neg-distrib-+ a ε/4) ⟩
        b + (- a - ε/4)   ≡⟨ ℚ.+-assoc b (- a) (- ε/4) ⟨
        ε - ε/4           ≡⟨ eps-eq ε ⟩
        ε * ¾             ∎ where open ≡-Reasoning
    ... | right Uv = (a , v) , La , Uv , eq
      where 
      eq = begin
        (b - ε/4) - a     ≡⟨ ℚ.+-assoc b (- ε/4) (- a) ⟩
        b + (- ε/4 - a)   ≡⟨ cong (b +_)  (ℚ.+-comm (- ε/4) (- a)) ⟩
        b + (- a - ε/4)   ≡⟨ ℚ.+-assoc b (- a) (- ε/4) ⟨
        ε - ε/4           ≡⟨ eps-eq ε ⟩
        ε * ¾             ∎ where open ≡-Reasoning


  refine-n : ∀ n x a b → L x a → U x b → Σ[ (u , v) ∈ ℚ × ℚ ] L x u ∧ U x v ∧ v - u ≡ (b - a) * (pow n ¾)
  refine-n zero _ a b La Ub = _ , La , Ub , sym (ℚ.*-identityʳ (b - a))
  refine-n (suc n) x a b La Ub = 
    let ((u₁ , v₁) , Lu₁ , Uv₁ , eq₁) = refine-n n x a b La Ub
        ((u₂ , v₂) , Lu₂ , Uv₂ , eq₂) = refine x u₁ v₁ Lu₁ Uv₁
        eq₃ = let open ≡-Reasoning in (begin
          v₂ - u₂                     ≡⟨ eq₂ ⟩
          (v₁ - u₁) * ¾               ≡⟨ cong (_* ¾) eq₁ ⟩
          (b - a) * pow n ¾ * ¾       ≡⟨ ℚ.*-assoc (b - a) (pow n ¾) ¾ ⟩
          (b - a) * (pow n ¾ * ¾)     ≡⟨ cong ((b - a) *_) (ℚ.*-comm (pow n ¾) ¾) ⟩
          (b - a) * pow (suc n) ¾   ∎)
    in (u₂ , v₂) , Lu₂ , Uv₂ , eq₃


estimate : ∀ x ε .{{_ : ℚ.Positive ε}} → ∃[ (u , v) ] L x u ∧ U x v ∧ v - u < ε
estimate x ε = 
  let q , Lq , r , Ur = inhabited x
      ε₀ = r - q
      q<r = reverse-located x Lq Ur
      ε₀>0 = a<b→0<b-a q<r
      instance 
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

_#ᵣ_ : ℝ → ℝ → Set₁
x #ᵣ y = (x <ᵣ y) ∨ (y <ᵣ x)

_≰ᵣ_ : ℝ → ℝ → Set₁
x ≰ᵣ y = ¬ (x ≤ᵣ y)

_≮ᵣ_ : ℝ → ℝ → Set₁
x ≮ᵣ y = ¬ (x <ᵣ y)

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
                      (s , b<s , L₂s) = Equivalence.to (proj₁ (rounded v₂ b b)) L₂b -- agda-unused doesn't see r
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
                      (q , q<b , U₂q) = Equivalence.to (proj₂ (rounded v₂ b b)) U₂b -- agda-unused bug on q
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
  
  disjoint' : ∀ q → ¬ (L' q ∧ U' q)
  disjoint' q (((a , b) , L₁a , L₂b , q=a+b) , (c , d) , U₁c , U₂d , q=c+d) = ℚ.<⇒≢ q<q refl 
    where
    q<q = begin-strict
      q       ≡⟨ q=a+b ⟩
      a + b   <⟨ ℚ.+-monoˡ-< b (reverse-located v₁ L₁a U₁c) ⟩
      c + b   <⟨ ℚ.+-monoʳ-< c (reverse-located v₂ L₂b U₂d) ⟩
      c + d   ≡⟨ q=c+d ⟨
      q       ∎ where open ℚ.≤-Reasoning
    
  located' : ∀ {q r} → q < r → L' q ∨ U' r
  located' {q} {r} q<r = located-helper (estimate v₁ ε/2) (estimate v₂ ε/2)
    where
    ε = r - q
    ε/2 = ε * ½
    instance 
      ε-pos = ℚ.positive (a<b→0<b-a q<r)
      ε/2-pos = pos*pos⇒pos ε ½

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
  located' q<r with located v (ℚ.neg-antimono-< q<r) 
  ... | left L-r = right L-r  
  ... | right U-q = left U-q      

_*ᵣ_ : ℝ → ℝ → ℝ
v₁ *ᵣ v₂ = real L' U' inhabited' rounded' disjoint' located'
  where
  *-lo : ℚ → ℚ → ℚ → ℚ → ℚ
  *-lo a b c d = (a * c) ⊓ (a * d) ⊓ (b * c) ⊓ (b * d)
  *-hi : ℚ → ℚ → ℚ → ℚ → ℚ
  *-hi a b c d = (a * c) ⊔ (a * d) ⊔ (b * c) ⊔ (b * d)

  L' = λ q → Σ[ (a , b , c , d) ∈ ℚ × ℚ × ℚ × ℚ ] (L v₁ a ∧ U v₁ b ∧ L v₂ c ∧ U v₂ d ∧ q < *-lo a b c d)
  U' = λ q → Σ[ (a , b , c , d) ∈ ℚ × ℚ × ℚ × ℚ ] (L v₁ a ∧ U v₁ b ∧ L v₂ c ∧ U v₂ d ∧ *-hi a b c d < q)

  inhabited' = let (a , L₁a , b , U₁b) = inhabited v₁
                   (c , L₂c , d , U₂d) = inhabited v₂
                   lo = *-lo a b c d
                   hi = *-hi a b c d
               in lo - 1ℚ , (_ , L₁a , U₁b , L₂c , U₂d , q-1<q lo) ,
                  hi + 1ℚ , (_ , L₁a , U₁b , L₂c , U₂d , q<q+1 hi)
                  
  rounded' : ∀ (q r : ℚ) → 
    L' q ⇔ (∃[ r ] q < r ∧ L' r) ∧
    U' r ⇔ (∃[ q ] q < r ∧ U' q)
  rounded' q r = 
    record 
      { to = λ{ ((a , b , c , d) , L₁a , U₁b , L₂c , U₂d , q<lo) → 
          let (r , q<r , r<lo) = ℚ.<-dense q<lo
          in _ , q<r , _ , L₁a , U₁b , L₂c , U₂d , r<lo }
      ; from = λ{ (r , q<r , (a , b , c , d) , L₁a , U₁b , L₂c , U₂d , r<lo) → 
          let q<lo = ℚ.<-trans q<r  r<lo
          in _ , L₁a , U₁b , L₂c , U₂d , q<lo }
      ; to-cong = λ{ refl → refl }
      ; from-cong = λ{ refl → refl } 
      } , 
    record 
      { to = λ{ ((a , b , c , d) , L₁a , U₁b , L₂c , U₂d , hi<r) → 
          let (q , hi<q , q<r) = ℚ.<-dense hi<r
          in _ , q<r , _ , L₁a , U₁b , L₂c , U₂d , hi<q } 
      ; from = λ{ (q , q<r , (a , b , c , d) , L₁a , U₁b , L₂c , U₂d , hi<q) → 
          let hi<r = ℚ.<-trans hi<q q<r 
          in _ , L₁a , U₁b , L₂c , U₂d , hi<r } 
      ; to-cong = λ{ refl → refl } 
      ; from-cong = λ{ refl → refl } 
      }

  disjoint' : ∀ q → ¬ (L' q ∧ U' q)
  disjoint' q 
    (((a₁ , b₁ , c₁ , d₁) , L₁a₁ , U₁b₁ , L₂c₁ , U₂d₁ , q<lo₁) , 
    ((a₂ , b₂ , c₂ , d₂) , L₁a₂ , U₁b₂ , L₂c₂ , U₂d₂ , q>hi₂)) = ℚ.<-irrefl refl q<q
    where
    a₁<b₁ = reverse-located v₁ L₁a₁ U₁b₁
    a₁<b₂ = reverse-located v₁ L₁a₁ U₁b₂
    a₂<b₁ = reverse-located v₁ L₁a₂ U₁b₁
    a₂<b₂ = reverse-located v₁ L₁a₂ U₁b₂

    a₁<b₁⊓b₂ = <-join-⊓ a₁<b₁ a₁<b₂
    a₂<b₁⊓b₂ = <-join-⊓ a₂<b₁ a₂<b₂
    a₁⊔a₂<b₁⊓b₂ = >-join-⊔ a₁<b₁⊓b₂ a₂<b₁⊓b₂
    
    c₁<d₁ = reverse-located v₂ L₂c₁ U₂d₁
    c₁<d₂ = reverse-located v₂ L₂c₁ U₂d₂
    c₂<d₁ = reverse-located v₂ L₂c₂ U₂d₁
    c₂<d₂ = reverse-located v₂ L₂c₂ U₂d₂

    c₁<d₁⊓d₂ = <-join-⊓ c₁<d₁ c₁<d₂
    c₂<d₁⊓d₂ = <-join-⊓ c₂<d₁ c₂<d₂
    c₁⊔c₂<d₁⊓d₂ = >-join-⊔ c₁<d₁⊓d₂ c₂<d₁⊓d₂
    
    a' = a₁ ⊔ a₂
    b' = b₁ ⊓ b₂
    c' = c₁ ⊔ c₂
    d' = d₁ ⊓ d₂
    lo₁ = *-lo a₁ b₁ c₁ d₁
    hi₂ = *-hi a₂ b₂ c₂ d₂
    lo' = *-lo a' b' c' d'
    hi' = *-hi a' b' c' d'

    lo₁≤lo' : lo₁ ≤ lo'
    lo₁≤lo' = {!   !}

    hi'≤hi₂ : hi' ≤ hi₂
    hi'≤hi₂ = {!   !}

    lo'≤hi' : lo' ≤ hi'
    lo'≤hi' = ac∙ad∙bc∙bd
      where
      ac∙ad = ℚ.p⊓q≤p⊔q (a' * c') (a' * d')
      ac∙ad∙bc = ⊓-⊔-mono-≤ ac∙ad ℚ.≤-refl
      ac∙ad∙bc∙bd = ⊓-⊔-mono-≤ ac∙ad∙bc ℚ.≤-refl 

    q<q : q < q
    q<q = begin-strict
      q   <⟨ q<lo₁ ⟩
      lo₁ ≤⟨ lo₁≤lo' ⟩
      lo' ≤⟨ lo'≤hi' ⟩
      hi' ≤⟨ hi'≤hi₂ ⟩
      hi₂ <⟨ q>hi₂ ⟩
      q   ∎ where open ℚ.≤-Reasoning
    
    -- res : ⊥
    -- res with  ℚ.<-cmp lo₁ 0ℚ |  ℚ.<-cmp hi₂ 0ℚ
    -- ... | tri< lo₁<0 _ _ | res2 = {!   !}
    -- ... | tri≈  b _ | res2 = {!   !}
    -- ... | tri> _ _ lo₁>0 | res2 = {!   !}

    -- res : ⊥
    -- res with ℚ.<-dense a₁⊔a₂<b₁⊓b₂ | ℚ.<-dense c₁⊔c₂<d₁⊓d₂
    -- ... | x , a₁⊔a₂<x , x<b₁⊓b₂ | y , c₁⊔c₂<y , y<d₁⊓d₂ 
    --   with ℚ.<-cmp x 0ℚ | ℚ.<-cmp y 0ℚ
    -- ... | tri≈ _ refl _ | _ = {!   !}
    -- ... | tri< x<0 _ _ | _ = {!   !}
    -- ... | tri> _ _ x>0 | _ = {!   !}
    
  located' : ∀ {q r} → q < r → L' q ∨ U' r
  located' {q} {r} q<r = {!   !}
 