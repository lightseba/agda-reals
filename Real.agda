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
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary using (yes; no; Dec)

open import Logic using (_∨_; _∧_; left; right; _,_; swap; proj₁; proj₂)
open import RealLemmas

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

reverse-located : ∀ (x : ℝ) {a b : ℚ} → L x a → U x b → a < b
reverse-located x {a} {b} La Ub with a ℚ.<? b | b ℚ.<? a
... | yes a<b | _ = a<b
... | no ¬a<b | yes b<a = ⊥-elim (disjoint x a (La , Ua))
  where
  Ua = Equivalence.from (proj₂ (rounded x a a)) (_ , b<a , Ub)
... | no ¬a<b | no ¬b<a = ⊥-elim (disjoint x a (La , Ua))
  where
  b=a = ℚ.≤-antisym (ℚ.≮⇒≥ ¬a<b) (ℚ.≮⇒≥ ¬b<a)
  Ua = subst (U x) b=a Ub

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

0ℝ : ℝ
0ℝ = ℚ→ℝ 0ℚ

1ℝ : ℝ
1ℝ = ℚ→ℝ 1ℚ

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
      b + (- a - ε/4)   ≡⟨ sym (ℚ.+-assoc b (- a) (- ε/4)) ⟩
      ε - ε/4           ≡⟨ eps-eq a<b ⟩
      ε * ¾             ∎
      where open ≡-Reasoning
  ... | right Uv = (a , v) , La , Uv , eq
    where 
    eq = begin
      (b - ε/4) - a     ≡⟨ ℚ.+-assoc b (- ε/4) (- a) ⟩
      b + (- ε/4 - a)   ≡⟨ cong (b +_)  (ℚ.+-comm (- ε/4) (- a)) ⟩
      b + (- a - ε/4)   ≡⟨ sym (ℚ.+-assoc b (- a) (- ε/4)) ⟩
      ε - ε/4           ≡⟨ eps-eq a<b ⟩
      ε * ¾             ∎
      where open ≡-Reasoning


refine-n : ∀ n x a b → L x a → U x b → Σ[ (u , v) ∈ ℚ × ℚ ] L x u ∧ U x v ∧ v - u ≡ (b - a) * (pow n ¾)
refine-n ℕ.zero x a b La Ub = _ , La , Ub , sym (ℚ.*-identityʳ (b - a))
refine-n (ℕ.suc n) x a b La Ub = 
  let ((u₁ , v₁) , Lu₁ , Uv₁ , eq₁) = refine-n n x a b La Ub
      ((u₂ , v₂) , Lu₂ , Uv₂ , eq₂) = refine x u₁ v₁ Lu₁ Uv₁
      eq₃ = let open ≡-Reasoning in begin
        v₂ - u₂                     ≡⟨ eq₂ ⟩
        (v₁ - u₁) * ¾               ≡⟨ cong (_* ¾) eq₁ ⟩
        (b - a) * pow n ¾ * ¾       ≡⟨ ℚ.*-assoc (b - a) (pow n ¾) ¾ ⟩
        (b - a) * (pow n ¾ * ¾)     ≡⟨ cong ((b - a) *_) (sym (pow-r n)) ⟩
        (b - a) * pow (ℕ.suc n) ¾   ∎
  in (u₂ , v₂) , Lu₂ , Uv₂ , eq₃


bench-estimate : ∀ x {ε} → ε > 0ℚ → Σ[ (u , v) ∈ ℚ × ℚ ] L x u ∧ U x v ∧ v - u < ε
bench-estimate x {ε} ε>0 = 
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

  in (u , v) , Lu , Uv , v-u<ε -- uncomment this line
