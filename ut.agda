open import bool
open import nat
open import pi
open import sigma
open import du

module _ where

  module univ where

    data fmU : Set
    exT : fmU → Set

    data fmU where
      boolhat : fmU
      nathat : fmU
      pihat  : (a : fmU) → (exT a → fmU) → fmU
      sihat  : (a : fmU) → (exT a → fmU) → fmU
      duhat  : (a b : fmU) → fmU

    exT boolhat = bool.fm 
    exT nathat = nat.fm
    exT (pihat a b) = pi.fm (exT a) (λ x → exT (b x))
    exT (sihat a b) = sigma.fm (exT a) (λ x → exT (b x))
    exT (duhat a b) = du.fm (exT a) (exT b)

    mutual 
     data fmU* : fmU → fmU → Set where
      bool= : fmU* boolhat boolhat
      nat= : fmU* nathat nathat
      pi=  : (a a' : fmU) → (a* : fmU* a a') → 
             (b : exT a → fmU) →
             (b' : exT a' → fmU) →
             (b* : (x : exT a) → (x' : exT a') →
                fmT* a a' a* x x' →  fmU* (b x) (b' x')) →
             fmU* (pihat a b) (pihat a' b')
      si=  : (a a' : fmU) → (a* : fmU* a a') → 
             (b : exT a → fmU) →
             (b' : exT a' → fmU) →
             (b* : (x : exT a) → (x' : exT a') →
                fmT* a a' a* x x' →  fmU* (b x) (b' x')) →
             fmU* (sihat a b) (sihat a' b')
      du=  : (a a' : fmU) → (a* : fmU* a a') →
             (b b' : fmU) → (b* : fmU* b b') →
             fmU* (duhat a b) (duhat a' b')
     fmT* : (u : fmU) → (u' : fmU)  → fmU* u u' → exT u → exT u' → Set
     fmT* boolhat boolhat bool= = bool.fm*   -- "equality" on bool
     fmT* nathat  nathat  nat=  = nat.fm*    -- "equality" on nat
     fmT* (pihat a b) (pihat a' b') (pi= a a' a* b b' b*)
        = let t : exT a → exT a' → Set
              t = fmT* a a' a*
              t' : (x : exT a) → (x' : exT a') →
                    fmT* a a' a* x x' → exT (b x) → exT (b' x') → Set 
              t' x x' x* = fmT* (b x) (b' x') (b* x x' x*)
              get : (A A' : Set) (A* : A → A' → Set) (B : A → Set) (B' : A' → Set)
                      (B* : (a : A) (a' : A') → A* a a' → B a → B' a' → Set) →
                      pi*.fm A A' A* B B' B* → pi*.fm' A A' A* B B' B* → Set 
              get = pi.pi*.fm*
          in get (exT a) (exT a') t 
                 (λ x → exT (b x)) (λ x → exT (b' x)) t'
     fmT* (sihat a b) (sihat a' b') (si= a a' a* b b' b*)
        = let t : exT a → exT a' → Set
              t = fmT* a a' a*
              t' : (x : exT a) → (x' : exT a') →
                    fmT* a a' a* x x' → exT (b x) → exT (b' x') → Set 
              t' x x' x* = fmT* (b x) (b' x') (b* x x' x*)
              get : (A A' : Set) (A* : A → A' → Set) (B : A → Set) (B' : A' → Set)
                      (B* : (a : A) (a' : A') → A* a a' → B a → B' a' → Set) →
                      sigma*.fm A A' A* B B' B* → sigma*.fm' A A' A* B B' B* → Set 
              get = sigma.sigma*.fm*
          in get (exT a) (exT a') t 
                 (λ x → exT (b x)) (λ x → exT (b' x)) t'
     fmT* (duhat a b) (duhat a' b') (du= a a' a* b b' b*)
        = let ta : exT a → exT a' → Set
              ta = fmT* a a' a*
              tb : exT b → exT b' → Set
              tb = fmT* b b' b*
              get : (A A' : Set) (A* : A → A' → Set) (B B' : Set) (B* : B → B' → Set) →
                      du*.fm A A' A* B B' B* → du*.fm' A A' A* B B' B* → Set
              get = du.du*.fm*
          in get (exT a) (exT a') ta (exT b) (exT b') tb 


