module _ where

  open import combinators
  open import s
  open import sigma

  module w (A : Set) (B : pow A) where

    data fm : Set where
      mk : (a : A) → (B a → fm) → fm

    ex : { C : pow fm }→
         ( c : (a : A)→ (f : B a → fm) → ((b : B a)→ C (f b)) → C (mk a f) ) → 
         (z : fm) → C z
    ex {C} c (mk a f) = c a f (λ b → ex {C} c (f b))
    
    Ex : { D : Set₁ }→           -- large iterator
         ( c : (a : A)→ (f : B a → fm) → ((b : B a)→ D) → D ) → 
         (z : fm) → D
    Ex {D} c (mk a f) = c a f (λ b → Ex {D} c (f b)) 

    -- examples (not needed ...) destructors of elements of W A B
    pi0 : fm → A
    pi0 = ex {λ _ → A} (λ a _ _ → a)
    pi1 : (z : fm) → B (pi0 z) → fm 
    pi1 = ex {λ x → B (pi0 x)→ fm} (λ _ f _ → f)
    pt : pow fm → pow fm    -- predicate transformer
    pt P z = ( t : B (pi0 z)) → P (pi1 z t)

    private Desc : fm -> Set -- assigns to any tree an index set for its (not-necc proper) descendants
            Desc = Ex (λ a f x → s.fm (sigma.fm (B a) x))  -- 1 + proper descendants 
    private dest : (z : fm) -> Desc z -> fm      -- deindex
            dest   = ex {λ z → Desc z -> fm}
                        (λ a f x →
                             let xt : (b : B a) → Desc (f b) → fm
                                 xt = x
                             in
                             s.ex (sigma.fm (B a) (λ b → Desc (f b)))
                                  (mk a f)  -- Nothing (improper descendant)
                                  (sigma.ex (B a) (λ b → Desc (f b)) x {- x -}) -- just a pair 
                        )
    private Descp : fm -> Set -- assigns to any tree an index set for its proper descendants
            Descp = Ex (λ a f x → sigma.fm (B a) λ b → s.fm (x b))  -- 1 + proper descendants 
    private destp : (z : fm) -> Descp z -> fm      -- deindex
            destp   = ex {λ z → Descp z -> fm}
                        (λ a f x →
                             let xt : (b : B a) → Descp (f b) → fm
                                 xt = x
                                 H : (b : B a) → Set
                                 H b = s.fm (Descp (f b))  -- not necc. proper
                                 h : (b : B a) (z : H b) → fm
                                 h b = s.ex (Descp (f b)) (f b) (x b)
                             in sigma.ex (B a) H -- (λ b → s.fm (Descp (f b)))
                                h -- λ b → s.ex (Descp (f b)) (f b) (x b) 
                        )


    data Acc : pow fm where
      mka : (z : fm)→ pt Acc z → Acc z
    acc : (z : fm)→ Acc z  -- all elements of a W-type are accessible in this sense.
    acc z = let h : (a : A) (f : B a → fm) → ((b : B a) → Acc (f b)) → Acc (mk a f)
                h a f = mka (mk a f) 
             in ex h z 

    eta : {X : fm → fm → Set}→ ((z : fm) → X z z) → (z : fm) → X z (mk (pi0 z) (pi1 z))
    eta r = ex (λ a f _ → r (mk a f)) 

  module w*  ( A : Set ) ( A' : Set ) ( A* : rel A A') 
             ( B : A → Set ) ( B' : A' → Set )
             ( B* : (a : A) → (a' : A') → A* a a' → rel (B a) (B' a') )
    where
    open w A B public 
    open w A' B' public renaming (fm to fm'; mk to mk' ; ex to ex' ; Ex to Ex' ; pi0 to pi0' ; pi1 to pi1' ; eta to eta') 
                        hiding (pt ; Acc ; acc )
    data fm* : rel fm fm' where
      mk* : (a : A) (a' : A') (a* : A* a a') →
               (f : B a → fm) (f' : B' a' → fm') →
               (f* : (b : B a) (b' : B' a') (b* : B* a a' a* b b') → fm* (f b) (f' b'))
               → fm* (mk a f) (mk' a' f') 

    ex* : {D : (z : fm) (z' : fm') → pow (fm* z z') }→ 
          (d : (a : A) → (a' : A') → (a* : A* a a') →
                (f : B a → fm) → (f' : B' a' → fm') →
                (f* : (b : B a) → (b' : B' a') → (b* : B* a a' a* b b') → fm* (f b) (f' b')) →
                ( (b  : B a) (b' : B' a') (b* : B* a a' a* b b') → D (f b) (f' b') (f* b b' b*) 
                ) →
                D (mk a f) (mk' a' f') (mk* a a' a* f f' f*)) →
          (z : fm) (z' : fm') (z* : fm* z z') →
          D z z' z*
    ex* {D} d (mk' a f) (mk' a' f') (mk* a a' a* f f' f*)
       = d a a' a* f f' f*
           λ b b' b* → ex* {D} d (f b) (f' b') (f* b b' b*)

  module w-simple ( A : Set) (A* : rel A A)   -- discard A' and B' stuff.
                  ( B : A → Set) (B* : (a a' : A) → A* a a' → B a → B a' → Set)
    where
      open w A B public
      data fm* : rel fm fm where
        mk* : (a a' : A) (a* : A* a a') →
                 (f : B a → fm) (f' : B a' → fm) →
                 (f* : (b : B a) (b' : B a') (b* : B* a a' a* b b') → fm* (f b) (f' b'))
               → fm* (mk a f) (mk a' f') 

      ex* : {D : (z z' : fm) → pow (fm* z z') }→ 
            (d : (a a' : A) → (a* : A* a a') →
                 (f : B a → fm)→ (f' : B a' → fm) →
                 (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                 ( (b : B a) (b' : B a') (b* : B* a a' a* b b') →
                   D (f b) (f' b') (f* b b' b*)
                 ) →
                 D (mk a f) (mk a' f') (mk* a a' a* f f' f*)
            ) →
            (z z' : fm) → (z* : fm* z z') → D z z' z*
      ex* {D} d (mk _ _) (mk _ _) (mk* a a' a* f f' f*)
         = d a a' a* f f' f*
           λ b b' b* → ex* {D} d (f b) (f' b') (f* b b' b*)
        

  module w-in-model ( A : Set ) ( A* : rel A A) 
                    ( B : A → Set ) ( B* : (a a' : A)→ A* a a' → rel (B a) (B a')) 
    where
    open w-simple A A* B B* public
 -- open w* A A A* B B B* public
    module _ (C : pow fm)
             (C* : (z z' : fm)→ (z* : fm* z z')→ rel (C z) (C z'))
             (c : (a : A)→ (f : B a → fm) → ((b : B a)→ C (f b)) → C (mk a f))
             (c* : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                   (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                   ( (b : B a) (b' : B a') (b* : B* a a' a* b b') →
                      C* (f b) (f' b') (f* b b' b*) (ex {C} c (f b)) (ex {C} c (f' b'))
                   ) →
                   C* (mk a f) (mk a' f') (mk* a a' a* f f' f*)
                      (c a f (λ b → ex {C} c (f b))) (c a' f' (λ b → ex {C} c (f' b)))
             ) where
          h : (z : fm) → C z
          h = ex {C} c
          D : (z z' : fm)→ pow (fm* z z')
          D z z' z* = C* z z' z* (h z) (h z')
          d : (a a' : A) (a* : A* a a') (f : B a → fm) (f' : B a' → fm)
                (f* : (b : B a) (b' : B a') → B* a a' a* b b' → fm* (f b) (f' b')) →
                ((b : B a) (b' : B a') (b* : B* a a' a* b b') →
--                 C* (f b) (f' b') (f* b b' b*) (h (f b)) (h (f' b'))
                   D (f b) (f' b') (f* b b' b*)
                ) →
--                C* (mk a f) (mk a' f') (mk* a a' a* f f' f*)
--                   (c a f (λ b → h (f b))) (c a' f' (λ b → h (f' b)))
                  D (mk a f) (mk a' f') (mk* a a' a* f f' f*)
          d = c*
          h* :  (z z' : fm) (z* : fm* z z')→ D z z' z*
          h* = ex* {D} d 
